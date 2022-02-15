-- Basic definition of a group (G, ⬝).
class group (G : Type*) :=
  (mul : G → G → G)
  (mul_assoc : ∀ a b c : G, (mul a (mul b c)) = (mul (mul a b) c))
  (id : G)
  (id_mul : ∀ a : G, (mul id a) = a)
  (mul_id : ∀ a : G, (mul a id) = a)
  (inv : G → G)
  (mul_inv : ∀ a : G, (mul a (inv a)) = id)
  (inv_mul : ∀ a : G, (mul (inv a) a) = id)
  
infix ` ⬝ `:65 := group.mul

-- The following theorems are simple rewrites that are just needed
-- because I don't know how to make the infix operator `⬝` work...

theorem int.my_add_assoc : ∀ a b c : ℤ, (a + (b + c)) = ((a + b) + c) := begin
  intros,
  rw int.add_assoc,
end

theorem int.my_zero_add : ∀ a : ℤ, (0 + a) = a := begin
  intros,
  rw int.zero_add,
end

theorem int.my_add_zero : ∀ a : ℤ, (a + 0) = a := begin
  intros,
  rw int.add_zero,
end

-- Basically, a proof that ℤ forms a group under addition, with
-- 0 as the identity element and (-a) as the inverse of a.
instance : group ℤ := {
  mul := int.add,
  mul_assoc := int.my_add_assoc,
  id := int.zero,
  id_mul := int.my_zero_add,
  mul_id := int.my_add_zero,
  inv := λ a : ℤ, -a,
  mul_inv := int.add_right_neg,
  inv_mul := int.add_left_neg,
}
