# Coordinate-wedge boundaries use signed coefficient deletion

Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For n : ℕ and any f : Fin (n + 1) → I,
write e_i = Finsupp.single i 1. Then d_x(n)(e_(f 0) ∧ … ∧ e_(f n)) = ∑ j : Fin (n + 1), ((−1 :
R)^j * a_(f j)) • (⋀ q : Fin n, e_(f(j.succAbove q))). The formula holds for every tuple, with
the undeleted coordinates in their original order.
