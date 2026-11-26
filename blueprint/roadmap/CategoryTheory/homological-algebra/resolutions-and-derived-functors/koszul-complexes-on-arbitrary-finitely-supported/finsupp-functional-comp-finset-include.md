# Finite-coordinate inclusion preserves the coefficient functional

Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For a finite subset s of I, composing
x_a with Finsupp.finsetInclude R s : (s → R) →ₗ[R] (I →₀ R) equals familyFunctional R (fun i :
s => a i.val). Thus the restricted finite family has the same functional values.
