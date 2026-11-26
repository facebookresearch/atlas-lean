# The Koszul complex on an arbitrary free coordinate module

Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Define finsuppComplex R a as the
exterior Koszul complex with degree-n term ⋀[R]^n (I →₀ R) and boundary given by contraction
with x_a. For R : Type u and I : Type v it lies in ChainComplex (ModuleCat.{max u v} R) ℕ.
