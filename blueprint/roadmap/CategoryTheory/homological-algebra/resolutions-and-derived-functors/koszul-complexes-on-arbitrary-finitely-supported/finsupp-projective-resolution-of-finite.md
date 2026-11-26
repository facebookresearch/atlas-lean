# Finite weak regularity gives an arbitrary-coordinate projective resolution

Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Assume that for every n : ℕ and
injective f : Fin n → I, the list [a_(f 0), …, a_(f(n−1))] is weakly regular over R, meaning
each coefficient acts injectively on the quotient by its predecessors. For R : Type u and I :
Type v, the complex finsuppComplex R a, with its quotient augmentation and projective exterior
terms, defines a ProjectiveResolution of ModuleCat.of R (ULift.{max u v} (R ⧸ Ideal.span
(Set.range a))).
