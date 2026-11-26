# Exterior-coordinate transport induces an isomorphism on each homology degree

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let K be an ℕ-indexed R-module chain complex in universe max u v and e_n : K.X n ≅
⋀[R]^n L degreewise coordinates. For every n : ℕ, the complex isomorphism with the
conjugated-boundary exterior model induces K.homology n ≅ (ChainData.ofComplex R L K
e).complex.homology n. Its forward map is homologyMap (ChainData.ofComplexIso R L K e).hom n.
