# Any projective resolution of the trivial module compares by homotopy equivalence

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. For Q : ProjectiveResolution T₀,
envelopingResolutionHomotopyEquivOfProjective gives HomotopyEquiv (envelopingComplex R L)
Q.complex by resolution comparison.
