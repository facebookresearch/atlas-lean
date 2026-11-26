# Right enveloping representation followed by left recovery preserves Lie coefficients

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. nativeRightCoefficientsIso : M ≅ rightCoefficients R L N uses
identity carrier maps in both directions. The double negative generator action recovers the
given Lie action, and the represented ground scalar action equals the R-action of M.
