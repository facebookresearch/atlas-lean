# Degree-zero Lie coefficient homology is the trivial balanced tensor

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. nativeCoefficientHomologyZeroTensorIso identifies H₀(CE(L,M)) with
ModuleCat.BalancedTensor.functor R U N applied to T₀, using coefficient recovery and the
coinvariant/unit tensor comparison.
