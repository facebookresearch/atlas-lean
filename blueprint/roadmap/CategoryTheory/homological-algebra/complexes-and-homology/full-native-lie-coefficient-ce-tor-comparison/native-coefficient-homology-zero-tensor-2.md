# The empty coefficient class maps to its scalar-unit balanced class

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. For m : M, the H₀ class of the empty exterior word ⊗ m maps under
nativeCoefficientHomologyZeroTensorIso to Balanced.mk R U N T₀ m (ULift.up 1).
