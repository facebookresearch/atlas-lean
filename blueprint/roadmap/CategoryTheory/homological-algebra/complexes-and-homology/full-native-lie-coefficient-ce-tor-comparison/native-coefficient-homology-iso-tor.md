# Free Lie carriers make every coefficient homology degree compute enveloping Tor

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Put H = max u v v' w and let M : LieModuleCat.{H} R L. Let N be its right U-representation,
with op(ι(x)) • m = −⁅x,m⁆. Assume Module.Free R L. For n : ℕ, nativeCoefficientHomologyIsoTor
identifies H_n(CE(L,M)) with the n-th left-derived functor of X ↦ Balanced(R,U,N,X), evaluated
at liftedEnvelopingTrivial in height H.
