# Derived right-tensor naturality gives the coefficient Tor map

Let R be commutative, L an R-Lie algebra and U its enveloping algebra. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ and g : N ⟶ N' be a right-module morphism. Let T₀ = envelopingTrivialObject
R L be the lifted scalar module with U-action through augmentation. For n : ℕ,
rightEnvelopingTorCoefficientMap is the component at T₀ of NatTrans.leftDerived
(rightTensorCoefficientTransformation g) n. It maps Tor_n^U(N,T₀) to Tor_n^U(N',T₀), with Tor
defined by the fixed-right balanced tensor left-derived functor.
