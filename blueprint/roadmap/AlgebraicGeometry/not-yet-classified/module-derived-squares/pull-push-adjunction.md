# Pull Push Adjunction

An adjunction $Lf^* \dashv Rf_*$ between the total derived pullback and direct image along a
morphism of schemes $f : X \to Y$ (assumed to exist: `HasDerivedPullbacks`,
`HasDerivedPushforwards`), whose unit is normalized by the ordinary unit: for every cochain complex
$K$ of $\mathcal{O}_Y$-modules such that the canonical map $Lf^*(QK) \to Q(f^*K)$ is an
isomorphism, the unit at $QK$ is `normalizedUnit f K h`, the composite of the localized termwise
unit $QK \to Q(f_*f^*K)$, the canonical map $Q(f_*f^*K) \to Rf_*(Q(f^*K))$ and $Rf_*$ of the
inverse of that isomorphism. Here $Q$ is the localization functor and $f^*$, $f_*$ act termwise.
