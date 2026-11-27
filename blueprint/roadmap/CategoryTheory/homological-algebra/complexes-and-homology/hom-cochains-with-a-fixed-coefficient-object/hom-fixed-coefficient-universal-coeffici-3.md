# The fixed-coefficient universal coefficient short exact sequence

Let C be an abelian category with objects in universe u and morphisms in universe v, P an
integer-indexed chain complex, M an object, and n an integer. Suppose the groups Ext¹_C(-,-) are
available in a universe w independent of C's object and morphism universes. Assume that Pₚ and
im(dₚ : Pₚ → Pₚ₋₁) are projective for every integer p. For every integer n there is a short
exact sequence 0 → Ext¹_C(Hₙ₋₁(P),M) → Hⁿ Hom(P,M) → Hom_C(Hₙ(P),M) → 0. The first arrow is the
positive Yoneda-extension injection and the second is canonical cycle restriction followed by
homology descent. Canonical lifts place all groups in universe max(v,w); no support bound on P
is assumed.

## Canonical maps

The injection \(\iota\) is constructed from the Yoneda extension of the
boundary–cycle–homology short exact sequence

\[
0\longrightarrow \operatorname{im}(d_n)
\longrightarrow Z_{n-1}(P)
\longrightarrow H_{n-1}(P)\longrightarrow 0.
\]

Its positive extension classes are sent to the cohomology classes obtained
from the inclusion of the outgoing-image Hom complex. Concretely, if
`S = homUniversalCoefficientSequenceEngine P (single M 0) n hP hI` and
`c = homFixedCoefficientUCTCoordinates P M n`, the first map is
`c.1.inv ≫ S.f ≫ c.2.1.hom`. The coordinate change fixes the positive Ext-class
normalization, as described by
`homFixedCoefficientUniversalCoefficientSequence_left_representative`.

The map \(\rho\) sends the class of a cocycle \(a:P_n\to M\) to the induced
map \(H_n(P)\to M\): restrict \(a\) to \(Z_n(P)\) and descend modulo boundaries.
If \(\pi_n:Z_n(P)\to H_n(P)\) and \(i_n:Z_n(P)\to P_n\) are the homology
projection and cycle inclusion, its value \(\bar a\) satisfies
\(\bar a\circ\pi_n=a\circ i_n\). The second map is this canonical cycle restriction,
transported to the common universe of the three abelian groups.

The theorem `homFixedCoefficientUniversalCoefficientSequence_shortExact`
proves that the first map is a monomorphism, the second map is an epimorphism,
and the image of the first is the kernel of the second. The canonical coordinate isomorphism identifies this short complex with the
Ext/Hom universal coefficient sequence.
