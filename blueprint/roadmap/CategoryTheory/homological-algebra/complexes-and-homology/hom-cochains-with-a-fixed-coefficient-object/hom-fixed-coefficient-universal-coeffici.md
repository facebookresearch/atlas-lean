# Hom Fixed Coefficient Universal Coefficient Sequence

Let `C : Type u` be an abelian category with morphisms in universe `v` and
`HasExt.{w} C`. Let `P : ChainComplex C ℤ`, let `M : C`, and let `n : ℤ` be arbitrary.
Assume that, **for every integer `p`**, both

- `P.X p` is projective;
- `Abelian.image (P.d p (p - 1))` is projective.

Write \(P_p=P.X\,p\), \(H_p(P)=P.\mathrm{homology}\,p\), and
\(K=\operatorname{Hom}_C(P,M)\). The cochain group of \(K\) in degree \(p\) is
\(\operatorname{Hom}_C(P_p,M)\), with differential
\(a\mapsto a\circ d_{p+1}\), given by positive precomposition.

The universal coefficient sequence is

\[
0\longrightarrow \operatorname{Ext}^{1}_C(H_{n-1}(P),M)
\xrightarrow{\iota} H^{n}(K)
\xrightarrow{\rho} \operatorname{Hom}_C(H_n(P),M)
\longrightarrow 0.
\]

In Lean, the Ext term is lifted by `AddCommGrpCat.uliftFunctor.{v, w}` and the
middle and right terms by `AddCommGrpCat.uliftFunctor.{w, v}`. Thus all three
terms belong to `AddCommGrpCat.{max v w}`; the object, morphism, and Ext
universes remain independent.

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
\(\bar a\circ\pi_n=a\circ i_n\). In Lean the second map is exactly
`AddCommGrpCat.uliftFunctor.{w, v}.map (homFixedCoefficientRestriction P M n)`.

The declaration constructs these three terms and maps as a short complex.
Their short exactness is proved by
`homFixedCoefficientUniversalCoefficientSequence_shortExact`.
