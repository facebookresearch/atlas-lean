# Hom Universal Coefficient Sequence Engine short Exact

Let `C : Type u` be an abelian category with morphisms in universe `v`.
Let `P : ChainComplex C ℤ`, let `Q : CochainComplex C ℤ`, and let `n : ℤ` be arbitrary.
Assume that, **for every integer `p`**, both

- `P.X p` is projective;
- `Abelian.image (P.d p (p - 1))` is projective.

Write \(K=\texttt{homCochainComplex}\ P\ Q\). This is the full Hom cochain
complex: its degree-\(m\) group is
\(\prod_{p\in\mathbb Z}\operatorname{Hom}_C(P_p,Q^{m-p})\).
Both given differentials are retained. In physical degree coordinates,

\[
(\delta^m a)_p
= a_{p-1}\circ d^P_p
  +(-1)^{m+1}d^Q_{m-p}\circ a_p.
\]

The short exact sequence is

\[
0\longrightarrow
\prod_{p\in\mathbb Z}\operatorname{Ext}^{1}_C(H_p(P),H^{n-1-p}(Q))
\xrightarrow{\iota} H^n(K)
\xrightarrow{\rho}
\prod_{p\in\mathbb Z}\operatorname{Hom}_C(H_p(P),H^{n-p}(Q))
\longrightarrow 0.
\]

All products range over the entire set of integer degrees, with no
finite-support or boundedness condition.

## Canonical maps

The short exact sequence of complexes

\[
0\longrightarrow \operatorname{Hom}(I(P),Q)
\longrightarrow K\longrightarrow \operatorname{Hom}(Z(P),Q)
\longrightarrow 0
\]

is `homCyclesSequence P Q`. Here \(Z(P)\) has terms \(Z_p(P)\) and zero
differential, and \(I(P)\) has terms \(\operatorname{im}(d^P_p)\) and zero
differential. Its first map precomposes with \(P_p\to\operatorname{im}(d^P_p)\);
its second restricts to \(Z_p(P)\).

The inclusion \(\iota\) is obtained from the long exact cohomology sequence
by factoring its map \(H^n(\operatorname{Hom}(I(P),Q))\to H^n(K)\) through the
cokernel of the preceding connecting map. The Yoneda presentation of
\(0\to\operatorname{im}(d^P_{p+1})\to Z_p(P)\to H_p(P)\to0\) identifies this
cokernel with the displayed product of Ext groups.

The projection \(\rho\) is the restriction map on cohomology, factored through
the kernel of the next connecting map. The cycles and homology comparison
`homUctKernelIso` identifies this kernel with the displayed Hom product,
using the grading convention of `homCochainComplex`.

Concretely, set `S = homCyclesCohomologyClip P Q n hI`. The hypotheses derive
`hZ : ∀ p : ℤ, Projective (P.cycles p)`. Define
`e₁ = homUctCokernelIso P Q n hI hZ` and
`e₃ = homUctKernelIso P Q n hI hZ`. The engine arrows are precisely
`e₁.inv ≫ S.f` and `S.g ≫ e₃.hom`.

## Universes and exactness

For `homUniversalCoefficientSequenceEngine_shortExact`, assume
`HasExt.{w} C`, with `w` independent of `u` and `v`. The actual three terms in
`AddCommGrpCat.{max v w}` are

- `AddCommGrpCat.of (∀ p : ℤ, ULift.{v, w}`
  `(Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1))`;
- `AddCommGrpCat.uliftFunctor.{w, v}.obj ((homCochainComplex P Q).homology n)`;
- `AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v}`
  `(P.homology p ⟶ Q.homology (n - p)))`.

The theorem transports short exactness of `homCyclesCohomologyClip P Q n hI`
through `homUniversalCoefficientSequenceEngineIso P Q n hP hI`. Thus the first
arrow is injective, the second is surjective, and the first image is the
second kernel.
