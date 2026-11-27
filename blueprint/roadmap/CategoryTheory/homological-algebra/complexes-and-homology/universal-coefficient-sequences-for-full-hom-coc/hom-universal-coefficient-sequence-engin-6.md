# The full-product universal coefficient short exact sequence

Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. There
is a short exact sequence 0 → ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) → Hⁿ Hom(P,Q) → ∏ₚ
Hom_C(Hₚ(P),H^{n-p}(Q)) → 0 in the common group universe max(v,w). The left map is the positive
Yoneda-extension comparison followed by the Hom long-exact-sequence inclusion; the right map is
cycles restriction followed by the homology-Hom comparison. Both projectivity families are used
to obtain projective cycles; Q is arbitrary.

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
