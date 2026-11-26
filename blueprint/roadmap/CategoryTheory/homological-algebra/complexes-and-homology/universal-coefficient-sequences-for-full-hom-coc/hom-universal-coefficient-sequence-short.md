# The full-product UCT short exact sequence in standard coordinates

Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. The sequence 0
→ ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) → Hⁿ Hom(P,Q) → ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)) → 0 is short exact.
The left product uses standard Ext classes, while the middle and full right product are
canonically lifted to universe max(u,v). The maps are the positive Hom-sequence inclusion and
canonical cycles restriction, after the Ext and Hom endpoint comparisons. Q has its original
differential.

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

## Standard universes and exactness

`homUniversalCoefficientSequence_shortExact` uses `HasExt.standard C`, which
supplies Ext in universe `max u v`; no separate `HasExt` instance is an input
of this standard theorem. The actual three terms in
`AddCommGrpCat.{max u v}` are

- `AddCommGrpCat.of (∀ p : ℤ,`
  `Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)`;
- `AddCommGrpCat.uliftFunctor.{u, v}.obj ((homCochainComplex P Q).homology n)`;
- `AddCommGrpCat.uliftFunctor.{u, v}.obj`
  `(AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p)))`.

The standard sequence transports the engine by
`e = homUniversalCoefficientStandardCoordinates P Q n`. If `T` is the engine
with `HasExt.standard C`, its arrows become
`e.1.inv ≫ T.f ≫ e.2.1.hom` and
`e.2.1.inv ≫ T.g ≫ e.2.2.hom`.

The theorem transports engine short exactness through
`homUniversalCoefficientSequenceIso P Q n hP hI`. Thus the first arrow is
injective, the second is surjective, and the first image is the second kernel.
