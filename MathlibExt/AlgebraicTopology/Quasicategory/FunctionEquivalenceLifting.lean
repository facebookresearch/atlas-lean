/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativePrism
public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Strict equivalence lifting for internal-Hom pullbacks

Let i : A -> B be a monomorphism and p : X -> Y an inner fibration with
quasicategory codomain and strict equivalence-edge lifting. The original
native internal-Hom pullback comparison admits strict equivalence-edge
lifting, with the prescribed target vertex and the actual image edge.

Project a prescribed equivalence edge to the two function objects, extend
the corresponding compatible prisms by the full relative source-prism
result, and curry the extension. Both pullback projections identify its
whole image edge with the prescribed edge. The pointwise equivalence
criterion proves that the lifted edge is an equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet

private lemma ihomSimplexOfPrism_post {A X Y : SSet.{u}} {n : ℕ}
    (F : A ⊗ Δ[n] ⟶ X) (p : X ⟶ Y) :
    ((ihom A).map p).app (op ⦋n⦌) (ihomSimplexOfPrism F) =
      ihomSimplexOfPrism (F ≫ p) := by
  dsimp only [ihomSimplexOfPrism]
  rw [MonoidalClosed.curry_natural_right, yonedaEquiv_comp]

private lemma pullbackObjObj_simplex_ext {A B X Y : SSet.{u}}
    {i : A ⟶ B} {p : X ⟶ Y}
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p)
    {n : ℕ} {s t : sq.pt _⦋n⦌}
    (hfst : sq.fst.app (op ⦋n⦌) s = sq.fst.app (op ⦋n⦌) t)
    (hsnd : sq.snd.app (op ⦋n⦌) s = sq.snd.app (op ⦋n⦌) t) : s = t := by
  apply yonedaEquiv.symm.injective
  apply sq.hom_ext
  · rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, hfst]
  · rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, hsnd]

/-- Strict equivalence lifting for the original internal-Hom pullback
comparison. The source quasicategory is inferred from p and its codomain. -/
public theorem hasStrictEquivalenceLifting_pullbackObjObjπ
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    [Mono i] [InnerFibration p] [Quasicategory Y] [HasStrictEquivalenceLifting p]
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p) :
    HasStrictEquivalenceLifting sq.π := by
  let : Quasicategory X := quasicategory_of_innerFibration p
  have extend : RelativePrismSrcExtension i p := relativePrismSrcExtension_of_mono i p
  let projA : sq.pt ⟶ (ihom A).obj X := sq.fst
  let projB : sq.pt ⟶ (ihom B).obj Y := sq.snd
  let q : (ihom B).obj X ⟶ sq.pt := sq.π
  have hqA : q ≫ projA = (pre i).app X := sq.π_fst
  have hqB : q ≫ projB = (ihom B).map p := sq.π_snd
  have hAB : projA ≫ (ihom A).map p = projB ≫ (pre i).app Y := sq.isPullback.w
  change HasStrictEquivalenceLifting q
  constructor
  intro U V g hg
  let H : A ⊗ Δ[1] ⟶ X := ihomPrismOfSimplex (g.map projA).edge
  let K : B ⊗ Δ[1] ⟶ Y := ihomPrismOfSimplex (g.map projB).edge
  let c : B ⟶ X := (ihomVertexEquiv B X).symm U
  have hc : ihomVertexEquiv B X c = U :=
    (ihomVertexEquiv B X).apply_symm_apply U
  have hHsrc : prismSectionAt A 0 ≫ H = i ≫ c := by
    apply (ihomVertexEquiv A X).injective
    dsimp only [H]
    rw [ihomVertexEquiv_prismSectionAt_zero_comp,
      ihomSimplexOfPrism_ihomPrismOfSimplex, (g.map projA).src_eq]
    change (q ≫ projA).app (op ⦋0⦌) U = ihomVertexEquiv A X (i ≫ c)
    rw [hqA]
    rw [← hc, ihomVertexEquiv_pre_app]
  have hKsrc : prismSectionAt B 0 ≫ K = c ≫ p := by
    apply (ihomVertexEquiv B Y).injective
    dsimp only [K]
    rw [ihomVertexEquiv_prismSectionAt_zero_comp,
      ihomSimplexOfPrism_ihomPrismOfSimplex, (g.map projB).src_eq]
    change (q ≫ projB).app (op ⦋0⦌) U = ihomVertexEquiv B Y (c ≫ p)
    rw [hqB]
    rw [← hc, ihomVertexEquiv_ihom_map]
  have hcompat : H ≫ p = (i ▷ Δ[1]) ≫ K := by
    apply (ihomSimplexEquiv A Y 1).injective
    change ihomSimplexOfPrism (H ≫ p) = ihomSimplexOfPrism ((i ▷ Δ[1]) ≫ K)
    rw [← ihomSimplexOfPrism_post, ← ihomSimplexOfPrism_pre_app]
    dsimp only [H, K]
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex,
      ihomSimplexOfPrism_ihomPrismOfSimplex]
    change (projA ≫ (ihom A).map p).app (op ⦋1⦌) g.edge =
      (projB ≫ (pre i).app Y).app (op ⦋1⦌) g.edge
    exact congr($(hAB).app (op ⦋1⦌) g.edge)
  have hHvert : PrismOneVerticalsEquivalences H :=
    prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence
      (g.map projA) (hg.map projA)
  have hKvert : PrismOneVerticalsEquivalences K :=
    prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence
      (g.map projB) (hg.map projB)
  obtain ⟨F, hFr, hFs, hFp, hFvert⟩ := extend H c K hHsrc hKsrc hcompat hHvert hKvert
  let s : ((ihom B).obj X) _⦋1⦌ := ihomSimplexOfPrism F
  have hsource : ((ihom B).obj X).δ 1 s = U := by
    dsimp only [s]
    rw [← ihomVertexEquiv_prismSectionAt_zero_comp, hFs]
    exact hc
  let U₁ : ((ihom B).obj X) _⦋0⦌ := ((ihom B).obj X).δ 0 s
  let f : Edge U U₁ := Edge.mk s hsource rfl
  have himage : (f.map q).edge = g.edge := by
    apply pullbackObjObj_simplex_ext sq
    · change (q ≫ projA).app (op ⦋1⦌) s = projA.app (op ⦋1⦌) g.edge
      rw [hqA]
      change ((pre i).app X).app (op ⦋1⦌) (ihomSimplexOfPrism F) =
        (g.map projA).edge
      rw [ihomSimplexOfPrism_pre_app, hFr]
      exact ihomSimplexOfPrism_ihomPrismOfSimplex (g.map projA).edge
    · change (q ≫ projB).app (op ⦋1⦌) s = projB.app (op ⦋1⦌) g.edge
      rw [hqB]
      change ((ihom B).map p).app (op ⦋1⦌) (ihomSimplexOfPrism F) =
        (g.map projB).edge
      rw [ihomSimplexOfPrism_post, hFp]
      exact ihomSimplexOfPrism_ihomPrismOfSimplex (g.map projB).edge
  have htarget : q.app (op ⦋0⦌) U₁ = V := by
    calc q.app (op ⦋0⦌) U₁
        = sq.pt.δ 0 (f.map q).edge := (f.map q).tgt_eq.symm
      _ = sq.pt.δ 0 g.edge := by rw [himage]
      _ = V := g.tgt_eq
  have hfequiv : f.IsEquivalence := by
    apply (f.isEquivalence_iff_forall_eval_vertex).mpr
    intro b
    apply (hFvert b).of_edge_eq
    have hv := ihomPrismOfSimplex_app_verticalOneSimplex f b
    change (ihomPrismOfSimplex (ihomSimplexOfPrism F)).app (op ⦋1⦌)
      (verticalOneSimplex b) = _ at hv
    simpa only [ihomPrismOfSimplex_ihomSimplexOfPrism, Edge.mk'_edge] using hv
  exact ⟨U₁, htarget, f, hfequiv, himage⟩

end SSet
