/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BinaryCoproductPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpSimplexCriterion
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# Binary coproduct stability of sharp maps

Sharpness is invariant under isomorphisms of arrows of simplicial sets and is preserved by binary coproducts, both over a common base and over the coproduct of the two bases. These coproduct maps remain sharp under arbitrary base change.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
namespace SSet.SharpCoproductClosure
open SharpSaturation SharpComparisonDraft BinaryCoproductPullback

private def arrowIsoPullback {X Y X' Y' T : SSet.{u}}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (e : Arrow.mk p ≅ Arrow.mk q) (t : T ⟶ Y) :
    pullback p t ≅ pullback q (t ≫ e.hom.right) :=
  asIso (pullback.map p t q (t ≫ e.hom.right) e.hom.left (𝟙 T) e.hom.right
    e.hom.w.symm (by simp))

private def arrowIsoComparison {X Y X' Y' : SSet.{u}}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (e : Arrow.mk p ≅ Arrow.mk q)
    (n m : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) (δ : ⦋m⦌ ⟶ ⦋n⦌) :
    Arrow.mk (pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
      (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp)) ≅
    Arrow.mk (pullback.map q (SSet.stdSimplex.map δ ≫ (b ≫ e.hom.right)) q
      (b ≫ e.hom.right) (𝟙 X') (SSet.stdSimplex.map δ) (𝟙 Y') (by simp) (by simp)) :=
  Arrow.isoMk
    (asIso (pullback.map p (SSet.stdSimplex.map δ ≫ b) q
      (SSet.stdSimplex.map δ ≫ (b ≫ e.hom.right)) e.hom.left
      (𝟙 (Δ[m] : SSet.{u})) e.hom.right e.hom.w.symm (by simp [Category.assoc])))
    (arrowIsoPullback e b) (by
      apply pullback.hom_ext <;> simp [arrowIsoPullback, pullback.map, Category.assoc])

private theorem condition_of_arrowIso {X Y X' Y' : SSet.{u}}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (e : Arrow.mk p ≅ Arrow.mk q)
    (hq : allSimplexComparisons q) : allSimplexComparisons p := by
  intro n m b δ
  exact (realizationWeakEquivalences.arrow_mk_iso_iff (arrowIsoComparison e n m b δ)).2
    (hq n m (b ≫ e.hom.right) δ)

/-- Sharpness is invariant under the whole original Arrow isomorphism, on both object sides. -/
theorem sharp_arrowIso_iff {X Y X' Y' : SSet.{u}}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (e : Arrow.mk p ≅ Arrow.mk q) : Sharp p ↔ Sharp q := by
  constructor
  · intro hp
    exact (sharp_iff_allSimplexComparisons q).2
      (condition_of_arrowIso e.symm ((sharp_iff_allSimplexComparisons p).1 hp))
  · intro hq
    exact (sharp_iff_allSimplexComparisons p).2
      (condition_of_arrowIso e ((sharp_iff_allSimplexComparisons q).1 hq))

/-- The original cofan over one common base is sharp when both original component arrows are
sharp. -/
theorem sharp_coprod_desc {X₁ X₂ Y : SSet.{u}} (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y)
    (hp₁ : Sharp p₁) (hp₂ : Sharp p₂) : Sharp (coprod.desc p₁ p₂) := by
  apply (sharp_iff_allSimplexComparisons _).2
  have h₁ := (sharp_iff_allSimplexComparisons p₁).1 hp₁
  have h₂ := (sharp_iff_allSimplexComparisons p₂).1 hp₂
  intro n m b δ
  exact (realizationWeakEquivalences.arrow_mk_iso_iff
    (binaryComparisonArrowIso p₁ p₂ (SSet.stdSimplex.map δ) b)).1
    (coprod_map_mem_realizationWeakEquivalences _ _ (h₁ n m b δ) (h₂ n m b δ))

private def componentPullbackIso {P X E Y T : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    pullback q β ≅ pullback p b := by
  have h : IsPullback (pullback.fst q β ≫ r) (pullback.snd q β) p b := by
    simpa only [hb] using (IsPullback.of_hasPullback q β).paste_horiz H
  exact h.isoPullback

private theorem componentPullbackIso_legs {P X E Y T : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    (componentPullbackIso H β b hb).hom ≫ pullback.fst p b = pullback.fst q β ≫ r ∧
    (componentPullbackIso H β b hb).hom ≫ pullback.snd p b = pullback.snd q β := by
  constructor <;> simp [componentPullbackIso]

private def componentComparisonArrowIso {P X E Y : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}
    (H : IsPullback r q p e) {n m : ℕ}
    (β : (Δ[n] : SSet.{u}) ⟶ E) (b : (Δ[n] : SSet.{u}) ⟶ Y)
    (hb : β ≫ e = b) (δ : ⦋m⦌ ⟶ ⦋n⦌) :
    Arrow.mk (pullback.map q (SSet.stdSimplex.map δ ≫ β) q β
      (𝟙 P) (SSet.stdSimplex.map δ) (𝟙 E) (by simp) (by simp)) ≅
    Arrow.mk (pullback.map p (SSet.stdSimplex.map δ ≫ b) p b
      (𝟙 X) (SSet.stdSimplex.map δ) (𝟙 Y) (by simp) (by simp)) :=
  Arrow.isoMk
    (componentPullbackIso H (SSet.stdSimplex.map δ ≫ β) (SSet.stdSimplex.map δ ≫ b)
      (by simp only [Category.assoc, hb]))
    (componentPullbackIso H β b hb) (by
      apply pullback.hom_ext
      · simp [Category.assoc, pullback.map, componentPullbackIso_legs]
      · simp [Category.assoc, pullback.map, componentPullbackIso_legs]
        simpa only [Category.assoc] using
          congrArg (fun k : pullback q (SSet.stdSimplex.map δ ≫ β) ⟶ (Δ[m] : SSet.{u}) =>
            k ≫ SSet.stdSimplex.map δ)
            (componentPullbackIso_legs H (SSet.stdSimplex.map δ ≫ β)
              (SSet.stdSimplex.map δ ≫ b) (by simp only [Category.assoc, hb])).2)

private theorem binaryMapCondition_at_simplex {X₁ X₂ Y₁ Y₂ : SSet.{u}}
    (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (h₁ : allSimplexComparisons p₁) (h₂ : allSimplexComparisons p₂)
    (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y₁ ⨿ Y₂) :
    ∀ (m : ℕ) (δ : ⦋m⦌ ⟶ ⦋n⦌), realizationWeakEquivalences
      (pullback.map (coprod.map p₁ p₂) (SSet.stdSimplex.map δ ≫ b) (coprod.map p₁ p₂) b
        (𝟙 (X₁ ⨿ X₂)) (SSet.stdSimplex.map δ) (𝟙 (Y₁ ⨿ Y₂)) (by simp) (by simp)) := by
  -- The original b is classified once, before m and delta are introduced.
  obtain ⟨β, hb⟩ | ⟨β, hb⟩ := simplex_coprod_factor n b
  · intro m δ
    exact (realizationWeakEquivalences.arrow_mk_iso_iff
      (componentComparisonArrowIso (binaryCoproductSquares p₁ p₂).1 β b hb δ)).1
      (h₁ n m β δ)
  · intro m δ
    exact (realizationWeakEquivalences.arrow_mk_iso_iff
      (componentComparisonArrowIso (binaryCoproductSquares p₁ p₂).2 β b hb δ)).1
      (h₂ n m β δ)

/-- The full original binary coproduct map is sharp on its original coproduct of bases. -/
theorem sharp_coprod_map {X₁ X₂ Y₁ Y₂ : SSet.{u}} (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (hp₁ : Sharp p₁) (hp₂ : Sharp p₂) : Sharp (coprod.map p₁ p₂) :=
  (sharp_iff_allSimplexComparisons _).2
    (fun n m b δ => binaryMapCondition_at_simplex p₁ p₂
      ((sharp_iff_allSimplexComparisons p₁).1 hp₁)
      ((sharp_iff_allSimplexComparisons p₂).1 hp₂) n b m δ)

/-- Actual base-change closure of the full original binary coproduct consumes the separate proved
pullback unit. -/
theorem sharp_coprod_map_pullbackSnd {X₁ X₂ Y₁ Y₂ T : SSet.{u}}
    (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) (t : T ⟶ Y₁ ⨿ Y₂)
    (hp₁ : Sharp p₁) (hp₂ : Sharp p₂) :
    Sharp (pullback.snd (coprod.map p₁ p₂) t) :=
  SharpPullbackClosure.sharp_pullback_snd (coprod.map p₁ p₂) t (sharp_coprod_map p₁ p₂ hp₁ hp₂)

end SSet.SharpCoproductClosure
