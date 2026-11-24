/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SSet.RezkPushoutCover

/-- The original binary coproduct cover of the actual chosen pushout. -/
def pushoutCover {Y0 Y1 Y2 : SSet.{u}} (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) :
    Y1 ⨿ Y2 ⟶ pushout a b :=
  coprod.desc (pushout.inl a b) (pushout.inr a b)

/-- The original pushout cover is epi, with no mono or weak hypothesis. -/
theorem pushoutCover_epi {Y0 Y1 Y2 : SSet.{u}} (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) :
    Epi (pushoutCover a b) := by
  change Epi (coprod.desc (pushout.inl a b) (pushout.inr a b))
  exact CategoryTheory.Limits.epi_coprod_to_pushout a b

/-- Both literal original degree maps are the actual pushout injections. -/
theorem pushoutCover_degree_legs {Y0 Y1 Y2 : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (n : SimplexCategoryᵒᵖ) :
    (coprod.inl : Y1 ⟶ Y1 ⨿ Y2).app n ≫ (pushoutCover a b).app n =
      (pushout.inl a b).app n ∧
    (coprod.inr : Y2 ⟶ Y1 ⨿ Y2).app n ≫ (pushoutCover a b).app n =
      (pushout.inr a b).app n := by
  have hl : (coprod.inl : Y1 ⟶ Y1 ⨿ Y2) ≫ pushoutCover a b = pushout.inl a b :=
    coprod.inl_desc _ _
  have hr : (coprod.inr : Y2 ⟶ Y1 ⨿ Y2) ≫ pushoutCover a b = pushout.inr a b :=
    coprod.inr_desc _ _
  exact ⟨by simpa only [NatTrans.comp_app] using congrArg (fun f => f.app n) hl,
    by simpa only [NatTrans.comp_app] using congrArg (fun f => f.app n) hr⟩

/-- Cover naturality retains every original simplex operator and degree value. -/
theorem pushoutCover_operator {Y0 Y1 Y2 : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) {m n : SimplexCategory} (δ : m ⟶ n)
    (z : (Y1 ⨿ Y2).obj (op n)) :
    (pushoutCover a b).app (op m) ((Y1 ⨿ Y2).map δ.op z) =
      (pushout a b).map δ.op ((pushoutCover a b).app (op n) z) := by
  exact ConcreteCategory.congr_hom ((pushoutCover a b).naturality δ.op) z

/-- The base-changed cover projects epimorphically to the original source X.
This makes no claim that the other pullback projection is epi or weak. -/
theorem pullbackPushoutCover_epi {Y0 Y1 Y2 X : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (p : X ⟶ pushout a b) :
    Epi (pullback.fst p (pushoutCover a b)) := by
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro n
  apply (CategoryTheory.epi_iff_surjective _).mpr
  intro x
  let _ : Epi ((pushoutCover a b).app n) :=
    (NatTrans.epi_iff_epi_app _).mp (pushoutCover_epi a b) n
  obtain ⟨z, hz⟩ := CategoryTheory.surjective_of_epi
    ((pushoutCover a b).app n) (p.app n x)
  obtain ⟨w, hw, _⟩ := CategoryTheory.Limits.Types.exists_of_isPullback
    ((IsPullback.of_hasPullback p (pushoutCover a b)).app n) x z hz.symm
  exact ⟨w, hw⟩

/-- Every original source simplex has a whole lift over the original cover,
including both complete pullback legs and all restrictions of that same lift.
No natural family of independently chosen simplex lifts is assumed. -/
theorem exists_simplex_pullback_cover {Y0 Y1 Y2 X : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (p : X ⟶ pushout a b)
    (n : ℕ) (x : (Δ[n] : SSet.{u}) ⟶ X) :
    ∃ (r : (Δ[n] : SSet.{u}) ⟶ Y1 ⨿ Y2)
      (l : (Δ[n] : SSet.{u}) ⟶ pullback p (pushoutCover a b)),
      r ≫ pushoutCover a b = x ≫ p ∧
      l ≫ pullback.fst p (pushoutCover a b) = x ∧
      l ≫ pullback.snd p (pushoutCover a b) = r ∧
      ∀ (m : ℕ) (δ : ⦋m⦌ ⟶ ⦋n⦌),
        SSet.stdSimplex.map δ ≫ l ≫ pullback.fst p (pushoutCover a b) =
          SSet.stdSimplex.map δ ≫ x ∧
        SSet.stdSimplex.map δ ≫ l ≫ pullback.snd p (pushoutCover a b) =
          SSet.stdSimplex.map δ ≫ r := by
  let _ : Epi ((pushoutCover a b).app (op ⦋n⦌)) :=
    (NatTrans.epi_iff_epi_app _).mp (pushoutCover_epi a b) (op ⦋n⦌)
  obtain ⟨z, hz⟩ := CategoryTheory.surjective_of_epi
    ((pushoutCover a b).app (op ⦋n⦌)) (SSet.yonedaEquiv (x ≫ p))
  let r : (Δ[n] : SSet.{u}) ⟶ Y1 ⨿ Y2 := SSet.yonedaEquiv.symm z
  have hr : r ≫ pushoutCover a b = x ≫ p := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, r, Equiv.apply_symm_apply] using hz
  let l : (Δ[n] : SSet.{u}) ⟶ pullback p (pushoutCover a b) :=
    pullback.lift x r hr.symm
  have hl : l ≫ pullback.fst p (pushoutCover a b) = x :=
    pullback.lift_fst _ _ _
  have hs : l ≫ pullback.snd p (pushoutCover a b) = r :=
    pullback.lift_snd _ _ _
  refine ⟨r, l, hr, hl, hs, ?_⟩
  intro m δ
  exact ⟨by simpa only [Category.assoc] using congrArg (SSet.stdSimplex.map δ ≫ ·) hl,
    by simpa only [Category.assoc] using congrArg (SSet.stdSimplex.map δ ≫ ·) hs⟩

/-- The exact cover square for the map of the two original compatible spans.
Only the source projection and the actual target coproduct cover are epi. -/
theorem compatible_spans_cover {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u : X0 ⟶ X1) (v : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (h1 : u ≫ p1 = p0 ≫ a) (h2 : v ≫ p2 = p0 ≫ b) :
    let p := pushout.map u v a b p1 p2 p0 h1 h2
    pushout.inl u v ≫ p = p1 ≫ pushout.inl a b ∧
    pushout.inr u v ≫ p = p2 ≫ pushout.inr a b ∧
    Epi (pushoutCover a b) ∧ Epi (pullback.fst p (pushoutCover a b)) ∧
      IsPullback (pullback.snd p (pushoutCover a b))
        (pullback.fst p (pushoutCover a b)) (pushoutCover a b) p := by
  dsimp only
  refine ⟨?_, ?_, pushoutCover_epi a b, pullbackPushoutCover_epi a b _,
    (IsPullback.of_hasPullback _ _).flip⟩
  · simp
  · simp

end SSet.RezkPushoutCover
