/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinBoundaryTargetEndpoint
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeJoinIntervalExtension

/-!
# Strict relative right special outer horns

This file proves the all-dimensional right-endpoint form of Joyal's
Theorem 4.13.  The target-endpoint relative join interval is identified with
the right outer horn, and the complete prescribed simplex in the base is
retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- Strict relative right special outer horn filling in every dimension at
least two, with the complete base simplex prescribed. -/
theorem exists_fill_relativeSpecialOuterHorn_right_of_isEquivalence
    {C D : SSet.{u}} {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    {n : ℕ}
    (σ₀ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ C)
    (σBar : (Δ[n + 2] : SSet.{u}) ⟶ D)
    (hsq : σ₀ ≫ q = (horn (n + 2) (Fin.last (n + 2))).ι ≫ σBar)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ C,
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ σ = σ₀ ∧
        σ ≫ q = σBar := by
  cases rightJoinHornIndex_zero_one_eq_last n
  let E := joinBoundaryTargetEndpointArrowIsoRaw.{u} n
  let corner := joinUnderPushoutObjObj (boundary.{u} n).ι
    (stdSimplex.δ (0 : Fin 2))
  let H := horn (n + (0 + 1) + 1)
    (rightJoinHornIndex n 0 (1 : Fin 2))
  have hH : H = horn (n + 2) (Fin.last (n + 2)) := rfl
  cases hH
  have Ehom_w : E.hom.left ≫ H.ι = corner.ι ≫ E.hom.right := E.hom.w
  have Einv_w : E.inv.left ≫ corner.ι = H.ι ≫ E.inv.right := E.inv.w
  let σ₀' : (H : SSet.{u}) ⟶ C := σ₀
  let σBar' : (Δ[n + (0 + 1) + 1] : SSet.{u}) ⟶ D := σBar
  have hsq' : σ₀' ≫ q = H.ι ≫ σBar' := hsq
  let critical : (H : SSet.{u}) _⦋1⦌ := rightHornEdgeSimplex.{u} n
  let ecritical := Edge.mk' (σ₀'.app _ critical)
  have hecritical : ecritical.IsEquivalence := by
    change (rightHornEdge σ₀).IsEquivalence
    exact h
  let u : corner.pt ⟶ C := E.hom.left ≫ σ₀'
  let v : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ D :=
    E.hom.right ≫ σBar'
  have huv : u ≫ q = corner.ι ≫ v := by
    dsimp only [u, v]
    calc
      (E.hom.left ≫ σ₀') ≫ q = E.hom.left ≫ (σ₀' ≫ q) :=
        Category.assoc _ _ _
      _ = E.hom.left ≫ (H.ι ≫ σBar') := by rw [hsq']
      _ = (E.hom.left ≫ H.ι) ≫ σBar' :=
        (Category.assoc _ _ _).symm
      _ = (corner.ι ≫ E.hom.right) ≫ σBar' := by rw [Ehom_w]
      _ = corner.ι ≫ (E.hom.right ≫ σBar') := Category.assoc _ _ _
  have hcritical :
      joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ corner.inr ≫
          E.hom.left =
        yonedaEquiv.symm critical := by
    apply (cancel_mono H.ι).mp
    calc
      (joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            corner.inr ≫ E.hom.left) ≫
          H.ι =
        joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          corner.inr ≫ corner.ι ≫ E.hom.right := by
            simpa only [Category.assoc] using congrArg
              (fun z => joinInr (boundary n : SSet.{u})
                (Δ[1] : SSet.{u}) ≫ corner.inr ≫ z) Ehom_w
      _ = joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          (joinStdSimplexIso n 1).hom := by
            have hinr : corner.inr ≫ corner.ι =
                (join.map (boundary n).ι).app (Δ[1] : SSet.{u}) :=
              corner.inr_ι
            calc
              _ = (joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
                    (join.map (boundary n).ι).app (Δ[1] : SSet.{u})) ≫
                    E.hom.right := by
                  simpa only [Category.assoc] using congrArg
                    (fun z => joinInr (boundary n : SSet.{u})
                      (Δ[1] : SSet.{u}) ≫ z ≫ E.hom.right) hinr
              _ = joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
                    E.hom.right := by rw [joinInr_comp_map]
              _ = _ := by rw [joinBoundaryTargetEndpointArrowIsoRaw_hom_right]
      _ = SSet.stdSimplex.map
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) :=
        joinInr_comp_joinStdSimplexIso_hom n 1
      _ = yonedaEquiv.symm critical ≫ H.ι := by
            apply yonedaEquiv.injective
            rw [SSet.yonedaEquiv_map, yonedaEquiv_comp,
              Equiv.apply_symm_apply]
            change stdSimplex.objEquiv.symm
                (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) =
              critical.val
            apply stdSimplex.objEquiv.injective
            rw [Equiv.apply_symm_apply]
            dsimp only [critical, rightHornEdgeSimplex, horn.edge]
            ext k
            fin_cases k <;> rfl
  have hcritMap :
      joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ corner.inr ≫ u =
        yonedaEquiv.symm ecritical.edge := by
    dsimp only [u]
    calc
      joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          corner.inr ≫ (E.hom.left ≫ σ₀') =
        (joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          corner.inr ≫ E.hom.left) ≫ σ₀' := by simp only [Category.assoc]
      _ = yonedaEquiv.symm critical ≫ σ₀' := by rw [hcritical]
      _ = yonedaEquiv.symm ecritical.edge := by
        rw [yonedaEquiv_symm_comp]
        rfl
  have hcrit : (Edge.mk' (yonedaEquiv
      (joinInr (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        corner.inr ≫ u))).IsEquivalence := by
    apply (Edge.isEquivalence_iff_of_edge_eq (e' := ecritical) (by
      rw [Edge.mk'_edge]
      apply yonedaEquiv.symm.injective
      simpa using hcritMap)).2
    exact hecritical
  obtain ⟨l, hl, hlq⟩ :=
    exists_fill_relativeJoinInterval_target_of_isEquivalence
      (boundary n).ι q u v huv hcrit
  let σ : (Δ[n + 2] : SSet.{u}) ⟶ C := E.inv.right ≫ l
  have hraw : H.ι ≫ (E.inv.right ≫ l) = σ₀' := by
    calc
      H.ι ≫ (E.inv.right ≫ l) = (H.ι ≫ E.inv.right) ≫ l :=
        (Category.assoc _ _ _).symm
      _ = (E.inv.left ≫ corner.ι) ≫ l :=
        congrArg (fun z => z ≫ l) Einv_w.symm
      _ = E.inv.left ≫ (corner.ι ≫ l) := Category.assoc _ _ _
      _ = E.inv.left ≫ u := by rw [hl]
      _ = σ₀' := by simp [u]
  have hbase : (E.inv.right ≫ l) ≫ q = σBar' := by
    calc
      (E.inv.right ≫ l) ≫ q = E.inv.right ≫ v := by
        rw [Category.assoc, hlq]
      _ = σBar' := by simp [v]
  dsimp only [H] at hraw
  refine ⟨σ, ?_, ?_⟩
  · dsimp only [σ, σ₀']
    convert hraw using 1 <;>
      cases rightJoinHornIndex_zero_one_eq_last n <;> rfl
  · simpa only [σ, σBar'] using hbase

/-- Dimension-two regression specialization of the all-dimensional strict
relative right special outer horn theorem. -/
theorem exists_fill_relativeSpecialOuterHorn_right_two_regression
    {C D : SSet.{u}} {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    (σ₀ : (horn 2 (Fin.last 2) : SSet.{u}) ⟶ C)
    (σBar : (Δ[2] : SSet.{u}) ⟶ D)
    (hsq : σ₀ ≫ q = (horn 2 (Fin.last 2)).ι ≫ σBar)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ C,
      (horn 2 (Fin.last 2)).ι ≫ σ = σ₀ ∧ σ ≫ q = σBar := by
  simpa using
    (exists_fill_relativeSpecialOuterHorn_right_of_isEquivalence
      (q := q) (n := 0) σ₀ σBar hsq h)

end SSet
