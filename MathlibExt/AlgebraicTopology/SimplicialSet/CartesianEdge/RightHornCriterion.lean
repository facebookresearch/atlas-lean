/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornLifting

/-!
# The exact critical right-horn criterion for a Cartesian edge

The intrinsic slice boundary condition is equivalent to filling every
original right outer-horn problem whose critical edge is the specified
whole edge. Both the restriction and the complete bottom simplex are
retained. This uses the actual target-endpoint join arrow isomorphism.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The original critical right outer-horn lifting problems characterize this intrinsic edge class. -/
theorem isPCartesian_iff_rightHornLifting {X B : SSet.{u}} (p : X ⟶ B)
    (e : (Δ[1] : SSet.{u}) ⟶ X) : IsPCartesian p e ↔
    ∀ (n : ℕ) (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
      (b : (Δ[n + 2] : SSet.{u}) ⟶ B),
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ b →
      (rightHornEdge σ₀).edge = yonedaEquiv e →
      ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
        Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = b := by
  constructor
  · intro he n σ₀ b hsq hedge
    have ee : yonedaEquiv.symm (rightHornEdge σ₀).edge = e := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, hedge]
    exact exists_fill_rightHorn_of_isPCartesian σ₀ b hsq (ee.symm ▸ he)
  · intro he
    apply (isPCartesian_iff_joinLifting p e).mpr
    intro n
    cases rightJoinHornIndex_zero_one_eq_last n
    refine ⟨fun {u v} sq => ?_⟩
    let J := joinUnderPushoutObjObj (boundary.{u} n).ι (stdSimplex.δ (0 : Fin 2))
    let H := horn (n + 2) (Fin.last (n + 2))
    let E := joinBoundaryTargetEndpointArrowIsoRaw.{u} n
    let u₀ : J.pt ⟶ X := u.right
    let v₀ : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ B := v.right
    let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
    let β : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
    let α' : (H : SSet.{u}) ⟶ J.pt := E.inv.left
    let β' : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⋆ Δ[1] := E.inv.right
    have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
    have hE' : α' ≫ J.ι = H.ι ≫ β' := E.inv.w
    have hα : α ≫ α' = 𝟙 J.pt := Arrow.hom_inv_id_left E
    have hβ : β ≫ β' = 𝟙 _ := Arrow.hom_inv_id_right E
    have hsq : u₀ ≫ p = J.ι ≫ v₀ := congrArg Under.Hom.right sq.w
    have hsource : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        J.inr ≫ u₀ = e := u.w
    have hcritical : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        J.inr ≫ α = yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) := rightHornCurve_eq n
    let σ₀ : (H : SSet.{u}) ⟶ X := α' ≫ u₀
    let σBar : (Δ[n + 2] : SSet.{u}) ⟶ B := β' ≫ v₀
    have hσ : σ₀ ≫ p = H.ι ≫ σBar := by
      dsimp only [σ₀, σBar]
      calc
        (α' ≫ u₀) ≫ p = α' ≫ (J.ι ≫ v₀) := by rw [Category.assoc, hsq]
        _ = (α' ≫ J.ι) ≫ v₀ := (Category.assoc _ _ _).symm
        _ = (H.ι ≫ β') ≫ v₀ := congrArg (fun f => f ≫ v₀) hE'
        _ = H.ι ≫ (β' ≫ v₀) := Category.assoc _ _ _
    have hedge : (rightHornEdge σ₀).edge = yonedaEquiv e := by
      rw [rightHornEdge_edge]
      calc
        σ₀.app _ (rightHornEdgeSimplex.{u} n) =
            yonedaEquiv (yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) ≫ σ₀) := by
              rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
        _ = yonedaEquiv e := congrArg yonedaEquiv (by
          dsimp only [σ₀]
          rw [← hcritical]
          calc
            _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
                J.inr ≫ (α ≫ α') ≫ u₀ := by simp only [Category.assoc]
            _ = e := by rw [hα, Category.id_comp]; exact hsource)
    obtain ⟨σ, hσ₀, hσBar⟩ := he n σ₀ σBar hσ hedge
    let l : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ X := β ≫ σ
    have hl : J.ι ≫ l = u₀ := by
      dsimp only [l]
      calc
        J.ι ≫ β ≫ σ = (α ≫ H.ι) ≫ σ := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ σ) hE.symm
        _ = α ≫ σ₀ := by rw [Category.assoc, hσ₀]
        _ = (α ≫ α') ≫ u₀ := (Category.assoc _ _ _).symm
        _ = u₀ := by rw [hα, Category.id_comp]
    have hp : l ≫ p = v₀ := by
      dsimp only [l]
      rw [Category.assoc, hσBar]
      change β ≫ β' ≫ v₀ = v₀
      rw [← Category.assoc, hβ, Category.id_comp]
    have hw : joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ l = e := by
      rw [← joinInr_comp_map (boundary.{u} n).ι (Δ[1] : SSet.{u}), ← J.inr_ι]
      simp only [Category.assoc]
      rw [hl]
      exact hsource
    refine ⟨Under.homMk l hw, ?_, ?_⟩
    · apply StructuredArrow.hom_ext
      exact hl
    · apply StructuredArrow.hom_ext
      exact hp

end SSet.CartesianEdge
