/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Comparison
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinBoundaryTargetEndpoint

/-!
# Strict right outer horns controlled by a Cartesian critical edge

The target-endpoint boundary join is the actual right outer horn. Its
original interval is the critical last edge. The canonical relative
Cartesian boundary-lifting condition therefore fills that entire outer
horn, with the complete supplied base simplex retained. No equivalence or
quasicategory hypothesis is needed for this consequence of the predicate.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The canonical boundary-join comparison retains the whole critical last edge. -/
theorem rightHornCurve_eq (n : ℕ) :
    joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (joinUnderPushoutObjObj (boundary.{u} n).ι (stdSimplex.δ (0 : Fin 2))).inr ≫
          (joinBoundaryTargetEndpointArrowIsoRaw.{u} n).hom.left =
      yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) := by
  cases rightJoinHornIndex_zero_one_eq_last n
  let J := joinUnderPushoutObjObj (boundary.{u} n).ι (stdSimplex.δ (0 : Fin 2))
  let H := horn (n + 2) (Fin.last (n + 2))
  let E := joinBoundaryTargetEndpointArrowIsoRaw.{u} n
  let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
  let β : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
  have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
  change joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ α = _
  apply (cancel_mono H.ι).mp
  calc
    _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ J.ι ≫ β := by
      simpa only [Category.assoc] using congrArg
        (fun f => joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ f) hE
    _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (join.map (boundary.{u} n).ι).app (Δ[1] : SSet.{u}) ≫ β := by
      simpa only [Category.assoc] using congrArg
        (fun f => joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ f ≫ β) J.inr_ι
    _ = joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ β := by
      rw [← Category.assoc, joinInr_comp_map]
    _ = yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) ≫ H.ι := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      change yonedaEquiv (joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ E.hom.right) =
        (rightHornEdgeSimplex.{u} n).val
      rw [joinBoundaryTargetEndpointArrowIsoRaw_hom_right,
        joinInr_comp_joinStdSimplexIso_hom, SSet.yonedaEquiv_map]
      apply stdSimplex.ext
      intro i
      rw [stdSimplex.objEquiv_symm_apply, AugmentedSimplexCategory.inr'_eval]
      apply Fin.ext
      fin_cases i <;> rfl

/-- A p-Cartesian critical last edge supplies the original strict relative right-horn filler. -/
theorem exists_fill_rightHorn_of_isPCartesian {X B : SSet.{u}} {p : X ⟶ B} {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (σBar : (Δ[n + 2] : SSet.{u}) ⟶ B)
    (hsq : σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ σBar)
    (he : IsPCartesian p (yonedaEquiv.symm (rightHornEdge σ₀).edge)) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
      Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = σBar := by
  cases rightJoinHornIndex_zero_one_eq_last n
  let J := joinUnderPushoutObjObj (boundary.{u} n).ι (stdSimplex.δ (0 : Fin 2))
  let H := horn (n + 2) (Fin.last (n + 2))
  let E := joinBoundaryTargetEndpointArrowIsoRaw.{u} n
  let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
  let β : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
  let α' : (H : SSet.{u}) ⟶ J.pt := E.inv.left
  let β' : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⋆ Δ[1] := E.inv.right
  have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
  have hE' : α' ≫ J.ι = H.ι ≫ β' := E.inv.w
  have hα : α' ≫ α = 𝟙 _ := Arrow.inv_hom_id_left E
  have hβ : β' ≫ β = 𝟙 _ := Arrow.inv_hom_id_right E
  let e : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm (σ₀.app _ (rightHornEdgeSimplex.{u} n))
  have he' : IsPCartesian p e := he
  let u : J.pt ⟶ X := α ≫ σ₀
  let v : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ B := β ≫ σBar
  have huv : u ≫ p = J.ι ≫ v := by
    dsimp only [u, v]
    calc
      (α ≫ σ₀) ≫ p = α ≫ (H.ι ≫ σBar) := by rw [Category.assoc, hsq]
      _ = (α ≫ H.ι) ≫ σBar := (Category.assoc _ _ _).symm
      _ = (J.ι ≫ β) ≫ σBar := congrArg (fun f => f ≫ σBar) hE
      _ = J.ι ≫ (β ≫ σBar) := Category.assoc _ _ _
  have hu : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ u = e := by
    have hc : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ α =
        yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) := rightHornCurve_eq n
    dsimp only [u, e]
    calc
      _ = (joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ α) ≫ σ₀ := by
        simp only [Category.assoc]
      _ = yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) ≫ σ₀ := congrArg (fun f => f ≫ σ₀) hc
      _ = _ := by apply yonedaEquiv.injective; simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hv : joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ v = e ≫ p := by
    have hi : joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ J.ι =
        joinInr (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) := by
      calc
        _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (join.map (boundary.{u} n).ι).app (Δ[1] : SSet.{u}) := by
              simpa only [Category.assoc] using congrArg
                (fun f => joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ f) J.inr_ι
        _ = _ := joinInr_comp_map (boundary.{u} n).ι (Δ[1] : SSet.{u})
    calc
      _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ J.ι ≫ v := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ v) hi.symm
      _ = joinInr (boundary.{u} n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ J.inr ≫ u ≫ p := by
        rw [← huv]
      _ = e ≫ p := by simpa only [Category.assoc] using congrArg (fun f => f ≫ p) hu
  let top : joinOverPushoutSource (stdSimplex.δ (0 : Fin 2)) (boundary.{u} n).ι ⟶
      Under.mk e := Under.homMk u hu
  let bottom : (joinOver (Δ[1] : SSet.{u})).obj (Δ[n] : SSet.{u}) ⟶
      Under.mk (e ≫ p) := Under.homMk v hv
  let _ : HasLiftingProperty
      (joinOverPushoutMap (stdSimplex.δ (0 : Fin 2)) (boundary.{u} n).ι)
      (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) :=
    (isPCartesian_iff_joinLifting p e).mp he' n
  have sq : CommSq top (joinOverPushoutMap (stdSimplex.δ (0 : Fin 2)) (boundary.{u} n).ι)
      (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) bottom := by
    constructor
    apply StructuredArrow.hom_ext
    exact huv
  let l : (Δ[n] : SSet.{u}) ⋆ (Δ[1] : SSet.{u}) ⟶ X := sq.lift.right
  have hl : J.ι ≫ l = u := congrArg Under.Hom.right sq.fac_left
  have hp : l ≫ p = v := congrArg Under.Hom.right sq.fac_right
  refine ⟨β' ≫ l, ?_, ?_⟩
  · calc
      H.ι ≫ β' ≫ l = α' ≫ J.ι ≫ l := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ l) hE'.symm
      _ = α' ≫ u := by rw [hl]
      _ = σ₀ := by dsimp only [u]; rw [← Category.assoc, hα, Category.id_comp]
  · rw [Category.assoc, hp]
    dsimp only [v]
    rw [← Category.assoc, hβ, Category.id_comp]

end SSet.CartesianEdge
