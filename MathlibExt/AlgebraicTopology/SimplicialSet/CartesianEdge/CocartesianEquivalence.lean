/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Comparison
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinBoundarySourceEndpoint
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornOpposite

/-!
# Equivalence edges satisfy the actual cocartesian slice condition

The source-endpoint boundary join is the left outer horn. Its original
interval is precisely the critical first edge. The existing strict
relative left outer-horn theorem therefore supplies all boundary lifts,
retaining the entire prescribed base simplex.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

private theorem cast_edge01 {m n : ℕ} (h : m = n) (hm : 1 < m + 1) (hn : 1 < n + 1) :
    (eqToHom (congrArg (fun k : ℕ => (Δ[k] : SSet.{u})) h)).app (op ⦋1⦌)
      (stdSimplex.edge m 0 ⟨1, hm⟩ (Fin.zero_le _)) =
        stdSimplex.edge n 0 ⟨1, hn⟩ (Fin.zero_le _) := by
  subst n
  rfl

private theorem sourceJoin_hom_right (n : ℕ) :
    (joinBoundarySourceEndpointArrowIso.{u} n).hom.right =
      (joinBoundarySourceEndpointArrowIsoRaw.{u} n).hom.right ≫
        eqToHom (congrArg (fun k : ℕ => (Δ[k] : SSet.{u}))
          (show (0 + 1) + n + 1 = n + 2 by omega)) := by
  let h₀ : Arrow.mk (horn.{u} ((0 + 1) + n + 1) (leftJoinHornIndex 0 n (0 : Fin 2))).ι =
      Arrow.mk (horn.{u} ((0 + 1) + n + 1) (0 : Fin (((0 + 1) + n + 1) + 1))).ι :=
    congrArg (fun i : Fin (((0 + 1) + n + 1) + 1) =>
      Arrow.mk (horn.{u} ((0 + 1) + n + 1) i).ι) (Fin.ext rfl)
  let h₁ : Arrow.mk (horn.{u} ((0 + 1) + n + 1) (0 : Fin (((0 + 1) + n + 1) + 1))).ι =
      Arrow.mk (horn.{u} (n + 2) (0 : Fin (n + 3))).ι :=
    congrArg (fun k : ℕ => Arrow.mk (horn.{u} k (0 : Fin (k + 1))).ι)
      (show (0 + 1) + n + 1 = n + 2 by omega)
  change ((joinBoundarySourceEndpointArrowIsoRaw.{u} n).hom.right ≫
    (eqToHom h₀).right) ≫ (eqToHom h₁).right = _
  simp only [Arrow.eqToHom_right, eqToHom_refl, Category.comp_id]

private theorem sourceJoin_first_edge (n : ℕ) :
    yonedaEquiv (joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
      (joinBoundarySourceEndpointArrowIso.{u} n).hom.right) =
        (leftHornEdgeSimplex.{u} n).val := by
  have hraw : yonedaEquiv (joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
      (joinBoundarySourceEndpointArrowIsoRaw.{u} n).hom.right) =
        stdSimplex.edge ((0 + 1) + n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) := by
    rw [joinBoundarySourceEndpointArrowIsoRaw_hom_right,
      joinInl_comp_joinStdSimplexIso_hom, SSet.yonedaEquiv_map]
    apply stdSimplex.ext
    intro i
    rw [stdSimplex.objEquiv_symm_apply, AugmentedSimplexCategory.inl'_eval]
    apply Fin.ext
    fin_cases i <;> rfl
  rw [sourceJoin_hom_right, ← Category.assoc, yonedaEquiv_comp, hraw]
  exact cast_edge01 (show (0 + 1) + n + 1 = n + 2 by omega) (by omega) (by omega)

/-- Every actual equivalence edge of an inner fibration over a quasicategory is p-cocartesian. -/
theorem isPCocartesian_of_isEquivalence {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : (Edge.mk' (yonedaEquiv e)).IsEquivalence) : IsPCocartesian p e := by
  apply (isPCocartesian_iff_joinLifting p e).mpr
  intro n
  refine ⟨fun {u v} sq => ?_⟩
  let J := joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι
  let H := horn (n + 2) (0 : Fin (n + 3))
  let E := joinBoundarySourceEndpointArrowIso.{u} n
  let u₀ : J.pt ⟶ X := u.right
  let v₀ : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ B := v.right
  let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
  let β : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
  let α' : (H : SSet.{u}) ⟶ J.pt := E.inv.left
  let β' : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⋆ Δ[n] := E.inv.right
  have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
  have hE' : α' ≫ J.ι = H.ι ≫ β' := E.inv.w
  have hα : α ≫ α' = 𝟙 J.pt := Arrow.hom_inv_id_left E
  have hβ : β ≫ β' = 𝟙 _ := Arrow.hom_inv_id_right E
  have hsq : u₀ ≫ p = J.ι ≫ v₀ := congrArg Under.Hom.right sq.w
  have hsource : joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
      J.inl ≫ u₀ = e := u.w
  have hcritical : joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
      J.inl ≫ α = yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) := by
    apply (cancel_mono H.ι).mp
    calc
      _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
          J.inl ≫ J.ι ≫ β := by
            simpa only [Category.assoc] using congrArg
              (fun f => joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ f) hE
      _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
          (join.obj (Δ[1] : SSet.{u})).map (boundary.{u} n).ι ≫ β := by
            simpa only [Category.assoc] using congrArg
              (fun f => joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ f ≫ β) J.inl_ι
      _ = joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ β := by
            rw [← Category.assoc, joinInl_comp_map]
      _ = yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) ≫ H.ι := by
            apply yonedaEquiv.injective
            simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
            exact sourceJoin_first_edge n
  let σ₀ : (H : SSet.{u}) ⟶ X := α' ≫ u₀
  let σBar : (Δ[n + 2] : SSet.{u}) ⟶ B := β' ≫ v₀
  have hσ : σ₀ ≫ p = H.ι ≫ σBar := by
    dsimp only [σ₀, σBar]
    calc
      (α' ≫ u₀) ≫ p = α' ≫ (J.ι ≫ v₀) := by rw [Category.assoc, hsq]
      _ = (α' ≫ J.ι) ≫ v₀ := (Category.assoc _ _ _).symm
      _ = (H.ι ≫ β') ≫ v₀ := congrArg (fun f => f ≫ v₀) hE'
      _ = H.ι ≫ (β' ≫ v₀) := Category.assoc _ _ _
  have hedge : (leftHornEdge σ₀).edge = (Edge.mk' (yonedaEquiv e)).edge := by
    rw [leftHornEdge_edge, Edge.mk'_edge]
    calc
      σ₀.app _ (leftHornEdgeSimplex.{u} n) =
          yonedaEquiv (yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) ≫ σ₀) := by
            rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      _ = yonedaEquiv e := congrArg yonedaEquiv (by
        dsimp only [σ₀]
        rw [← hcritical]
        calc
          _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
              J.inl ≫ (α ≫ α') ≫ u₀ := by simp only [Category.assoc]
          _ = e := by rw [hα, Category.id_comp]; exact hsource)
  have hσe : (leftHornEdge σ₀).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq hedge).mpr he
  obtain ⟨σ, hσ₀, hσBar⟩ :=
    exists_fill_relativeSpecialOuterHorn_left_of_isEquivalence σ₀ σBar hσ hσe
  let l : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ X := β ≫ σ
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
  have hw : joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ l = e := by
    rw [← joinInl_comp_map (Δ[1] : SSet.{u}) (boundary.{u} n).ι, ← J.inl_ι]
    simp only [Category.assoc]
    rw [hl]
    exact hsource
  refine ⟨Under.homMk l hw, ?_, ?_⟩
  · apply StructuredArrow.hom_ext
    exact hl
  · apply StructuredArrow.hom_ext
    exact hp

end SSet.CocartesianEdge
