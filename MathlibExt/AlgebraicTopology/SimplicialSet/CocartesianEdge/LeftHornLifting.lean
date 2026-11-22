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
# Strict left-horn lifting through the original cocartesian critical edge

The source-endpoint boundary join is the actual left outer horn. Its first
edge and both prescribed maps are identified explicitly, so the intrinsic
cocartesian boundary condition lifts the same entire base simplex.
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

/-- The original source-endpoint join comparison retains the whole critical first edge. -/
theorem leftHornCurve_eq (n : ℕ) :
    joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
      (joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι).inl ≫
        (joinBoundarySourceEndpointArrowIso.{u} n).hom.left =
          yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) := by
  let J := joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι
  let H := horn (n + 2) (0 : Fin (n + 3))
  let E := joinBoundarySourceEndpointArrowIso.{u} n
  let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
  let β : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
  have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
  change joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ α = _
  apply (cancel_mono H.ι).mp
  calc
    _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ J.ι ≫ β := by
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

/-- A p-cocartesian critical first edge supplies the original strict relative left-horn filler. -/
theorem exists_fill_leftHorn_of_isPCocartesian {X B : SSet.{u}} {p : X ⟶ B} {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (σBar : (Δ[n + 2] : SSet.{u}) ⟶ B)
    (hsq : σ₀ ≫ p = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σBar)
    (he : IsPCocartesian p (yonedaEquiv.symm (leftHornEdge σ₀).edge)) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
      Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ = σ₀ ∧ σ ≫ p = σBar := by
  let J := joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι
  let H := horn (n + 2) ((0 : Fin (n + 3)))
  let E := joinBoundarySourceEndpointArrowIso.{u} n
  let α : J.pt ⟶ (H : SSet.{u}) := E.hom.left
  let β : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ Δ[n + 2] := E.hom.right
  let α' : (H : SSet.{u}) ⟶ J.pt := E.inv.left
  let β' : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⋆ Δ[n] := E.inv.right
  have hE : α ≫ H.ι = J.ι ≫ β := E.hom.w
  have hE' : α' ≫ J.ι = H.ι ≫ β' := E.inv.w
  have hα : α' ≫ α = 𝟙 _ := Arrow.inv_hom_id_left E
  have hβ : β' ≫ β = 𝟙 _ := Arrow.inv_hom_id_right E
  let e : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm (σ₀.app _ (leftHornEdgeSimplex.{u} n))
  have he' : IsPCocartesian p e := he
  let u : J.pt ⟶ X := α ≫ σ₀
  let v : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ B := β ≫ σBar
  have huv : u ≫ p = J.ι ≫ v := by
    dsimp only [u, v]
    calc
      (α ≫ σ₀) ≫ p = α ≫ (H.ι ≫ σBar) := by rw [Category.assoc, hsq]
      _ = (α ≫ H.ι) ≫ σBar := (Category.assoc _ _ _).symm
      _ = (J.ι ≫ β) ≫ σBar := congrArg (fun f => f ≫ σBar) hE
      _ = J.ι ≫ (β ≫ σBar) := Category.assoc _ _ _
  have hu : joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ u = e := by
    have hc : joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ α =
        yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) := leftHornCurve_eq n
    dsimp only [u, e]
    calc
      _ = (joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ α) ≫ σ₀ := by
        simp only [Category.assoc]
      _ = yonedaEquiv.symm (leftHornEdgeSimplex.{u} n) ≫ σ₀ := congrArg (fun f => f ≫ σ₀) hc
      _ = _ := by apply yonedaEquiv.injective; simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hv : joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ v = e ≫ p := by
    have hi : joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ J.ι =
        joinInl (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) := by
      calc
        _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫
            (join.obj (Δ[1] : SSet.{u})).map (boundary.{u} n).ι := by
              simpa only [Category.assoc] using congrArg
                (fun f => joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ f) J.inl_ι
        _ = _ := joinInl_comp_map (Δ[1] : SSet.{u}) (boundary.{u} n).ι
    calc
      _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ J.ι ≫ v := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ v) hi.symm
      _ = joinInl (Δ[1] : SSet.{u}) (boundary.{u} n : SSet.{u}) ≫ J.inl ≫ u ≫ p := by
        rw [← huv]
      _ = e ≫ p := by simpa only [Category.assoc] using congrArg (fun f => f ≫ p) hu
  let top : joinUnderPushoutSource (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι ⟶
      Under.mk e := Under.homMk u hu
  let bottom : (joinUnder (Δ[1] : SSet.{u})).obj (Δ[n] : SSet.{u}) ⟶
      Under.mk (e ≫ p) := Under.homMk v hv
  let _ : HasLiftingProperty
      (joinUnderPushoutMap (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι)
      (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) :=
    (isPCocartesian_iff_joinLifting p e).mp he' n
  have sq : CommSq top (joinUnderPushoutMap (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι)
      (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) bottom := by
    constructor
    apply StructuredArrow.hom_ext
    exact huv
  let l : (Δ[1] : SSet.{u}) ⋆ (Δ[n] : SSet.{u}) ⟶ X := sq.lift.right
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


end SSet.CocartesianEdge
