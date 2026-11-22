/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalProductUnits
import MathlibExt.CategoryTheory.Limits.Types.BinaryCofan

/-!
# Naturality and full boundary monicity for the relative interval

Both zero units, the two entire endpoint copies and the native swap are
natural in each original slice map. Evaluation of the original double
point proves that the actual whole scalar boundary is monic, with its
two different interval coordinates still distinguished.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The original relative zero-unit inverses retain every whole original source map. -/
theorem relativePointProductIso_inv_natural {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    f ≫ (relativePointProductIso Z Y).inv = (relativePointProductIso Z X).inv ≫
      (overParameterMap f).app (Δ[0] : SSet.{u}) := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  rfl

/-- The actual coordinate swap is natural over the unchanged original base. -/
theorem relativeIntervalProductIso_natural {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    (overParameterMap f).app (Δ[1] : SSet.{u}) ≫ (relativeIntervalProductIso Z Y).hom =
      (relativeIntervalProductIso Z X).hom ≫ (relativeIntervalCylinder Z).I.map f := by
  apply Over.OverMorphism.ext
  apply Hom.ext
  rfl

/-- Both original double-point copies are natural under their complete slice source maps. -/
theorem relativeDoublePointProductIso_inv_natural {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    coprod.map f f ≫ (relativeDoublePointProductIso Z Y).inv =
      (relativeDoublePointProductIso Z X).inv ≫ (overParameterMap f).app relativeIntervalDoublePoint.{u} := by
  let GX := overParameterFunctor Z X
  let GY := overParameterFunctor Z Y
  let τ := overParameterMap f
  let vX : X ⨿ X ⟶ GX.obj relativeIntervalDoublePoint.{u} := (relativeDoublePointProductIso Z X).inv
  let vY : Y ⨿ Y ⟶ GY.obj relativeIntervalDoublePoint.{u} := (relativeDoublePointProductIso Z Y).inv
  let UX : GX.obj (Δ[0] : SSet.{u}) ≅ X := relativePointProductIso Z X
  let UY : GY.obj (Δ[0] : SSet.{u}) ≅ Y := relativePointProductIso Z Y
  have hU : f ≫ UY.inv = UX.inv ≫ τ.app (Δ[0] : SSet.{u}) := relativePointProductIso_inv_natural f
  change coprod.map f f ≫ vY = vX ≫ τ.app relativeIntervalDoublePoint.{u}
  apply coprod.hom_ext
  · calc
      coprod.inl ≫ (coprod.map f f ≫ vY) = f ≫ (coprod.inl ≫ vY) := by rw [coprod.inl_map_assoc]
      _ = f ≫ (UY.inv ≫ GY.map coprod.inl) := congrArg (fun z => f ≫ z) (relativeDoublePointProductIso_inv_inl Z Y)
      _ = (UX.inv ≫ τ.app (Δ[0] : SSet.{u})) ≫ GY.map coprod.inl :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _) hU)
      _ = UX.inv ≫ (GX.map coprod.inl ≫ τ.app relativeIntervalDoublePoint.{u}) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => UX.inv ≫ z) (τ.naturality coprod.inl).symm)
      _ = (coprod.inl ≫ vX) ≫ τ.app relativeIntervalDoublePoint.{u} :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ _) (relativeDoublePointProductIso_inv_inl Z X).symm)
      _ = coprod.inl ≫ (vX ≫ τ.app relativeIntervalDoublePoint.{u}) := Category.assoc _ _ _
  · calc
      coprod.inr ≫ (coprod.map f f ≫ vY) = f ≫ (coprod.inr ≫ vY) := by rw [coprod.inr_map_assoc]
      _ = f ≫ (UY.inv ≫ GY.map coprod.inr) := congrArg (fun z => f ≫ z) (relativeDoublePointProductIso_inv_inr Z Y)
      _ = (UX.inv ≫ τ.app (Δ[0] : SSet.{u})) ≫ GY.map coprod.inr :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _) hU)
      _ = UX.inv ≫ (GX.map coprod.inr ≫ τ.app relativeIntervalDoublePoint.{u}) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => UX.inv ≫ z) (τ.naturality coprod.inr).symm)
      _ = (coprod.inr ≫ vX) ≫ τ.app relativeIntervalDoublePoint.{u} :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ _) (relativeDoublePointProductIso_inv_inr Z X).symm)
      _ = coprod.inr ≫ (vX ≫ τ.app relativeIntervalDoublePoint.{u}) := Category.assoc _ _ _

/-- The original whole double-point boundary is genuinely monic in every original simplicial degree. -/
theorem relativeIntervalWholeBoundary_mono : Mono relativeIntervalWholeBoundary.{u} := by
  let a := relativeIntervalWholeBoundary.{u}
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (a.app n) := fun n => by
    rcases n with ⟨⟨m⟩⟩
    let n := op ⦋m⦌
    let G := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj n
    let c : BinaryCofan ((Δ[0] : SSet.{u}).obj n) ((Δ[0] : SSet.{u}).obj n) :=
      BinaryCofan.mk (G.map (coprod.inl : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}))
        (G.map (coprod.inr : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}))
    let hc : IsColimit c := isColimitOfHasBinaryCoproductOfPreservesColimit G _ _
    have h₀ : c.inl ≫ a.app n = (stdSimplex.{u}.δ (1 : Fin 2)).app n := by
      change G.map (coprod.inl : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}) ≫
        G.map relativeIntervalWholeBoundary.{u} = G.map (stdSimplex.{u}.δ (1 : Fin 2))
      rw [← CategoryTheory.Functor.map_comp, relativeIntervalWholeBoundary, coprod.inl_desc]
    have h₁ : c.inr ≫ a.app n = (stdSimplex.{u}.δ (0 : Fin 2)).app n := by
      change G.map (coprod.inr : (Δ[0] : SSet.{u}) ⟶ relativeIntervalDoublePoint.{u}) ≫
        G.map relativeIntervalWholeBoundary.{u} = G.map (stdSimplex.{u}.δ (0 : Fin 2))
      rw [← CategoryTheory.Functor.map_comp, relativeIntervalWholeBoundary, coprod.inr_desc]
    apply Types.binaryCofan_mono_of_disjoint hc (a.app n)
    · rw [h₀]
      intro x y _
      apply DFunLike.ext
      intro j
      apply Fin.ext
      omega
    · rw [h₁]
      intro x y _
      apply DFunLike.ext
      intro j
      apply Fin.ext
      omega
    · apply Set.disjoint_left.mpr
      rintro z ⟨x, hx⟩ ⟨y, hy⟩
      have h := hx.trans hy.symm
      rw [h₀, h₁] at h
      have hx' : x = stdSimplex.const 0 0 n := by
        apply DFunLike.ext
        intro j
        apply Fin.ext
        omega
      have hy' : y = stdSimplex.const 0 0 n := by
        apply DFunLike.ext
        intro j
        apply Fin.ext
        omega
      have h' := congrArg (fun q => stdSimplex.asOrderHom q 0) h
      rw [hx', hy'] at h'
      change (0 : Fin 2) = 1 at h'
      exact (by decide : (0 : Fin 2) ≠ 1) h'
  exact NatTrans.mono_of_mono_app _

end SSet.Marked
