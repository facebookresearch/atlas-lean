/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerGeneratingCofibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelClasses

/-!
# Genuine fixed-object cofibrations lift in the original global carrier

Reindex an arbitrary original global right map along the actual upper
and lower object functions of its full lifting square. The square's
literal object equations give the fixed-label right map, whose whole
original Hom maps retain only those proved endpoint transports. Its
actual scalar boundary RLP supplies the existing fixed-object lift.
Projection recovers both complete original global triangles. This
transfers the genuine fixed-object cofibrations to the global C0 left
class, without a global model-structure premise.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.Bergner
open FixedObjects

/-- The genuine original global cofibration class, defined by lifting against the full C0 right class. -/
abbrev cofibrations : MorphismProperty Carrier.{u} := generatingCofibrations.rlp.llp

/-- A genuine fixed-object cofibration lifts against arbitrary original global maps with ALL actual Hom boundary
lifts. -/
theorem fixedCofibration_hasLiftingProperty {O : Type u} {A B : FixedObjects O} (i : A ⟶ B)
    (hi : FixedObjectModel.cofibrations O i) {E H : Carrier.{u}} (r : E ⟶ H)
    (hr : ∀ x y : E, SSet.modelCategoryQuillen.I.rlp (r.map x y)) :
    HasLiftingProperty i.val r := by
  refine ⟨fun {top bottom} sq => ?_⟩
  let a : O → E := fun x => top.obj (vertex A x)
  let b : O → H := fun x => bottom.obj (vertex B x)
  let T := CarrierReindexing.object E a
  let U := CarrierReindexing.object H b
  let projectionE := CarrierReindexing.toTarget E a
  let projectionH := CarrierReindexing.toTarget H b
  have objects : ∀ x, (projectionE ≫ r).obj (vertex T x) = b x := by
    intro x
    change r.obj (top.obj (vertex A x)) = bottom.obj (vertex B x)
    have hx := congrArg (fun F : A.val ⟶ H => F.obj (vertex A x)) sq.w
    change r.obj (top.obj (vertex A x)) = bottom.obj (i.val.obj (vertex A x)) at hx
    rw [map_vertex i x] at hx
    exact hx
  let top' : A ⟶ T := CarrierLabelReadback.map A a top (fun _ => rfl)
  let bottom' : B ⟶ U := CarrierLabelReadback.map B b bottom (fun _ => rfl)
  let r' : T ⟶ U := CarrierLabelReadback.map T b (projectionE ≫ r) objects
  have top_fac : top'.val ≫ projectionE = top :=
    CarrierLabelReadback.map_fac A a top (fun _ => rfl)
  have bottom_fac : bottom'.val ≫ projectionH = bottom :=
    CarrierLabelReadback.map_fac B b bottom (fun _ => rfl)
  have right_fac : r'.val ≫ projectionH = projectionE ≫ r :=
    CarrierLabelReadback.map_fac T b (projectionE ≫ r) objects
  have hr' : FixedObjectModel.trivialFibrations O r' := by
    apply (boundaryFamily_rlp_iff r').mpr
    intro x y
    rw [CarrierLabelReadback.homMap_map]
    have hx : r.obj (a x) = b x := objects x
    have hy : r.obj (a y) = b y := objects y
    let e : (r.obj (a x) ⟶[SSet.{u}] r.obj (a y)) = (b x ⟶[SSet.{u}] b y) :=
      congrArg₂ (fun s t : H => (s ⟶[SSet.{u}] t)) hx hy
    change SSet.modelCategoryQuillen.I.rlp ((𝟙 _ ≫ r.map (a x) (a y)) ≫ eqToHom e)
    rw [Category.id_comp]
    exact SSet.modelCategoryQuillen.I.rlp.comp_mem _ _ (hr (a x) (a y))
      (MorphismProperty.rlp_of_isIso (C := SSet.{u}) SSet.modelCategoryQuillen.I (eqToHom e))
  have sq' : CommSq top' i r' bottom' := ⟨by
    apply CarrierLabelMaps.projection_injective b
    change (top'.val ≫ r'.val) ≫ projectionH = (i.val ≫ bottom'.val) ≫ projectionH
    calc
      (top'.val ≫ r'.val) ≫ projectionH = top'.val ≫ (r'.val ≫ projectionH) := Category.assoc _ _ _
      _ = top'.val ≫ (projectionE ≫ r) := congrArg (fun k => top'.val ≫ k) right_fac
      _ = (top'.val ≫ projectionE) ≫ r := (Category.assoc _ _ _).symm
      _ = top ≫ r := congrArg (fun k => k ≫ r) top_fac
      _ = i.val ≫ bottom := sq.w
      _ = i.val ≫ (bottom'.val ≫ projectionH) := congrArg (fun k => i.val ≫ k) bottom_fac.symm
      _ = (i.val ≫ bottom'.val) ≫ projectionH := (Category.assoc _ _ _).symm⟩
  let _ : HasLiftingProperty i r' := hi r' hr'
  let lift' : B ⟶ T := sq'.lift
  let lift : B.val ⟶ E := lift'.val ≫ projectionE
  refine CommSq.HasLift.mk' ⟨lift, ?_, ?_⟩
  · change i.val ≫ (lift'.val ≫ projectionE) = top
    calc
      i.val ≫ (lift'.val ≫ projectionE) = (i.val ≫ lift'.val) ≫ projectionE := (Category.assoc _ _ _).symm
      _ = top'.val ≫ projectionE := congrArg (fun F : A ⟶ T => F.val ≫ projectionE) sq'.fac_left
      _ = top := top_fac
  · change (lift'.val ≫ projectionE) ≫ r = bottom
    calc
      (lift'.val ≫ projectionE) ≫ r = lift'.val ≫ (projectionE ≫ r) := Category.assoc _ _ _
      _ = lift'.val ≫ (r'.val ≫ projectionH) := congrArg (fun k => lift'.val ≫ k) right_fac.symm
      _ = (lift'.val ≫ r'.val) ≫ projectionH := (Category.assoc _ _ _).symm
      _ = bottom'.val ≫ projectionH := congrArg (fun F : B ⟶ U => F.val ≫ projectionH) sq'.fac_right
      _ = bottom := bottom_fac

/-- Forgetting a genuine fixed-object cofibration preserves the exact global C0 left lifting class on the SAME full
map. -/
theorem fixedCofibration_global {O : Type u} {A B : FixedObjects O} (i : A ⟶ B)
    (hi : FixedObjectModel.cofibrations O i) : cofibrations i.val := by
  intro E H r hr
  exact fixedCofibration_hasLiftingProperty i hi r ((generatingCofibrations_rlp_iff r).mp hr).2

end CategoryTheory.SimplicialEnrichment.Bergner
