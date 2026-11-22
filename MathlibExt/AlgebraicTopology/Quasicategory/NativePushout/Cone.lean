/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Basic
public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.JoinShape
public import MathlibExt.AlgebraicTopology.Quasicategory.ColimitCone

/-!
# The actual native pushout cone point

The entire original walking-span diamond is the right cone on its original
span. The opposite join comparison constructs this full shape isomorphism.
Actual under-slice index transport and currying then identify the native
pushout condition with initiality of the given original whole cone point.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.NativePushout

/-- The reversed whole left cone is the right cone on the original full span. -/
def reversedConeJoinIso : NativePullback.squareShape.{u}.op ≅ spanShape.{u} ⋆ Δ[0] :=
  opFunctor.mapIso NativePullback.shapeJoinIso ≪≫
    joinOppositeIso Δ[0] NativePullback.cospanShape ≪≫
      (join.obj NativePullback.cospanShape.op).mapIso (stdSimplex.opIso ⦋0⦌) ≪≫
        (join.flip.obj (Δ[0] : SSet.{u})).mapIso spanOppositeIso

/-- The whole original coherent diamond is its entire right cone. -/
def shapeJoinIso : squareShape.{u} ≅ spanShape.{u} ⋆ Δ[0] :=
  squareOppositeIso.symm ≪≫ reversedConeJoinIso

/-- The reversed full cospan inclusion is the original right-cone diagram inclusion. -/
theorem op_cospanInclusion_comp_reversedConeJoinIso_hom :
    opFunctor.map NativePullback.cospanInclusion.{u} ≫ reversedConeJoinIso.hom =
      spanOppositeIso.hom ≫ joinInl spanShape Δ[0] := by
  change opFunctor.map NativePullback.cospanInclusion ≫
      (opFunctor.map NativePullback.shapeJoinIso.hom ≫
        ((joinOppositeIso Δ[0] NativePullback.cospanShape).hom ≫
          ((join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
            (join.map spanOppositeIso.hom).app Δ[0]))) = _
  calc
    _ = ((opFunctor.map (NativePullback.cospanInclusion ≫
        NativePullback.shapeJoinIso.hom) ≫
        (joinOppositeIso Δ[0] NativePullback.cospanShape).hom) ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom) ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ((opFunctor.map (joinInr Δ[0] NativePullback.cospanShape) ≫
        (joinOppositeIso Δ[0] NativePullback.cospanShape).hom) ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom) ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      rw [NativePullback.cospanInclusion_comp_shapeJoinIso_hom]
    _ = (joinInl NativePullback.cospanShape.op (Δ[0] : SSet.{u}).op ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom) ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      rw [op_joinInr_comp_joinOppositeIso_hom]
    _ = joinInl NativePullback.cospanShape.op Δ[0] ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by rw [joinInl_comp_map]
    _ = spanOppositeIso.hom ≫ joinInl spanShape Δ[0] :=
      (map_comp_joinInl spanOppositeIso.hom Δ[0]).symm

/-- The original full span inclusion is the original right-cone inclusion. -/
@[reassoc]
theorem spanInclusion_comp_shapeJoinIso_hom :
    spanInclusion.{u} ≫ shapeJoinIso.hom = joinInl spanShape Δ[0] := by
  apply (cancel_epi spanOppositeIso.hom).mp
  calc
    spanOppositeIso.hom ≫ (spanInclusion ≫ shapeJoinIso.hom) =
        (opFunctor.map NativePullback.cospanInclusion ≫ squareOppositeIso.hom) ≫
          shapeJoinIso.hom := by
      rw [← Category.assoc, ← op_cospanInclusion_comp_squareOppositeIso_hom]
    _ = opFunctor.map NativePullback.cospanInclusion ≫ reversedConeJoinIso.hom := by
      change (opFunctor.map NativePullback.cospanInclusion ≫ squareOppositeIso.hom) ≫
        (squareOppositeIso.inv ≫ reversedConeJoinIso.hom) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = spanOppositeIso.hom ≫ joinInl spanShape Δ[0] :=
      op_cospanInclusion_comp_reversedConeJoinIso_hom

/-- Reversal retains the actual adjoined cone vertex through the whole right-cone shape. -/
theorem opposite_initialPoint_comp_reversedConeJoinIso_hom :
    oppositeVertex (NativePullback.point WithInitial.star) ≫ reversedConeJoinIso.{u}.hom =
      joinInr spanShape Δ[0] := by
  change ((stdSimplex.opIso ⦋0⦌).inv ≫
      opFunctor.map (NativePullback.point WithInitial.star)) ≫
      (opFunctor.map NativePullback.shapeJoinIso.hom ≫
        ((joinOppositeIso Δ[0] NativePullback.cospanShape).hom ≫
          ((join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
            (join.map spanOppositeIso.hom).app Δ[0]))) = _
  calc
    _ = (((stdSimplex.opIso ⦋0⦌).inv ≫
        opFunctor.map (NativePullback.point WithInitial.star ≫
          NativePullback.shapeJoinIso.hom)) ≫
        (joinOppositeIso Δ[0] NativePullback.cospanShape).hom) ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (((stdSimplex.opIso ⦋0⦌).inv ≫
        opFunctor.map (joinInl Δ[0] NativePullback.cospanShape)) ≫
        (joinOppositeIso Δ[0] NativePullback.cospanShape).hom) ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      rw [NativePullback.initialPoint_comp_shapeJoinIso_hom]
    _ = ((stdSimplex.opIso ⦋0⦌).inv ≫
        joinInr NativePullback.cospanShape.op (Δ[0] : SSet.{u}).op) ≫
        (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      simpa only [Category.assoc] using congrArg
        (fun f => (stdSimplex.opIso ⦋0⦌).inv ≫ f ≫
          (join.obj NativePullback.cospanShape.op).map (stdSimplex.opIso ⦋0⦌).hom ≫
            (join.map spanOppositeIso.hom).app Δ[0])
        (op_joinInl_comp_joinOppositeIso_hom (Δ[0] : SSet.{u}) NativePullback.cospanShape)
    _ = (((stdSimplex.opIso ⦋0⦌).inv ≫ (stdSimplex.opIso ⦋0⦌).hom) ≫
        joinInr NativePullback.cospanShape.op Δ[0]) ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      simpa only [Category.assoc] using congrArg
        (fun f => (stdSimplex.opIso ⦋0⦌).inv ≫ f ≫ (join.map spanOppositeIso.hom).app Δ[0])
        (map_comp_joinInr (stdSimplex.opIso ⦋0⦌).hom NativePullback.cospanShape.op).symm
    _ = joinInr NativePullback.cospanShape.op Δ[0] ≫
        (join.map spanOppositeIso.hom).app Δ[0] := by
      rw [Iso.inv_hom_id, Category.id_comp]
    _ = joinInr spanShape Δ[0] := joinInr_comp_map spanOppositeIso.hom Δ[0]

/-- The original terminal square vertex is the original right-cone vertex. -/
@[reassoc]
theorem terminalPoint_comp_shapeJoinIso_hom :
    point WithTerminal.star ≫ shapeJoinIso.{u}.hom = joinInr spanShape Δ[0] := by
  rw [← opposite_initialPoint_comp_squareOppositeIso_hom]
  change (oppositeVertex (NativePullback.point WithInitial.star) ≫ squareOppositeIso.hom) ≫
      (squareOppositeIso.inv ≫ reversedConeJoinIso.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact opposite_initialPoint_comp_reversedConeJoinIso_hom

variable {X : SSet.{u}}

/-- The entire original coherent square expressed as its original right cone. -/
def coneDiagram (q : squareShape.{u} ⟶ X) : spanShape.{u} ⋆ Δ[0] ⟶ X :=
  shapeJoinIso.inv ≫ q

/-- Restricting the original whole cone retains the same full original span. -/
theorem coneDiagram_fixed (q : squareShape.{u} ⟶ X) :
    joinInl spanShape Δ[0] ≫ coneDiagram q = spanInclusion ≫ q := by
  have hi : joinInl spanShape Δ[0] ≫ shapeJoinIso.inv = spanInclusion := by
    apply (cancel_mono shapeJoinIso.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, spanInclusion_comp_shapeJoinIso_hom]
  rw [coneDiagram, ← Category.assoc, hi]

/-- The whole original right cone has the actual original terminal square point as its vertex. -/
theorem coneDiagram_vertex (q : squareShape.{u} ⟶ X) :
    joinInr spanShape Δ[0] ≫ coneDiagram q = point WithTerminal.star ≫ q := by
  have hi : joinInr spanShape Δ[0] ≫ shapeJoinIso.inv = point WithTerminal.star := by
    apply (cancel_mono shapeJoinIso.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, terminalPoint_comp_shapeJoinIso_hom]
  rw [coneDiagram, ← Category.assoc, hi]

/-- The actual whole cone point projects to the same original terminal square vertex. -/
theorem conePoint_proj (q : squareShape.{u} ⟶ X) :
    sliceUnder.conePoint (spanInclusion ≫ q) (coneDiagram q) (coneDiagram_fixed q) ≫
      sliceUnder.proj X (spanInclusion ≫ q) = point WithTerminal.star ≫ q :=
  (sliceUnder.conePoint_proj _ _ (coneDiagram_fixed q)).trans (coneDiagram_vertex q)

/-- The native square condition is the colimit condition of its entire original right cone. -/
theorem isPushoutSquare_iff_isColimitCone (q : squareShape.{u} ⟶ X) :
    IsPushoutSquare q ↔ IsColimitCone (coneDiagram q) := by
  have hi : joinInl spanShape Δ[0] ≫ shapeJoinIso.inv =
      (Iso.refl spanShape).hom ≫ spanInclusion := by
    apply (cancel_mono shapeJoinIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.refl_hom, Category.id_comp, spanInclusion_comp_shapeJoinIso_hom]
  unfold IsPushoutSquare IsColimitCone
  apply forall_congr'
  intro n
  exact sliceUnder.hasLiftingProperty_restrictionIndex_iff X q spanInclusion
    (joinInl spanShape Δ[0]) shapeJoinIso.symm (Iso.refl spanShape) hi (boundary n).ι

/-- The original pushout condition is initiality of its actual whole cone point. -/
theorem isPushoutSquare_iff_isInitialVertex (q : squareShape.{u} ⟶ X) :
    IsPushoutSquare q ↔ IsInitialVertex
      (sliceUnder.conePoint (spanInclusion ≫ q) (coneDiagram q) (coneDiagram_fixed q)) :=
  (isPushoutSquare_iff_isColimitCone q).trans
    (isColimitCone_iff_isInitialVertex _ _ (coneDiagram_fixed q))

end SSet.NativePushout
