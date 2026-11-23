/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization.Denominator
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.CategoryTheory.NerveCommonHom
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Realization of the denominator comma adjunction

The denominator comma retraction and inclusion induce continuous maps between
the realizations of the comma category and the fixed-denominator strict fiber.
Their adjunction gives a homotopy equivalence with these literal forward and
inverse maps. The adjunction unit is reversed after realization to obtain the
required inverse homotopy.
-/

@[expose] public section

universe u v uX vX

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.IsCofibered
open scoped CategoryTheory.Limits.CoreBiprodMonoidal
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.MonoidalActionCategory

-- Both original nerves live at max(u,v,uX,vX), with their original categories.
-- The comma object level may exceed the strict-fiber object level.
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- Realization of the actual comma retraction and inclusion gives a homotopy equivalence.
The adjunction unit is reversed only after it is realized as a continuous homotopy. -/
def denominatorCommaRealizedHomotopyEquiv (s : Core C) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj
        (nerve (CostructuredArrow (denominatorProjection (Core C) X)
          (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) : SSet.{max u v uX vX}))
      (SSet.toTop.obj (nerve (denominatorFiber (X := X) s) : SSet.{max u v uX vX})) := by
  let L := denominatorCommaRetraction (X := X) s
  let R := denominatorCommaInclusion (X := X) s
  let h : L ⊣ R := denominatorCommaAdjunction (X := X) s
  let NC : SSet.{max u v uX vX} := nerve (CostructuredArrow (denominatorProjection (Core C) X)
    (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)))
  let NF : SSet.{max u v uX vX} := nerve (denominatorFiber (X := X) s)
  let f : NC ⟶ NF := nerveMapCommonHom.{max u uX, max u v, vX} L
  let g : NF ⟶ NC := nerveMapCommonHomUp.{max u uX, max u v, vX} R
  have hLR : f ≫ g = nerveMap (L ⋙ R) :=
    nerveMapCommonHom_comp_up.{max u uX, max u v, vX} L R
  have hRL : g ≫ f = nerveMap (R ⋙ L) :=
    nerveMapCommonHomUp_comp.{max u uX, max u v, vX} R L
  refine
    { toFun := (SSet.toTop.map f).hom
      invFun := (SSet.toTop.map g).hom
      left_inv := ?_
      right_inv := ?_ }
  · have hu0 : SSet.Homotopy (𝟙 NC) (nerveMap (L ⋙ R)) := by
      simpa only [nerveMap_id] using CategoryTheory.NatTrans.nerveHomotopy h.unit
    have hu : SSet.Homotopy (𝟙 NC) (f ≫ g) := hLR.symm ▸ hu0
    let ht := SSet.realizeHomotopy NC NC (𝟙 NC) (f ≫ g) hu
    have hComp : (SSet.toTop.map (f ≫ g)).hom =
        (SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 NC)).hom = ContinuousMap.id (SSet.toTop.obj NC) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.symm.cast hComp hId⟩
  · have he0 : SSet.Homotopy (nerveMap (R ⋙ L)) (𝟙 NF) := by
      simpa only [nerveMap_id] using CategoryTheory.NatTrans.nerveHomotopy h.counit
    have he : SSet.Homotopy (g ≫ f) (𝟙 NF) := hRL.symm ▸ he0
    let ht := SSet.realizeHomotopy NF NF (g ≫ f) (𝟙 NF) he
    have hComp : (SSet.toTop.map (g ≫ f)).hom =
        (SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 NF)).hom = ContinuousMap.id (SSet.toTop.obj NF) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.cast hComp hId⟩
/-- Its forward continuous map is the realized actual comma retraction. -/
theorem denominatorCommaRealizedHomotopyEquiv_toFun (s : Core C) :
    (denominatorCommaRealizedHomotopyEquiv (X := X) s).toFun =
      (SSet.toTop.map
      (nerveMapCommonHom.{max u uX, max u v, vX}
        (denominatorCommaRetraction (X := X) s))).hom := rfl

/-- Its reverse continuous map is the realized actual strict-fiber inclusion. -/
theorem denominatorCommaRealizedHomotopyEquiv_invFun (s : Core C) :
    (denominatorCommaRealizedHomotopyEquiv (X := X) s).invFun =
      (SSet.toTop.map
      (nerveMapCommonHomUp.{max u uX, max u v, vX}
        (denominatorCommaInclusion (X := X) s))).hom := rfl

end CategoryTheory.MonoidalActionCategory

end
