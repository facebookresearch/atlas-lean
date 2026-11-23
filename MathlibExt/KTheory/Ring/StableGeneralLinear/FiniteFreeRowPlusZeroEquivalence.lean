/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowPlusComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentHSpace
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentOrdinaryHSpace
public import MathlibExt.Topology.Homotopy.HSpaceHomologyWhitehead
public import MathlibExt.Topology.CWComplex.NativeSingularModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# The actual independent cell plus and the original row zero component

The original row comparison extends across the independently constructed
cell plus with its strict source triangle. Its all-degree ordinary integral
homology isomorphism is already derived. The actual cell H-space and the
actual ordinary zero H-space supply the hypotheses of the accepted
homology Whitehead theorem. Both point cofibrations and genuine CW types
are derived from their original models. The resulting inverse families
fix the original points, and the original source-relative uniqueness
families are retained. No H-space, homology, model, factor or inverse is
an input of the Ring theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The independently constructed ORIGINAL cell plus is based homotopy
equivalent to the original small-projective zero space. Its literal
forward field has the strict original row-source triangle, and BOTH
inverse families fix the original marked points. The complete original
source-relative uniqueness families remain available for every candidate. -/
public theorem finiteFreeRowIndependentPlusZeroEquivalence_exists :
    let B := independentBGLCellTarget R
    let i := independentBGLCellInclusion R
    let b := independentBGLCellPoint R
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    ∃ e : B ≃ₕ Y,
      e.toFun.comp i.hom = (finiteFreeRowBasedZeroComparison R).hom ∧
      e.toFun b = y ∧ e.invFun y = b ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id B) {b}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) ∧
      ∀ G : B ⟶ Y, i ≫ G = finiteFreeRowBasedZeroComparison R →
        Nonempty (ContinuousMap.HomotopyRel e.toFun G.hom (Set.range i)) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom e.toFun (Set.range i)) := by
  let B := independentBGLCellTarget R
  let i := independentBGLCellInclusion R
  let b := independentBGLCellPoint R
  let C := FGProjectiveCat.IdempotentModel R
  let K := nerve (SInverseS.ZeroComponent (C := C))
  let Y := SInverseS.ComponentTranslation.zeroSpace (C := C)
  let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := C)
  letI : HSpace B := (independentBGLCellHSpace R).val
  letI : HSpace Y := (SInverseS.ComponentTranslation.ordinaryZeroHSpace C).val
  letI : PathConnectedSpace B := independentBGLCellTarget_pathConnected R
  letI : SSet.IsConnected K :=
    CategoryTheory.nerve_isConnected_of_category_isConnected (C := SInverseS.ZeroComponent (C := C))
  letI : PathConnectedSpace Y := SSet.pathConnectedSpace_realization_of_isConnected K
  letI : Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) :=
    independentBGLCellPoint_cofibration R
  letI : Cofibration (TopCat.const y : TopCat.of PUnit.{u + 1} ⟶ Y) := by
    have hPoint : y = SSet.realizedVertex
        (ComposableArrows.mk₀ (SInverseS.zeroComponentBaseObject (C := C))) :=
      SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex (C := C)
    rw [hPoint]
    exact SSet.realizedVertex_pointMap_cofibration K
      (ComposableArrows.mk₀ (SInverseS.zeroComponentBaseObject (C := C)))
  let M := TopCat.nativeSingularPointModelOfCofibrantPoint B b
  have hCWB : ∃ A : TopCat.{u}, ∃ _ : T2Space A,
      ∃ _ : Topology.CWComplex (Set.univ : Set A), Nonempty (A ≃ₕ B) := M.cwType
  have hCWY : ∃ A : TopCat.{u}, ∃ _ : T2Space A,
      ∃ _ : Topology.CWComplex (Set.univ : Set A), Nonempty (A ≃ₕ Y) :=
    ⟨Y, SSet.realization_t2Space K, SSet.instCWComplexToTop K,
      ⟨ContinuousMap.HomotopyEquiv.refl Y⟩⟩
  obtain ⟨F, hF, hPoint, hHomology, hUnique⟩ :=
    finiteFreeRowIndependentPlusComparison_exists R
  have hFPoint : F b = y :=
    (congrArg F (independentBGLCellInclusion_point R)).symm.trans hPoint
  letI : Cofibration (TopCat.const (F b) : TopCat.of PUnit.{u + 1} ⟶ Y) := by
    have hConst : (TopCat.const (F b) : TopCat.of PUnit.{u + 1} ⟶ Y) =
        TopCat.const y := congrArg
      (fun z : Y => (TopCat.const z : TopCat.of PUnit.{u + 1} ⟶ Y)) hFPoint
    rw [hConst]
    infer_instance
  obtain ⟨g, hg, ⟨L⟩, ⟨S⟩⟩ :=
    TopCat.HSpaceHomologyWhitehead.exists_point_relative_inverse_of_integralHomology_isIso
      hCWB hCWY F hHomology b
  let LB := L.cast (TopCat.hom_comp F g) (TopCat.hom_id (X := B))
  let SY := S.cast (TopCat.hom_comp g F) (TopCat.hom_id (X := Y))
  let e : B ≃ₕ Y :=
    { toFun := F.hom
      invFun := g.hom
      left_inv := ⟨LB.toHomotopy⟩
      right_inv := ⟨SY.toHomotopy⟩ }
  have hTriangle : e.toFun.comp i.hom = (finiteFreeRowBasedZeroComparison R).hom :=
    (TopCat.hom_comp i F).symm.trans (congrArg TopCat.Hom.hom hF)
  have hInversePoint : e.invFun y = b := (congrArg g hFPoint).symm.trans hg
  have hRight : Nonempty
      (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) :=
    Eq.mp (congrArg (fun z : Y => Nonempty
      (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {z}))
      hFPoint) ⟨SY⟩
  exact ⟨e, hTriangle, hFPoint, hInversePoint, ⟨LB⟩, hRight, hUnique⟩

end AlgebraicKTheory.StableGL

end
