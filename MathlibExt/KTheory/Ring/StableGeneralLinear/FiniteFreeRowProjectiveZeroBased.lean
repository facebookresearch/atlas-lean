/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveZeroSpace
public import MathlibExt.Topology.CWComplex.BasedWhiteheadUniverseLift
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.Topology.Category.TopCat.HomotopyExtension
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Based transport of the original projective zero-space model

The source realization is moved to the actual common-universe nerve model.
Its realized-vertex Hurewicz cofibration extends the computed original
zero-unit path. The derived based weak map has actual point cofibrations,
so the existing based inverse theorem supplies both point-relative inverse
families. The actual source homeomorphism returns them to the original
small row realization. No based model or family is a caller input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped unitInterval TopCat.modelCategory

attribute [local instance] uliftCategory

universe u v

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original small and full-projective zero spaces have a derived
based HE with BOTH complete point-relative inverse families. Its forward
retuning follows the SAME computed additive zero-unit path at every time.
The Ring and independent projective carrier are unchanged. -/
public theorem finiteFreeRowProjectiveZeroBasedEquivalence_exists :
    let X := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
    let x := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun x = y ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) ∧
      ∃ K : ContinuousMap.Homotopy
          (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun e.toFun,
        ∀ t : unitInterval, K (t, x) = finiteFreeRowProjectiveZeroUnitPath.{u, v} R t := by
  let C : Type u := SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)
  let X : TopCat.{u} :=
    SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
  let Y : TopCat.{(max u v) + 1} :=
    SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
  let x : X :=
    SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
  let y : Y :=
    SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
  let z : C := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)
  let A : Type ((max u v) + 1) :=
    ULiftHom.{(max u v) + 1} (ULift.{(max u v) + 1} C)
  let M : TopCat.{(max u v) + 1} := SSet.toTop.obj (nerve A)
  let vm : ComposableArrows A 0 :=
    ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up z) : A)
  let m : M := SSet.realizedVertex (X := nerve A) vm
  let h : M ≃ₜ X := SSet.realizedNerveLiftHomeomorph.{u, u, (max u v) + 1} C
  let e₀ : ContinuousMap.HomotopyEquiv X Y :=
    finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R
  let p₀ : Path (e₀.toFun x) y := finiteFreeRowProjectiveZeroUnitPath.{u, v} R
  have hm : h m = x :=
    (SSet.realizedNerveLiftHomeomorph_vertex.{u, u, (max u v) + 1} C z).trans
      (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.IdempotentModel R)).symm
  have hHEP : TopCat.IsHurewiczCofibration
      (TopCat.const m : TopCat.of PUnit.{(max u v) + 2} ⟶ M) :=
    SSet.realizedVertex_isHurewiczCofibration (X := nerve A) vm
  letI : Cofibration (TopCat.const m : TopCat.of PUnit.{(max u v) + 2} ⟶ M) :=
    SSet.realizedVertex_pointMap_cofibration (nerve A) vm
  let D : Type ((max u v) + 1) := SInverseS.ZeroComponent (C := FGProjectiveCat.{max u v} R)
  let vy : ComposableArrows D 0 := ComposableArrows.mk₀
    (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max u v} R))
  letI : Cofibration (TopCat.const y : TopCat.of PUnit.{(max u v) + 2} ⟶ Y) := by
    have hy : y = SSet.realizedVertex (X := nerve D) vy :=
      SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
        (C := FGProjectiveCat.{max u v} R)
    rw [hy]
    exact SSet.realizedVertex_pointMap_cofibration (nerve D) vy
  exact TopCat.exists_pointRelativeEquivalence_of_sourceHomeomorph X M Y x m y h hm e₀ p₀ hHEP

end AlgebraicKTheory.StableGL

end
