/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence
public import MathlibExt.Topology.CWComplex.BasedWhitehead
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# The original completed-Core and additive-Pair realizations at zero

The existing actual category equivalence keeps both positive-first
coordinates. Its realized forward map therefore takes the original
positive Core unit to the original Pair zero vertex. The original nerve
map is weak, and both points are the actual realized-vertex cofibrations.
The accepted based inverse theorem gives an inverse and BOTH complete
singleton-relative families while keeping that literal forward map.
No model, inverse, point equality or family is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped ContinuousMap TopCat.modelCategory ZeroObject
  CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] MonoidalActionCategory.diagonalAction

universe u v

namespace CategoryTheory.CoreLocalizationComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private theorem completedCoreUnit_toPair :
    (coreAdditivePairEquivalence (C := C)).functor.obj
        ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))) =
      (⟨0, 0⟩ : SInverseS.Pair C) := by
  rw [coreAdditivePairEquivalence_functor_obj]
  rfl

/-- The SAME canonical realized Core-to-Pair map preserves the actual
completed unit and original Pair zero point. -/
public theorem coreAdditivePairRealization_unit :
    (SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor))
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀
        ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) =
      SSet.realizedVertex (X := nerve (SInverseS.Pair C))
        (ComposableArrows.mk₀ (⟨0, 0⟩ : SInverseS.Pair C)) := by
  let E := coreAdditivePairEquivalence (C := C)
  let a := (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  exact (SSet.realizedVertex_naturality (nerveMap E.functor)
    (ComposableArrows.mk₀ a)).symm.trans
      ((congrArg (SSet.realizedVertex (X := nerve (SInverseS.Pair C)))
        (nerveMap_app_mk₀ E.functor a)).trans
        (congrArg (fun b : SInverseS.Pair C =>
          SSet.realizedVertex (X := nerve (SInverseS.Pair C)) (ComposableArrows.mk₀ b))
          (completedCoreUnit_toPair (C := C))))

/-- The original categorical equivalence realizes to a based homotopy
equivalence on ALL components. Its forward field is the literal original
Core-to-Pair map and BOTH inverse families fix the original zero vertices.
The category's object and Hom universes remain independent. -/
public theorem coreAdditivePairRealizationBasedEquivalence_exists :
    let X := SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))
    let Y := SSet.toTop.obj (nerve (SInverseS.Pair C))
    let x := SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
      (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))
    let y := SSet.realizedVertex (X := nerve (SInverseS.Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : SInverseS.Pair C))
    let f := SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)
    ∃ e : X ≃ₕ Y, e.toFun = f.hom ∧ e.toFun x = y ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  let X : TopCat.{max u v} := SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))
  let Y : TopCat.{max u v} := SSet.toTop.obj (nerve (SInverseS.Pair C))
  let x : X := SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
    (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))
  let y : Y := SSet.realizedVertex (X := nerve (SInverseS.Pair C))
    (ComposableArrows.mk₀ (⟨0, 0⟩ : SInverseS.Pair C))
  let E := coreAdditivePairEquivalence (C := C)
  let f : X ⟶ Y := SSet.toTop.map (nerveMap E.functor)
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{(max u v) + 1} ⟶ X) :=
    SSet.realizedVertex_pointMap_cofibration (nerve (SInverse (Core C) (Core C)))
      (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))
  letI : Cofibration (TopCat.const y : TopCat.of PUnit.{(max u v) + 1} ⟶ Y) :=
    SSet.realizedVertex_pointMap_cofibration (nerve (SInverseS.Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : SInverseS.Pair C))
  have hf : TopCat.weakHomotopyEquivalences f :=
    nerveMap_mem_realizationWeakEquivalences_of_isEquivalence E.functor
  obtain ⟨g, hg, ⟨L⟩, ⟨R⟩⟩ :=
    TopCat.exists_based_inverse_of_weak_of_cofibrant_points X Y x y f
      (coreAdditivePairRealization_unit (C := C)) hf
  let LX := L.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))
  let RY := R.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))
  let e : X ≃ₕ Y :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := ⟨LX.toHomotopy⟩
      right_inv := ⟨RY.toHomotopy⟩ }
  exact ⟨e, rfl, coreAdditivePairRealization_unit (C := C), hg, ⟨LX⟩, ⟨RY⟩⟩

end CategoryTheory.CoreLocalizationComparison

end
