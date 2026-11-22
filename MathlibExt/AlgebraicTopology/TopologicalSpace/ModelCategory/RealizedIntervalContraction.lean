/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorAction

/-!
# Explicit contraction of the SAME original realized interval coefficient

The actual original general realization of Δ[1] is compared with the literal
lifted unit interval. Its contraction is computed from that original native
comparison and unit-interval multiplication and symmetry. The full ordinary
homotopy fixes the original δ0 endpoint at every time. Its genuinely computed
free-point monoidal image retains both endpoints and the whole fixed-subspace
equation. No source cofibrancy, model law or supplied SDR data is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace CGWH.RealizedIntervalContraction

/-- The actual original endpoint comparison retains the full selected terminal-unit isomorphism. -/
def pointToUnit : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
  CGWH.point_isTerminal.{u, v}.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

/-- The original δ0 endpoint is exactly the time-one point of the native interval comparison. -/
theorem intervalOne_eq :
    CGWH.intervalOne.{u, v} = pointToUnit.hom ≫
      CGWH.homotopyIntervalEndpoint.{u, v} 1 ≫ CGWH.homotopyIntervalIsoInterval.{u, v}.hom := by
  rw [CGWH.homotopyIntervalIsoInterval_one, ← Category.assoc,
    CGWH.point_isTerminal.{u, v}.hom_ext
      (pointToUnit.hom ≫ CGWH.point_isTerminal.{u, v}.from (𝟙_ CGWH.{u, v})) (𝟙 _),
    Category.id_comp]

/-- Every original endpoint point has exactly the time-one coordinate under the same comparison. -/
theorem intervalOne_coordinate (p : CGWH.point.{u, v}) :
    CGWH.homotopyIntervalIsoInterval.{u, v}.inv (CGWH.intervalOne.{u, v} p) = ULift.up (1 :
      unitInterval) := by
  have h : CGWH.intervalOne.{u, v} ≫ CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
      pointToUnit.hom ≫ CGWH.homotopyIntervalEndpoint.{u, v} 1 := by
    rw [intervalOne_eq.{u, v}, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact ConcreteCategory.congr_hom h p

/--
The original native interval contracts to its actual δ0 endpoint, using its full chosen
comparison.
-/
def homotopy : TopCat.Homotopy
    (CGWH.cgwhToTop.{u, v}.map (𝟙 CGWH.interval.{u, v}))
    (CGWH.cgwhToTop.{u, v}.map
      (CGWH.intervalAugmentation.{u, v} ≫ CGWH.intervalOne.{u, v})) where
  toFun z := CGWH.homotopyIntervalIsoInterval.{u, v}.hom
    (ULift.up (unitInterval.symm (unitInterval.symm z.1 *
      unitInterval.symm (CGWH.homotopyIntervalIsoInterval.{u, v}.inv z.2).down)))
  continuous_toFun := by
    apply (ConcreteCategory.hom CGWH.homotopyIntervalIsoInterval.{u, v}.hom).continuous.comp
    apply continuous_uliftUp.comp
    apply unitInterval.continuous_symm.comp
    exact (unitInterval.continuous_symm.comp continuous_fst).mul
      (unitInterval.continuous_symm.comp
        (continuous_uliftDown.comp
          ((ConcreteCategory.hom CGWH.homotopyIntervalIsoInterval.{u, v}.inv).continuous.comp
            continuous_snd)))
  map_zero_left := by
    intro x
    change CGWH.homotopyIntervalIsoInterval.{u, v}.hom
      (ULift.up (unitInterval.symm (unitInterval.symm (0 : unitInterval) *
        unitInterval.symm (CGWH.homotopyIntervalIsoInterval.{u, v}.inv x).down))) = x
    simp only [unitInterval.symm_zero, one_mul, unitInterval.symm_symm]
    exact (CGWH.homeoOfIso.{u, v} CGWH.homotopyIntervalIsoInterval.{u, v}).apply_symm_apply x
  map_one_left := by
    intro x
    change CGWH.homotopyIntervalIsoInterval.{u, v}.hom
      (ULift.up (unitInterval.symm (unitInterval.symm (1 : unitInterval) *
        unitInterval.symm (CGWH.homotopyIntervalIsoInterval.{u, v}.inv x).down))) =
      CGWH.intervalOne.{u, v} (CGWH.intervalAugmentation.{u, v} x)
    simp only [unitInterval.symm_one, zero_mul, unitInterval.symm_zero]
    rw [← intervalOne_coordinate.{u, v} (CGWH.intervalAugmentation.{u, v} x)]
    exact (CGWH.homeoOfIso.{u, v} CGWH.homotopyIntervalIsoInterval.{u, v}).apply_symm_apply _

/-- The full all-time original contraction fixes every actual included δ0 endpoint point. -/
theorem homotopy_fixed (t : unitInterval) (p : CGWH.point.{u, v}) :
    homotopy.{u, v} (t, CGWH.intervalOne.{u, v} p) = CGWH.intervalOne.{u, v} p := by
  change CGWH.homotopyIntervalIsoInterval.{u, v}.hom
    (ULift.up (unitInterval.symm (unitInterval.symm t *
      unitInterval.symm (CGWH.homotopyIntervalIsoInterval.{u, v}.inv (CGWH.intervalOne.{u, v}
        p)).down))) = _
  rw [intervalOne_coordinate.{u, v}]
  simp only [unitInterval.symm_one, mul_zero, unitInterval.symm_zero]
  rw [← intervalOne_coordinate.{u, v} p]
  exact (CGWH.homeoOfIso.{u, v} CGWH.homotopyIntervalIsoInterval.{u, v}).apply_symm_apply _

/--
The genuine native time action is the transpose of that SAME jointly continuous original
homotopy.
-/
def action : CGWH.homotopyInterval.{u, v} ⊗ CGWH.interval.{u, v} ⟶ CGWH.interval.{u, v} :=
  CGWH.intervalHomotopyTensor.{u, v} (𝟙 CGWH.interval.{u, v})
    (CGWH.intervalAugmentation.{u, v} ≫ CGWH.intervalOne.{u, v}) homotopy.{u, v}

/-- At literal time zero the entire original native action is the identity. -/
theorem action_zero :
    (λ_ CGWH.interval.{u, v}).inv ≫
      (CGWH.homotopyIntervalEndpoint.{u, v} 0 ⊗ₘ 𝟙 _) ≫ action = 𝟙 _ := by
  apply CGWH.intervalHomotopyTensor_endpoint.{u, v}
  intro x
  exact homotopy.{u, v}.apply_zero x

/--
At literal time one the entire native action is the SAME original augmentation followed by δ0.
-/
theorem action_one :
    (λ_ CGWH.interval.{u, v}).inv ≫
      (CGWH.homotopyIntervalEndpoint.{u, v} 1 ⊗ₘ 𝟙 _) ≫ action =
        CGWH.intervalAugmentation.{u, v} ≫ CGWH.intervalOne.{u, v} := by
  apply CGWH.intervalHomotopyTensor_endpoint.{u, v}
  intro x
  exact homotopy.{u, v}.apply_one x

/--
The full native contraction fixes the whole original included endpoint, with the actual
terminal collapse.
-/
theorem action_fixed :
    (𝟙 CGWH.homotopyInterval.{u, v} ⊗ₘ CGWH.intervalOne.{u, v}) ≫ action =
      (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v} ⊗ₘ 𝟙 CGWH.point.{u, v}) ≫
        (λ_ CGWH.point.{u, v}).hom ≫ CGWH.intervalOne.{u, v} := by
  apply CGWH.intervalHomotopyTensor_fix.{u, v}
  exact homotopy_fixed.{u, v}

end CGWH.RealizedIntervalContraction

namespace PointedCGWH.RealizedIntervalContraction

/--
The whole original zero-simplex comparison agrees with the existing selected native zero-
simplex comparison.
-/
theorem zeroSimplexIsoPoint_eq :
    IntervalCoefficient.zeroSimplexIsoPoint.{u, v} =
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v} := by
  apply Iso.ext
  exact CGWH.point_isTerminal.{u, v}.hom_ext _ _

/--
The original first coefficient endpoint is exactly the native δ0 map after adding its original
basepoint.
-/
theorem endpoint_zero_eq : IntervalCoefficient.endpoint.{u, v} 0 =
    (Under.costar CGWH.point.{u, v}).map CGWH.intervalOne.{u, v} := by
  rw [IntervalCoefficient.endpoint_eq, zeroSimplexIsoPoint_eq]
  rfl

/--
The original second coefficient endpoint is exactly the native δ1 map after adding its
original basepoint.
-/
theorem endpoint_one_eq : IntervalCoefficient.endpoint.{u, v} 1 =
    (Under.costar CGWH.point.{u, v}).map CGWH.intervalZero.{u, v} := by
  rw [IntervalCoefficient.endpoint_eq, zeroSimplexIsoPoint_eq]
  rfl

/--
The original codegeneracy augmentation is exactly the actual terminal augmentation after
adding its basepoint.
-/
theorem augmentation_eq : IntervalCoefficient.augmentation.{u, v} =
    (Under.costar CGWH.point.{u, v}).map CGWH.intervalAugmentation.{u, v} := by
  rw [IntervalCoefficient.augmentation_eq]
  congr 1

/-- The actual literal time coefficient, with its original freely adjoined basepoint. -/
abbrev time : PointedCGWH.{u, v} :=
  (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval.{u, v}

/-- The computed original free-point monoidal image of the actual interval contraction. -/
def action : time.{u, v} ⊗ IntervalCoefficient.interval.{u, v} ⟶
    IntervalCoefficient.interval.{u, v} := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point.{u, v} CGWH.point_isTerminal.{u, v}
  exact Functor.CoreMonoidal.intervalActionImage F hF
    CGWH.RealizedIntervalContraction.action.{u, v}

/-- The entire original pointed action is the identity at literal time zero. -/
theorem action_zero : (λ_ IntervalCoefficient.interval.{u, v}).inv ≫
    (PointedCGWH.freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫ action = 𝟙 _ := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point.{u, v} CGWH.point_isTerminal.{u, v}
  change (λ_ _).inv ≫
      ((hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint.{u, v} 0)) ⊗ₘ 𝟙 _) ≫
        Functor.CoreMonoidal.intervalActionImage F hF
          CGWH.RealizedIntervalContraction.action.{u, v} = 𝟙 _
  rw [Functor.CoreMonoidal.intervalActionImage_endpoint F hF
    CGWH.RealizedIntervalContraction.action.{u, v} (CGWH.homotopyIntervalEndpoint.{u, v} 0)
    (𝟙 _) CGWH.RealizedIntervalContraction.action_zero.{u, v}, F.map_id]

/--
At literal time one the entire action is the SAME original augmentation followed by the
original first endpoint.
-/
theorem action_one : (λ_ IntervalCoefficient.interval.{u, v}).inv ≫
    (PointedCGWH.freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫ action =
      IntervalCoefficient.augmentation ≫ IntervalCoefficient.endpoint 0 := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point.{u, v} CGWH.point_isTerminal.{u, v}
  change (λ_ _).inv ≫
      ((hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint.{u, v} 1)) ⊗ₘ 𝟙 _) ≫
        Functor.CoreMonoidal.intervalActionImage F hF
          CGWH.RealizedIntervalContraction.action.{u, v} = _
  rw [Functor.CoreMonoidal.intervalActionImage_endpoint F hF
    CGWH.RealizedIntervalContraction.action.{u, v} (CGWH.homotopyIntervalEndpoint.{u, v} 1)
    (CGWH.intervalAugmentation.{u, v} ≫ CGWH.intervalOne.{u, v})
      CGWH.RealizedIntervalContraction.action_one.{u, v},
    F.map_comp, augmentation_eq, endpoint_zero_eq]
  rfl

/-- The full original free-point action fixes the whole original first endpoint at every time. -/
theorem action_fixed :
    (𝟙 time.{u, v} ⊗ₘ IntervalCoefficient.endpoint 0) ≫ action =
      (PointedCGWH.freePointIntervalCollapse ⊗ₘ 𝟙 (𝟙_ PointedCGWH.{u, v})) ≫
        (λ_ (𝟙_ PointedCGWH.{u, v})).hom ≫ IntervalCoefficient.endpoint 0 := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point.{u, v} CGWH.point_isTerminal.{u, v}
  rw [endpoint_zero_eq]
  change (𝟙 _ ⊗ₘ F.map CGWH.intervalOne.{u, v}) ≫
      Functor.CoreMonoidal.intervalActionImage F hF CGWH.RealizedIntervalContraction.action.{u, v} =
    (Functor.CoreMonoidal.intervalCollapseImage F hF
      (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v}) ⊗ₘ 𝟙 _) ≫
        (λ_ _).hom ≫ F.map CGWH.intervalOne.{u, v}
  exact Functor.CoreMonoidal.intervalActionImage_fix F hF
    CGWH.RealizedIntervalContraction.action.{u, v} CGWH.intervalOne.{u, v}
    (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v})
    CGWH.RealizedIntervalContraction.action_fixed.{u, v}

end PointedCGWH.RealizedIntervalContraction
