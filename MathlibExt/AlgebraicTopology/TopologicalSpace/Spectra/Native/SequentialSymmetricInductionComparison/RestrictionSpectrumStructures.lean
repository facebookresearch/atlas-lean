/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionStructures
import MathlibExt.CategoryTheory.Monoidal.Sequence.TensorPower

/-!
# The original restricted tensor-power structure maps

The complete restricted module gives the original one-step structure map.
Its source unitor, full symmetric action and original forward degree map
are retained before selecting the native coefficient category.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.CoefficientRestriction
universe uV vV
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (K : V)
/-- The same original tensor-power monoid is installed on the original ordered coefficient. -/
local instance originalTensorPowerMonoid : MonObj (A K) :=
  CategoryTheory.Sequence.tensorPowerSequenceMonObj K
variable (X : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid V)
  (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)

/-- The original restricted structure map keeps its full source unitor, symmetric pair and degree transport. -/
theorem moduleData_structureMap_original (n : ℕ) :
    CategoryTheory.Sequence.TensorPowerModule.structureMap (moduleData K X s one mul) n =
      ((λ_ K).inv ⊗ₘ 𝟙 ((R.obj X).functor.obj (CategoryTheory.Sequence.index n))) ≫
      (DayFunctor.η (S K) X).app
        (degreeInclusion.obj (CategoryTheory.Sequence.index 1),
         degreeInclusion.obj (CategoryTheory.Sequence.index n)) ≫
      s.natTrans.app (degreeInclusion.obj
        (CategoryTheory.Sequence.index 1 ⊗ CategoryTheory.Sequence.index n)) ≫
      X.functor.map (degreeInclusion.map
        (eqToHom ((CategoryTheory.Sequence.tensorObj_index 1 n).trans
          (congrArg CategoryTheory.Sequence.index (Nat.one_add n))))) := by
  have h := moduleDataArrowAction_original K X s one mul
    (CategoryTheory.Sequence.index 1) (CategoryTheory.Sequence.index n)
    (CategoryTheory.Sequence.index (n + 1))
    (eqToHom ((CategoryTheory.Sequence.tensorObj_index 1 n).trans
      (congrArg CategoryTheory.Sequence.index (Nat.one_add n))))
  exact (CategoryTheory.Sequence.TensorPowerModule.structureMap_eq
    (moduleData K X s one mul) n).trans
      (congrArg (fun f =>
        ((λ_ K).inv ⊗ₘ 𝟙 ((R.obj X).functor.obj (CategoryTheory.Sequence.index n))) ≫ f) h)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.CoefficientRestriction
