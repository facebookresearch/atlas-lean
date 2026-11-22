/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.ModuleData
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionOperators

/-!
# Complete ordered arrows of the original restricted module

The original restricted module action and every target degree map are retained
together before the coefficient category is selected.
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
  (K : V) [MonObj (A K)] (X : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid V)
  (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)

/-- Every ordered arrow acts through the full original module action and its actual target map. -/
def moduleDataArrowAction (a b c : CategoryTheory.Sequence.Index) (f : a ⊗ b ⟶ c) :
    (A K).functor.obj a ⊗ (R.obj X).functor.obj b ⟶ (R.obj X).functor.obj c :=
  (DayFunctor.η (A K) (moduleData K X s one mul).X).app (a, b) ≫
    (moduleData K X s one mul).mod.smul.natTrans.app (a ⊗ b) ≫
    (moduleData K X s one mul).X.functor.map f

/-- The complete arrow formula preserves every coefficient, pair and original degree arrow. -/
theorem moduleDataArrowAction_original (a b c : CategoryTheory.Sequence.Index) (f : a ⊗ b ⟶ c) :
    moduleDataArrowAction K X s one mul a b c f =
      (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        s.natTrans.app (degreeInclusion.obj (a ⊗ b)) ≫ X.functor.map (degreeInclusion.map f) := by
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ X.functor.map (degreeInclusion.map f))
      (moduleData_pair K X s one mul a b))).trans (Category.assoc _ _ _)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.CoefficientRestriction
