/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Symmetrization

/-!
# The original restriction module data before selecting the coefficient category

The constructor stores the original action and its ordinary module laws.
The full pair formula is proved on that same construction before a native
module or coefficient category is selected.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.CoefficientRestriction
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (K : V) [MonObj (A K)] (X : DayFunctor I V) (s : S K ⊗ X ⟶ X)

/-- The same original complete action on every original restricted coefficient diagram. -/
def moduleAction : A K ⊗ R.obj X ⟶ R.obj X :=
  (inclusion K ▷ R.obj X) ≫ tensorator (S K) X ≫ R.map s

/-- The original module is assembled from its same carrier, full action and ordinary module laws. -/
def moduleData
    (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
    (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
      (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s) :
    Mod (DayFunctor N V) (A K) where
  X := R.obj X
  mod := { smul := moduleAction K X s
           one_smul := one
           mul_smul := mul }

/-- Every original pair of the assembled module is its full original symmetric action pair. -/
theorem moduleData_pair
    (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
    (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
      (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)
    (a b : N) :
    (DayFunctor.η (A K) (moduleData K X s one mul).X).app (a, b) ≫
      (moduleData K X s one mul).mod.smul.natTrans.app (a ⊗ b) =
    (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      s.natTrans.app (degreeInclusion.obj (a ⊗ b)) :=
  originalActionPair K X s a b

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.CoefficientRestriction
