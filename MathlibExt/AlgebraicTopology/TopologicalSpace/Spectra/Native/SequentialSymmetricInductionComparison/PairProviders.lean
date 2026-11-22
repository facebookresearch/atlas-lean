/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.ModuleData
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.PairingProviders

/-!
# Day pair actions under coefficient restriction

With chosen ordered and symmetric Day pairing data, compares the full pair action of a restricted module with its symmetric pair action at the included degrees. The construction retains the given module unit and associativity equations.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe uV vV uC vC

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- Complete arrow data, including both original Hom functions on the same actual source and target. -/
private structure PairData (V : Type uV) [Category.{vV} V] where
  /-- The complete original source field. -/
  source : V
  /-- The complete original target field. -/
  target : V
  /-- The complete original left field. -/
  left : source ⟶ target
  /-- The complete original right field. -/
  right : source ⟶ target

/-- The full pair equation is independently specified on both original Hom functions. -/
private def PairData.Equation (d : PairData V) : Prop := d.left = d.right

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
open CoefficientRestriction
open CategoryTheory.MonoidalCategory.DayFunctor (PairingProviders)

variable [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (orderedProviders : PairingProviders (V := V) N) (symmetricProviders : PairingProviders (V := V) I)
  (K : V) [MonObj (A K)] (X : DayFunctor I V) (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)

/-- The complete original module pair is computed with the actual provider matrix before its equation. -/
private def fullPairData (a b : N) : PairData V where
  source := ((A K).functor ⊠ (R.obj X).functor).obj (a, b)
  target := (R.obj X).functor.obj (a ⊗ b)
  left := by
    let originalMonObj : MonObj (A K) := inferInstance
    letI : MonoidalCategory (DayFunctor N V) :=
      @DayFunctor.inst N _ V _ _ _ orderedProviders.tensorExtensions orderedProviders.unitExtensions
        orderedProviders.leftTensor orderedProviders.rightTensor orderedProviders.leftUnit
        orderedProviders.rightUnit orderedProviders.rightMixedUnit orderedProviders.rightTriple
    letI : MonObj (A K) := originalMonObj
    let Q : CategoryTheory.Mod (DayFunctor N V) (A K) := moduleData K X s one mul
    exact (@DayFunctor.η N _ V _ _ _ orderedProviders.tensorExtensions orderedProviders.unitExtensions
      orderedProviders.leftTensor orderedProviders.rightTensor orderedProviders.leftUnit
      orderedProviders.rightUnit orderedProviders.rightMixedUnit orderedProviders.rightTriple
      (A K) Q.X).app (a, b) ≫ Q.mod.smul.natTrans.app (a ⊗ b)
  right := by
    letI : MonoidalCategory (DayFunctor I V) :=
      @DayFunctor.inst I _ V _ _ _ symmetricProviders.tensorExtensions symmetricProviders.unitExtensions
        symmetricProviders.leftTensor symmetricProviders.rightTensor symmetricProviders.leftUnit
        symmetricProviders.rightUnit symmetricProviders.rightMixedUnit symmetricProviders.rightTriple
    exact (@DayFunctor.η I _ V _ _ _ symmetricProviders.tensorExtensions symmetricProviders.unitExtensions
      symmetricProviders.leftTensor symmetricProviders.rightTensor symmetricProviders.leftUnit
      symmetricProviders.rightUnit symmetricProviders.rightMixedUnit symmetricProviders.rightTriple
      (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      s.natTrans.app (degreeInclusion.obj (a ⊗ b))


/-- Every coefficient, full action and original degree satisfies the whole original computed equation. -/
private theorem fullPairData_equation (a b : N) :
    PairData.Equation (fullPairData orderedProviders symmetricProviders K X s one mul a b) :=
  moduleData_pair K X s one mul a b

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
