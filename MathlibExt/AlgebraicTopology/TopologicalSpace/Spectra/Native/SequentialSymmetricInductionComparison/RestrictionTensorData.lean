/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.ModuleData
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.PairProviders

/-!
# Restriction of Day-module tensor actions

This file records the ordered pairing, unit and multiplication maps of a restricted
Day-module action. A compatible module action with the supplied unit and associativity laws
constructs this record and satisfies its coefficientwise formula. The same formula follows
for any record given to be equal to that construction.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.RestrictionTensorData
universe uV vV uC vC
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
open PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CoefficientRestriction
open CategoryTheory.MonoidalCategory.DayFunctor (PairingProviders PairingFamily)
variable [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Both complete tensors, both full pairing functions and both actual module structures are retained. -/
structure Data (K : V) (X : DayFunctor I V) where
  /-- The complete original ordered field. -/
  ordered : MonoidalCategory (DayFunctor N V)
  /-- The complete original symmetric field. -/
  symmetric : MonoidalCategory (DayFunctor I V)
  /-- The complete original ordered monoid field. -/
  orderedMonoid : letI := ordered; MonObj (A K)
  /-- The complete original source monoid field. -/
  sourceMonoid : letI := symmetric; MonObj (S K)
  /-- The complete original source module field. -/
  sourceModule : letI := symmetric; letI := sourceMonoid; ModObj (S K) X
  /-- The complete original restricted module field. -/
  restrictedModule : letI := ordered; letI := orderedMonoid; ModObj (A K) (R.obj X)
  /-- The complete original ordered pairing field. -/
  orderedPairing : PairingFamily ordered
  /-- The complete original symmetric pairing field. -/
  symmetricPairing : PairingFamily symmetric

/-- The independently stated pair equation uses the complete supplied tensor and module data. -/
def Data.Formula {K : V} {X : DayFunctor I V} (d : Data K X) (a b : N) : Prop :=
  letI := d.ordered
  letI := d.symmetric
  letI := d.orderedMonoid
  letI := d.sourceMonoid
  (d.orderedPairing (A K) (R.obj X)).app (a,b) ≫
      d.restrictedModule.smul.natTrans.app (a ⊗ b) =
    (d.symmetricPairing (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      d.sourceModule.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))

variable (pN : PairingProviders (V := V) N) (pI : PairingProviders (V := V) I)
  (K : V) [MonObj (A K)] (X : DayFunctor I V)
  (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)
  [MonObj (S K)] (sourceOne : (η[S K] ▷ X) ≫ s = (λ_ X).hom)
  (sourceMul : (μ[S K] ▷ X) ≫ s = (α_ (S K) (S K) X).hom ≫ (S K ◁ s) ≫ s)

/-- The same original constructor supplies every tensor, pairing and ordinary module-law field. -/
private def ofModuleAction : Data K X where
  ordered := @DayFunctor.inst N _ V _ _ _ pN.tensorExtensions pN.unitExtensions
    pN.leftTensor pN.rightTensor pN.leftUnit pN.rightUnit pN.rightMixedUnit pN.rightTriple
  symmetric := @DayFunctor.inst I _ V _ _ _ pI.tensorExtensions pI.unitExtensions
    pI.leftTensor pI.rightTensor pI.leftUnit pI.rightUnit pI.rightMixedUnit pI.rightTriple
  orderedMonoid := inferInstance
  sourceMonoid := inferInstance
  sourceModule := { smul := s, one_smul := sourceOne, mul_smul := sourceMul }
  restrictedModule := (moduleData K X s one mul).mod
  orderedPairing := fun F G =>
    @DayFunctor.η N _ V _ _ _ pN.tensorExtensions pN.unitExtensions
      pN.leftTensor pN.rightTensor pN.leftUnit pN.rightUnit pN.rightMixedUnit pN.rightTriple F G
  symmetricPairing := fun F G =>
    @DayFunctor.η I _ V _ _ _ pI.tensorExtensions pI.unitExtensions
      pI.leftTensor pI.rightTensor pI.leftUnit pI.rightUnit pI.rightMixedUnit pI.rightTriple F G

/-- The original full generic action proves every pair equation on those same construction fields. -/
private theorem ofModuleAction_formula (a b : N) :
    (ofModuleAction pN pI K X s one mul sourceOne sourceMul).Formula a b :=
  moduleData_pair K X s one mul a b

/-- Equality of whole original construction data moves only its independently stated proposition. -/
private theorem formula_ofModuleAction (d : Data K X)
    (h : d = ofModuleAction pN pI K X s one mul sourceOne sourceMul) (a b : N) :
    d.Formula a b := by
  cases h
  exact ofModuleAction_formula pN pI K X s one mul sourceOne sourceMul a b

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.RestrictionTensorData
