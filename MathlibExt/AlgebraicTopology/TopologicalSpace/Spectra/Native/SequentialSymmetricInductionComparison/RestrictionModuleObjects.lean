/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionTensorData

/-!
# Module objects and pairings for degree restriction

Records the ordered and symmetric Day tensors, coefficient monoids, source and
restricted modules, level isomorphisms and pairing maps. From the supplied Day
Kan-extension and tensor-preservation data, the module-action construction proves the
coefficient-pair formula at every pair of degrees.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.RestrictionModuleObjects
universe uV vV
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
open PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CoefficientRestriction
open CategoryTheory.MonoidalCategory.DayFunctor (PairingProviders PairingFamily)

/-- Complete original tensors, coefficients, both module objects, all pairings and ordinary level Isos. -/
structure Data where
  /-- The complete original ordered field. -/
  ordered : MonoidalCategory (DayFunctor N V)
  /-- The complete original symmetric field. -/
  symmetric : MonoidalCategory (DayFunctor I V)
  /-- The complete original ordered coefficient field. -/
  orderedCoefficient : DayFunctor N V
  /-- The complete original symmetric coefficient field. -/
  symmetricCoefficient : DayFunctor I V
  /-- The complete original ordered monoid field. -/
  orderedMonoid : letI := ordered; MonObj orderedCoefficient
  /-- The complete original source monoid field. -/
  sourceMonoid : letI := symmetric; MonObj symmetricCoefficient
  /-- The complete original source field. -/
  source : letI := symmetric; letI := sourceMonoid; Mod (DayFunctor I V) symmetricCoefficient
  /-- The complete original target field. -/
  target : letI := ordered; letI := orderedMonoid; Mod (DayFunctor N V) orderedCoefficient
  /-- The complete original coefficient iso field. -/
  coefficientIso : ∀ a : N,
    orderedCoefficient.functor.obj a ≅ symmetricCoefficient.functor.obj (degreeInclusion.obj a)
  /-- The complete original level iso field. -/
  levelIso : ∀ a : N, target.X.functor.obj a ≅ source.X.functor.obj (degreeInclusion.obj a)
  /-- The complete original ordered pairing field. -/
  orderedPairing : CategoryTheory.MonoidalCategory.DayFunctor.PairingFamily ordered
  /-- The complete original symmetric pairing field. -/
  symmetricPairing : CategoryTheory.MonoidalCategory.DayFunctor.PairingFamily symmetric

/-- The independent full formula keeps both original module objects and all ordinary level maps. -/
def Data.Formula (d : Data (V := V)) (a b : N) : Prop :=
  letI := d.ordered
  letI := d.symmetric
  letI := d.orderedMonoid
  letI := d.sourceMonoid
  (d.orderedPairing d.orderedCoefficient d.target.X).app (a,b) ≫
      d.target.mod.smul.natTrans.app (a ⊗ b) ≫ (d.levelIso (a ⊗ b)).hom =
    (tensorIso (d.coefficientIso a) (d.levelIso b)).hom ≫
      (d.symmetricPairing d.symmetricCoefficient d.source.X).app
        (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      d.source.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))

variable [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (pN : PairingProviders (V := V) N) (pI : PairingProviders (V := V) I)
  (K : V) [MonObj (A K)] (X : DayFunctor I V) (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)
  [MonObj (S K)] (sourceOne : (η[S K] ▷ X) ≫ s = (λ_ X).hom)
  (sourceMul : (μ[S K] ▷ X) ≫ s = (α_ (S K) (S K) X).hom ≫ (S K ◁ s) ≫ s)

/-- The actual original constructor supplies every field before the coefficient category is selected. -/
def ofModuleAction : Data (V := V) where
  ordered := @DayFunctor.inst N _ V _ _ _ pN.tensorExtensions pN.unitExtensions
    pN.leftTensor pN.rightTensor pN.leftUnit pN.rightUnit pN.rightMixedUnit pN.rightTriple
  symmetric := @DayFunctor.inst I _ V _ _ _ pI.tensorExtensions pI.unitExtensions
    pI.leftTensor pI.rightTensor pI.leftUnit pI.rightUnit pI.rightMixedUnit pI.rightTriple
  orderedCoefficient := A K
  symmetricCoefficient := S K
  orderedMonoid := inferInstance
  sourceMonoid := inferInstance
  source := { X := X, mod := { smul := s, one_smul := sourceOne, mul_smul := sourceMul } }
  target := moduleData K X s one mul
  coefficientIso := fun _ => Iso.refl _
  levelIso := fun _ => Iso.refl _
  orderedPairing := fun F G =>
    @DayFunctor.η N _ V _ _ _ pN.tensorExtensions pN.unitExtensions
      pN.leftTensor pN.rightTensor pN.leftUnit pN.rightUnit pN.rightMixedUnit pN.rightTriple F G
  symmetricPairing := fun F G =>
    @DayFunctor.η I _ V _ _ _ pI.tensorExtensions pI.unitExtensions
      pI.leftTensor pI.rightTensor pI.leftUnit pI.rightUnit pI.rightMixedUnit pI.rightTriple F G

/-- Every complete original module pair satisfies the full formula before native specialization. -/
theorem ofModuleAction_formula (a b : N) :
    (ofModuleAction pN pI K X s one mul sourceOne sourceMul).Formula a b := by
  change (DayFunctor.η (A K) (moduleData K X s one mul).X).app (a,b) ≫
      ((moduleData K X s one mul).mod.smul.natTrans.app (a ⊗ b) ≫ 𝟙 _) =
    (𝟙 ((A K).functor.obj a) ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) ≫ (DayFunctor.η (S K) X).app
      (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      s.natTrans.app (degreeInclusion.obj (a ⊗ b))
  let p := (DayFunctor.η (A K) (moduleData K X s one mul).X).app (a,b)
  let t := (moduleData K X s one mul).mod.smul.natTrans.app (a ⊗ b)
  let q := (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
    s.natTrans.app (degreeInclusion.obj (a ⊗ b))
  have ht : p ≫ (t ≫ 𝟙 _) = p ≫ t :=
    congrArg (fun f => p ≫ f) (Category.comp_id t)
  have he : (𝟙 ((A K).functor.obj a) ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) =
      𝟙 (((S K).functor ⊠ X.functor).obj (degreeInclusion.obj a, degreeInclusion.obj b)) :=
    (tensorHom_id (𝟙 ((A K).functor.obj a)) ((R.obj X).functor.obj b)).trans
      (id_whiskerRight ((A K).functor.obj a) ((R.obj X).functor.obj b))
  have hq : (𝟙 ((A K).functor.obj a) ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) ≫ q = q :=
    (congrArg (fun f => f ≫ q) he).trans (Category.id_comp q)
  exact ht.trans ((moduleData_pair K X s one mul a b).trans hq.symm)

/-- Equality of complete construction data transports only the independently declared proposition. -/
private theorem formula_ofModuleAction (d : Data (V := V))
    (h : d = ofModuleAction pN pI K X s one mul sourceOne sourceMul) (a b : N) :
    d.Formula a b := by
  cases h
  exact ofModuleAction_formula pN pI K X s one mul sourceOne sourceMul a b

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.RestrictionModuleObjects
