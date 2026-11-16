/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootEtaleWeightNormalizations
public import MathlibExt.AlgebraicGeometry.ParabolicRootMonoidalModels

/-!
# Joint normalized construction data for the Borne–Vistoli functor

All dictionaries, root restrictions, balanced parabolic tensor/unit,
projection-formula periods, affine coefficient comparisons and native
unit/tensor maps are selected together. The target is the independently
defined actual Parabolic category. The source theorem's equivalence is
a separate output condition; it is never used to define the target.

Source: Borne–Vistoli arXiv:1001.0466v2, Theorem6.1 on arbitrary
coherent DF structures and coherent denominator systems. No SNC,
residue-characteristic or finite-presentation restriction is added.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ParabolicRootComparisonData

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.CartesianStackModules _root_.AlgebraicGeometry.CartesianStackTensorProducts
open DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories RootWeightEvaluations GlobalParabolicRootModels
open ParabolicBilinearTensorModels ParabolicRootComparisonMaps ParabolicRootEtaleMaps
open RootEtaleWeightNormalizations ParabolicRootMonoidalModels

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X))

structure Data where
  sourceTensor : TensorLanding R.stack
  localData : EtaleRootData I D j G R
  phi : PhiAssembly I D j G R localData
  structural : StructuralRestriction I D j G R sourceTensor localData
  lineLaws : ∀ U : X.Etale, LineFunctorLaws (G.chart U)
  parabolicTensor : TensorModel G j
  parabolicUnit : UnitModel G j lineLaws
  tensorBilinear : TensorBilinearity I D j G R sourceTensor localData phi structural
  unitCocones : UnitCocones I D j G R sourceTensor localData structural lineLaws
  unit : UnitComparison I D j G R sourceTensor localData phi structural lineLaws parabolicUnit unitCocones
  localStacks : LocalStackModels I D j G R localData
  restriction : RestrictionNormalization I D j G R localData localStacks
  baseLanding : ∀ {U V : X.Etale} (f : V ⟶ U), StackProjectionBaseChange.SchemePullbackLanding f.left
  baseSquare : ∀ {U V : X.Etale} (f : V ⟶ U),
    LocalPullbackSquare I D j G R localData localStacks f (baseLanding f)
  weightRestriction : WeightRestriction I D j G R localData localStacks restriction
  familyMaps : FamilyMaps I D j G R localData localStacks
  weightNormalization : WeightFamilyNormalization I D j G R localData localStacks familyMaps
    restriction weightRestriction
  phiReindex : PhiReindexNormalization I D j G R localData localStacks restriction weightRestriction
    phi baseLanding baseSquare
  targetMonoidal : MonoidalRealization D j G parabolicTensor lineLaws parabolicUnit

def Comparison (E : Data I D j G R) : Type 1 :=
  BorneVistoliComparison I D j G R E.sourceTensor E.localData E.phi E.structural
    E.parabolicTensor E.lineLaws E.parabolicUnit E.tensorBilinear E.unitCocones E.unit E.targetMonoidal

end MathlibExt.AlgebraicGeometry.ParabolicRootComparisonData
