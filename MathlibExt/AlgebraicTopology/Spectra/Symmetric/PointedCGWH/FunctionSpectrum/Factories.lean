/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Original

/-!
# Original native witnesses for symmetric free-function comparisons

These names refer only to the existing pointed CGWH coproducts, Day Kan extensions,
left and right tensor adjunctions, and small limits. Sharing their full families lets
native free-function constructors retain identical witnesses when comparing the
original whole module maps and their components. No comparison is supplied as input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace PointedCGWH.SymmetricFunctionFactories

/-- The original small finite-bijection groupoid for every native sequence index. -/
abbrev I := Operad.SmallFinBijGroupoid
/-- The complete original pointed CGWH coefficient category in both universes. -/
abbrev V := PointedCGWH.{u, v}
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The actual native coproducts for each original Hom-indexed free diagram. -/
theorem indexedCoproducts (a b : I) : HasCoproductsOfShape (a ⟶ b) V.{u, v} :=
  inferInstance

/-- Native colimits supply the full original Day tensor extension family. -/
theorem tensorExtensions (F G : I ⥤ V.{u, v}) :
    (tensor I).HasPointwiseLeftKanExtension (F ⊠ G) := by
  intro d
  infer_instance

/-- Native colimits supply the original Day unit extension family. -/
theorem unitExtensions :
    (Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (𝟙_ V.{u, v})) := by
  intro d
  infer_instance

/-- Actual native left tensor adjunctions preserve every original Day tensor shape. -/
theorem tensorLeftTensorShape (X : V.{u, v}) (d : I) :
    PreservesColimitsOfShape (CostructuredArrow (tensor I) d) (tensorLeft X) :=
  inferInstance

/-- Actual native right tensor adjunctions preserve every original Day tensor shape. -/
theorem tensorRightTensorShape (X : V.{u, v}) (d : I) :
    PreservesColimitsOfShape (CostructuredArrow (tensor I) d) (tensorRight X) :=
  inferInstance

/-- Actual native left tensor adjunctions preserve the original unit extension shape. -/
theorem tensorLeftUnitShape (X : V.{u, v}) (d : I) :
    PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft X) :=
  inferInstance

/-- Actual native right tensor adjunctions preserve the original unit extension shape. -/
theorem tensorRightUnitShape (X : V.{u, v}) (d : I) :
    PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight X) :=
  inferInstance

/-- The actual right tensor functor preserves every original mixed unit shape. -/
theorem tensorRightMixedUnitShape (X : V.{u, v}) (d : I × I) :
    PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight X) :=
  inferInstance

/-- The actual right tensor functor preserves every original triple tensor shape. -/
theorem tensorRightTripleShape (X : V.{u, v}) (d : I × I) :
    PreservesColimitsOfShape
      (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight X) :=
  inferInstance

/-- The actual small native limits supply all original Day internal-Hom ends. -/
theorem internalHomEnds (F G : I ⥤ V.{u, v}) (c : I) :
    HasEnd ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c) :=
  inferInstance

attribute [local instance] indexedCoproducts tensorExtensions unitExtensions
  tensorLeftTensorShape tensorRightTensorShape tensorLeftUnitShape tensorRightUnitShape
  tensorRightMixedUnitShape tensorRightTripleShape internalHomEnds

/-- Naming the original primitive witnesses retains the whole original Day structure. -/
@[instance_reducible]
def monoidal : MonoidalCategory PointedCGWH.SymmetricSequence.{u, v} := inferInstance

/-- The named factory retains the identical original Day tensor, maps and coherence. -/
theorem monoidal_eq_original : monoidal.{u, v} =
    PointedCGWH.originalSymmetricSequenceMonoidal.{u, v} := rfl

end PointedCGWH.SymmetricFunctionFactories
