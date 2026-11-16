/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels
public import MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual valuation reduction/localization/residue diagrams and categorical comparisons

The four rings are literally V, V/p, Localization.AtPrime(p) and
FractionRing(V/p). Every arrow is its original quotient, localization,
fraction-field map or the already normalized local-to-residue map.
The residue-field isomorphism and its source equation stay in the
original ValuationExcision payload.

The coefficient categorical limit uses native cocartesian sections of
the full actual family. Its comparison is the inverse of the fixed
initial-index evaluation followed by whole-diagram restriction.
The perfected Perf limit instead uses the direct all-affine module
Grothendieck diagram and literal source reindexing.

Sources: Bhatt--Mathew1807.04725v4, Theorem4.1, Theorems5.13/5.16,
and the Milnor squares in their proofs. Native ring, Spec, section and
coefficient source revisions and license notices are retained in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeValuationDiagramModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoherentFamilies
open GeneralCoefficientHyperdescentModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.NativeInitialSectionModels
open MathlibExt.AlgebraicTopology.NativeDiagramFamilies
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open scoped Simplicial

variable (V : ValuationRingData) (p : PrimeSpectrum V.ring) (E : ValuationExcision V p)

/-- The actual quotient arrow Spec(V/p)→Spec(V). -/
def reductionSpec : Spec (.of (V.ring ⧸ p.asIdeal)) ⟶ Spec (.of V.ring) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))

/-- The actual localization arrow Spec(V_p)→Spec(V). -/
def localizationSpec : Spec (.of (Localization.AtPrime p.asIdeal)) ⟶ Spec (.of V.ring) :=
  Spec.map (CommRingCat.ofHom (algebraMap V.ring (Localization.AtPrime p.asIdeal)))

/-- The residue fraction-field arrow uses the original quotient ring. -/
def residueReductionSpec : Spec (.of (FractionRing (V.ring ⧸ p.asIdeal))) ⟶ Spec (.of (V.ring ⧸ p.asIdeal)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (V.ring ⧸ p.asIdeal) (FractionRing (V.ring ⧸ p.asIdeal))))

/-- The other residue arrow is the exact native local-to-fraction-field map. -/
def residueLocalizationSpec : Spec (.of (FractionRing (V.ring ⧸ p.asIdeal))) ⟶
    Spec (.of (Localization.AtPrime p.asIdeal)) :=
  Spec.map (CommRingCat.ofHom E.localToKappa)

/-- Both original source paths are equal by the native ring-map normalization. -/
theorem residue_square :
    residueLocalizationSpec V p E ≫ localizationSpec V p = residueReductionSpec V p ≫ reductionSpec V p := by
  unfold residueLocalizationSpec localizationSpec residueReductionSpec reductionSpec
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun f : V.ring →+* FractionRing (V.ring ⧸ p.asIdeal) => f r) E.comm

def reductionObject : Over (affine (.of V.ring)) :=
  Over.mk (Y := affine (.of (V.ring ⧸ p.asIdeal))) (reductionSpec V p)

def localizationObject : Over (affine (.of V.ring)) :=
  Over.mk (Y := affine (.of (Localization.AtPrime p.asIdeal))) (localizationSpec V p)

def residueObject : Over (affine (.of V.ring)) :=
  Over.mk (Y := affine (.of (FractionRing (V.ring ⧸ p.asIdeal))))
    (residueReductionSpec V p ≫ reductionSpec V p :
      Spec (.of (FractionRing (V.ring ⧸ p.asIdeal))) ⟶ Spec (.of V.ring))

def residueReduction : residueObject V p ⟶ reductionObject V p :=
  Over.homMk (residueReductionSpec V p)

def residueLocalization : residueObject V p ⟶ localizationObject V p :=
  Over.homMk (residueLocalizationSpec V p E) (residue_square V p E)

/-- The full native scheme span is the reverse of the actual categorical excision cospan. -/
def excisionSpan : WalkingSpan ⥤ Over (affine (.of V.ring)) :=
  span (residueReduction V p) (residueLocalization V p E)

/-- The characteristic-ℓ base map is the actual original coefficient ring map. -/
def valuationFpScheme {ℓ : ℕ} (b : ZMod ℓ →+* V.ring) : FrobeniusPerfectionModels.FpSchemes ℓ :=
  Over.mk (Y := affine (.of V.ring)) (Spec.map (CommRingCat.ofHom b))

section CoefficientDiagrams
variable {J : Type} [Category.{0} J] {X : QcqsScheme} (H : J ⥤ Over X)

/-- The entire actual augmented scheme diagram, retaining every original over-map. -/
def augmentedSchemeDiagram : WithTerminal J ⥤ QcqsScheme :=
  WithTerminal.lift (Z := X) (H ⋙ Over.forget X) (fun j => (H.obj j).hom)
    (by intro i j f; exact Over.w (H.map f))

theorem augmentation_restriction : WithTerminal.incl ⋙ augmentedSchemeDiagram H = H ⋙ Over.forget X := by
  exact _root_.CategoryTheory.Functor.ext (fun _ => rfl)

def coefficientIndexInclusion : Jᵒᵖ ⥤ (WithTerminal J)ᵒᵖ := (WithTerminal.incl (C := J)).op

def liftedCoefficientInclusion : liftSet.{0, 2} (nerve Jᵒᵖ) ⟶
    liftSet.{0, 2} (nerve (WithTerminal J)ᵒᵖ) :=
  (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{2}).map (nerveMap (coefficientIndexInclusion (J := J)))

def augmentedCoefficientBase : liftSet.{0, 2} (nerve (WithTerminal J)ᵒᵖ) ⟶ BaseSet :=
  diagramBaseMap (augmentedSchemeDiagram H).op

def unaugmentedCoefficientBase : liftSet.{0, 2} (nerve Jᵒᵖ) ⟶ BaseSet :=
  diagramBaseMap (H ⋙ Over.forget X).op

theorem coefficient_base_restriction :
    liftedCoefficientInclusion ≫ augmentedCoefficientBase H = unaugmentedCoefficientBase H := by
  ext n a
  apply congrArg ULift.up
  have h := congrArg _root_.CategoryTheory.Functor.op (augmentation_restriction H)
  change (a.down ⋙ coefficientIndexInclusion) ⋙ (augmentedSchemeDiagram H).op =
    a.down ⋙ (H ⋙ Over.forget X).op
  rw [Functor.assoc]
  exact congrArg (fun F => a.down ⋙ F) h

def coefficientAugmentationVertex : (liftSet.{0, 2} (nerve (WithTerminal J)ᵒᵖ)) _⦋0⦌ :=
  ULift.up (ComposableArrows.mk₀ (op (WithTerminal.star : WithTerminal J)))

theorem coefficient_augmentation_base :
    baseVertex (augmentedCoefficientBase H) coefficientAugmentationVertex = schemeBaseVertex X := rfl

/-- The actual full categorical comparison uses only the native initial evaluation inverse and source restriction. -/
def coefficientDiagramComparison {Z : SSet.{2}} (q : Z ⟶ BaseSet)
    (I : InitialSectionComparison q (augmentedCoefficientBase H) coefficientAugmentationVertex) :
    fibre q (schemeBaseVertex X) ⟶ sectionsOver q (unaugmentedCoefficientBase H) :=
  eqToHom (congrArg (fibre q) (coefficient_augmentation_base H).symm) ≫ I.inverse ≫
    sectionsOverMap q (augmentedCoefficientBase H) (unaugmentedCoefficientBase H)
      liftedCoefficientInclusion (coefficient_base_restriction H)

end CoefficientDiagrams

end MathlibExt.AlgebraicGeometry.NativeValuationDiagramModels
