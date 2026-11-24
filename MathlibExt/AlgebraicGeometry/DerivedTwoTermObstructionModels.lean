/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass
public import MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Original derived obstruction maps and their genuine cochain presentations

The original obstruction morphism is a morphism in the native derived
category. Its two-term vector-bundle source and normalized full cotangent
target are retained. A cochain presentation uses an actual K-injective
cotangent replacement, fixed on all original affine comparisons. The
representing cochain equals the original derived morphism after that
replacement. No global strict cochain lift of an arbitrary target is assumed.

Reference: Graber--Pandharipande alg-geom/9708001v2, Section1;
Behrend--Fantechi alg-geom/9601010, Section4. Native L_f construction is
completed in Axiom Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
SchemeCotangentComplex.lean; replacement/adapter proofs are separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DerivedTwoTermObstructionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GlobalPOTVirtualClass
open AlgebraicWeightBundleModels LinearizedLineBundles TorusFixedSchemeModels
attribute [local instance] HasDerivedCategory.standard

/-- The actual general two-term perfect obstruction theory has its original derived phi. -/
structure DerivedPOT (X : Over base) where
  model : TwoTermModel X.left
  cotangent : CotangentNormalization X.hom
  map : DerivedCategory.Q.obj (sourceComplex model) ⟶
    DerivedCategory.Q.obj cotangent.complex
  amplitude : LocallyPerfectAmplitude (sourceComplex model)
  h0 : IsIso ((DerivedCategory.homologyFunctor X.left.Modules 0).map map)
  hMinus : Epi ((DerivedCategory.homologyFunctor X.left.Modules (-1)).map map)

/-- The replacement preserves the whole actual cotangent-comparison system. -/
structure CotangentKInjectiveReplacement {X : Over base} (C : CotangentNormalization X.hom) where
  cotangent : CotangentNormalization X.hom
  injective : cotangent.complex.IsKInjective
  map : C.complex ⟶ cotangent.complex
  quasiIso : QuasiIso map
  affine : ∀ a : AffineChart X.hom,
    cotangent.resolution a = C.resolution a
  comparison : ∀ a : AffineChart X.hom,
    HEq (cotangent.comparison a)
      (C.comparison a ≫ ((moduleSections a.source).mapHomologicalComplex (.up ℤ)).map map)
  affineQuasiIso : ∀ a : AffineChart X.hom,
    QuasiIso (((moduleSections a.source).mapHomologicalComplex (.up ℤ)).map map)

/-- A genuine source cochain represents the given original derived map. -/
structure CochainPresentation {X : Over base} (P : DerivedPOT X) where
  replacement : CotangentKInjectiveReplacement P.cotangent
  map : sourceComplex P.model ⟶ replacement.cotangent.complex
  normalized : DerivedCategory.Q.map map = P.map ≫ DerivedCategory.Q.map replacement.map
  h0 : IsIso ((DerivedCategory.homologyFunctor X.left.Modules 0).map (DerivedCategory.Q.map map))
  hMinus : Epi ((DerivedCategory.homologyFunctor X.left.Modules (-1)).map (DerivedCategory.Q.map
    map))

/-- The native global cone/POT construction uses that exact representing map. -/
def CochainPresentation.native {X : Over base} {P : DerivedPOT X} (Q : CochainPresentation P) :
    TwoTermPOT X where
  model := P.model
  cotangent := Q.replacement.cotangent
  map := Q.map
  amplitude := P.amplitude
  h0 := Q.h0
  hMinus := Q.hMinus

/-- Source equivariant bundle maps and actual fixed/moving differentials are retained. -/
structure EquivariantObstructionTerms (X : Over base) [ModObj Gm X] where
  obstruction : DerivedPOT X
  negative : Linearization Gm X obstruction.model.negative
  degreeZero : Linearization Gm X obstruction.model.degreeZero
  differential : IsLinearizedMap negative degreeZero obstruction.model.differential

/-- The fixed and moving source terms are genuine bundle-weight summands. -/
structure FixedTerms {X : Over base} [ModObj Gm X] (P : EquivariantObstructionTerms X)
    {F : Over base} (i : F ⟶ X) (hi : FixedPoint Gm X i) where
  negative : WeightDecomposition P.negative i hi
  degreeZero : WeightDecomposition P.degreeZero i hi

/-- The exact fixed source differential, not a separately named fixed complex. -/
def FixedTerms.fixedDifferential {X : Over base} [ModObj Gm X] {P : EquivariantObstructionTerms X}
    {F : Over base} {i : F ⟶ X} {hi : FixedPoint Gm X i} (Q : FixedTerms P i hi) :
    Q.negative.fixed ⟶ Q.degreeZero.fixed :=
  AlgebraicWeightBundleModels.fixedDifferential Q.negative Q.degreeZero
    P.obstruction.model.differential

/-- The moving part uses the same original source differential and native summands. -/
def FixedTerms.movingDifferential {X : Over base} [ModObj Gm X] {P : EquivariantObstructionTerms X}
    {F : Over base} {i : F ⟶ X} {hi : FixedPoint Gm X i} (Q : FixedTerms P i hi) :
    Q.negative.moving ⟶ Q.degreeZero.moving :=
  AlgebraicWeightBundleModels.movingDifferential Q.negative Q.degreeZero
    P.obstruction.model.differential

end MathlibExt.AlgebraicGeometry.DerivedTwoTermObstructionModels
