/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
public import Batteries.Util.ProofWanted

/-!
# Source relative de Rham and tensor construction requests

The product resolution is chosen with its natural augmentation square.
Every relative map is fixed by actual simplicial generators, native
Moore–AW maps and coefficient tensor maps. The global projection
formula is a separate proof under fully sourced compactness.
Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.NegativeTensorNormalizations
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
open MathlibExt.AlgebraicGeometry.NormalizedRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u

def_wanted compatibleProductResolution (k : Type u) [CommRing k] [Algebra ℚ k] :
    (Q : AlgebraReplacementFunctor k) × ProductReplacementSystem Q

def_wanted nativeStrongCochainLift (k : Type u) [CommRing k]
    (L : CochainLiftModel k) : StrongCochainLift L

def_wanted nativeNegativeTensorExtension (R : Type u) [CommRing R]
    (A B : ChainComplex (ModuleCat.{u} R) ℕ) : TensorExtensionModel A B

def_wanted nativeLeftShiftTensor (R : Type u) [CommRing R]
    (A B : Cochains R) (n : ℤ) : LeftShiftTensorModel A B n

def_wanted nativeRawRelativeDR (k : Type u) [CommRing k]
    (A B : SAlg k) (M : SimplicialDRModel A) (P : SimplicialDRModel (A ⊗ B))
    (D : RawDRModel A M) (E : RawDRModel (A ⊗ B) P)
    (F : ProjectionModel A B M P) (T : PureTensorModel D.graded (normalizedCoefficient B)) :
    RelativeDRModel D E F T

def_wanted nativeRawRelativeAffineDiagram (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (F X : Prestack k) : RelativeAffineFamilyDiagram D R F X

def_wanted nativeLiftedRelativeAffineDiagram (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (S : StrongCochainLift L)
    (N : ShuffleAlgebraFunctor k) (F X : Prestack k) (A : RelativeAffineFamilyDiagram D R F X)
    (C : Families X ⥤ Cochains (LargeScalar k))
    (value : ∀ j : Families X, C.obj j = affineCoefficient L N ((algebraProjection X).obj j))
    (maps : ∀ (j l : Families X) (f : j ⟶ l),
      HEq (C.map f) (affineCoefficientMap L N ((algebraProjection X).map f)))
    (B : TensorMixedDiagram (first F X ⋙ algebraProjection F ⋙ D.functor ⋙ T.functor)
      (second F X ⋙ C)) : LiftedRelativeFamilyDiagram D R T S N F X A C value B

def_wanted nativeTensorMixedDiagram (k : Type u) [CommRing k]
    (J : Type (u + 1)) [Category.{u} J]
    (F : J ⥤ GradedMixed (LargeScalar k)) (C : J ⥤ Cochains (LargeScalar k)) : TensorMixedDiagram F C

def_wanted nativeTensorDiagramMap (k : Type u) [CommRing k]
    (J : Type (u + 1)) [Category.{u} J]
    (F F' : J ⥤ GradedMixed (LargeScalar k)) (C C' : J ⥤ Cochains (LargeScalar k))
    (f : F ⟶ F') (c : C ⟶ C') (P : TensorMixedDiagram F C) (P' : TensorMixedDiagram F' C') :
    TensorDiagramMap f c P P'

def_wanted nativePureTensorMap (R : Type u) [CommRing R]
    (E E' : GradedMixed R) (C C' : Cochains R) (f : MixedMap E E') (c : C ⟶ C')
    (P : PureTensorModel E C) (P' : PureTensorModel E' C') : PureTensorMap f c P P'

def_wanted nativeMixedDiagramLimit (k : Type u) [CommRing k]
    (J : Type (u + 1)) [Category.{u} J] (D : J ⥤ GradedMixed (LargeScalar k)) : MixedLimitModel D

def_wanted nativeProjectionFormulaRepresentative (k : Type u) [CommRing k]
    (J : Type (u + 1)) [Category.{u} J]
    (F₀ F₁ : J ⥤ GradedMixed (LargeScalar k)) (C₀ C₁ : J ⥤ Cochains (LargeScalar k))
    (E : GradedMixed (LargeScalar k)) (C : Cochains (LargeScalar k))
    (f : F₀ ⟶ F₁) (c : C₀ ⟶ C₁)
    (formCone : (Functor.const J).obj E ⟶ F₁) (coefficientCone : (Functor.const J).obj C ⟶ C₁)
    (P : PureTensorModel E C) (B : ProjectionFormulaDiagram f c formCone coefficientCone P)
    (H : MixedLimitModel B.replacement.diagram) : ProjectionFormulaRealization B H

def_wanted nativeGlobalRelativeDR (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (RM : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (SL : StrongCochainLift L) (V : NerveLiftModel L)
    (F X : DerivedStack Q) (B : SourcedScalarFamily M U RM Q L V X.functor)
    (G : GlobalMixedModel D T F.functor) (GP : GlobalMixedModel D T (F.functor ⊗ X.functor))
    (P : PureTensorModel G.mixed (gammaCoefficients B.family.model B.absolute B.scalar)) :
    GlobalRelativeModel B.family.model B.absolute B.scalar B.gamma R SL G GP P

theorem_wanted actualGlobalProjectionFormulaQuasiIso (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (RM : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (SL : StrongCochainLift L) (V : NerveLiftModel L)
    (F X : DerivedStack Q) (B : SourcedScalarFamily M U RM Q L V X.functor)
    (compact : IsSourcedOCompact B.family)
    (G : GlobalMixedModel D T F.functor) (GP : GlobalMixedModel D T (F.functor ⊗ X.functor))
    (P : PureTensorModel G.mixed (gammaCoefficients B.family.model B.absolute B.scalar))
    (A : GlobalRelativeModel B.family.model B.absolute B.scalar B.gamma R SL G GP P) :
    ∀ w : ℤ, QuasiIso (A.projection.map.map w)

end MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
