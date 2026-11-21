/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

/-!
# Intermediate extensions and intersection-complex normalization

The middle t-structure is the support/cosupport-characterized input from the
unchanged PR1970 core. This module introduces no additional perverse-provider
request. Intermediate extension is specified by an actual restriction
isomorphism and the absence of boundary-supported subobjects and quotients.

All restriction, ambient inclusion and normalization constructions have
complete bodies. The intermediate-extension provider and its geometric laws
are requested in the matching Wanted module.

## References

* BBD, *Faisceaux pervers*, Astérisque 100 (1982), §1.4, intermediate extension.
* de Cataldo–Migliorini, https://arxiv.org/abs/0712.0349, §§2.1 and 2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntersectionComplexes

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- Exactness hypotheses for the fixed actual inverse-image sheaf functor.
They are ordinary Mathlib properties, not an independently chosen operator. -/
class OpenRestrictionExact {U X : ComplexScheme} (j : U ⟶ X) : Prop where
  [additive : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (spaceMap j)).Additive]
  [limits : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (spaceMap j))]
  [colimits : PreservesFiniteColimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (spaceMap j))]

attribute [instance] OpenRestrictionExact.additive OpenRestrictionExact.limits
  OpenRestrictionExact.colimits

/-- The actual inverse image on derived rational sheaves. -/
def derivedRestriction {U X : ComplexScheme} (j : U ⟶ X) [OpenRestrictionExact j] :
    RationalDerived (space X) ⥤ RationalDerived (space U) :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (spaceMap j)).mapDerivedCategory

/-- Include the actual perverse heart into the ambient derived category. -/
def perverseAmbient (X : ComplexScheme) [IsComplexVariety X] [PerverseSheafTheory X] :
    PerverseSheaf X ⥤ RationalDerived (space X) :=
  (perverseTStructure X).heart.ι ⋙ (boundedConstructible X).ι

instance perverseAmbient_faithful (X : ComplexScheme) [IsComplexVariety X]
    [PerverseSheafTheory X] : (perverseAmbient X).Faithful := by
  dsimp only [perverseAmbient]
  infer_instance

/-- Restrict a perverse object, keeping the target in the actual derived category. -/
def perverseRestriction {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X) [OpenRestrictionExact j] :
    PerverseSheaf X ⥤ RationalDerived (space U) :=
  perverseAmbient X ⋙ derivedRestriction j

/-- Boundary support means that the actual restriction is zero. -/
def IsBoundarySupported {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X) [OpenRestrictionExact j]
    (P : PerverseSheaf X) : Prop :=
  IsZero ((perverseRestriction j).obj P)

/-- No nonzero subobject supported on the complement of the open. -/
def NoBoundarySubobjects {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X) [OpenRestrictionExact j]
    (P : PerverseSheaf X) : Prop :=
  ∀ (Q : PerverseSheaf X) (a : Q ⟶ P), Mono a → IsBoundarySupported j Q → IsZero Q

/-- No nonzero quotient supported on the complement of the open. -/
def NoBoundaryQuotients {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X) [OpenRestrictionExact j]
    (P : PerverseSheaf X) : Prop :=
  ∀ (Q : PerverseSheaf X) (a : P ⟶ Q), Epi a → IsBoundarySupported j Q → IsZero Q

/-- The source-normalized intermediate-extension functor, characterized
without an arbitrary predicate called "intersection complex". -/
structure IntermediateExtensionData {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [OpenRestrictionExact j] where
  /-- The actual perverse-category functor. -/
  functor : PerverseSheaf U ⥤ PerverseSheaf X
  /-- Its restriction is naturally the source object. -/
  restriction : functor ⋙ perverseRestriction j ≅ perverseAmbient U
  /-- Its objects have no boundary-supported subobjects. -/
  noSubobjects : ∀ P, NoBoundarySubobjects j (functor.obj P)
  /-- Its objects have no boundary-supported quotients. -/
  noQuotients : ∀ P, NoBoundaryQuotients j (functor.obj P)

/-- Faithfulness is a formal consequence of the natural restriction
comparison and the faithful ambient inclusion. No geometric provider is
needed for this completed helper. -/
instance intermediateExtension_faithful {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [OpenRestrictionExact j] (J : IntermediateExtensionData j) :
    J.functor.Faithful :=
  J.restriction.faithful_of_comp

/-- A finite-rank rational local system placed in degree `-d`, namely `L[d]`. -/
def normalizedLocalSystem (U : ComplexScheme) (L : RationalSheaf (space U)) (d : ℕ) :
    RationalDerived (space U) :=
  (DerivedCategory.singleFunctor _ (-(d : ℤ))).obj L

/-- Realize the normalized local system in the actual perverse heart. -/
structure LocalSystemPerverseRealization (U : ComplexScheme) [IsComplexVariety U]
    [PerverseSheafTheory U] (L : RationalSheaf (space U)) (d : ℕ) where
  /-- The perverse object. -/
  object : PerverseSheaf U
  /-- Its underlying complex is exactly `L[d]`. -/
  comparison : (perverseAmbient U).obj object ≅ normalizedLocalSystem U L d

/-- Construct `IC` from intermediate extension and the normalized local system.
For a dense smooth open `U`, this is the perverse-normalized intersection complex. -/
def intersectionComplex {U X : ComplexScheme} [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [OpenRestrictionExact j] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) (R : LocalSystemPerverseRealization U L d) :
    PerverseSheaf X := J.functor.obj R.object

/-- The constructed intersection complex restricts to `L[d]` by its actual
comparison maps. -/
def intersectionComplex_restriction {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [OpenRestrictionExact j] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) (R : LocalSystemPerverseRealization U L d) :
    (perverseRestriction j).obj (intersectionComplex j J L d R) ≅
      normalizedLocalSystem U L d :=
  J.restriction.app R.object ≪≫ R.comparison

end MathlibExt.AlgebraicGeometry.IntersectionComplexes
