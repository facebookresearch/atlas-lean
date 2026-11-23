/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-!
# Intermediate extensions and intersection-complex normalization

The perverse t-structure is the support/cosupport-characterized
`PerverseSheafTheory`. Restriction to an open is the exact inverse image of
sheaves, derived (`ConstructibleComplexes.derivedPullback`). Intermediate
extension is specified by a natural restriction isomorphism and the absence of
subobjects and quotients supported on the boundary, which characterize it
(BBD, §1.4). For a sheaf `L`, `L[d]` is `L` placed in cohomological degree
`-d`. The intersection complex `j_{!*}(L[d])` is formed only for a finite-rank
local system `L` on a smooth open `U` of pure dimension `d`: the intermediate
extension of an arbitrary perverse `L[d]` need not be one (de Cataldo–Migliorini,
§2.7).

All constructions here are complete. The existence, fullness and uniqueness of
intermediate extension and the perversity of `L[d]` are requested in
`WantedExt/AlgebraicGeometry/IntersectionComplexesWanted.lean`.

## References

* A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982), §1.4.
* M. A. de Cataldo and L. Migliorini, https://arxiv.org/abs/0712.0349,
  §§2.1 and 2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntersectionComplexes

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- The actual inverse image on derived rational sheaves, induced by the exact
inverse-image functor of sheaves. -/
def derivedRestriction {U X : ComplexScheme} (j : U ⟶ X) :
    RationalDerived (space X) ⥤ RationalDerived (space U) :=
  ConstructibleComplexes.derivedPullback ℚ (spaceMap j)

/-- Restrict a perverse object, keeping the target in the actual derived category. -/
def perverseRestriction {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X) :
    PerverseSheaf X ⥤ RationalDerived (space U) :=
  perverseAmbient X ⋙ derivedRestriction j

/-- Boundary support means that the actual restriction is zero. -/
def IsBoundarySupported {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X)
    (P : PerverseSheaf X) : Prop :=
  IsZero ((perverseRestriction j).obj P)

/-- No nonzero subobject supported on the complement of the open. -/
def NoBoundarySubobjects {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X)
    (P : PerverseSheaf X) : Prop :=
  ∀ (Q : PerverseSheaf X) (a : Q ⟶ P), Mono a → IsBoundarySupported j Q → IsZero Q

/-- No nonzero quotient supported on the complement of the open. -/
def NoBoundaryQuotients {U X : ComplexScheme} [IsComplexVariety X]
    [PerverseSheafTheory X] (j : U ⟶ X)
    (P : PerverseSheaf X) : Prop :=
  ∀ (Q : PerverseSheaf X) (a : P ⟶ Q), Epi a → IsBoundarySupported j Q → IsZero Q

/-- The source-normalized intermediate-extension functor, characterized
without an arbitrary predicate called "intersection complex". -/
structure IntermediateExtensionData {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) where
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
    (j : U ⟶ X) (J : IntermediateExtensionData j) :
    J.functor.Faithful :=
  J.restriction.faithful_of_comp

/-- A rational sheaf `L` placed in cohomological degree `-d`, namely `L[d]`. -/
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

/-- The intersection complex `j_{!*}(L[d])` of a finite-rank local system `L` on a
smooth open `U` of pure dimension `d`. For dense `U` this is `IC_X(L)`; in general
it is the intersection complex of the closure of `U`, extended by zero. -/
def intersectionComplex {U X : ComplexScheme} [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [IsOpenImmersion j.left] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) [SmoothOfRelativeDimension d U.hom]
    (_hL : IsFiniteRankLocalSystem (space U) L) (R : LocalSystemPerverseRealization U L d) :
    PerverseSheaf X := J.functor.obj R.object

/-- The constructed intersection complex restricts to `L[d]` by its actual
comparison maps. -/
def intersectionComplex_restriction {U X : ComplexScheme}
    [IsComplexVariety U] [IsComplexVariety X]
    [PerverseSheafTheory U] [PerverseSheafTheory X]
    (j : U ⟶ X) [IsOpenImmersion j.left] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) [SmoothOfRelativeDimension d U.hom]
    (hL : IsFiniteRankLocalSystem (space U) L) (R : LocalSystemPerverseRealization U L d) :
    (perverseRestriction j).obj (intersectionComplex j J L d hL R) ≅
      normalizedLocalSystem U L d :=
  J.restriction.app R.object ≪≫ R.comparison

end MathlibExt.AlgebraicGeometry.IntersectionComplexes
