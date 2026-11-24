/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageNaturality

/-! # Ordinary consumers of native second-page naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantSecondPageNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- Consumers can recover the actual second-page map from the fixed comparison.
The theorem applies to the existing map, so this identity does not define it. -/
theorem actual_map_from_iterated_homology (f : K ⟶ L) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex f p q =
      (horizontalSecondPageVerticalHorizontalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap f q) p ≫
        (horizontalSecondPageVerticalHorizontalHomologyIso L p q).inv := by
  apply (cancel_mono (horizontalSecondPageVerticalHorizontalHomologyIso L p q).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality f p q

/-- A composite bicomplex map yields the composite iterated-homology map after
the same fixed second-page comparison. -/
theorem actual_composite_map (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex (f ≫ g) p q ≫
        (horizontalSecondPageVerticalHorizontalHomologyIso M p q).hom =
      (horizontalSecondPageVerticalHorizontalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap f q) p ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap g q) p := by
  simpa only [verticalHomologyComplexMap_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc] using
    horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality (f ≫ g) p q

/-- The native successor square includes the left boundary bidegree. -/
theorem native_successor_at_left_boundary (f : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap (horizontalPageMapOfBicomplex f 1 (le_refl 1))
        (0, q) ≫ ((horizontalFirstQuadrantSpectralSequence L).iso 1 2 (0, q)).hom =
      ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).hom ≫
        horizontalSecondPageMapOfBicomplex f 0 q :=
  horizontalPageMapOfBicomplex_successor_one_two f 0 q

/-- The signed comparison and actual page map also agree at the corner. -/
theorem actual_map_at_corner (f : K ⟶ L) :
    horizontalSecondPageMapOfBicomplex f 0 0 =
      (horizontalSecondPageVerticalHorizontalHomologyIso K 0 0).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap f 0) 0 ≫
        (horizontalSecondPageVerticalHorizontalHomologyIso L 0 0).inv :=
  actual_map_from_iterated_homology f 0 0

end HomologicalComplex₂.FirstQuadrantSecondPageNaturalityTests
