/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.ProjectiveResolutionNormalization
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Transport of projective resolutions normalized at zero objects

Let F : C → D be a faithful additive functor between preadditive categories
with zero objects. Suppose F preserves projective objects and homology, and
D has homology. Mapping a projective resolution after normalizing it at a
zero object is canonically isomorphic to normalizing its mapped resolution.
The comparison preserves the augmentation.

Mapping the forward normalization comparison preserves its augmentation
for any additive F preserving projectives and homology, with abelian C and
preadditive D having a zero object and homology.

For abelian C and D, the mapped normalization comparison and the comparison
chosen in D commute up to homotopy. The source and target category and
morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v u' v'

namespace CategoryTheory.ProjectiveResolution

section Transport

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]
variable (F : C ⥤ D) [F.Additive] [F.Faithful]
  [F.PreservesProjectiveObjects] [F.PreservesHomology]

private lemma isZero_of_obj_isZero {Z : C} (h : IsZero (F.obj Z)) : IsZero Z := by
  rw [IsZero.iff_id_eq_zero]
  apply F.zero_of_map_zero (𝟙 Z)
  rw [F.map_id]
  exact h.eq_of_src _ _

/-- For a projective resolution P of Z and a faithful additive F preserving
projectives and homology, the complex of F(P.zeroNormalized) is canonically
isomorphic to the complex of (F(P)).zeroNormalized. At a zero object this is
the single-complex transport isomorphism; otherwise both complexes are F(P). -/
def zeroNormalizedMapComplexIso {Z : C} (P : ProjectiveResolution Z) :
    (F.mapProjectiveResolution P.zeroNormalized).complex ≅
      (F.mapProjectiveResolution P).zeroNormalized.complex := by
  classical
  by_cases hZ : IsZero Z
  · have hFZ : IsZero (F.obj Z) := F.map_isZero hZ
    rw [P.zeroNormalized_of_isZero hZ,
      (F.mapProjectiveResolution P).zeroNormalized_of_isZero hFZ]
    change (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ C).obj Z) ≅ (ChainComplex.single₀ D).obj (F.obj Z)
    exact (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app Z
  · have hFZ : ¬ IsZero (F.obj Z) := fun h => hZ (isZero_of_obj_isZero F h)
    rw [P.zeroNormalized_of_not_isZero hZ,
      (F.mapProjectiveResolution P).zeroNormalized_of_not_isZero hFZ]
    exact Iso.refl _

/-- For the normalization transport comparison E, E.hom followed by the
augmentation of (F(P)).zeroNormalized equals the augmentation of
F(P.zeroNormalized), as maps to the single complex on F(Z). -/
@[reassoc]
theorem zeroNormalizedMapComplexIso_hom_π {Z : C} (P : ProjectiveResolution Z) :
    (zeroNormalizedMapComplexIso F P).hom ≫
        (F.mapProjectiveResolution P).zeroNormalized.π =
      (F.mapProjectiveResolution P.zeroNormalized).π := by
  classical
  by_cases hZ : IsZero Z
  · have hFZ : IsZero (F.obj Z) := F.map_isZero hZ
    apply HomologicalComplex.to_single_hom_ext
    exact hFZ.eq_of_tgt _ _
  · have hFZ : ¬ IsZero (F.obj Z) := fun h => hZ (isZero_of_obj_isZero F h)
    simp [zeroNormalizedMapComplexIso, zeroNormalized, hZ, hFZ]

/-- The inverse normalization transport comparison followed by the mapped
source augmentation is the augmentation of the normalized target resolution. -/
@[reassoc]
theorem zeroNormalizedMapComplexIso_inv_π {Z : C} (P : ProjectiveResolution Z) :
    (zeroNormalizedMapComplexIso F P).inv ≫
        (F.mapProjectiveResolution P.zeroNormalized).π =
      (F.mapProjectiveResolution P).zeroNormalized.π := by
  rw [← zeroNormalizedMapComplexIso_hom_π F P]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Transport

section MappedComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]
variable (F : C ⥤ D) [F.Additive]
  [F.PreservesProjectiveObjects] [F.PreservesHomology]

/-- Let C be abelian and let D be preadditive with a zero object and homology.
For additive F : C → D preserving projectives and homology, mapping the forward
normalization comparison of a projective resolution P of Z preserves its
augmentation to the single complex F(Z)[0]. -/
@[reassoc]
theorem map_zeroNormalizedHomotopyEquiv_hom_π {Z : C} (P : ProjectiveResolution Z) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        P.zeroNormalizedHomotopyEquiv.hom ≫ (F.mapProjectiveResolution P).π =
      (F.mapProjectiveResolution P.zeroNormalized).π := by
  let M : ChainComplex C ℕ ⥤ ChainComplex D ℕ :=
    F.mapHomologicalComplex (ComplexShape.down ℕ)
  change M.map P.zeroNormalizedHomotopyEquiv.hom ≫
      (M.map P.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.down ℕ) 0).hom.app Z) = _
  rw [← Category.assoc, ← M.map_comp, zeroNormalizedHomotopyEquiv_hom_π]
  rfl

end MappedComparison

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.Faithful]
  [F.PreservesProjectiveObjects] [F.PreservesHomology]

/-- For abelian C and D, the mapped source normalization comparison is
homotopic to the normalization transport isomorphism followed by the
normalization comparison chosen for F(P). Both maps run from
F(P.zeroNormalized).complex to F(P).complex and preserve the same augmentation. -/
def zeroNormalizedMapComparisonHomotopy {Z : C} (P : ProjectiveResolution Z) :
    Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        P.zeroNormalizedHomotopyEquiv.hom)
      ((zeroNormalizedMapComplexIso F P).hom ≫
        (F.mapProjectiveResolution P).zeroNormalizedHomotopyEquiv.hom) := by
  apply ProjectiveResolution.liftHomotopy (𝟙 (F.obj Z))
  · simpa only [Functor.map_id, Category.comp_id] using
      map_zeroNormalizedHomotopyEquiv_hom_π F P
  · rw [Category.assoc, zeroNormalizedHomotopyEquiv_hom_π,
      zeroNormalizedMapComplexIso_hom_π]
    simp only [Functor.map_id, Category.comp_id]

end Abelian

end CategoryTheory.ProjectiveResolution
