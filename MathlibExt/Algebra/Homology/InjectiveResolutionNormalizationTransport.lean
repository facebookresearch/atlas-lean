/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.CategoryTheory.Abelian.Injective.MapResolution
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Zero-object normalization and transport of injective resolutions

An injective resolution of a zero object may be replaced by the resolution
concentrated on that object in degree zero. At a nonzero object its
zero normalization retains the given resolution.

A faithful additive functor preserving injectives and homology identifies
the mapped normalization with the normalization of the mapped resolution.
The isomorphism preserves the initial inclusion. In abelian categories,
the two resulting normalization comparison maps are homotopic.

The mapped forward normalization comparison preserves its initial inclusion
for any additive functor preserving injectives and homology, with abelian
source and preadditive target having a zero object and homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v u' v'

namespace CategoryTheory.InjectiveResolution

section ZeroObjects

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- For a zero object Z, the injective resolution concentrated on Z in
degree zero has identity inclusion from Z[0] and zero positive terms. -/
def ofIsZero (Z : C) (hZ : IsZero Z) : InjectiveResolution Z := by
  letI : Injective Z := hZ.injective
  exact InjectiveResolution.self Z

/-- Normalize an injective resolution I at its resolved object Z: use the
single-degree resolution if Z is zero, and retain I otherwise. -/
def zeroNormalized {Z : C} (I : InjectiveResolution Z) : InjectiveResolution Z := by
  classical
  exact if hZ : IsZero Z then ofIsZero Z hZ else I

/-- If the resolved object Z is zero, the normalization of I is the
injective resolution concentrated on Z in degree zero. -/
@[simp]
theorem zeroNormalized_of_isZero {Z : C} (I : InjectiveResolution Z)
    (hZ : IsZero Z) : I.zeroNormalized = ofIsZero Z hZ := by
  simp [zeroNormalized, hZ]

/-- If the resolved object Z is nonzero, normalization retains the
given injective resolution I. -/
@[simp]
theorem zeroNormalized_of_not_isZero {Z : C} (I : InjectiveResolution Z)
    (hZ : ¬ IsZero Z) : I.zeroNormalized = I := by
  simp [zeroNormalized, hZ]

/-- If Z is a zero object, every natural-degree term of the zero-normalized
injective resolution of Z is a zero object. -/
theorem zeroNormalized_cocomplex_X_isZero {Z : C} (I : InjectiveResolution Z)
    (hZ : IsZero Z) (n : ℕ) : IsZero (I.zeroNormalized.cocomplex.X n) := by
  rw [zeroNormalized_of_isZero I hZ]
  cases n with
  | zero => simpa [ofIsZero, InjectiveResolution.self] using hZ
  | succ n =>
      change IsZero (((CochainComplex.single₀ C).obj Z).X (n + 1))
      exact HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℕ) 0 Z (n + 1) (Nat.succ_ne_zero n)

end ZeroObjects

section Transport

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]
variable (F : C ⥤ D) [F.Additive] [F.Faithful]
  [F.PreservesInjectiveObjects] [F.PreservesHomology]

private lemma isZero_of_obj_isZero {Z : C} (h : IsZero (F.obj Z)) : IsZero Z := by
  rw [IsZero.iff_id_eq_zero]
  apply F.zero_of_map_zero (𝟙 Z)
  rw [F.map_id]
  exact h.eq_of_src _ _

/-- For a faithful additive F preserving injectives and homology, mapping
I.zeroNormalized and normalizing F(I) give canonically isomorphic cochain
complexes. At a zero object the comparison is single-complex transport. -/
def zeroNormalizedMapComplexIso {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I.zeroNormalized).cocomplex ≅
      (F.mapInjectiveResolution I).zeroNormalized.cocomplex := by
  classical
  by_cases hZ : IsZero Z
  · have hFZ : IsZero (F.obj Z) := F.map_isZero hZ
    rw [I.zeroNormalized_of_isZero hZ,
      (F.mapInjectiveResolution I).zeroNormalized_of_isZero hFZ]
    change (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ C).obj Z) ≅ (CochainComplex.single₀ D).obj (F.obj Z)
    exact (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).app Z
  · have hFZ : ¬ IsZero (F.obj Z) := fun h => hZ (isZero_of_obj_isZero F h)
    rw [I.zeroNormalized_of_not_isZero hZ,
      (F.mapInjectiveResolution I).zeroNormalized_of_not_isZero hFZ]
    exact Iso.refl _

/-- The mapped normalized inclusion followed by the normalization transport
isomorphism equals the inclusion of the normalized target resolution. -/
@[reassoc]
theorem zeroNormalizedMapComplexIso_ι_hom {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I.zeroNormalized).ι ≫
        (zeroNormalizedMapComplexIso F I).hom =
      (F.mapInjectiveResolution I).zeroNormalized.ι := by
  classical
  by_cases hZ : IsZero Z
  · have hFZ : IsZero (F.obj Z) := F.map_isZero hZ
    apply HomologicalComplex.from_single_hom_ext
    exact hFZ.eq_of_src _ _
  · have hFZ : ¬ IsZero (F.obj Z) := fun h => hZ (isZero_of_obj_isZero F h)
    simp [zeroNormalizedMapComplexIso, zeroNormalized, hZ, hFZ]

/-- Composing the normalized target inclusion with the inverse transport
comparison recovers the mapped normalized source inclusion. -/
@[reassoc]
theorem zeroNormalizedMapComplexIso_ι_inv {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I).zeroNormalized.ι ≫
        (zeroNormalizedMapComplexIso F I).inv =
      (F.mapInjectiveResolution I.zeroNormalized).ι := by
  rw [← zeroNormalizedMapComplexIso_ι_hom F I]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Transport

section AbelianSource

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category, the zero-normalized resolution of Z and the
given injective resolution I have homotopy equivalent cochain complexes. -/
def zeroNormalizedHomotopyEquiv {Z : C} (I : InjectiveResolution Z) :
    HomotopyEquiv I.zeroNormalized.cocomplex I.cocomplex :=
  InjectiveResolution.homotopyEquiv I.zeroNormalized I

/-- The forward normalization homotopy equivalence preserves the inclusion
from the single complex on the resolved object Z. -/
@[reassoc]
theorem zeroNormalizedHomotopyEquiv_hom_ι {Z : C} (I : InjectiveResolution Z) :
    I.zeroNormalized.ι ≫ I.zeroNormalizedHomotopyEquiv.hom = I.ι :=
  InjectiveResolution.homotopyEquiv_hom_ι I.zeroNormalized I

end AbelianSource

section MappedComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]
variable (F : C ⥤ D) [F.Additive]
  [F.PreservesInjectiveObjects] [F.PreservesHomology]

/-- Let C be abelian and let D be preadditive with a zero object and homology.
For additive F : C → D preserving injectives and homology, mapping the forward
normalization comparison of an injective resolution I of Z preserves its
initial inclusion from the single complex F(Z)[0]. -/
@[reassoc]
theorem map_zeroNormalizedHomotopyEquiv_hom_ι {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I.zeroNormalized).ι ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          I.zeroNormalizedHomotopyEquiv.hom =
      (F.mapInjectiveResolution I).ι := by
  let M : CochainComplex C ℕ ⥤ CochainComplex D ℕ :=
    F.mapHomologicalComplex (ComplexShape.up ℕ)
  change ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).inv.app Z ≫ M.map I.zeroNormalized.ι) ≫
        M.map I.zeroNormalizedHomotopyEquiv.hom = _
  rw [Category.assoc, ← M.map_comp, zeroNormalizedHomotopyEquiv_hom_ι]
  rfl

end MappedComparison

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.Faithful]
  [F.PreservesInjectiveObjects] [F.PreservesHomology]

/-- For abelian C and D, the mapped source normalization comparison is
homotopic to the transport isomorphism followed by the normalization
comparison chosen for F(I). Both maps preserve the inclusion of F(Z). -/
def zeroNormalizedMapComparisonHomotopy {Z : C} (I : InjectiveResolution Z) :
    Homotopy
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        I.zeroNormalizedHomotopyEquiv.hom)
      ((zeroNormalizedMapComplexIso F I).hom ≫
        (F.mapInjectiveResolution I).zeroNormalizedHomotopyEquiv.hom) := by
  apply InjectiveResolution.descHomotopy (𝟙 (F.obj Z))
  · simpa only [Functor.map_id, Category.id_comp] using
      map_zeroNormalizedHomotopyEquiv_hom_ι F I
  · rw [← Category.assoc, zeroNormalizedMapComplexIso_ι_hom,
      zeroNormalizedHomotopyEquiv_hom_ι]
    simp only [Functor.map_id, Category.id_comp]

end Abelian

end CategoryTheory.InjectiveResolution
