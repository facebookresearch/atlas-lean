/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.ProjectiveResolutionNormalizationTransport
public import MathlibExt.Algebra.Homology.InjectiveResolutionNormalizationTransport
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Data.ZMod.Basic

/-!
# Nonzero resolution comparisons across module universes

The native universe-lift functor carries integer modules with carriers in
universe zero to carriers in universe one. A chosen projective resolution of
the regular integer module has an element mapping to 5 under its augmentation.
A chosen injective resolution of ZMod 6 has a nonzero image of the residue 1
under its initial inclusion. Normalization transport and the mapped
normalization comparisons preserve these values.

The zero-object cases also test every natural-number-indexed term of the
normalized resolutions. Projectivity, injectivity, and exactness of universe
lift come from their native module-category instances.
-/

noncomputable section

open CategoryTheory Limits

namespace MathlibExtTest.ResolutionNormalizationTransport

private abbrev C := ModuleCat.{0} ℤ
private abbrev D := ModuleCat.{1} ℤ
private abbrev F : C ⥤ D := ModuleCat.uliftFunctor.{1, 0} ℤ

private abbrev Z : C := ModuleCat.of ℤ ℤ
private def P : ProjectiveResolution Z := ProjectiveResolution.of Z

private def pFive : P.zeroNormalized.complex.X 0 :=
  Classical.choose
    ((ModuleCat.epi_iff_surjective (P.zeroNormalized.π.f 0)).mp inferInstance (5 : Z))

private lemma pFive_augmentation :
    (P.zeroNormalized.π.f 0).hom pFive = (5 : ℤ) :=
  Classical.choose_spec
    ((ModuleCat.epi_iff_surjective (P.zeroNormalized.π.f 0)).mp inferInstance (5 : Z))

private lemma mappedProjective_augmentation_apply {M : C}
    (Q : ProjectiveResolution M) (x : Q.complex.X 0) :
    ((F.mapProjectiveResolution Q).π.f 0).hom (ULift.up x) =
      ULift.up ((Q.π.f 0).hom x) := by
  change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).hom.app M).f 0).hom _ = _
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    Functor.map_id, Category.comp_id]
  rfl

example : (P.zeroNormalized.π.f 0).hom pFive = (5 : ℤ) :=
  pFive_augmentation

example : pFive ≠ 0 := by
  intro h
  have hFive := pFive_augmentation
  rw [h, map_zero] at hFive
  exact (by decide : (0 : ℤ) ≠ 5) hFive

example :
    ((F.mapProjectiveResolution P.zeroNormalized).π.f 0).hom (ULift.up pFive) =
      ULift.up (5 : ℤ) := by
  rw [mappedProjective_augmentation_apply, pFive_augmentation]

example :
    ((F.mapProjectiveResolution P).zeroNormalized.π.f 0).hom
        (((ProjectiveResolution.zeroNormalizedMapComplexIso F P).hom.f 0).hom
          (ULift.up pFive)) =
      ULift.up (5 : ℤ) := by
  have h := congrArg
    (fun f : (F.mapProjectiveResolution P.zeroNormalized).complex ⟶
        (ChainComplex.single₀ D).obj (F.obj Z) =>
      (f.f 0).hom (ULift.up pFive))
    (ProjectiveResolution.zeroNormalizedMapComplexIso_hom_π F P)
  calc
    _ = ((F.mapProjectiveResolution P.zeroNormalized).π.f 0).hom
        (ULift.up pFive) := h
    _ = ULift.up (5 : ℤ) := by
      rw [mappedProjective_augmentation_apply, pFive_augmentation]

example :
    ((F.mapProjectiveResolution P).π.f 0).hom
        ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          P.zeroNormalizedHomotopyEquiv.hom).f 0).hom (ULift.up pFive)) =
      ULift.up (5 : ℤ) := by
  have h := congrArg
    (fun f : (F.mapProjectiveResolution P.zeroNormalized).complex ⟶
        (ChainComplex.single₀ D).obj (F.obj Z) =>
      (f.f 0).hom (ULift.up pFive))
    (ProjectiveResolution.map_zeroNormalizedHomotopyEquiv_hom_π F P)
  calc
    _ = ((F.mapProjectiveResolution P.zeroNormalized).π.f 0).hom
        (ULift.up pFive) := h
    _ = ULift.up (5 : ℤ) := by
      rw [mappedProjective_augmentation_apply, pFive_augmentation]

example :
    Nonempty (Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        P.zeroNormalizedHomotopyEquiv.hom)
      ((ProjectiveResolution.zeroNormalizedMapComplexIso F P).hom ≫
        (F.mapProjectiveResolution P).zeroNormalizedHomotopyEquiv.hom)) :=
  ⟨ProjectiveResolution.zeroNormalizedMapComparisonHomotopy F P⟩

private abbrev A : C := ModuleCat.of ℤ (ZMod 6)
private def I : InjectiveResolution A := InjectiveResolution.of A

private def unitInNormalizedI : I.zeroNormalized.cocomplex.X 0 :=
  (I.zeroNormalized.ι.f 0).hom (1 : ZMod 6)

private lemma unitInNormalizedI_ne_zero : unitInNormalizedI ≠ 0 := by
  intro h
  have hOne : (1 : ZMod 6) = 0 :=
    (ModuleCat.mono_iff_injective (I.zeroNormalized.ι.f 0)).mp inferInstance
      (by simpa only [unitInNormalizedI, map_zero] using h)
  exact one_ne_zero hOne

private lemma mappedInjective_inclusion_apply {M : C}
    (J : InjectiveResolution M) (x : M) :
    ((F.mapInjectiveResolution J).ι.f 0).hom (ULift.up x) =
      ULift.up ((J.ι.f 0).hom x) := by
  change (((HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℕ) 0).inv.app M ≫
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map J.ι).f 0).hom _ = _
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    Functor.map_id, Category.id_comp]
  rfl

private lemma transported_inclusion_value :
    ((InjectiveResolution.zeroNormalizedMapComplexIso F I).hom.f 0).hom
        (ULift.up unitInNormalizedI) =
      ((F.mapInjectiveResolution I).zeroNormalized.ι.f 0).hom
        (ULift.up (1 : ZMod 6)) := by
  have h := congrArg
    (fun f : (CochainComplex.single₀ D).obj (F.obj A) ⟶
        (F.mapInjectiveResolution I).zeroNormalized.cocomplex =>
      (f.f 0).hom (ULift.up (1 : ZMod 6)))
    (InjectiveResolution.zeroNormalizedMapComplexIso_ι_hom F I)
  change ((InjectiveResolution.zeroNormalizedMapComplexIso F I).hom.f 0).hom
      (((F.mapInjectiveResolution I.zeroNormalized).ι.f 0).hom
        (ULift.up (1 : ZMod 6))) = _ at h
  rw [mappedInjective_inclusion_apply] at h
  exact h

example : unitInNormalizedI ≠ 0 :=
  unitInNormalizedI_ne_zero

example :
    ((F.mapInjectiveResolution I.zeroNormalized).ι.f 0).hom
        (ULift.up (1 : ZMod 6)) = ULift.up unitInNormalizedI :=
  mappedInjective_inclusion_apply I.zeroNormalized (1 : ZMod 6)

example :
    ((InjectiveResolution.zeroNormalizedMapComplexIso F I).hom.f 0).hom
        (ULift.up unitInNormalizedI) =
      ((F.mapInjectiveResolution I).zeroNormalized.ι.f 0).hom
        (ULift.up (1 : ZMod 6)) :=
  transported_inclusion_value

example :
    ((InjectiveResolution.zeroNormalizedMapComplexIso F I).hom.f 0).hom
        (ULift.up unitInNormalizedI) ≠ 0 := by
  rw [transported_inclusion_value]
  intro h
  have hOne : (ULift.up (1 : ZMod 6) : F.obj A) = 0 :=
    (ModuleCat.mono_iff_injective
      ((F.mapInjectiveResolution I).zeroNormalized.ι.f 0)).mp inferInstance
      (by simpa only [map_zero] using h)
  exact one_ne_zero (congrArg ULift.down hOne)

example :
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        I.zeroNormalizedHomotopyEquiv.hom).f 0).hom
      (ULift.up unitInNormalizedI) =
        ULift.up ((I.ι.f 0).hom (1 : ZMod 6)) := by
  have h := congrArg
    (fun f : (CochainComplex.single₀ D).obj (F.obj A) ⟶
        (F.mapInjectiveResolution I).cocomplex =>
      (f.f 0).hom (ULift.up (1 : ZMod 6)))
    (InjectiveResolution.map_zeroNormalizedHomotopyEquiv_hom_ι F I)
  change (((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      I.zeroNormalizedHomotopyEquiv.hom).f 0).hom
        (((F.mapInjectiveResolution I.zeroNormalized).ι.f 0).hom
          (ULift.up (1 : ZMod 6))) =
      ((F.mapInjectiveResolution I).ι.f 0).hom (ULift.up (1 : ZMod 6)) at h
  rw [mappedInjective_inclusion_apply, mappedInjective_inclusion_apply] at h
  exact h

example :
    Nonempty (Homotopy
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        I.zeroNormalizedHomotopyEquiv.hom)
      ((InjectiveResolution.zeroNormalizedMapComplexIso F I).hom ≫
        (F.mapInjectiveResolution I).zeroNormalizedHomotopyEquiv.hom)) :=
  ⟨InjectiveResolution.zeroNormalizedMapComparisonHomotopy F I⟩

example (n : ℕ) :
    IsZero ((F.mapProjectiveResolution
      (ProjectiveResolution.of (0 : C))).zeroNormalized.complex.X n) :=
  ProjectiveResolution.zeroNormalized_complex_X_isZero _
    (F.map_isZero (isZero_zero C)) n

example (n : ℕ) :
    IsZero ((F.mapInjectiveResolution
      (InjectiveResolution.of (0 : C))).zeroNormalized.cocomplex.X n) :=
  InjectiveResolution.zeroNormalized_cocomplex_X_isZero _
    (F.map_isZero (isZero_zero C)) n

end MathlibExtTest.ResolutionNormalizationTransport
