/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Category.ModuleCat.AugmentedFlatComplexTensor
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Tensor augmentation of a projective resolution of a flat module

The coefficient tensor augmentation of a projective resolution agrees with the tensor image of its
projective augmentation followed by concentration in degree zero. Flatness of the target and the
projective terms makes this augmentation a quasi-isomorphism; positive homology vanishes for every
coefficient.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]
  (M : ModuleCat.{v} R) {X : ModuleCat.{max u w} R}
  (P : ProjectiveResolution X)

/--
The original heterogeneous fixed-coefficient tensor functor is right exact in the source and
target universes.
-/
theorem projectiveCoefficientTensor_preservesFiniteColimits :
    PreservesFiniteColimits ((tensorBifunctorAt.{u, v, max u w} R).obj M) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2
  intro S hS
  have hg : Function.Surjective S.g := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  constructor
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact M
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hg
  · exact (ModuleCat.epi_iff_surjective _).mpr (LinearMap.lTensor_surjective M hg)

/-- The original coefficient tensor functor acts on the given original resolution complex. -/
def projectiveCoefficientComplex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  (((tensorBifunctorAt.{u, v, max u w} R).obj M).mapHomologicalComplex (.down ℕ)).obj P.complex

/-- The original augmentation's incoming differential is annihilated after the tensor functor. -/
theorem projectiveCoefficientAugmentation_zero :
    (projectiveCoefficientComplex R M P).d 1 0 ≫
      ((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0) = 0 := by
  let F := (tensorBifunctorAt.{u, v, max u w} R).obj M
  have h : P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
    have hπ := (P.π.comm 1 0).symm
    rw [HomologicalComplex.single_obj_d, comp_zero] at hπ
    exact hπ
  change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
  exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_zero _ _))

/-- The coefficient tensor augmentation retains the original tensor of the augmentation component. -/
def projectiveCoefficientAugmentation : projectiveCoefficientComplex R M P ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
      (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X) :=
  (ChainComplex.toSingle₀Equiv (projectiveCoefficientComplex R M P)
    (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X)).symm
      ⟨((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0),
        projectiveCoefficientAugmentation_zero R M P⟩

/-- Component zero is the tensor map of the original projective augmentation. -/
theorem projectiveCoefficientAugmentation_f_zero :
    (projectiveCoefficientAugmentation R M P).f 0 =
      ((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/--
The original coefficient augmentation is exactly the tensor image of the original resolution
augmentation followed by single-zero transport.
-/
private theorem projectiveCoefficientAugmentation_eq_actual :
    projectiveCoefficientAugmentation R M P =
      augmentedFlatComplexTensorAugmentation R P.complex X P.π M := by
  apply (ChainComplex.toSingle₀Equiv (projectiveCoefficientComplex R M P)
    (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X)).injective
  apply Subtype.ext
  change (projectiveCoefficientAugmentation R M P).f 0 =
    (augmentedFlatComplexTensorAugmentation R P.complex X P.π M).f 0
  rw [projectiveCoefficientAugmentation_f_zero,
    augmentedFlatComplexTensorAugmentation_f_zero]

/--
Original projectivity makes every resolution term flat; the general arbitrary-coefficient
augmentation theorem then proves the original map quasi-isomorphic.
-/
private theorem projectiveCoefficientAugmentation_actual_quasiIso [Module.Flat R X] :
    _root_.QuasiIso (projectiveCoefficientAugmentation R M P) := by
  let : ∀ n, Module.Flat R (P.complex.X n) := fun n => by infer_instance
  rw [projectiveCoefficientAugmentation_eq_actual]
  exact augmentedFlatComplexTensorAugmentation_quasiIso R P.complex X P.π M

/--
The original coefficient complex has zero positive homology for a flat resolved target. The
original coefficient and original projective resolution are retained.
-/
theorem projectiveCoefficientHomology_isZero_succ [Module.Flat R X] (n : ℕ) :
    IsZero ((projectiveCoefficientComplex R M P).homology (n + 1)) := by
  let : _root_.QuasiIso (projectiveCoefficientAugmentation R M P) :=
    projectiveCoefficientAugmentation_actual_quasiIso R M P
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (.down ℕ) 0
      (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X) (n + 1) (by omega))
    (_root_.isoOfQuasiIsoAt (projectiveCoefficientAugmentation R M P) (n + 1))

/--
Every degree of the original coefficient tensor augmentation is a quasi-isomorphism for a flat
resolved target, with the original arbitrary coefficient M.
-/
instance projectiveCoefficientAugmentation_quasiIso_of_flat_target [Module.Flat R X] :
    _root_.QuasiIso (projectiveCoefficientAugmentation R M P) :=
  projectiveCoefficientAugmentation_actual_quasiIso R M P

section OriginalCarriers

variable (M₀ : Type v) (X₀ : Type w) [AddCommGroup M₀] [AddCommGroup X₀]
  [Module R M₀] [Module R X₀]

/-- The original target and coefficient carriers are returned by the tensor/ULift equivalences. -/
def originalTargetTensorIso :
    ((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).obj
        (ModuleCat.of R (ULift.{u} X₀)) ≅
      ModuleCat.of R (ULift.{u} (M₀ ⊗[R] X₀)) :=
  ((TensorProduct.congr (LinearEquiv.refl R M₀)
    (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)).trans
      (ULift.moduleEquiv : ULift.{u} (M₀ ⊗[R] X₀) ≃ₗ[R] M₀ ⊗[R] X₀).symm).toModuleIso

/-- The original tensor element is unchanged, with only the explicit joint-height lift. -/
theorem originalTargetTensorIso_tmul (m : M₀) (x : X₀) :
    (originalTargetTensorIso R M₀ X₀).hom.hom (m ⊗ₜ[R] ULift.up x) = ULift.up (m ⊗ₜ[R] x) := rfl

variable (P₀ : ProjectiveResolution (ModuleCat.of R (ULift.{u} X₀)))

/--
The augmentation of the original arbitrary coefficient and original target, using a resolution of
the explicitly lifted target.
-/
def originalTargetCoefficientAugmentation :
    projectiveCoefficientComplex R (ModuleCat.of R M₀) P₀ ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
        (ModuleCat.of R (ULift.{u} (M₀ ⊗[R] X₀))) :=
  projectiveCoefficientAugmentation R (ModuleCat.of R M₀) P₀ ≫
    (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map (originalTargetTensorIso R M₀ X₀).hom

/-- The original-target augmentation has exactly the original tensor augmentation at component zero. -/
theorem originalTargetCoefficientAugmentation_f_zero :
    (originalTargetCoefficientAugmentation R M₀ X₀ P₀).f 0 =
      ((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).map (P₀.π.f 0) ≫
        (originalTargetTensorIso R M₀ X₀).hom := by
  rw [originalTargetCoefficientAugmentation, HomologicalComplex.comp_f,
    projectiveCoefficientAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
  rfl

/-- The all-degree original-carrier augmentation is a quasi-isomorphism for the original flat target.
No Small, flat coefficient or equality of original carrier universes is required. -/
instance originalTargetCoefficientAugmentation_quasiIso [Module.Flat R X₀] :
    _root_.QuasiIso (originalTargetCoefficientAugmentation R M₀ X₀ P₀) := by
  let _ : Module.Flat R (ModuleCat.of R (ULift.{u} X₀)) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)
  unfold originalTargetCoefficientAugmentation
  infer_instance

end OriginalCarriers

end ModuleCat
