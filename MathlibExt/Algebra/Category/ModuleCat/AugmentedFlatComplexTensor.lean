/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.RingTheory.Flat.KernelOfFlatSurjection
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Tensoring augmented complexes of flat modules

A quasi-isomorphic augmentation from a nonnegative complex of flat modules to a flat module
remains a quasi-isomorphism after tensoring with an arbitrary coefficient. Successive differential
kernels and ranges, flat kernels, and tensor-kernel injections prove the result. The ring,
complex, and coefficient carrier universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]

private theorem kernel_flat_of_flat_range
    {N P : Type v} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
    [Module.Flat R N] (f : N →ₗ[R] P) [Module.Flat R (LinearMap.range f)] :
    Module.Flat R (LinearMap.ker f) := by
  have : Module.Flat R (LinearMap.ker f.rangeRestrict) :=
    Module.Flat.kernel_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofEq _ _ f.ker_rangeRestrict.symm)

private theorem tensor_exact_of_flat_kernel_quotient
    {L N P : Type v} [AddCommGroup L] [AddCommGroup N] [AddCommGroup P]
    [Module R L] [Module R N] [Module R P]
    (f : L →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (M : Type w) [AddCommGroup M] [Module R M]
    (hι : Function.Injective ((LinearMap.range g).subtype.lTensor M)) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  have h' : Function.Exact f g.rangeRestrict := by
    rw [← (LinearMap.range g).subtype_injective.comp_exact_iff_exact,
      g.subtype_comp_rangeRestrict]
    exact h
  have ht := lTensor_exact M h' g.surjective_rangeRestrict
  have hcomp := hι.comp_exact_iff_exact.mpr ht
  simpa only [← LinearMap.lTensor_comp, g.subtype_comp_rangeRestrict] using hcomp

section Augmentation

variable (Q : ChainComplex (ModuleCat.{v} R) ℕ) (X : ModuleCat.{v} R)
  (π : Q ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj X) [QuasiIso π]


private theorem augmentation_exact :
    Function.Exact (Q.d 1 0).hom (π.f 0).hom := by
  have h := (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
      (ComplexShape.down ℕ) 1 0 0).map π)
    (Q.shape 0 0 (by simp [ComplexShape.down_Rel]))
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 X 1 0)
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 X 0 0)).mp
      ((ChainComplex.quasiIsoAt₀_iff π).mp inferInstance)
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.1

private theorem augmentation_surjective : Function.Surjective (π.f 0).hom := by
  have h := (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
      (ComplexShape.down ℕ) 1 0 0).map π)
    (Q.shape 0 0 (by simp [ComplexShape.down_Rel]))
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 X 1 0)
    (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 X 0 0)).mp
      ((ChainComplex.quasiIsoAt₀_iff π).mp inferInstance)
  exact (ModuleCat.epi_iff_surjective _).mp h.2

include X π in
private theorem positive_exact (n : ℕ) :
    Function.Exact (Q.d (n + 2) (n + 1)).hom (Q.d (n + 1) n).hom := by
  have hn : Q.ExactAt (n + 1) :=
    (quasiIsoAt_iff_exactAt' π (n + 1)
      (HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 X
        (n + 1) (by omega))).mp inferInstance
  have he := (Q.exactAt_iff' (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).mp hn
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he

variable [Module.Flat R X] [∀ n, Module.Flat R (Q.X n)]

include X π in
private theorem differential_range_flat (n : ℕ) :
    Module.Flat R (LinearMap.range (Q.d (n + 1) n).hom) := by
  induction n with
  | zero =>
      let : Module.Flat R (((ChainComplex.single₀ (ModuleCat.{v} R)).obj X).X 0) := by
        exact Module.Flat.of_linearEquiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).toLinearEquiv
      have : Module.Flat R (LinearMap.ker (π.f 0).hom) :=
        Module.Flat.kernel_of_surjective (π.f 0).hom
          (augmentation_surjective R Q X π)
      exact Module.Flat.of_linearEquiv
        (LinearEquiv.ofEq _ _ (augmentation_exact R Q X π).linearMap_ker_eq.symm)
  | succ n ih =>
      let : Module.Flat R (LinearMap.range (Q.d (n + 1) n).hom) := ih
      have : Module.Flat R (LinearMap.ker (Q.d (n + 1) n).hom) :=
        kernel_flat_of_flat_range R (Q.d (n + 1) n).hom
      exact Module.Flat.of_linearEquiv
        (LinearEquiv.ofEq _ _ (positive_exact R Q X π n).linearMap_ker_eq.symm)

include X π in
/-- The differential image is flat, with its submodule action. -/
theorem augmentedFlatComplexTensor_range_flat (n : ℕ) :
    Module.Flat R (LinearMap.range (Q.d (n + 1) n).hom) :=
  differential_range_flat R Q X π n

variable (M : ModuleCat.{w} R)

/-- The fixed-coefficient heterogeneous tensor functor. -/
abbrev originalCoefficientTensorFunctor :
    ModuleCat.{v} R ⥤ ModuleCat.{max v w} R :=
  (tensorBifunctorAt R).obj M

/-- The image of the complex under that same tensor functor. -/
abbrev originalCoefficientTensorComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ((originalCoefficientTensorFunctor R M).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q

local notation "F" => originalCoefficientTensorFunctor R M
local notation "TQ" => originalCoefficientTensorComplex R Q M

/--
Apply the tensor functor to the augmentation, followed by the single-zero transport. Both factors
are retained.
-/
def augmentedFlatComplexTensorAugmentation :
    TQ ⟶ (ChainComplex.single₀ (ModuleCat.{max v w} R)).obj ((F).obj X) :=
  ((F).mapHomologicalComplex (ComplexShape.down ℕ)).map π ≫
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X

omit [QuasiIso π] [Module.Flat R X] [∀ n, Module.Flat R (Q.X n)] in
/-- Degree zero is precisely the coefficient tensor of the augmentation map. -/
theorem augmentedFlatComplexTensorAugmentation_f_zero :
    (augmentedFlatComplexTensorAugmentation R Q X π M).f 0 = (F).map (π.f 0) := by
  simp only [augmentedFlatComplexTensorAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  change (F).map (π.f 0) ≫ (F).map (𝟙 _) ≫ 𝟙 _ = (F).map (π.f 0)
  rw [(F).map_id, Category.comp_id, Category.comp_id]

include X π in
private theorem positive_tensor_exact (n : ℕ) :
    Function.Exact ((Q.d (n + 2) (n + 1)).hom.lTensor M)
      ((Q.d (n + 1) n).hom.lTensor M) := by
  let g := (Q.d (n + 1) n).hom
  have hι : Function.Injective ((LinearMap.range g).subtype.lTensor M) := by
    cases n with
    | zero =>
        let : Module.Flat R (((ChainComplex.single₀ (ModuleCat.{v} R)).obj X).X 0) := by
          exact Module.Flat.of_linearEquiv
            (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).toLinearEquiv
        have he := (augmentation_exact R Q X π).linearMap_ker_eq
        let e := LinearEquiv.ofEq (LinearMap.range g) (LinearMap.ker (π.f 0).hom) he.symm
        have hi := LinearMap.lTensor_injective_of_exact_of_flat
          (π.f 0).hom (augmentation_surjective R Q X π)
          (LinearMap.ker (π.f 0).hom).subtype
          (LinearMap.ker (π.f 0).hom).subtype_injective
          (LinearMap.exact_subtype_ker_map (π.f 0).hom) M
        have hsub : (LinearMap.ker (π.f 0).hom).subtype.comp e.toLinearMap =
            (LinearMap.range g).subtype := by ext x; rfl
        rw [← hsub, LinearMap.lTensor_comp]
        exact hi.comp (e.lTensor M).injective
    | succ n =>
        let h := (Q.d (n + 1) n).hom
        let : Module.Flat R (LinearMap.range h) := differential_range_flat R Q X π n
        have he := (positive_exact R Q X π n).linearMap_ker_eq
        let e := LinearEquiv.ofEq (LinearMap.range g) (LinearMap.ker h.rangeRestrict)
          (he.symm.trans h.ker_rangeRestrict.symm)
        have hi := LinearMap.lTensor_injective_of_exact_of_flat h.rangeRestrict
          h.surjective_rangeRestrict (LinearMap.ker h.rangeRestrict).subtype
          (LinearMap.ker h.rangeRestrict).subtype_injective
          (LinearMap.exact_subtype_ker_map h.rangeRestrict) M
        have hsub : (LinearMap.ker h.rangeRestrict).subtype.comp e.toLinearMap =
            (LinearMap.range g).subtype := by ext x; rfl
        rw [← hsub, LinearMap.lTensor_comp]
        exact hi.comp (e.lTensor M).injective
  exact tensor_exact_of_flat_kernel_quotient R
    (Q.d (n + 2) (n + 1)).hom g (positive_exact R Q X π n) M hι

/--
The heterogeneous coefficient tensor augmentation is a quasi-isomorphism. Only the complex terms
and target are flat; the coefficient is arbitrary.
-/
theorem augmentedFlatComplexTensorAugmentation_quasiIso :
    QuasiIso (augmentedFlatComplexTensorAugmentation R Q X π M) := by
  let τ := augmentedFlatComplexTensorAugmentation R Q X π M
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros'
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{max v w} R)
          (ComplexShape.down ℕ) 1 0 0).map τ)
        ((TQ).shape 0 0 (by simp [ComplexShape.down_Rel]))
        (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 ((F).obj X) 1 0)
        (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 ((F).obj X) 0 0)).mpr
      constructor
      · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        change Function.Exact ((TQ).d 1 0).hom (τ.f 0).hom
        change Function.Exact ((TQ).d 1 0).hom
          ((augmentedFlatComplexTensorAugmentation R Q X π M).f 0).hom
        rw [augmentedFlatComplexTensorAugmentation_f_zero]
        change Function.Exact ((Q.d 1 0).hom.lTensor M) ((π.f 0).hom.lTensor M)
        exact lTensor_exact M (augmentation_exact R Q X π)
          (augmentation_surjective R Q X π)
      · rw [ModuleCat.epi_iff_surjective]
        change Function.Surjective (τ.f 0).hom
        change Function.Surjective
          ((augmentedFlatComplexTensorAugmentation R Q X π M).f 0).hom
        rw [augmentedFlatComplexTensorAugmentation_f_zero]
        change Function.Surjective ((π.f 0).hom.lTensor M)
        exact LinearMap.lTensor_surjective M (augmentation_surjective R Q X π)
  | succ n =>
      apply (quasiIsoAt_iff_exactAt' τ (n + 1)
        (HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0
          ((F).obj X) (n + 1) (by omega))).mpr
      rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
        (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))]
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact positive_tensor_exact R Q X π M n

end Augmentation

end ModuleCat
