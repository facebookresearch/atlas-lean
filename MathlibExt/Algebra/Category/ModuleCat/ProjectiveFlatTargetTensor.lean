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
# Tensor augmentation of a projective resolution of a flat target

Let `R` be commutative in universe `u`, coefficient module `M` lie
in `v`, and a resolution `P` resolve `X` in `max(u,w)`.
The tensor complex `M ⊗[R] P` lies in `max(u,v,w)` and its
augmentation has degree-zero map `M ⊗ π₀`. When `X` is flat, this
augmentation is a quasi-isomorphism and all positive tensor homology
vanishes. The pure-tensor formulas also hold for independently sized
original carriers after explicit target lifting.
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

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. The fixed-coefficient tensor functor from
`ModuleCat_max(u,w)(R)` to `ModuleCat_max(u,v,w)(R)` preserves finite
colimits and is therefore right exact. -/
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

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. Applying the fixed-coefficient tensor functor to `P` gives
the nonnegative chain complex `M ⊗[R] P` in
`ModuleCat_max(u,v,w)(R)`. -/
def projectiveCoefficientComplex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  (((tensorBifunctorAt.{u, v, max u w} R).obj M).mapHomologicalComplex (.down ℕ)).obj P.complex

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. The first differential of `M ⊗[R] P` followed by the tensor
augmentation `M ⊗ P₀ → M ⊗ X` is zero. -/
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

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. Tensoring the augmentation of `P` gives the chain map
`M ⊗[R] P → (M ⊗[R] X)[0]`, whose degree-zero map is `M ⊗ π₀`. -/
def projectiveCoefficientAugmentation : projectiveCoefficientComplex R M P ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
      (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X) :=
  (ChainComplex.toSingle₀Equiv (projectiveCoefficientComplex R M P)
    (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X)).symm
      ⟨((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0),
        projectiveCoefficientAugmentation_zero R M P⟩

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. The degree-zero component of the coefficient tensor
augmentation is the tensor-functor image of `π₀ : P₀ → X`. -/
theorem projectiveCoefficientAugmentation_f_zero :
    (projectiveCoefficientAugmentation R M P).f 0 =
      ((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. The coefficient augmentation equals the augmentation obtained
by tensoring the original chain augmentation and identifying the
mapped single complex with `(M ⊗ X)[0]`. -/
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

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. If `X` is flat, the coefficient tensor augmentation is a
quasi-isomorphism, using flatness of every projective resolution term. -/
private theorem projectiveCoefficientAugmentation_actual_quasiIso [Module.Flat R X] :
    _root_.QuasiIso (projectiveCoefficientAugmentation R M P) := by
  let : ∀ n, Module.Flat R (P.complex.X n) := fun n => by infer_instance
  rw [projectiveCoefficientAugmentation_eq_actual]
  exact augmentedFlatComplexTensorAugmentation_quasiIso R P.complex X P.π M

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. If `X` is flat, `H_(n+1)(M ⊗[R] P)=0` for every `n`. -/
theorem projectiveCoefficientHomology_isZero_succ [Module.Flat R X] (n : ℕ) :
    IsZero ((projectiveCoefficientComplex R M P).homology (n + 1)) := by
  let : _root_.QuasiIso (projectiveCoefficientAugmentation R M P) :=
    projectiveCoefficientAugmentation_actual_quasiIso R M P
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (.down ℕ) 0
      (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X) (n + 1) (by omega))
    (_root_.isoOfQuasiIsoAt (projectiveCoefficientAugmentation R M P) (n + 1))

/-- Let `R` be a commutative ring in universe `u`, `M` an `R`-module
in universe `v`, and `X` an `R`-module in universe `max(u,w)`. Let `P` be a projective resolution of `X`. If `X` is flat, the augmentation
`M ⊗[R] P → (M ⊗[R] X)[0]` is a quasi-isomorphism. -/
instance projectiveCoefficientAugmentation_quasiIso_of_flat_target [Module.Flat R X] :
    _root_.QuasiIso (projectiveCoefficientAugmentation R M P) :=
  projectiveCoefficientAugmentation_actual_quasiIso R M P

section OriginalCarriers

variable (M₀ : Type v) (X₀ : Type w) [AddCommGroup M₀] [AddCommGroup X₀]
  [Module R M₀] [Module R X₀]

/-- Let `R` be commutative in universe `u`, and let `M₀,X₀` be
`R`-modules with carriers in `v,w`. There is a canonical module
isomorphism `M₀ ⊗[R] ULift_u(X₀) ≅ ULift_u(M₀ ⊗[R] X₀)` in
carrier universe `max(u,v,w)`. -/
def originalTargetTensorIso :
    ((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).obj
        (ModuleCat.of R (ULift.{u} X₀)) ≅
      ModuleCat.of R (ULift.{u} (M₀ ⊗[R] X₀)) :=
  ((TensorProduct.congr (LinearEquiv.refl R M₀)
    (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)).trans
      (ULift.moduleEquiv : ULift.{u} (M₀ ⊗[R] X₀) ≃ₗ[R] M₀ ⊗[R] X₀).symm).toModuleIso

/-- Let `R` be commutative in universe `u`, and `M₀,X₀` be
`R`-modules with carriers in `v,w`. The canonical target-lift tensor
isomorphism sends `m ⊗ ULift(x)` to `ULift(m ⊗ x)`. -/
theorem originalTargetTensorIso_tmul (m : M₀) (x : X₀) :
    (originalTargetTensorIso R M₀ X₀).hom.hom (m ⊗ₜ[R] ULift.up x) = ULift.up (m ⊗ₜ[R] x) := rfl

variable (P₀ : ProjectiveResolution (ModuleCat.of R (ULift.{u} X₀)))

/-- Let `R` be commutative in universe `u`, `M₀,X₀` modules with
carriers in `v,w`, and `P₀` a projective resolution of `ULift_u(X₀)`.
The coefficient tensor augmentation, followed by the target-lift
isomorphism, is a chain map to `ULift_u(M₀ ⊗[R] X₀)[0]`. -/
def originalTargetCoefficientAugmentation :
    projectiveCoefficientComplex R (ModuleCat.of R M₀) P₀ ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
        (ModuleCat.of R (ULift.{u} (M₀ ⊗[R] X₀))) :=
  projectiveCoefficientAugmentation R (ModuleCat.of R M₀) P₀ ≫
    (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map (originalTargetTensorIso R M₀ X₀).hom

/-- Let `R` be commutative in universe `u`, `M₀,X₀` modules with
carriers in `v,w`, and `P₀` resolve `ULift_u(X₀)`. The original-target
augmentation in degree zero is the tensor image of `π_P₀,₀` followed
by `M₀ ⊗ ULift_u(X₀) ≅ ULift_u(M₀ ⊗ X₀)`. -/
theorem originalTargetCoefficientAugmentation_f_zero :
    (originalTargetCoefficientAugmentation R M₀ X₀ P₀).f 0 =
      ((tensorBifunctorAt.{u, v, max u w} R).obj (ModuleCat.of R M₀)).map (P₀.π.f 0) ≫
        (originalTargetTensorIso R M₀ X₀).hom := by
  rw [originalTargetCoefficientAugmentation, HomologicalComplex.comp_f,
    projectiveCoefficientAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
  rfl

/-- Let `R` be commutative in universe `u`, `M₀,X₀` modules with
carriers in `v,w`, and `P₀` resolve `ULift_u(X₀)`. If `X₀` is flat,
the augmentation to `ULift_u(M₀ ⊗[R] X₀)[0]` is a quasi-isomorphism
for this arbitrary coefficient `M₀`. -/
instance originalTargetCoefficientAugmentation_quasiIso [Module.Flat R X₀] :
    _root_.QuasiIso (originalTargetCoefficientAugmentation R M₀ X₀ P₀) := by
  let _ : Module.Flat R (ModuleCat.of R (ULift.{u} X₀)) :=
    Module.Flat.of_linearEquiv (ULift.moduleEquiv : ULift.{u} X₀ ≃ₗ[R] X₀)
  unfold originalTargetCoefficientAugmentation
  infer_instance

end OriginalCarriers

end ModuleCat
