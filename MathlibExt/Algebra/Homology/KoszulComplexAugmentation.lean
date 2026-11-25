/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
-- Original authors: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplex
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Degree-zero augmentation of a Koszul complex

The degree-zero cokernel of the Koszul differential associated to
`x : M →ₗ[R] R` is the quotient of `R` by the range ideal of `x`. This file
constructs the raw quotient map, its universe-lifted categorical version, the
augmentation to a complex concentrated in degree zero, and the corresponding
exactness and cokernel proofs.

## Main declarations

* `KoszulComplex.ideal`
* `KoszulComplex.augmentationLinear`
* `KoszulComplex.augmentation`
* `KoszulComplex.augmentation_exact_zero`
* `KoszulComplex.augmentationIsCokernel`
-/

@[expose] public section


noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The ideal which is the range of the coefficient functional. -/
def ideal (x : M →ₗ[R] R) : Ideal R :=
  LinearMap.range x

/-- In degrees one and zero, the Koszul differential is the coefficient
functional under the canonical exterior-power equivalences. -/
theorem differential_zero_equiv (x : M →ₗ[R] R) :
    (exteriorPower.zeroEquiv R M).toLinearMap.comp (differential R M x 0) =
      x.comp (exteriorPower.oneEquiv R M).toLinearMap := by
  simpa only [differential_eq_contractLeft] using
    exteriorPower.zeroEquiv_comp_contractLeft R M x

/-- The degree-zero quotient map of the Koszul complex. -/
@[no_expose]
def augmentationLinear (x : M →ₗ[R] R) :
    (⋀[R]^0 M) →ₗ[R] R ⧸ ideal R M x :=
  (Ideal.Quotient.mkₐ R (ideal R M x)).toLinearMap.comp
    (exteriorPower.zeroEquiv R M).toLinearMap

/-- The degree-zero augmentation is the quotient projection. -/
theorem augmentationLinear_apply (x : M →ₗ[R] R) (z : ⋀[R]^0 M) :
    augmentationLinear R M x z =
      Ideal.Quotient.mk (ideal R M x) (exteriorPower.zeroEquiv R M z) := by
  unfold augmentationLinear
  rfl

/-- The raw augmentation sends the canonical degree-zero exterior generator
to the class of one. -/
@[simp]
theorem augmentationLinear_apply_ιMulti (x : M →ₗ[R] R)
    (b : Fin 0 → M) :
    augmentationLinear R M x (exteriorPower.ιMulti R 0 b) =
      Ideal.Quotient.mk (ideal R M x) 1 := by
  simp [augmentationLinear, LinearMap.comp_apply]

/-- The degree-one differential is killed by the quotient augmentation. -/
theorem differential_zero_comp_augmentationLinear (x : M →ₗ[R] R) :
    (augmentationLinear R M x).comp (differential R M x 0) = 0 := by
  rw [augmentationLinear, LinearMap.comp_assoc, differential_zero_equiv]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  change Ideal.Quotient.mk (ideal R M x)
      (x ((exteriorPower.oneEquiv R M) z)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact LinearMap.mem_range_self x ((exteriorPower.oneEquiv R M) z)

/-- The raw quotient augmentation is surjective. -/
theorem augmentationLinear_surjective (x : M →ₗ[R] R) :
    Function.Surjective (augmentationLinear R M x) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨(exteriorPower.zeroEquiv R M).symm r, ?_⟩
  simp [augmentationLinear]

/-- Universe-lifted degree-zero quotient map, so that it belongs to the same
`ModuleCat` as every exterior-power term. -/
@[no_expose]
def augmentationLinearLifted (x : M →ₗ[R] R) :
    (⋀[R]^0 M) →ₗ[R] ULift.{max u v, u} (R ⧸ ideal R M x) :=
  ULift.moduleEquiv.symm.toLinearMap.comp (augmentationLinear R M x)

/-- The lifted original augmentation carries the canonical quotient value through `ULift.up`. -/
theorem augmentationLinearLifted_apply (x : M →ₗ[R] R) (z : ⋀[R]^0 M) :
    augmentationLinearLifted R M x z = ULift.up (augmentationLinear R M x z) := by
  unfold augmentationLinearLifted
  rfl

/-- The degree-one differential is also killed by the lifted augmentation. -/
theorem differential_zero_comp_augmentationLinearLifted (x : M →ₗ[R] R) :
    (augmentationLinearLifted R M x).comp (differential R M x 0) = 0 := by
  rw [augmentationLinearLifted, LinearMap.comp_assoc,
    differential_zero_comp_augmentationLinear R M x, LinearMap.comp_zero]

/-- The universe-lifted quotient augmentation is surjective. -/
theorem augmentationLinearLifted_surjective (x : M →ₗ[R] R) :
    Function.Surjective (augmentationLinearLifted R M x) := by
  intro z
  obtain ⟨a, ha⟩ := augmentationLinear_surjective R M x z.down
  refine ⟨a, ?_⟩
  apply ULift.down_injective
  simpa [augmentationLinearLifted] using ha

/-- The quotient augmentation as a map to a complex concentrated in degree zero. -/
def augmentation (x : M →ₗ[R] R) :
    complex R M x ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
        (ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x))) := by
  have hz : (complex R M x).d 1 0 ≫
      ModuleCat.ofHom (augmentationLinearLifted R M x) = 0 := by
    rw [complex_d_succ]
    apply ModuleCat.hom_ext
    change (augmentationLinearLifted R M x).comp (differential R M x 0) = 0
    exact differential_zero_comp_augmentationLinearLifted R M x
  exact (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (augmentationLinearLifted R M x), hz⟩

/-- The degree-zero component of the quotient augmentation. -/
theorem augmentation_f_zero (x : M →ₗ[R] R) :
    (augmentation R M x).f 0 =
      ModuleCat.ofHom (augmentationLinearLifted R M x) := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

/-- The degree-zero component is the lifted quotient projection. -/
theorem augmentation_f_zero_apply (x : M →ₗ[R] R) (z : ⋀[R]^0 M) :
    ((augmentation R M x).f 0).hom z = augmentationLinearLifted R M x z := by
  exact LinearMap.congr_fun
    (congrArg (fun f : (complex R M x).X 0 ⟶
      ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x)) => f.hom)
      (augmentation_f_zero R M x)) z

/-- The degree-one differential followed by the quotient map, as a short
complex of modules. -/
def augmentationShortComplex (x : M →ₗ[R] R) :
    ShortComplex (ModuleCat.{max u v} R) :=
  ShortComplex.moduleCatMk
    (differential R M x 0)
    (augmentationLinearLifted R M x)
    (differential_zero_comp_augmentationLinearLifted R M x)

/-- Exactness of the Koszul augmentation at degree zero. -/
theorem augmentation_exact_zero (x : M →ₗ[R] R) :
    (augmentationShortComplex R M x).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro z hz
  have hz0lift := LinearMap.mem_ker.mp hz
  have hz0 : augmentationLinear R M x z = 0 := by
    change ULift.up (augmentationLinear R M x z) = ULift.up 0 at hz0lift
    exact ULift.up_injective hz0lift
  change Ideal.Quotient.mk (ideal R M x)
      ((exteriorPower.zeroEquiv R M) z) = 0 at hz0
  have hzrange : (exteriorPower.zeroEquiv R M) z ∈ LinearMap.range x :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz0
  rcases hzrange with ⟨m, hm⟩
  refine ⟨(exteriorPower.oneEquiv R M).symm m, ?_⟩
  apply (exteriorPower.zeroEquiv R M).injective
  have hdeg := LinearMap.congr_fun (differential_zero_equiv R M x)
    ((exteriorPower.oneEquiv R M).symm m)
  simp only [LinearMap.comp_apply] at hdeg
  calc
    (exteriorPower.zeroEquiv R M)
        (differential R M x 0 ((exteriorPower.oneEquiv R M).symm m)) =
        x ((exteriorPower.oneEquiv R M)
          ((exteriorPower.oneEquiv R M).symm m)) := hdeg
    _ = x m := by rw [LinearEquiv.apply_symm_apply]
    _ = (exteriorPower.zeroEquiv R M) z := hm

/-- The quotient augmentation is the cokernel of the degree-one differential. -/
noncomputable def augmentationIsCokernel (x : M →ₗ[R] R) :
    IsColimit (CokernelCofork.ofπ
      (augmentationShortComplex R M x).g
      (augmentationShortComplex R M x).zero) := by
  let S := augmentationShortComplex R M x
  change IsColimit (CokernelCofork.ofπ S.g S.zero)
  have hS : S.Exact := by
    simpa only [S] using augmentation_exact_zero R M x
  letI : Epi S.g := (ModuleCat.epi_iff_surjective S.g).mpr (by
    change Function.Surjective (augmentationLinearLifted R M x)
    exact augmentationLinearLifted_surjective R M x)
  exact ((ShortComplex.exact_and_epi_g_iff_g_is_cokernel S).mp
    ⟨hS, inferInstance⟩).some

end KoszulComplex

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Postcomposition with a single-zero map composes the quotient augmentation with its target map. -/
theorem augmentation_comp_single₀_f_zero (x : M →ₗ[R] R)
    {N : ModuleCat.{max u v} R}
    (f : ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x)) ⟶ N) :
    (augmentation R M x ≫ (ChainComplex.single₀ (ModuleCat.{max u v} R)).map f).f 0 =
      ModuleCat.ofHom (augmentationLinearLifted R M x) ≫ f := by
  let Q : ModuleCat.{max u v} R :=
    ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x))
  let F : complex R M x ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj Q :=
    augmentation R M x
  let g : (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj Q ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N :=
    (ChainComplex.single₀ (ModuleCat.{max u v} R)).map f
  have hcomp := HomologicalComplex.comp_f
    (C₁ := complex R M x)
    (C₂ := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj Q)
    (C₃ := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N) F g 0
  have hF : F.f 0 = ModuleCat.ofHom (augmentationLinearLifted R M x) :=
    augmentation_f_zero R M x
  have hg : g.f 0 = f := ChainComplex.single₀_map_f_zero f
  exact hcomp.trans
    ((congrArg (fun h : (complex R M x).X 0 ⟶ Q => h ≫ g.f 0) hF).trans
      (congrArg (fun h : Q ⟶ N => ModuleCat.ofHom (augmentationLinearLifted R M x) ≫ h) hg))

/-- The postcomposed augmentation applies the target morphism to the lifted quotient class. -/
theorem augmentation_comp_single₀_f_zero_apply (x : M →ₗ[R] R)
    {N : ModuleCat.{max u v} R}
    (f : ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x)) ⟶ N)
    (z : ⋀[R]^0 M) :
    ((augmentation R M x ≫ (ChainComplex.single₀ (ModuleCat.{max u v} R)).map f).f 0).hom z =
      f.hom (augmentationLinearLifted R M x z) := by
  have hhom := congrArg (fun g : (complex R M x).X 0 ⟶ N => g.hom)
    (augmentation_comp_single₀_f_zero R M x f)
  have hcomp := ModuleCat.hom_comp (ModuleCat.ofHom (augmentationLinearLifted R M x)) f
  have hraw := ModuleCat.hom_ofHom (augmentationLinearLifted R M x)
  have hmaps := hhom.trans
    (hcomp.trans (congrArg (fun g => f.hom.comp g) hraw))
  exact LinearMap.congr_fun hmaps z

end KoszulComplex
