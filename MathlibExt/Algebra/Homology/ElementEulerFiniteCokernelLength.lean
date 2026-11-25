/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.ElementEuler

/-! # Principal quotient lengths across a finite-length cokernel

Multiplication has zero Euler characteristic on a finite-length module.
Short-exact additivity then compares principal quotient lengths across an
injection with finite-length cokernel, provided multiplication is injective
on both original modules. No branch normalization data is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
namespace Module
variable (R : Type u) [CommRing R]

/-- A multiplication endomorphism of a finite-length module has equal
actual kernel and cokernel lengths. -/
theorem length_lsmul_kernel_eq_cokernel_of_module_length
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (hM : Module.length R M ≠ ⊤) :
    Module.length R (LinearMap.lsmul R M r).ker =
      Module.length R (M ⧸ (LinearMap.lsmul R M r).range) := by
  let d := LinearMap.lsmul R M r
  let h := ElementEulerFiniteLength.of_module_length R M r hM
  have hRange : Module.length R d.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective d.range.subtype (Submodule.injective_subtype _))
  have hKerRange := Module.length_eq_add_of_exact d.ker.subtype d.rangeRestrict
    (Submodule.injective_subtype _) d.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have hRangeCoker := Module.length_eq_add_of_exact d.range.subtype d.range.mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  have h₁ := congrArg ENat.toNat hKerRange
  have h₂ := congrArg ENat.toNat hRangeCoker
  rw [ENat.toNat_add h.kernel_ne_top hRange] at h₁
  rw [ENat.toNat_add hRange h.cokernel_ne_top] at h₂
  dsimp [d] at h₁ h₂
  have hNat : (Module.length R (LinearMap.lsmul R M r).ker).toNat =
      (Module.length R (M ⧸ (LinearMap.lsmul R M r).range)).toNat := by omega
  calc
    Module.length R (LinearMap.lsmul R M r).ker =
        ((Module.length R (LinearMap.lsmul R M r).ker).toNat : ENat) :=
      (ENat.natCast_toNat h.kernel_ne_top).symm
    _ = ((Module.length R (M ⧸ (LinearMap.lsmul R M r).range)).toNat : ENat) := by
      rw [hNat]
    _ = Module.length R (M ⧸ (LinearMap.lsmul R M r).range) :=
      ENat.natCast_toNat h.cokernel_ne_top

/-- Every endomorphism given by multiplication on a finite-length module has
zero cokernel-minus-kernel Euler characteristic. -/
theorem elementEulerCharacteristic_eq_zero_of_module_length
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (hM : Module.length R M ≠ ⊤)
    (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h = 0 := by
  unfold elementEulerCharacteristic
  rw [length_lsmul_kernel_eq_cokernel_of_module_length R M r hM, sub_self]

/-- In an actual short exact sequence with finite-length right module,
regular multiplication on the first two modules gives equal actual
principal quotient lengths. Finiteness of the second quotient is derived. -/
theorem length_lsmul_cokernel_eq_of_shortExact
    {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (r : R) (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hr₁ : Function.Injective (LinearMap.lsmul R M₁ r))
    (hr₂ : Function.Injective (LinearMap.lsmul R M₂ r))
    (hquot : Module.length R (M₁ ⧸ (LinearMap.lsmul R M₁ r).range) ≠ ⊤)
    (hM₃ : Module.length R M₃ ≠ ⊤) :
    Module.length R (M₁ ⧸ (LinearMap.lsmul R M₁ r).range) =
      Module.length R (M₂ ⧸ (LinearMap.lsmul R M₂ r).range) := by
  let h₁ := ElementEulerFiniteLength.of_injective R M₁ r hr₁ hquot
  let h₃ := ElementEulerFiniteLength.of_module_length R M₃ r hM₃
  let h₂ := ElementEulerFiniteLength.of_shortExact R r i p hi hp hip h₁ h₃
  have he := elementEulerCharacteristic_additive R r i p hi hp hip h₁ h₂ h₃
  rw [elementEulerCharacteristic_eq_quotient_of_injective R M₂ r hr₂ h₂,
    elementEulerCharacteristic_eq_quotient_of_injective R M₁ r hr₁ h₁,
    elementEulerCharacteristic_eq_zero_of_module_length R M₃ r hM₃ h₃] at he
  have hNat : (Module.length R (M₁ ⧸ (LinearMap.lsmul R M₁ r).range)).toNat =
      (Module.length R (M₂ ⧸ (LinearMap.lsmul R M₂ r).range)).toNat :=
    Int.natCast_inj.mp (by simpa using he.symm)
  calc
    Module.length R (M₁ ⧸ (LinearMap.lsmul R M₁ r).range) =
        ((Module.length R (M₁ ⧸ (LinearMap.lsmul R M₁ r).range)).toNat : ENat) :=
      (ENat.natCast_toNat h₁.cokernel_ne_top).symm
    _ = ((Module.length R (M₂ ⧸ (LinearMap.lsmul R M₂ r).range)).toNat : ENat) := by
      rw [hNat]
    _ = Module.length R (M₂ ⧸ (LinearMap.lsmul R M₂ r).range) :=
      ENat.natCast_toNat h₂.cokernel_ne_top

end Module
