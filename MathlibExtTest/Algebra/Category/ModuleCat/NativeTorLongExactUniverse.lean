/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Nonzero Tor from the integral mod-two sequence

The integral multiplication-by-two sequence gives a nonzero Tor boundary
identifying degree-one Tor with the mod-two coefficient.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace NativeTorBoundaryTests

/-- The free integer module. -/
abbrev Z : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The integer module `ℤ/2`. -/
abbrev Q : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)

/-- Multiplication by two in the integral sequence. -/
abbrev mulTwo : Z ⟶ Z := ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

/-- Reduction of integers modulo two. -/
abbrev quotient : Z ⟶ Q :=
  ModuleCat.ofHom ((Int.castAddHom (ZMod 2)).toIntLinearMap)

theorem mulTwo_quotient_zero : mulTwo ≫ quotient = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((2 * z : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul]
  have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp only [Int.cast_ofNat, h2, zero_mul]

/-- The integral presentation of `ℤ/2`. -/
abbrev integralShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk mulTwo quotient mulTwo_quotient_zero

theorem integralShortComplex_shortExact : integralShortComplex.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro z
    change (z : ZMod 2) = 0 ↔ ∃ w : ℤ, 2 * w = z
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, hw.symm⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, hw.symm⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y h
    change (2 : ℤ) * x = 2 * y at h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective ((↑) : ℤ → ZMod 2)
    exact ZMod.intCast_surjective

theorem length_Q : Module.length ℤ Q = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  calc
    Module.length ℤ Q = Module.length (ZMod 2) (ZMod 2) :=
      Module.length_eq_of_surjective (R := ZMod 2) (M := ZMod 2) (S := ℤ)
        ZMod.intCast_surjective
    _ = 1 := Module.length_eq_one (ZMod 2) (ZMod 2)

/-- Degree-zero Tor with the free integer module identifies with `ℤ/2`. -/
def zeroFreeIso : (((Tor (ModuleCat ℤ) 0).obj Q).obj Z) ≅ Q :=
  ModuleCat.UniverseTensor.nativeTorZeroIso ℤ Q Z ≪≫ (TensorProduct.rid ℤ Q).toModuleIso

theorem zero_map_mulTwo : ((Tor (ModuleCat ℤ) 0).obj Q).map mulTwo = 0 := by
  let F := (tensoringLeft (ModuleCat ℤ)).obj Q
  have hF : F.map mulTwo = 0 := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    change x ⊗ₜ[ℤ] ((2 : ℤ) * z) = 0
    rw [two_mul, TensorProduct.tmul_add, ← TensorProduct.add_tmul]
    have hx : x + x = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
    rw [hx, TensorProduct.zero_tmul]
  let e := ModuleCat.UniverseTensor.nativeTorZeroIso ℤ Q Z
  have h : ((Tor (ModuleCat ℤ) 0).obj Q).map mulTwo ≫ e.hom = e.hom ≫ F.map mulTwo :=
    ModuleCat.UniverseTensor.nativeTorZeroIso_hom_naturality_resolved ℤ Q mulTwo
  rw [hF, comp_zero] at h
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using h

/-- The integral-sequence boundary identifies degree-one Tor with degree-zero Tor. -/
def boundaryIso : (((Tor (ModuleCat ℤ) 1).obj Q).obj Q) ≅
    (((Tor (ModuleCat ℤ) 0).obj Q).obj Z) := by
  have hZ : IsZero (((Tor (ModuleCat ℤ) 1).obj Q).obj integralShortComplex.X₂) := by
    change IsZero (((Tor (ModuleCat ℤ) (0 + 1)).obj Q).obj Z)
    exact isZero_Tor_succ_of_projective (ModuleCat ℤ) Q Z 0
  let : IsIso (ModuleCat.UniverseTensor.nativeTorConnecting ℤ Q integralShortComplex
      integralShortComplex_shortExact 0) :=
    ModuleCat.UniverseTensor.nativeTorConnecting_isIso ℤ Q integralShortComplex
      integralShortComplex_shortExact 0 hZ zero_map_mulTwo
  exact asIso (ModuleCat.UniverseTensor.nativeTorConnecting ℤ Q integralShortComplex
    integralShortComplex_shortExact 0)

theorem nativeTor_one_length :
    Module.length ℤ (((Tor (ModuleCat ℤ) 1).obj Q).obj Q) = 1 :=
  boundaryIso.toLinearEquiv.length_eq.trans (zeroFreeIso.toLinearEquiv.length_eq.trans length_Q)

theorem nativeTor_one_nonzero : ¬ IsZero (((Tor (ModuleCat ℤ) 1).obj Q).obj Q) := by
  intro h
  have hz : Module.length ℤ (((Tor (ModuleCat ℤ) 1).obj Q).obj Q) = 0 :=
    Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp h)
  rw [nativeTor_one_length] at hz
  exact one_ne_zero hz

example (q : ℕ) :
    (ModuleCat.UniverseTensor.nativeTorLongExactWindow ℤ Q integralShortComplex
      integralShortComplex_shortExact q).Exact :=
  ModuleCat.UniverseTensor.nativeTorLongExactWindow_exact ℤ Q integralShortComplex
    integralShortComplex_shortExact q

example (q : ℕ) :
    (ModuleCat.UniverseTensor.nativeTorLongExactWindowFirst ℤ Q integralShortComplex
      integralShortComplex_shortExact q).Exact :=
  ModuleCat.UniverseTensor.nativeTorLongExactWindowFirst_exact ℤ Q integralShortComplex
    integralShortComplex_shortExact q

end NativeTorBoundaryTests

universe u v

example {R : Type u} [CommRing R] (M N : ModuleCat.{max u v} R) :
    (((Tor (ModuleCat.{max u v} R) 0).obj M).obj N) ≅ ModuleCat.of R (M ⊗[R] N) :=
  ModuleCat.UniverseTensor.nativeTorZeroIso R M N
