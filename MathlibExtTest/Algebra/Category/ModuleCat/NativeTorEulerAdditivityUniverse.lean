/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExtTest.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import MathlibExt.Algebra.Category.ModuleCat.NativeTorProjectiveDimensionUniverse

/-! Native Euler sums for a genuine nonsplit integral mod-two coefficient sequence. -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

namespace NativeTorBoundaryTests

open ModuleCat.UniverseTensor

theorem zeroQuotient_isIso : IsIso (((Tor (ModuleCat ℤ) 0).obj Q).map quotient) := by
  let F := (tensoringLeft (ModuleCat ℤ)).obj Q
  let T := F.leftDerived 0
  obtain ⟨w, h⟩ := LeftDerivedDelta.LDexact_B F 0 integralShortComplex
    integralShortComplex_shortExact
  let S : ShortComplex (ModuleCat ℤ) := ShortComplex.mk (T.map mulTwo) (T.map quotient) w
  have : Mono (T.map quotient) := (S.exact_iff_mono zero_map_mulTwo).mp h
  have : Epi (T.map quotient) := nativeTor_epi_zero ℤ Q integralShortComplex
    integralShortComplex_shortExact
  change IsIso (T.map quotient)
  exact isIso_of_mono_of_epi _

/-- The actual native degree-zero quotient map is an isomorphism in the mod-two client. -/
def zeroQuotientIso : (((Tor (ModuleCat ℤ) 0).obj Q).obj Z) ≅
    (((Tor (ModuleCat ℤ) 0).obj Q).obj Q) := by
  letI : IsIso (((Tor (ModuleCat ℤ) 0).obj Q).map quotient) := zeroQuotient_isIso
  exact asIso (((Tor (ModuleCat ℤ) 0).obj Q).map quotient)

theorem nativeTor_zero_free_length :
    Module.length ℤ (((Tor (ModuleCat ℤ) 0).obj Q).obj Z) = 1 :=
  zeroFreeIso.toLinearEquiv.length_eq.trans length_Q

theorem nativeTor_zero_quotient_length :
    Module.length ℤ (((Tor (ModuleCat ℤ) 0).obj Q).obj Q) = 1 :=
  zeroQuotientIso.symm.toLinearEquiv.length_eq.trans nativeTor_zero_free_length

theorem nativeTor_free_vanishes (q : ℕ) (hq : 1 ≤ q) :
    IsZero (((Tor (ModuleCat ℤ) q).obj Q).obj Z) :=
  nativeTor_isZero_of_projectiveDimensionLE_resolved ℤ Q Z 0 q (by omega)

theorem nativeTor_one_free_length :
    Module.length ℤ (((Tor (ModuleCat ℤ) 1).obj Q).obj Z) = 0 :=
  Module.length_eq_zero_iff.mpr
    (ModuleCat.isZero_iff_subsingleton.mp (nativeTor_free_vanishes 1 le_rfl))

theorem quotient_projectiveDimension : HasProjectiveDimensionLE Q 1 := by
  have hP : Projective integralShortComplex.X₂ := by
    change Projective Z
    infer_instance
  have hK : HasProjectiveDimensionLT integralShortComplex.X₁ 1 := by
    change HasProjectiveDimensionLT Z 1
    infer_instance
  exact (integralShortComplex_shortExact.hasProjectiveDimensionLT_X₃_iff 0 hP).mpr hK

theorem nativeTor_quotient_vanishes (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((Tor (ModuleCat ℤ) q).obj Q).obj Q) := by
  have : HasProjectiveDimensionLE Q 1 := quotient_projectiveDimension
  exact nativeTor_isZero_of_projectiveDimensionLE_resolved ℤ Q Q 1 q (by omega)

theorem nativeTor_free_length_ne_top (q : ℕ) :
    Module.length ℤ (((Tor (ModuleCat ℤ) q).obj Q).obj Z) ≠ ⊤ := by
  by_cases hq : q = 0
  · subst q
    rw [nativeTor_zero_free_length]
    simp
  · have hz := nativeTor_free_vanishes q (by omega)
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    simp

theorem nativeTor_quotient_length_ne_top (q : ℕ) (hq : q < 2) :
    Module.length ℤ (((Tor (ModuleCat ℤ) q).obj Q).obj Q) ≠ ⊤ := by
  have h : q = 0 ∨ q = 1 := by omega
  rcases h with rfl | rfl
  · rw [nativeTor_zero_quotient_length]
    simp
  · rw [nativeTor_one_length]
    simp

theorem nativeEuler_free : rawNativeTorEulerSum ℤ Q Z 2 = 1 := by
  norm_num [rawNativeTorEulerSum, Finset.sum_range_succ, nativeTor_zero_free_length,
    nativeTor_one_free_length]

theorem nativeEuler_quotient : rawNativeTorEulerSum ℤ Q Q 2 = 0 := by
  norm_num [rawNativeTorEulerSum, Finset.sum_range_succ, nativeTor_zero_quotient_length,
    nativeTor_one_length]

theorem nativeEuler_quotient_before_boundary : rawNativeTorEulerSum ℤ Q Q 1 = 1 := by
  norm_num [rawNativeTorEulerSum, Finset.sum_range_succ, nativeTor_zero_quotient_length]

example : rawNativeTorEulerSum ℤ Q Q 1 ≠ rawNativeTorEulerSum ℤ Q Q 2 := by
  rw [nativeEuler_quotient_before_boundary, nativeEuler_quotient]
  norm_num

example : rawNativeTorEulerSum ℤ Q Z 2 =
    rawNativeTorEulerSum ℤ Q Z 2 + rawNativeTorEulerSum ℤ Q Q 2 :=
  rawNativeTorEulerSum_shortExactSecond ℤ Q integralShortComplex
    integralShortComplex_shortExact 2 (fun q _ => nativeTor_free_length_ne_top q)
    (fun q _ => nativeTor_free_length_ne_top q) nativeTor_quotient_length_ne_top
    (nativeTor_quotient_vanishes 2 le_rfl)

example : rawNativeTorEulerSum ℤ Q Z 3 =
    rawNativeTorEulerSum ℤ Q Z 1 + rawNativeTorEulerSum ℤ Q Q 2 :=
  rawNativeTorEulerSum_shortExactSecond_of_finite ℤ Q integralShortComplex
    integralShortComplex_shortExact 1 3 2 (fun q _ => nativeTor_free_length_ne_top q)
    (fun q _ => nativeTor_free_length_ne_top q) nativeTor_quotient_length_ne_top
    nativeTor_free_vanishes (fun q hq => nativeTor_free_vanishes q (by omega))
    nativeTor_quotient_vanishes

example : rawNativeTorEulerSum ℤ Z Q 2 =
    rawNativeTorEulerSum ℤ Z Q 2 + rawNativeTorEulerSum ℤ Q Q 2 := by
  apply rawNativeTorEulerSum_shortExactFirst ℤ Q integralShortComplex
    integralShortComplex_shortExact 2
  · intro q _
    rw [nativeTor_length_symm ℤ Z Q q]
    exact nativeTor_free_length_ne_top q
  · intro q _
    rw [nativeTor_length_symm ℤ Z Q q]
    exact nativeTor_free_length_ne_top q
  · exact nativeTor_quotient_length_ne_top
  · exact nativeTor_quotient_vanishes 2 le_rfl

end NativeTorBoundaryTests
