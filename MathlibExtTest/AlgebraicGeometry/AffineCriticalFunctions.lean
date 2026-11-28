/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps
import Mathlib.Algebra.Polynomial.Div

/-!
# A nonreduced critical-function fixture

The class of X³ for the presentation I=(X²) is critical, vanishes on the
reduction, and remains nonzero modulo I²=(X⁴). This distinguishes the
actual critical subquotient from its reduction or from a zero quotient.
-/

noncomputable section

namespace AffineCriticalFunctionsTest

open Polynomial
open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions
open MathlibExt.AlgebraicGeometry.AffineCriticalFunctionMaps

abbrev presentationIdeal : Ideal ℚ[X] := Ideal.span {X ^ 2}

lemma cubicDifferential :
    KaehlerDifferential.D ℚ ℚ[X] (X ^ 3) ∈ idealDifferentials ℚ ℚ[X] presentationIdeal := by
  rw [KaehlerDifferential.polynomial_D_apply]
  have h : derivative (X ^ 3 : ℚ[X]) = (3 : ℚ[X]) * X ^ 2 := by
    norm_num [Polynomial.derivative_pow]
    exact Polynomial.C_ofNat 3
  rw [h]
  exact Submodule.smul_mem_smul
    (presentationIdeal.mul_mem_left 3 (Ideal.mem_span_singleton_self _))
    (Submodule.mem_top)

lemma cubicReduction : (X ^ 3 : ℚ[X]) ∈ presentationIdeal.radical := by
  change ∃ n : ℕ, (X ^ 3 : ℚ[X]) ^ n ∈ presentationIdeal
  refine ⟨2, Ideal.mem_span_singleton.mpr ⟨X ^ 4, ?_⟩⟩
  ring

example : criticalClass presentationIdeal (X ^ 3) cubicDifferential cubicReduction ≠ 0 := by
  intro h
  have hm := (criticalClass_eq_zero_iff presentationIdeal (X ^ 3)
    cubicDifferential cubicReduction).mp h
  have hd : (X ^ 4 : ℚ[X]) ∣ X ^ 3 := by
    simpa only [presentationIdeal, Ideal.span_singleton_pow, ← pow_mul,
      show 2 * 2 = 4 from rfl, Ideal.mem_span_singleton] using hm
  have hc := (X_pow_dvd_iff.mp hd) 3 (by decide)
  norm_num at hc

def scaling : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (2 * X)

lemma scaling_preserves : presentationIdeal.map scaling.toRingHom ≤ presentationIdeal := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  change scaling (X ^ 2) ∈ presentationIdeal
  simp only [map_pow, scaling, aeval_X]
  apply Ideal.mem_span_singleton.mpr
  exact ⟨4, by ring⟩

example :
    localZeroMap scaling scaling_preserves
      (criticalClass presentationIdeal (X ^ 3) cubicDifferential cubicReduction) =
    (8 : ℚ) • criticalClass presentationIdeal (X ^ 3) cubicDifferential cubicReduction := by
  have hc : scaling (X ^ 3 : ℚ[X]) = (8 : ℚ) • (X ^ 3 : ℚ[X]) := by
    simp only [scaling, map_pow, aeval_X, Algebra.smul_def]
    change (2 * X) ^ 3 = C (8 : ℚ) * X ^ 3
    rw [Polynomial.C_ofNat]
    ring
  change (zeroSquareDenominator ℚ ℚ[X] presentationIdeal).mkQ
    (numeratorMap scaling scaling_preserves
      (⟨X ^ 3, (mem_zeroCriticalFunctions).mpr ⟨cubicDifferential, cubicReduction⟩⟩ :
        zeroCriticalFunctions ℚ ℚ[X] presentationIdeal)) = _
  have hn : numeratorMap scaling scaling_preserves
      (⟨X ^ 3, (mem_zeroCriticalFunctions).mpr ⟨cubicDifferential, cubicReduction⟩⟩ :
        zeroCriticalFunctions ℚ ℚ[X] presentationIdeal) =
      (8 : ℚ) • (⟨X ^ 3, (mem_zeroCriticalFunctions).mpr
        ⟨cubicDifferential, cubicReduction⟩⟩ : zeroCriticalFunctions ℚ ℚ[X] presentationIdeal) :=
    Subtype.ext hc
  rw [hn, map_smul]
  rfl

end AffineCriticalFunctionsTest
