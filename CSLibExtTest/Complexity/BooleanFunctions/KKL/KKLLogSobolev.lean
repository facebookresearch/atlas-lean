/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogSobolev
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BourgainPerCoord

/-!
# Tests for the Fourier-side Poincaré and hypercontractive bounds

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogSobolev` at the `AND` function on
`{0, 1}^Bool`:

* `kls_var_le_W` is `3/16 ≤ 1`;
* `kls_fluctWeight_le_pow` at `ρ = 1` holds with equality: both sides are `3/16`;
* the hypothesis of `kls_LogOptimisation` holds for every `φ` (`kls_fluctWeight_le_pow`), and
  `kls_logOptimisation_zero`, `kls_logSobolevStep` give `KKLHypercontractive (1/2) 0`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

lemma bnt_uexp_andInd : bnt_uexp andInd = 1 / 4 := by
  rw [khc_uexp_eq_coeff_empty, fourier_andInd_empty]

example : (3 / 16 : ℝ) ≤ 1 := by
  have h := kls_var_le_W andFun
  rw [sum_erase_empty_finset_bool, sum_finset_bool, fourier_andInd_empty, fourier_andInd_true,
    fourier_andInd_false, fourier_andInd_univ] at h
  norm_num at h ⊢

/-- `kls_fluctWeight_le_pow` at `AND`, `ρ = 1`: `3/16 ≤ (1/4)^1 - (1/4)^2`, an equality. -/
example : (3 / 16 : ℝ) ≤ (1 / 4) ^ (2 / (1 + (1 : ℝ) ^ 2)) - (1 / 4) ^ 2 := by
  have h := kls_fluctWeight_le_pow (ρ := 1) zero_le_one le_rfl andFun
  rw [sum_erase_empty_finset_bool, fourier_andInd_true, fourier_andInd_false,
    fourier_andInd_univ, bnt_uexp_andInd] at h
  norm_num at h ⊢

example : (1 / 4 : ℝ) ^ (2 / (1 + (1 : ℝ) ^ 2)) - (1 / 4) ^ 2 = 3 / 16 := by norm_num

/-- The hypothesis of `kls_LogOptimisation` holds for every Boolean function. -/
example (φ : ConfigSpace (Fin 3) → Bool) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin 3))),
        (ρ ^ S.card) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 :=
  kls_fluctWeight_le_pow h0 h1 φ

example : KKLHypercontractive (1 / 2) 0 := kls_logSobolevStep kls_logOptimisation_zero

end StatMechTest.BooleanFunctions
