/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLfromHC
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# Tests for Fourier analysis on the uniform cube

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLfromHC` on `{0, 1}^Bool`:

* `khc_sign`, `khc_walshChar` and `khc_fourierCoeff` at small inputs; the four Fourier
  coefficients of `AND` are `1/4, -1/4, -1/4, 1/4`;
* `khc_var_eq_fourierWeight`, `khc_totalInfl_eq_fourierWeight` and `khc_parseval` agree with
  the direct computations `Var(AND) = 3/16`, `∑ₑ Infₑ(AND) = 1`, `𝔼[AND²] = 1/4`;
* the hypothesis of `khc_LogSobolevStep` holds for every `φ` (`khc_lowDegreeWeight_le`), and
  `khc_logSobolevStep_zero`, `khc_KKL` give `KKLHypercontractive (1/2) 0`;
* the bridges `khc_walshChar_eq_cubeChi` and `khc_var_half_eq_boolVariance` on `Fin 1`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- The four subsets of `Bool`. -/
lemma univ_finset_bool :
    (Finset.univ : Finset (Finset Bool)) = {∅, {true}, {false}, {true, false}} := by decide

/-- A sum over the subsets of `Bool`, written out. -/
lemma sum_finset_bool (c : Finset Bool → ℝ) :
    ∑ S : Finset Bool, c S = c ∅ + c {true} + c {false} + c {true, false} := by
  rw [univ_finset_bool, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

example (x : Bool → Bool) : khc_walshChar ∅ x = 1 := by simp
example : khc_walshChar {true} (fun _ => true) = -1 := by simp [khc_walshChar]
example : khc_walshChar {true, false} (fun x => x) = -1 := by simp [khc_walshChar]

lemma bnt_uexp_bool (f : ConfigSpace Bool → ℝ) :
    bnt_uexp f = (∑ a : Bool, ∑ b : Bool, f (fun x => cond x b a)) / 4 := by
  rw [bnt_uexp, sum_configSpace_bool]; norm_num

lemma fourier_andInd_empty : khc_fourierCoeff andInd ∅ = 1 / 4 := by
  rw [khc_fourierCoeff, bnt_uexp_bool]
  simp only [Fintype.sum_bool]
  norm_num [andInd, andFun]

lemma fourier_andInd_true : khc_fourierCoeff andInd {true} = -1 / 4 := by
  simp [khc_fourierCoeff, bnt_uexp_bool, andFun, khc_walshChar]

lemma fourier_andInd_false : khc_fourierCoeff andInd {false} = -1 / 4 := by
  simp [khc_fourierCoeff, bnt_uexp_bool, andFun, khc_walshChar]

lemma fourier_andInd_univ : khc_fourierCoeff andInd {true, false} = 1 / 4 := by
  simp [khc_fourierCoeff, bnt_uexp_bool, andFun, khc_walshChar]

/-- `khc_var_eq_fourierWeight` at `AND`: `3/16 = 3 · (1/4)²`. -/
example : var νHalf andInd = (-1 / 4) ^ 2 + (-1 / 4) ^ 2 + (1 / 4) ^ 2 := by
  rw [var_andFun]; norm_num

example :
    ∑ S ∈ (Finset.univ.erase (∅ : Finset Bool)), (khc_fourierCoeff andInd S) ^ 2 = 3 / 16 := by
  rw [← khc_var_eq_fourierWeight, var_andFun]

/-- The total-influence identity at `AND`, computed from the explicit coefficients. -/
example : ∑ S : Finset Bool, 4 * (S.card : ℝ) * (khc_fourierCoeff andInd S) ^ 2 = 1 := by
  rw [sum_finset_bool, fourier_andInd_empty, fourier_andInd_true, fourier_andInd_false,
    fourier_andInd_univ]
  norm_num

example : ∑ S : Finset Bool, 4 * (S.card : ℝ) * (khc_fourierCoeff andInd S) ^ 2 = 1 := by
  rw [← khc_totalInfl_eq_fourierWeight, totalInfl_andInd]

/-- Parseval at `AND`: `𝔼[AND²] = ∑_S f̂(S)² = 4 · 1/16`. -/
example : bnt_uexp (fun x => andInd x * andInd x) = 1 / 4 := by
  rw [khc_parseval, sum_finset_bool, fourier_andInd_empty, fourier_andInd_true,
    fourier_andInd_false, fourier_andInd_univ]
  norm_num

/-! ## The predicate `khc_LogSobolevStep` -/

/-- The hypothesis of `khc_LogSobolevStep` holds for every Boolean function. -/
example (φ : ConfigSpace (Fin 3) → Bool) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (∑ S : Finset (Fin 3), (ρ ^ S.card) ^ 2
        * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (bnt_qnorm (1 + ρ ^ 2) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 :=
  khc_lowDegreeWeight_le h0 h1 _

example : KKLHypercontractive (1 / 2) 0 := khc_KKL khc_logSobolevStep_zero

/-- Bonami–Beckner on `{0, 1}^Bool` at `ρ = 1/2`. -/
example (g : ConfigSpace Bool → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp (1 / 2) g) ≤ bnt_qnorm (1 + (1 / 2) ^ 2) g :=
  khc_hypercontractivity_general (by norm_num) (by norm_num) g

/-! ## Bridges to `BooleanCube` -/

example (x : Fin 1 → Bool) :
    khc_walshChar {0} x = -BooleanCube.cubeChi 1 {0} x := by
  rw [khc_walshChar_eq_cubeChi]; simp

example (f : (Fin 1 → Bool) → ℝ) :
    var (bernoulliWeight (1 / 2)) f = BooleanCube.boolVariance f :=
  khc_var_half_eq_boolVariance f

end StatMechTest.BooleanFunctions
