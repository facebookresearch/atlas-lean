/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLfromHC

/-!
# Hypercontractivity bounds for indicator functions

For the indicator `f = 1_A` of an event of uniform measure `m` on `{0, 1}^ι`, every
`L^q` norm is a power of `m`, so the Bonami–Beckner inequality reads
`∑_{S ≠ ∅} ρ^{2|S|} f̂(S)² ≤ m^{2/(1+ρ²)} - m²`. This file proves that bound and the
elementary Fourier comparisons used in the KKL argument (variance at most total influence,
per-coordinate Fourier weight at most the maximal influence), and reduces the Fourier form of
the KKL inequality to the predicate `kls_LogOptimisation`.

## Main definitions

* `StatMech.Probability.kls_LogOptimisation`: the KKL inequality at `p = 1/2` in Fourier form,
  with the indicator hypercontractive bound as a hypothesis.

## Main results

* `StatMech.Probability.kls_fluctWeight_le_pow`: the hypercontractive bound for indicators.
* `StatMech.Probability.kls_var_le_W`: `Var(1_A) ≤ ∑_S 4 |S| f̂(S)²` (Poincaré inequality in
  Fourier form).
* `StatMech.Probability.kls_logSobolevStep`: `kls_LogOptimisation c` implies
  `KKLHypercontractive (1/2) c`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem kls_indicator_rpow {q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) (ω : ConfigSpace ι) :
    |(fun ω => if φ ω then (1 : ℝ) else 0) ω| ^ q
      = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
  simp only
  by_cases h : φ ω
  · simp [h, Real.one_rpow]
  · simp [h, Real.zero_rpow (ne_of_gt hq)]

theorem kls_qnormPow_indicator {q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) :
    bnt_qnormPow q (fun ω => if φ ω then (1 : ℝ) else 0)
      = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) := by
  unfold bnt_qnormPow
  congr 1
  funext ω
  exact kls_indicator_rpow hq φ ω

theorem kls_mean_eq_coeff_empty (φ : ConfigSpace ι → Bool) :
    bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
      = khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) ∅ :=
  khc_uexp_eq_coeff_empty _

theorem kls_qnorm_indicator_sq {ρ : ℝ} (φ : ConfigSpace ι → Bool) :
    (bnt_qnorm (1 + ρ ^ 2) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2
      = (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) := by
  have hq : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  unfold bnt_qnorm
  rw [kls_qnormPow_indicator hq φ]
  set m := bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) with hm
  have hmnn : 0 ≤ m := by
    rw [hm]; unfold bnt_uexp
    apply div_nonneg
    · apply Finset.sum_nonneg; intro ω _; by_cases h : φ ω <;> simp [h]
    · positivity
  rw [← Real.rpow_natCast (m ^ (1 / (1 + ρ ^ 2))) 2, ← Real.rpow_mul hmnn]
  congr 1
  push_cast
  field_simp

/-- Bonami–Beckner for an indicator of uniform measure `m`: `∑_{S ≠ ∅} ρ^{2|S|} f̂(S)² ≤
  m^{2/(1+ρ²)} - m²` for `0 ≤ ρ ≤ 1`. -/
theorem kls_fluctWeight_le_pow {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (φ : ConfigSpace ι → Bool) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (ρ ^ S.card) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hbase := khc_lowDegreeWeight_fluct_le h0 h1 f
  rw [kls_qnorm_indicator_sq φ] at hbase
  rw [← kls_mean_eq_coeff_empty φ] at hbase
  exact hbase

theorem kls_var_nonneg_fourier (φ : ConfigSpace ι → Bool) :
    0 ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)),
        (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 :=
  Finset.sum_nonneg (fun _S _ => sq_nonneg _)

theorem kls_W_nonneg (φ : ConfigSpace ι → Bool) :
    0 ≤ ∑ S : Finset ι, 4 * (S.card : ℝ)
        * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 :=
  Finset.sum_nonneg (fun S _ => by positivity)

/-- Poincaré inequality in Fourier form: `∑_{S ≠ ∅} f̂(S)² ≤ ∑_S 4 |S| f̂(S)²`. -/
theorem kls_var_le_W (φ : ConfigSpace ι → Bool) :
    (∑ S ∈ (univ.erase (∅ : Finset ι)),
        (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι =>
      (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  calc (∑ S ∈ (univ.erase (∅ : Finset ι)), c S)
      ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), 4 * (S.card : ℝ) * c S := by
        apply Finset.sum_le_sum
        intro S hS
        have hSne : S ≠ ∅ := Finset.ne_of_mem_erase hS
        have hcard : 1 ≤ (S.card : ℝ) := by
          have : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
          exact_mod_cast this
        have hcnn : 0 ≤ c S := by rw [hc]; exact sq_nonneg _
        nlinarith [hcnn, hcard]
    _ ≤ ∑ S : Finset ι, 4 * (S.card : ℝ) * c S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro S _ _; positivity

open StatMech.OSSS in
theorem kls_fourierInflWeight_le_maxInfl [Nonempty ι] (φ : ConfigSpace ι → Bool) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [← khc_infl_eq_fourierWeight φ e]
  exact kkl_infl_le_maxInfl _ _ e

/-- The KKL inequality at `p = 1/2` in Fourier form, with the indicator hypercontractive bound `∑_{S
  ≠ ∅} ρ^{2|S|} f̂(S)² ≤ m^{2/(1+ρ²)} - m²` (for all `ρ ∈ [0, 1]`) as a hypothesis, where `f =
  1_φ` and `m = 𝔼 f`. The hypothesis always holds (`kls_fluctWeight_le_pow`). -/
def kls_LogOptimisation (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        (∑ S ∈ (univ.erase (∅ : Finset E)), (ρ ^ S.card) ^ 2
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
            - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2

/-- `kls_LogOptimisation 0` holds trivially. -/
theorem kls_logOptimisation_zero : kls_LogOptimisation 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ

/-- `kls_LogOptimisation c` implies `khc_LogSobolevStep c`. -/
theorem kls_logOptimisation_implies_step {c : ℝ} (H : kls_LogOptimisation c) :
    khc_LogSobolevStep c := by
  intro E _ _ _ φ _hstar
  exact H φ (fun ρ h0 h1 => kls_fluctWeight_le_pow h0 h1 φ)

/-- `kls_LogOptimisation c` implies the KKL inequality `KKLHypercontractive (1/2) c`. -/
theorem kls_logSobolevStep {c : ℝ} (H : kls_LogOptimisation c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  khc_KKL (kls_logOptimisation_implies_step H)

end StatMech.Probability
