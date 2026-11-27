/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# The Good–Turing identity for the missing mass

Draw an independent sample `ω : Fin N → α` of size `N` from a distribution `p` on a finite set
`α` of species. This file defines the probability `sampleProb p ω` of the ordered sample, the
number `count ω a` of occurrences of the species `a`, the number `freqOfFreq ω r` of species seen
exactly `r` times, their total population frequency `massSeen p ω r`, and the expectation
`expect N p f` over samples of size `N`. It proves Good's exact identity for the missing mass,
`E[M₀(N)] = E[n₁(N + 1)] / (N + 1)` (`expect_missingMass`).

## References

* I. J. Good, "The population frequencies of species and the estimation of population
  parameters", Biometrika 40 (1953) 237–264, doi:10.1093/biomet/40.3-4.237, eqs. 9 and 15.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.GoodTuringWanted

open Finset

/-- The probability `∏ⱼ p(ωⱼ)` of the ordered sample `ω` of size `N` drawn independently from the
species distribution `p`. -/
noncomputable def sampleProb {α : Type*} {N : ℕ} (p : α → ℝ) (ω : Fin N → α) : ℝ :=
  ∏ j, p (ω j)

/-- The number of times species `a` occurs in the sample `ω`. -/
def count {α : Type*} [DecidableEq α] {N : ℕ} (ω : Fin N → α) (a : α) : ℕ := #{j | ω j = a}

/-- `n_r`: the number of species seen exactly `r` times in the sample `ω`. -/
def freqOfFreq {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (ω : Fin N → α) (r : ℕ) : ℕ :=
  #{a | count ω a = r}

/-- The total population frequency `∑_{a : count a = r} p(a)` of the species seen exactly `r`
times in the sample `ω`; for `r = 0` this is the missing mass `M₀`. -/
noncomputable def massSeen {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} (p : α → ℝ)
    (ω : Fin N → α) (r : ℕ) : ℝ :=
  ∑ a with count ω a = r, p a

/-- The expectation `∑_ω p(ω) f(ω)` of a function of a sample of size `N` drawn independently from
`p`. -/
noncomputable def expect {α : Type*} [Fintype α] (N : ℕ) (p : α → ℝ) (f : (Fin N → α) → ℝ) : ℝ :=
  ∑ ω : Fin N → α, sampleProb p ω * f ω

private theorem count_cons {α : Type*} [DecidableEq α] {N : ℕ}
    (b : α) (ω : Fin N → α) (a : α) :
    count (Fin.cons b ω) a = (if b = a then 1 else 0) + count ω a := by
  have hc {n : ℕ} (v : Fin n → α) :
      count v a = ∑ j, if v j = a then (1 : ℕ) else 0 := by
    simp [count]
  rw [hc, hc, Fin.sum_univ_succ]
  simp

private theorem sampleProb_cons {α : Type*} {N : ℕ} (p : α → ℝ)
    (b : α) (ω : Fin N → α) :
    sampleProb p (Fin.cons b ω) = p b * sampleProb p ω := by
  simp [sampleProb, Fin.prod_univ_succ]

private theorem sum_samples_succ {α : Type*} [Fintype α] (N : ℕ)
    (f : (Fin (N + 1) → α) → ℝ) :
    ∑ ω, f ω = ∑ b, ∑ ω : Fin N → α, f (Fin.cons b ω) := by
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => α)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

private noncomputable def countWeight {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) (a : α) (r : ℕ) : ℝ :=
  ∑ ω : Fin N → α, if count ω a = r then sampleProb p ω else 0

private theorem countWeight_zero_succ {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) (a : α) :
    countWeight (N + 1) p a 0 = (∑ b with b ≠ a, p b) * countWeight N p a 0 := by
  unfold countWeight
  rw [sum_samples_succ]
  simp_rw [count_cons, sampleProb_cons]
  have h (b : α) (ω : Fin N → α) :
      (if (if b = a then 1 else 0) + count ω a = 0 then p b * sampleProb p ω else 0) =
      (if b ≠ a then p b else 0) * (if count ω a = 0 then sampleProb p ω else 0) := by
    by_cases hb : b = a <;> by_cases hω : count ω a = 0 <;> simp [hb, hω]
  simp_rw [h]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  simp only [sum_filter]

private theorem countWeight_succ {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) (a : α) (r : ℕ) :
    countWeight (N + 1) p a (r + 1) =
      p a * countWeight N p a r + (∑ b with b ≠ a, p b) * countWeight N p a (r + 1) := by
  unfold countWeight
  rw [sum_samples_succ]
  simp_rw [count_cons, sampleProb_cons]
  have h (b : α) (ω : Fin N → α) :
      (if (if b = a then 1 else 0) + count ω a = r + 1 then p b * sampleProb p ω else 0) =
      (if b = a then p b else 0) * (if count ω a = r then sampleProb p ω else 0) +
      (if b ≠ a then p b else 0) * (if count ω a = r + 1 then sampleProb p ω else 0) := by
    by_cases hb : b = a
    · have hc : 1 + count ω a = r + 1 ↔ count ω a = r := by omega
      simp [hb, hc]
    · simp [hb]
  simp_rw [h, sum_add_distrib, ← mul_sum]
  rw [← sum_mul, ← sum_mul]
  simp [sum_filter]

private theorem countWeight_zero {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) (a : α) :
    countWeight N p a 0 = (∑ b with b ≠ a, p b) ^ N := by
  induction N with
  | zero => simp [countWeight, count, sampleProb]
  | succ N ih => rw [countWeight_zero_succ, ih, pow_succ']

private theorem countWeight_one {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) (a : α) :
    countWeight (N + 1) p a 1 = (N + 1) * p a * (∑ b with b ≠ a, p b) ^ N := by
  induction N with
  | zero =>
    rw [countWeight_succ 0 p a 0]
    simp [countWeight, count, sampleProb]
  | succ N ih =>
    rw [countWeight_succ (N + 1) p a 0, countWeight_zero, ih]
    push_cast
    ring

private theorem expect_massSeen_zero {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) :
    expect N p (fun ω => massSeen p ω 0) =
      ∑ a, p a * (∑ b with b ≠ a, p b) ^ N := by
  have hm (ω : Fin N → α) :
      massSeen p ω 0 = ∑ a, if count ω a = 0 then p a else 0 := by
    simp [massSeen, sum_filter]
  unfold expect
  simp_rw [hm, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← countWeight_zero N p a]
  unfold countWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro ω _
  by_cases h : count ω a = 0 <;> simp [h, mul_comm]

private theorem expect_freqOfFreq_one {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (p : α → ℝ) :
    expect (N + 1) p (fun ω => (freqOfFreq ω 1 : ℝ)) =
      (N + 1) * ∑ a, p a * (∑ b with b ≠ a, p b) ^ N := by
  have hf (ω : Fin (N + 1) → α) :
      (freqOfFreq ω 1 : ℝ) = ∑ a, if count ω a = 1 then (1 : ℝ) else 0 := by
    simp [freqOfFreq]
  unfold expect
  simp_rw [hf, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, ← countWeight_one N p a]
  unfold countWeight
  apply sum_congr rfl
  intro ω _
  by_cases h : count ω a = 1 <;> simp [h]

/-- **The Good–Turing identity for the missing mass** (Good 1953, eq. 15 with `r = 0`, in
total-mass form; its approximation is eq. 9): let `p` be a probability distribution on a finite
set of species (every `p(a) ≥ 0`, `∑ p(a) = 1`) and `N` a sample size. Then the expected total
probability of the species not seen in a sample of size `N` equals the expected number of species
seen exactly once in a sample of size `N + 1`, divided by `N + 1`:
`E[M₀(N)] = E[n₁(N + 1)] / (N + 1)`.

Source: Good (1953), eqs. 15 and 9. -/
public theorem expect_missingMass {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : ∑ a, p a = 1) (N : ℕ) :
    expect N p (fun ω => massSeen p ω 0) =
      expect (N + 1) p (fun ω => (freqOfFreq ω 1 : ℝ)) / (N + 1)
    := by
  have _ := hp
  have _ := hp₁
  rw [expect_massSeen_zero, expect_freqOfFreq_one]
  have hN : (N + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  exact (mul_div_cancel_left₀ _ hN).symm

end WantedExt.Biology.StatisticalGenetics.GoodTuringWanted
