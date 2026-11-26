/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLTruncation

@[expose] public section

/-!
# Level-at-least-two Fourier mass and the BKKKL master estimates

Upper bounds for the damped level-≥2 Fourier mass and the target/damped comparison, and
the two residue predicates `bkt2_levelGe2MasterResidue` and `bkt2_RemainingGoal`, each a
uniform estimate over `p ∈ (1/2, q)`. Status: both residues are refuted for every `q > 1/2`
(`ctc_levelGe2_false_of_half_lt`, `ctc_remainingGoal_false_of_half_lt`). They are kept
only as the statements of those refutations; no chain derives the low-degree master
estimate, the master estimate or rho-optimisation from them.

## Main definitions

* `bkt2_levelGe2MasterResidue`, `bkt2_RemainingGoal`: uniform level-≥2 estimates over a
  window `(1/2, q)`; both false for every `q > 1/2`.

## Main results

* `bkt2_capped_levelGe2_damped`, `bkt2_damped_le_target`: damped level-≥2 mass bounds.
-/

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bkt2_capped_levelGe2_damped [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have hfull := lib_capped_optimal_weight hp0 hp1 φ hu0 hu1
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hsub : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * ∑ S : Finset ι, (S.card : ℝ)
          * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro S _ _
    have : (0 : ℝ) ≤ ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by positivity
    positivity
  exact le_trans hsub hfull

theorem bkt2_damped_le_target {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1)
    (d : ℕ) :
    ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) ≤ (1 - u) ^ (d - 1) := by
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hs0 : (0 : ℝ) ≤ 4 * p * (1 - p) := by nlinarith
  have hs1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [hs1, h1u0]

theorem bkt2_target_eq_damped_of_p_half {u : ℝ} (d : ℕ) :
    (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = (1 - u) ^ (d - 1) := by
  norm_num

/-- The uniform level-≥2 master residue over a window `(1/2, q)`: the damped
level-≥2 mass is controlled for every `p` in the window. False for every `q > 1/2`
(`ctc_levelGe2_false_of_half_lt`). -/
def bkt2_levelGe2MasterResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ k : ℕ, 1 ≤ k ∧
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2

/-- The uniform remaining-goal estimate over a window `(1/2, q)`. False for every `q > 1/2`
(`ctc_remainingGoal_false_of_half_lt`). -/
def bkt2_RemainingGoal (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ k : ℕ, 1 ≤ k ∧
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
                - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1))
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
                  (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
                    * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)

theorem bkt2_truncDamped_le [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  refine le_trans ?_ (bkt2_capped_levelGe2_damped hp0 hp1 φ hu0 hu1)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS; rw [Finset.mem_filter] at hS ⊢; exact ⟨hS.1, hS.2.1⟩
  · intro S _ _
    have h1 : (0 : ℝ) ≤ ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by positivity
    positivity

theorem bkt2_weightGap_nonneg {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1) (d : ℕ) :
    0 ≤ (1 - u) ^ (d - 1) - ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) := by
  have := bkt2_damped_le_target hp0 hp1 hu1 d
  linarith

end StatMech.Probability
