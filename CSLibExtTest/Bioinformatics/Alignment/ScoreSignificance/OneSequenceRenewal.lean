/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.OneSequenceRenewal

/-!
# Tests for the lattice obstruction to `OneSequenceTail`

* Lattice hypothesis: the scores `+1` / `-2` lie on `1ℤ`, checked letter by letter.
* Lattice values: a concrete maximal segment score is an integer, computed from the fold.
* Cell constancy, computed from the definition at `L = 1`: `P(M_1 > 1/4) = P(M_1 > 3/4) = 1/2`.
  Boundary: the cell must be open; at the lattice point `t = 1`, `P(M_1 > 1) = 0 ≠ 1/2`.
* Non-vacuity: a lattice score (the zero score, `h = 1`) with `θ = 1 > 0` satisfies
  `OneSequenceTail` with `K = 0`, proved from the definition, so the hypotheses of
  `OneSequenceTail.eq_zero_of_lattice` are jointly satisfiable.
* Usage: the `+1` / `-2` scores admit no one-sequence tail with `K ≠ 0` at any `θ > 0`.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence.OneSequenceRenewalTest

open Real Finset
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
open Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

/-- Fair letters. -/
noncomputable def q₀ : Bool → ℝ := fun _ => 1 / 2

theorem hq₀ : IsDist q₀ := ⟨fun _ => by norm_num [q₀], by norm_num [q₀]⟩

/-- Match `+1`, mismatch `-2`. -/
def fs : Bool → ℝ := fun b => if b then 1 else -2

/-- The zero score. -/
def f0 : Bool → ℝ := fun _ => 0

/-! ## The lattice hypothesis, computed letter by letter -/

theorem fs_lattice : ∀ b, ∃ k : ℤ, fs b = k * 1 := by
  intro b; cases b
  · exact ⟨-2, by norm_num [fs]⟩
  · exact ⟨1, by norm_num [fs]⟩

theorem f0_lattice : ∀ b, ∃ k : ℤ, f0 b = k * 1 := fun _ => ⟨0, by norm_num [f0]⟩

/-! ## Lattice values of the maximal segment score -/

-- the best run of `[1, -2, 1, 1]` is the final `[1, 1]`
example : maxSegScore [1, -2, 1, 1] = 2 := by norm_num [maxSegScore]

example : ∃ k : ℤ, maxSegScore [1, -2, 1, 1] = k * 1 :=
  exists_int_maxSegScore_eq_mul fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨1, by norm_num⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨-2, by norm_num⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨1, by norm_num⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨1, by norm_num⟩
    simp at hx

/-! ## Cell constancy, computed from the definition at `L = 1` -/

theorem maxSegScore_singleton (a : ℝ) : maxSegScore [a] = max 0 a := by
  simp [maxSegScore]

/-- `P(M_1 > t) = (1 [t < 1] + 1 [t < 0]) / 2` for the `+1` / `-2` scores. -/
theorem scoreProb_one_fs (t : ℝ) :
    scoreProb q₀ fs 1 (fun l => t < maxSegScore l) =
      1 / 2 * (if t < 1 then 1 else 0) + 1 / 2 * (if t < 0 then 1 else 0) := by
  classical
  rw [scoreProb_succ, Fintype.sum_bool]
  simp only [scoreProb, scoreExpect_zero, maxSegScore_singleton, fs, q₀]
  norm_num

example : scoreProb q₀ fs 1 (fun l => 1 / 4 < maxSegScore l) = 1 / 2 := by
  rw [scoreProb_one_fs]; norm_num

example : scoreProb q₀ fs 1 (fun l => 3 / 4 < maxSegScore l) = 1 / 2 := by
  rw [scoreProb_one_fs]; norm_num

/-- Boundary: the lattice point `t = 1` is not inside the cell, and the probability jumps there. -/
example : scoreProb q₀ fs 1 (fun l => 1 < maxSegScore l) = 0 := by
  rw [scoreProb_one_fs]; norm_num

/-! ## Non-vacuity: a lattice score with `θ > 0` satisfying `OneSequenceTail` (`K = 0`) -/

theorem scoreProb_f0 (L : ℕ) {t : ℝ} (ht : 0 < t) :
    scoreProb q₀ f0 L (fun l => t < maxSegScore l) = 0 := by
  classical
  unfold scoreProb scoreExpect
  refine sum_eq_zero fun w _ => ?_
  have h0 : maxSegScore (List.ofFn fun i => f0 (w i)) = 0 :=
    maxSegScore_eq_zero_of_nonpos fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      simp [f0]
  simp [h0, not_lt.2 ht.le]

/-- The zero score, a lattice score, has a one-sequence tail with `θ = 1` and `K = 0`, from the
definition of `OneSequenceTail`. -/
theorem oneSequenceTail_f0 : OneSequenceTail q₀ f0 1 0 := by
  intro ε hε
  refine ⟨1, 1 / 2, by norm_num, 1, one_pos, fun L hL t ht _ => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have htpos : 0 < t := by
    by_contra h
    push Not at h
    have : 1 ≤ exp (-1 * t) := one_le_exp (by linarith)
    nlinarith
  rw [scoreProb_f0 L htpos]
  simp only [zero_mul, sub_zero, abs_zero]
  positivity

-- the hypotheses of the obstruction are jointly satisfiable, and its conclusion `K = 0` agrees
example : OneSequenceTail q₀ f0 1 0 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ ∀ b, ∃ k : ℤ, f0 b = k * 1 :=
  ⟨oneSequenceTail_f0, one_pos, one_pos, f0_lattice⟩

/-! ## Usage -/

example {θ K : ℝ} (hθ : 0 < θ) (htail : OneSequenceTail q₀ fs θ K) : K = 0 :=
  htail.eq_zero_of_lattice hθ one_pos fs_lattice

example {θ : ℝ} (hθ : 0 < θ) : ¬ OneSequenceTail q₀ fs θ 1 :=
  not_oneSequenceTail_of_lattice hθ one_pos fs_lattice one_ne_zero

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence.OneSequenceRenewalTest
