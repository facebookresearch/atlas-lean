/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.TwoSequenceLattice

/-!
# Two-sequence lattice Gumbel tests

* The first lattice point above a threshold and the periodic correction, computed from the
  definitions: `t⁺` is strictly above `t` (a lattice point maps to the next one), the correction
  takes its lower end `e^{-θ h}` at lattice points, and it repeats with period `h`.
* Why the lattice hypothesis is needed in `lt_iff_latticeAbove_le`: an off-lattice value breaks it.
* The match `+1` / mismatch `-2` scores are on `ℤ`, so `P(M_L > 1/2) = P(M_L ≥ 1)`.
* For `K > 0` the two ends of the liminf/limsup bounds differ.
* Non-vacuity: the zero score matrix with `K = 0`, `h = 1` satisfies every hypothesis of the
  periodic-correction theorem and of the bounds. No instance with `K ≠ 0` is constructed.
  The zero-score setup (`p₀`, `s0`, `scoreMGF_s0`, `mem_zipWith_s0`, `maxSegScore_diag_s0`, the
  `K = 0` tail proof, `crossDep_s0`) is copied from
  `CSLibExtTest/Bioinformatics/Alignment/ScoreSignificance/TwoSequence.lean`: that module has no
  public section, so its declarations are not exported and cannot be imported.
* Type-check: the theorem applied to the match/mismatch model, with the lattice tail as a
  hypothesis.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequenceLattice

open Real Finset Filter Topology
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
open Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

/-! ## `t⁺` and the periodic correction, from the definitions -/

theorem latticeAbove_one_half : latticeAbove 1 (1 / 2) = 1 := by
  have h : ⌊(1 / 2 : ℝ) / 1⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
  rw [latticeAbove, h]; norm_num

/-- A lattice point maps to the next lattice point: `t⁺` is strictly above `t`. -/
example : latticeAbove 1 1 = 2 := by
  rw [latticeAbove, div_one, Int.floor_one]; norm_num

example : latticeAbove 2 3 = 4 := by
  have h : ⌊(3 : ℝ) / 2⌋ = 1 := by rw [Int.floor_eq_iff]; norm_num
  rw [latticeAbove, h]; norm_num

theorem latticeAbove_one_three_halves : latticeAbove 1 (3 / 2) = 2 := by
  have h : ⌊(3 / 2 : ℝ) / 1⌋ = 1 := by rw [Int.floor_eq_iff]; norm_num
  rw [latticeAbove, h]; norm_num

/-- At a lattice point the correction takes its lower end `e^{-θ h}`. -/
example (θ : ℝ) : latticeCorr θ 1 0 = exp (-θ) := by
  rw [latticeCorr, latticeAbove, zero_div, Int.floor_zero]
  congr 1; push_cast; ring

/-- Halfway between lattice points it is `e^{-θ h / 2}`. -/
example (θ : ℝ) : latticeCorr θ 1 (1 / 2) = exp (-(θ / 2)) := by
  rw [latticeCorr, latticeAbove_one_half]; congr 1; ring

/-- Period `h = 1`, computed from the definition (not through `latticeCorr_add`). -/
example (θ : ℝ) : latticeCorr θ 1 (3 / 2) = exp (-(θ / 2)) := by
  rw [latticeCorr, latticeAbove_one_three_halves]; congr 1; ring

/-- `lt_iff_latticeAbove_le` needs `y` on the lattice: `1/4 < 1/2` but `(1/4)⁺ = 1 > 1/2`. -/
example : (1 / 4 : ℝ) < 1 / 2 ∧ ¬ latticeAbove 1 (1 / 4) ≤ 1 / 2 := by
  have h : ⌊(1 / 4 : ℝ) / 1⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
  rw [latticeAbove, h]; norm_num

/-- For `K > 0` the two ends of `eventually_lattice_bounds` differ (`K = θ = h = 1`, `x = 0`):
`exp (-K e^{-θ x}) < exp (-K e^{-θ (x + h)})`. -/
example : exp (-(1 * exp (-1 * 0))) < exp (-(1 * exp (-1 * (0 + 1)))) := by
  have h : exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have e1 : -(1 * exp (-1 * 0)) = -1 := by norm_num
  have e2 : -(1 * exp (-1 * (0 + 1))) = -exp (-1) := by norm_num
  rw [e1, e2]
  exact exp_lt_exp.2 (neg_lt_neg h)

/-! ## A lattice scoring matrix -/

/-- Match `+1`, mismatch `-2`. -/
def sm : Bool → Bool → ℝ := fun a b => if a = b then 1 else -2

/-- Fair letters. -/
noncomputable def p₀ : Bool → ℝ := fun _ => 1 / 2

theorem hp₀ : IsDist p₀ := ⟨fun _ => by norm_num [p₀], by norm_num [p₀]⟩

/-- The match/mismatch pair scores lie on `ℤ`. -/
theorem sm_lattice (a : Bool × Bool) : ∃ k : ℤ, pairScore sm a = k * 1 := by
  by_cases hab : a.1 = a.2
  · exact ⟨1, by simp [pairScore, sm, hab]⟩
  · exact ⟨-2, by simp [pairScore, sm, hab]⟩

/-- For integer scores, exceeding `1/2` is reaching `1`. -/
example (L : ℕ) :
    scoreProb (pairLaw p₀ p₀) (pairScore sm) L (fun l => (1 / 2 : ℝ) < maxSegScore l) =
      scoreProb (pairLaw p₀ p₀) (pairScore sm) L (fun l => 1 ≤ maxSegScore l) := by
  have h := scoreProb_lt_maxSegScore_eq (pairLaw p₀ p₀) (pairScore sm) one_pos sm_lattice L
    (1 / 2)
  rwa [latticeAbove_one_half] at h

-- Type-checks only: the periodic-correction theorem for the match/mismatch model (span `1`), with
-- the Cramér root, the lattice tail and asymptotic independence as hypotheses.
example {θ K : ℝ} (hθ : 0 < θ) (hroot : scoreMGF (pairLaw p₀ p₀) (pairScore sm) θ = 1)
    (htail : OneSequenceLatticeTail (pairLaw p₀ p₀) (pairScore sm) θ K 1)
    {m n : ℕ → ℕ} (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ)
    (hdep : ∀ k, Tendsto (fun N => crossDep p₀ p₀ sm (m N) (n N)
      (log (m N * n N) / θ + x) k) atTop (𝓝 0)) :
    Tendsto (fun N => twoProb p₀ p₀ (m N) (n N)
        (fun u v => maxAlignScore sm u v ≤ log (m N * n N) / θ + x) -
          exp (-(K * exp (-θ * x) * latticeCorr θ 1 (log (m N * n N) / θ + x)))) atTop
      (𝓝 0) :=
  tendsto_twoProb_maxAlignScore_le_sub_lattice sm hp₀ hp₀ hθ one_pos hroot htail hm hn hnm hmn x
    hdep

/-! ## Non-vacuity: the zero score matrix -/

/-- The zero scoring matrix (lattice-valued, any span). -/
def s0 : Bool → Bool → ℝ := fun _ _ => 0

theorem scoreMGF_s0 (θ : ℝ) : scoreMGF (pairLaw p₀ p₀) (pairScore s0) θ = 1 := by
  simp only [scoreMGF, pairScore, s0, mul_zero, exp_zero, mul_one]
  exact (isDist_pairLaw hp₀ hp₀).2

private theorem mem_zipWith_s0 :
    ∀ (u v : List Bool) (x : ℝ), x ∈ List.zipWith s0 u v → x ≤ 0
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: u, _ :: v, x, h => by
      rw [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact le_rfl
      · exact mem_zipWith_s0 u v x h

theorem maxSegScore_diag_s0 (u v : List Bool) (d : ℤ) : maxSegScore (diag s0 u v d) = 0 :=
  maxSegScore_eq_zero_of_nonpos fun x hx => mem_zipWith_s0 _ _ x hx

/-- The lattice one-sequence tail with `K = 0`, span `1`, holds for zero scores. -/
theorem oneSequenceLatticeTail_s0 :
    OneSequenceLatticeTail (pairLaw p₀ p₀) (pairScore s0) 1 0 1 := by
  intro ε hε
  refine ⟨1, 1 / 2, by norm_num, 1, one_pos, fun L hL t ht _ => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hE : exp (-1 * t) ≤ 1 / 2 := le_trans (by nlinarith [exp_pos (-1 * t)]) ht
  have htpos : 0 < t := by
    by_contra h; push Not at h
    have : 1 ≤ exp (-1 * t) := one_le_exp (by linarith)
    linarith
  have h0 : scoreProb (pairLaw p₀ p₀) (pairScore s0) L (fun l => t < maxSegScore l) = 0 := by
    refine le_antisymm ?_ (scoreProb_nonneg _ (isDist_pairLaw hp₀ hp₀).1 _ _)
    rw [← scoreProb_maxSegScore_pos_eq_zero (pairScore s0) (isDist_pairLaw hp₀ hp₀).1
      (fun _ _ => le_rfl) L]
    exact scoreProb_mono _ (isDist_pairLaw hp₀ hp₀).1 fun l _ h => htpos.trans h
  rw [h0]; simp only [zero_mul, sub_zero, abs_zero]; positivity

/-- For zero scores and `t > 0` no diagonal exceeds `t`, so every dependence coefficient is `0`. -/
theorem crossDep_s0 (m n k : ℕ) {t : ℝ} (ht : 0 < t) : crossDep p₀ p₀ s0 m n t k = 0 := by
  have hW : ∀ u v : List Bool, exceedCount s0 m n t u v = 0 := fun u v => by
    simp [exceedCount, maxSegScore_diag_s0, not_lt.2 ht.le]
  have hprob : exceedProb p₀ p₀ s0 m n t = fun _ => 0 := funext fun d => by
    simp [exceedProb, maxSegScore_diag_s0, not_lt.2 ht.le, twoProb, twoExpect_const hp₀ hp₀]
  rw [crossDep, exceedMoment, hprob]
  simp only [hW]
  rw [twoExpect_const hp₀ hp₀]
  cases k with
  | zero => simp [elemSymm_zero]
  | succ k =>
    rw [Nat.choose_zero_succ, Nat.cast_zero, zero_sub, neg_eq_zero, elemSymm]
    refine sum_eq_zero fun T hT => ?_
    obtain ⟨i, hi⟩ := card_pos.1 (by rw [(mem_powersetCard.1 hT).2]; omega)
    exact prod_eq_zero hi rfl

theorem tendsto_nat_succ_s0 : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1

theorem tendsto_log_succ_div :
    Tendsto (fun N : ℕ => log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  ((tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp tendsto_nat_succ_s0)).congr fun N => by simp

theorem crossDep_s0_tendsto (x : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => crossDep p₀ p₀ s0 (N + 1) (N + 1)
      (log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x) k) atTop (𝓝 0) := by
  have hNR : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_succ_s0
  have ht : Tendsto (fun N : ℕ => log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x) atTop
      atTop := by
    refine tendsto_atTop_add_const_right _ x ?_
    simp only [div_one]
    exact tendsto_log_atTop.comp (hNR.atTop_mul_atTop₀ hNR)
  exact tendsto_const_nhds.congr'
    ((ht.eventually_gt_atTop 0).mono fun N hN => (crossDep_s0 _ _ k hN).symm)

/-- **Non-vacuity of the periodic-correction theorem**: for the zero scoring matrix (`θ = 1`,
`K = 0`, span `h = 1`, square grids `m = n = N + 1`) every hypothesis holds; the correction term
is `exp 0 = 1`, so the probabilities tend to `1`. -/
example (x : ℝ) : Tendsto (fun N : ℕ => twoProb p₀ p₀ (N + 1) (N + 1)
      fun u v => maxAlignScore s0 u v ≤ log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x)
    atTop (𝓝 1) := by
  have h := tendsto_twoProb_maxAlignScore_le_sub_lattice s0 hp₀ hp₀ one_pos one_pos
    (scoreMGF_s0 1) oneSequenceLatticeTail_s0 tendsto_nat_succ_s0 tendsto_nat_succ_s0
    tendsto_log_succ_div tendsto_log_succ_div x (crossDep_s0_tendsto x)
  simpa using h.add_const 1

/-- **Non-vacuity of the liminf/limsup bounds** for the zero scoring matrix. -/
example (x : ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    exp (-(0 * exp (-1 * x))) - ε ≤ twoProb p₀ p₀ (N + 1) (N + 1)
        (fun u v => maxAlignScore s0 u v ≤ log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x) ∧
      twoProb p₀ p₀ (N + 1) (N + 1)
        (fun u v => maxAlignScore s0 u v ≤ log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x) ≤
        exp (-(0 * exp (-1 * (x + 1)))) + ε :=
  eventually_lattice_bounds s0 hp₀ hp₀ one_pos one_pos le_rfl (scoreMGF_s0 1)
    oneSequenceLatticeTail_s0 tendsto_nat_succ_s0 tendsto_nat_succ_s0 tendsto_log_succ_div
    tendsto_log_succ_div x (crossDep_s0_tendsto x) hε

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequenceLattice
