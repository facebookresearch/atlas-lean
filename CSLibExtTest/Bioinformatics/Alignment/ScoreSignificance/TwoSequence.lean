/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.TwoSequence
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Two-sequence maximal segment score tests

* A binary alphabet with match `+1` / mismatch `-2`: maximal ungapped alignment scores of concrete
  `2 × 2` grids computed by enumerating all `27` alignments from the definition, and checked
  against the diagonal decomposition.
* The single-diagonal slice: a diagonal probability computed by enumerating all `16` pairs of
  words equals the one-sequence probability computed by enumerating all `16` pair words.
* Dependence: two diagonals sharing letters are not independent (biased letters), two
  letter-disjoint diagonals are.
* Negative expected score (the Gumbel regime): the Karlin–Altschul root is `log φ`, and the
  unconditional bound `P(M ≥ t) ≤ m n φ^{-t}` holds. Non-negative expected score (not claimed):
  no root `θ > 0` exists, and for all-positive scores `M_{m,n} ≥ min m n`.
* Non-vacuity of the Gumbel theorem: a zero score matrix with `K = 0` satisfies every hypothesis.
  The zero score is lattice-valued, so `OneSequenceTail` does not exclude lattice scores; its
  intended regime is `K > 0`. No instance with `K ≠ 0` is constructed (that needs renewal theory).
* `alignScore` takes a length bound: windows running past the end of a sequence are truncated.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

open Real Finset Filter Topology
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

/-! ## A concrete alphabet and scoring matrix -/

/-- Match `+1`, mismatch `-2`. -/
def sm : Bool → Bool → ℝ := fun a b => if a = b then 1 else -2

/-- Fair letters. -/
noncomputable def p₀ : Bool → ℝ := fun _ => 1 / 2

theorem hp₀ : IsDist p₀ := ⟨fun _ => by norm_num [p₀], by norm_num [p₀]⟩

example : offsets 2 2 = {-1, 0, 1} := by decide

-- the three diagonals of `u = [T, F]`, `v = [T, T]`
example : diag sm [true, false] [true, true] (-1) = [-2] := by norm_num [diag, diagFrom, sm]
example : diag sm [true, false] [true, true] 0 = [1, -2] := by norm_num [diag, diagFrom, sm]
example : diag sm [true, false] [true, true] 1 = [1] := by norm_num [diag, diagFrom, sm]

/-- `alignScore` takes `ℓ` as a length bound: starting at the end of `u = [T]`, the window of `u`
is empty, so the "length-1" alignment scores no pair. -/
example : alignScore sm [true] [false] 1 0 1 = 0 := by norm_num [alignScore]

/-- The same through `alignScore_eq_min`: the bound is cut to `min 1 (min (1 - 1) (1 - 0)) = 0`. -/
example : alignScore sm [true] [false] 1 0 1 = alignScore sm [true] [false] 1 0 0 := by
  rw [alignScore_eq_min]
  norm_num

/-- Within both sequences the bound is the length: `alignScore sm [T, F] [T, T] 0 0 2 = 1 - 2`. -/
example : alignScore sm [true, false] [true, true] 0 0 2 = -1 := by norm_num [alignScore, sm]

/-- Enumerating all `3 × 3 × 3` alignments `(i, j, ℓ)` of `u = [T, F]`, `v = [T, T]`: the best
score is `1` (a single match). -/
theorem maxAlignScore_TF_TT : maxAlignScore sm [true, false] [true, true] = 1 := by
  refine le_antisymm (sup'_le _ _ fun c hc => ?_) ?_
  · obtain ⟨i, j, l⟩ := c
    simp only [List.length_cons, List.length_nil, mem_product, mem_range] at hc
    obtain ⟨hi, hj, hl⟩ := hc
    interval_cases i <;> interval_cases j <;> interval_cases l <;> norm_num [alignScore, sm]
  · exact (show (1 : ℝ) = alignScore sm [true, false] [true, true] 0 0 1 by
      norm_num [alignScore, sm]) ▸ alignScore_le_maxAlignScore sm _ _ (by simp) (by simp) (by simp)

/-- Enumerating all alignments of `u = [T, T]`, `v = [T, T]`: the main diagonal scores `2`. -/
theorem maxAlignScore_TT_TT : maxAlignScore sm [true, true] [true, true] = 2 := by
  refine le_antisymm (sup'_le _ _ fun c hc => ?_) ?_
  · obtain ⟨i, j, l⟩ := c
    simp only [List.length_cons, List.length_nil, mem_product, mem_range] at hc
    obtain ⟨hi, hj, hl⟩ := hc
    interval_cases i <;> interval_cases j <;> interval_cases l <;> norm_num [alignScore, sm]
  · exact (show (2 : ℝ) = alignScore sm [true, true] [true, true] 0 0 2 by
      norm_num [alignScore, sm]) ▸ alignScore_le_maxAlignScore sm _ _ (by simp) (by simp) (by simp)

/-- Enumerating all alignments of `u = [T, F]`, `v = [F, T]`: no diagonal has two matches, the
best is a single match. -/
theorem maxAlignScore_TF_FT : maxAlignScore sm [true, false] [false, true] = 1 := by
  refine le_antisymm (sup'_le _ _ fun c hc => ?_) ?_
  · obtain ⟨i, j, l⟩ := c
    simp only [List.length_cons, List.length_nil, mem_product, mem_range] at hc
    obtain ⟨hi, hj, hl⟩ := hc
    interval_cases i <;> interval_cases j <;> interval_cases l <;> norm_num [alignScore, sm]
  · exact (show (1 : ℝ) = alignScore sm [true, false] [false, true] 0 1 1 by
      norm_num [alignScore, sm]) ▸ alignScore_le_maxAlignScore sm _ _ (by simp) (by simp) (by simp)

-- agreement with the diagonal decomposition: the best diagonal is `1` (offset `1`)
example : maxSegScore (diag sm [true, false] [true, true] 1) =
    maxAlignScore sm [true, false] [true, true] := by
  rw [maxAlignScore_TF_TT]; norm_num [diag, diagFrom, sm, maxSegScore]
-- `u = [T, T]`, `v = [T, T]`: the best diagonal is the main one, `[1, 1]`
example : maxSegScore (diag sm [true, true] [true, true] 0) =
    maxAlignScore sm [true, true] [true, true] := by
  rw [maxAlignScore_TT_TT]; norm_num [diag, diagFrom, sm, maxSegScore]
-- `u = [T, F]`, `v = [F, T]`: the best diagonals are offsets `-1` and `1`, each a single match
example : maxSegScore (diag sm [true, false] [false, true] 1) =
    maxAlignScore sm [true, false] [false, true] := by
  rw [maxAlignScore_TF_FT]; norm_num [diag, diagFrom, sm, maxSegScore]
example : maxSegScore (diag sm [true, false] [false, true] (-1)) =
    maxAlignScore sm [true, false] [false, true] := by
  rw [maxAlignScore_TF_FT]; norm_num [diag, diagFrom, sm, maxSegScore]
example : maxAlignScore sm [true, false] [true, true] ≤ 1 ↔
    ∀ d ∈ offsets 2 2, ¬ 1 < maxSegScore (diag sm [true, false] [true, true] d) :=
  maxAlignScore_le_iff sm _ _ zero_le_one
-- the best score `1` is not below `1/2`: some diagonal exceeds `1/2`
example : ∃ d ∈ offsets 2 2, (1 / 2 : ℝ) ≤ maxSegScore (diag sm [true, false] [true, true] d) :=
  (le_maxAlignScore_iff sm [true, false] [true, true] (by norm_num)).1
    (by rw [maxAlignScore_TF_TT]; norm_num)
-- the cell count `∑_d diagLen = m n` for a `2 × 3` grid
example : ∑ d ∈ offsets 2 3, (diagLen 2 3 d : ℝ) = 6 := by
  rw [sum_diagLen]; norm_num

/-! ## The single-diagonal slice, by enumeration -/

/-- On the main diagonal of the fair `2 × 2` model, `P(some segment scores ≥ 1) = 3/4`
(enumerating the `16` pairs of words). -/
theorem twoProb_diag_zero_enum :
    twoProb p₀ p₀ 2 2 (fun u v => 1 ≤ maxSegScore (diag sm u v 0)) = 3 / 4 := by
  simp only [twoProb, twoExpect, wordExpect_succ, wordExpect_zero, Fintype.sum_bool]
  norm_num [diag, diagFrom, sm, p₀, maxSegScore]

/-- The same probability for the one-sequence model over the pair alphabet `Bool × Bool`
(enumerating the `16` pair words). -/
theorem scoreProb_pair_enum :
    scoreProb (pairLaw p₀ p₀) (pairScore sm) 2 (fun l => 1 ≤ maxSegScore l) = 3 / 4 := by
  simp only [scoreProb, scoreExpect_succ, scoreExpect_zero, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [pairLaw, pairScore, sm, p₀, maxSegScore]

-- the slice theorem identifies them
example : twoProb p₀ p₀ 2 2 (fun u v => 1 ≤ maxSegScore (diag sm u v 0)) =
    scoreProb (pairLaw p₀ p₀) (pairScore sm) 2 (fun l => 1 ≤ maxSegScore l) :=
  twoProb_diag hp₀ hp₀ sm 2 2 0 fun l => 1 ≤ maxSegScore l

-- a single diagonal of an `L × L` grid is a one-sequence model of length `L`
example (L : ℕ) (P : List ℝ → Prop) :
    twoProb p₀ p₀ L L (fun u v => P (diag sm u v 0)) =
      scoreProb (pairLaw p₀ p₀) (pairScore sm) L P := by
  rw [twoProb_diag hp₀ hp₀]; simp [diagLen]

/-! ## Dependence between diagonals -/

/-- Biased letters: `P(T) = 3/4`. -/
noncomputable def p₁ : Bool → ℝ := fun b => if b then 3 / 4 else 1 / 4

theorem hp₁ : IsDist p₁ := ⟨fun b => by cases b <;> norm_num [p₁], by norm_num [p₁]⟩

/-- `P(first score of diagonal 0 is a match) = 5/8`. -/
theorem twoProb_diag0_head : twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 0).head? = some 1) =
    5 / 8 := by
  simp only [twoProb, twoExpect, wordExpect_succ, wordExpect_zero, Fintype.sum_bool]
  norm_num [diag, diagFrom, sm, p₁]

/-- `P(first score of diagonal 1 is a match) = 5/8`. -/
theorem twoProb_diag1_head : twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 1).head? = some 1) =
    5 / 8 := by
  simp only [twoProb, twoExpect, wordExpect_succ, wordExpect_zero, Fintype.sum_bool]
  norm_num [diag, diagFrom, sm, p₁]

/-- Both match: `u₀ = v₀ = v₁`, probability `(3/4)³ + (1/4)³ = 7/16`. -/
theorem twoProb_diag0_diag1_head :
    twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 0).head? = some 1 ∧
      (diag sm u v 1).head? = some 1) = 7 / 16 := by
  simp only [twoProb, twoExpect, wordExpect_succ, wordExpect_zero, Fintype.sum_bool]
  norm_num [diag, diagFrom, sm, p₁]

/-- **Diagonals sharing a letter are dependent**: `7/16 ≠ (5/8)²`. -/
example : twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 0).head? = some 1 ∧
      (diag sm u v 1).head? = some 1) ≠
    twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 0).head? = some 1) *
      twoProb p₁ p₁ 2 2 (fun u v => (diag sm u v 1).head? = some 1) := by
  rw [twoProb_diag0_diag1_head, twoProb_diag0_head, twoProb_diag1_head]; norm_num

-- **letter-disjoint diagonals are independent**: offsets `-1` and `1` of a `2 × 2` grid
example (A B : List ℝ → Prop) :
    twoProb p₁ p₁ 2 2 (fun u v => A (diag sm u v (-(1 : ℕ))) ∧ B (diag sm u v (1 : ℕ))) =
      twoProb p₁ p₁ 2 2 (fun u v => A (diag sm u v (-(1 : ℕ)))) *
        twoProb p₁ p₁ 2 2 (fun u v => B (diag sm u v (1 : ℕ))) :=
  twoProb_diag_and_diag_of_disjoint hp₁ hp₁ sm (by norm_num) (by norm_num) (by decide)
    (by decide) A B

-- the dependence coefficients vanish to first order
example (t : ℝ) : crossDep p₁ p₁ sm 2 2 t 1 = 0 := crossDep_one sm 2 2 t
example (t : ℝ) : crossDep p₁ p₁ sm 2 2 t 0 = 0 := crossDep_zero sm 2 2 t hp₁ hp₁

/-! ## Negative expected score: the Gumbel regime -/

theorem mean_sm : ∑ a, ∑ b, p₀ a * p₀ b * sm a b = -1 / 2 := by norm_num [p₀, sm]

/-- The Karlin–Altschul root of match `+1` / mismatch `-2` with fair letters is `log φ`. -/
theorem scoreMGF_sm (θ : ℝ) :
    scoreMGF (pairLaw p₀ p₀) (pairScore sm) θ = (exp θ + exp (-(2 * θ))) / 2 := by
  simp only [scoreMGF, Fintype.sum_prod_type, Fintype.sum_bool, pairLaw, pairScore, sm, p₀]
  norm_num
  ring_nf

theorem scoreMGF_log_goldenRatio :
    scoreMGF (pairLaw p₀ p₀) (pairScore sm) (log goldenRatio) = 1 := by
  have hφ : 0 < goldenRatio := goldenRatio_pos
  rw [scoreMGF_sm, exp_log hφ, exp_neg, ← log_rpow hφ, exp_log (by positivity)]
  have h2 : goldenRatio ^ (2 : ℝ) = goldenRatio + 1 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, goldenRatio_sq]
  rw [h2]
  have hsq := goldenRatio_sq
  generalize goldenRatio = φ at hφ hsq ⊢
  field_simp
  nlinarith [hsq]

theorem log_goldenRatio_pos : 0 < log goldenRatio := log_pos one_lt_goldenRatio

-- `λ = log φ` is the unique Karlin–Altschul root
example : ∃! θ, 0 < θ ∧ scoreMGF (pairLaw p₀ p₀) (pairScore sm) θ = 1 := by
  have hu := existsUnique_karlinAltschul_root hp₀ (fun _ => by norm_num [p₀])
    (by rw [mean_sm]; norm_num) ⟨true, true, by norm_num [sm]⟩
  exact ⟨log goldenRatio, ⟨log_goldenRatio_pos, scoreMGF_log_goldenRatio⟩,
    fun θ hθ => hu.unique hθ ⟨log_goldenRatio_pos, scoreMGF_log_goldenRatio⟩⟩

-- the unconditional Karlin–Altschul bound: `P(M_{100,200} ≥ 30) ≤ 100 · 200 · φ^{-30}`
example : twoProb p₀ p₀ 100 200 (fun u v => 30 ≤ maxAlignScore sm u v) ≤
    (100 : ℕ) * (200 : ℕ) * exp (-log goldenRatio * 30) :=
  twoProb_le_maxAlignScore_le hp₀ hp₀ sm log_goldenRatio_pos.le scoreMGF_log_goldenRatio
    100 200 (by norm_num)

-- Type-checks only: the Gumbel theorem applied to this model, with the one-sequence tail as a
-- hypothesis. Match `+1` / mismatch `-2` is a nondegenerate lattice score, outside the intended
-- regime of `OneSequenceTail`; whether it holds here for some `K` is not decided in this file.
example {K : ℝ} (htail : OneSequenceTail (pairLaw p₀ p₀) (pairScore sm) (log goldenRatio) K)
    {m n : ℕ → ℕ} (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ)
    (hdep : ∀ k, Tendsto (fun N => crossDep p₀ p₀ sm (m N) (n N)
      (log (m N * n N) / log goldenRatio + x) k) atTop (𝓝 0)) :
    Tendsto (fun N => twoProb p₀ p₀ (m N) (n N)
        fun u v => maxAlignScore sm u v ≤ log (m N * n N) / log goldenRatio + x) atTop
      (𝓝 (exp (-(K * exp (-log goldenRatio * x))))) :=
  tendsto_twoProb_maxAlignScore_le sm hp₀ hp₀ log_goldenRatio_pos scoreMGF_log_goldenRatio
    htail hm hn hnm hmn x hdep

/-! ## Non-negative expected score: not claimed -/

/-- Match `+1` / mismatch `-1`: expected score `0`. -/
def sz : Bool → Bool → ℝ := fun a b => if a = b then 1 else -1

example : ∑ a, ∑ b, p₀ a * p₀ b * sz a b = 0 := by norm_num [p₀, sz]

/-- Mean zero: the pair-score MGF is `cosh θ > 1`, so there is no root `θ > 0` and the Gumbel
theorem does not apply. -/
example : ¬ ∃ θ, 0 < θ ∧ scoreMGF (pairLaw p₀ p₀) (pairScore sz) θ = 1 := by
  rintro ⟨θ, hθ, h⟩
  have hc : scoreMGF (pairLaw p₀ p₀) (pairScore sz) θ = cosh θ := by
    simp only [scoreMGF, Fintype.sum_prod_type, Fintype.sum_bool, pairLaw, pairScore, sz, p₀]
    norm_num [cosh_eq]; ring
  rw [hc] at h
  exact (one_lt_cosh.2 hθ.ne').ne' h

/-- All scores `+1`: positive mean. -/
def sp : Bool → Bool → ℝ := fun _ _ => 1

example : ¬ ∃ θ, 0 < θ ∧ scoreMGF (pairLaw p₀ p₀) (pairScore sp) θ = 1 := by
  rintro ⟨θ, hθ, h⟩
  simp only [scoreMGF, Fintype.sum_prod_type, Fintype.sum_bool, pairLaw, pairScore, sp, p₀] at h
  norm_num at h
  have : 1 < exp θ := one_lt_exp_iff.2 hθ
  linarith

private theorem sum_zipWith_one :
    ∀ u v : List Bool, (List.zipWith sp u v).sum = (min u.length v.length : ℕ)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | _ :: u, _ :: v => by
      rw [List.zipWith_cons_cons, List.sum_cons, sum_zipWith_one u v]
      simp [sp, Nat.min_def]; split_ifs <;> ring

/-- With all scores positive, `M_{m,n} ≥ min m n` grows linearly: `P(M ≤ t) = 0` for
`t < min m n`, so there is no Gumbel limit at the `log (m n)` scale. -/
example (m n : ℕ) {t : ℝ} (ht : t < min m n) :
    twoProb p₀ p₀ m n (fun u v => maxAlignScore sp u v ≤ t) = 0 := by
  refine le_antisymm ?_ (twoProb_nonneg hp₀.1 hp₀.1 _ _ _)
  calc twoProb p₀ p₀ m n (fun u v => maxAlignScore sp u v ≤ t)
      ≤ twoProb p₀ p₀ m n (fun _ _ => False) := twoProb_mono hp₀.1 hp₀.1 fun u v hu hv h => by
        have hle := alignScore_le_maxAlignScore sp u v (i := 0) (j := 0)
          (ℓ := min u.length v.length) (Nat.zero_le _) (Nat.zero_le _) (min_le_left _ _)
        rw [alignScore, List.drop_zero, List.drop_zero, sum_zipWith_one] at hle
        simp only [List.length_take, hu, hv] at hle
        rw [show min (min m n) m = min m n by omega, show min (min m n) n = min m n by omega,
          min_self] at hle
        linarith
    _ = 0 := by simp [twoProb, twoExpect_const hp₀ hp₀]

/-! ## Non-vacuity: a zero score matrix -/

/-- The zero scoring matrix. -/
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

/-- The one-sequence tail with `K = 0` holds for zero scores. -/
theorem oneSequenceTail_s0 : OneSequenceTail (pairLaw p₀ p₀) (pairScore s0) 1 0 := by
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

/-- **Non-vacuity of the Gumbel theorem**: for the zero scoring matrix (`θ = 1`, `K = 0`, square
grids `m = n = N + 1`) every hypothesis holds, and the limit is `exp 0 = 1`. -/
example (x : ℝ) : Tendsto (fun N : ℕ => twoProb p₀ p₀ (N + 1) (N + 1)
      fun u v => maxAlignScore s0 u v ≤ log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x)
    atTop (𝓝 1) := by
  have hN : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hNR : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have ht : Tendsto (fun N : ℕ => log (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) / 1 + x) atTop
      atTop := by
    refine tendsto_atTop_add_const_right _ x ?_
    simp only [div_one]
    exact tendsto_log_atTop.comp (hNR.atTop_mul_atTop₀ hNR)
  have hlog : Tendsto (fun N : ℕ => log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    ((tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hNR).congr fun N => by simp
  have h := tendsto_twoProb_maxAlignScore_le s0 hp₀ hp₀ one_pos (scoreMGF_s0 1)
    oneSequenceTail_s0 hN hN hlog hlog x fun k => tendsto_const_nhds.congr'
      ((ht.eventually_gt_atTop 0).mono fun N hN => (crossDep_s0 _ _ k hN).symm)
  simpa using h

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence
