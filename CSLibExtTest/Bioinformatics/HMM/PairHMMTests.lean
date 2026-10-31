/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.HMM.PairHMM
public meta import CSLibExt.Bioinformatics.HMM.PairHMM
public import Mathlib.Algebra.Order.Field.Rat
public meta import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Pair HMM tests

Executed fixtures: for all pairs of binary sequences of lengths up to 3, `alignmentsOf` has
no duplicates, has the Delannoy number of elements, consists of valid alignments, and equals
`alignments`; on 40 pseudo-random pair HMMs over `ℚ` (random nonnegative weights) the sum
recursion equals the brute-force sum of `alignProb` over `alignments` and the max recursion
equals the brute-force maximum. Each run throws on a disagreement.

Non-vacuity: `toyPair` is a nonnegative pair HMM over `ℚ`. `witness` is a probabilistic memoryless pair HMM over `Bool` (transition rows and
emission tables sum to one) whose per-column log-odds scores against the uniform independence
model with `η = 1/2` are the integers `σ a a = 1`, `σ a b = -1` (`a ≠ b`) and `gap = -1`; it
satisfies `LinearGapLogOdds`, so `log_viterbi_div_background` applies to it.
-/

namespace Cslib.Bioinformatics.HMM

open Cslib.Algorithms.Lean

/-! ## Executed fixtures -/

/-- All binary sequences of length at most `n`. -/
def boolSeqs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: ((boolSeqs n).flatMap fun s => [false :: s, true :: s]) |>.dedup

/-- The Delannoy number `D(m, n)`, the number of global alignments of lengths `m` and `n`. -/
def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => delannoy m n + delannoy m (n + 1) + delannoy (m + 1) n

#eval do
  for xs in boolSeqs 3 do
    for ys in boolSeqs 3 do
      let As : List (Alignment Bool) := alignmentsOf xs ys
      unless As.Nodup do throw (IO.userError s!"duplicate alignment for {xs} {ys}")
      unless As.length == delannoy xs.length ys.length do
        throw (IO.userError s!"wrong count for {xs} {ys}")
      unless As == alignments xs ys do throw (IO.userError "differs from `alignments`")
      for (A : Alignment Bool) in As do
        unless A.filterMap Prod.fst == xs && A.filterMap Prod.snd == ys &&
            A.all (· != (none, none)) do
          throw (IO.userError s!"invalid alignment {A}")
  IO.println "all pairs up to length 3: alignmentsOf is the nodup Delannoy-size list of alignments"

#eval do
  let mut s := 7
  for _ in [0:40] do
    let mut ws : Array ℚ := #[]
    for _ in [0:30] do
      s := (s * 1103515245 + 12345) % 2147483648
      ws := ws.push ((s / 13 % 5 : ℕ) : ℚ)
    let idx : PairState → ℕ := fun | .M => 0 | .X => 1 | .Y => 2
    let h : PairHMM Bool ℚ :=
      { start := fun t => ws[idx t]!, startStop := ws[3]!,
        trans := fun u t => ws[4 + 3 * idx u + idx t]!, stop := fun u => ws[13 + idx u]!,
        emitM := fun a b => ws[16 + 2 * a.toNat + b.toNat]!,
        emitX := fun a => ws[20 + a.toNat]!, emitY := fun b => ws[22 + b.toNat]! }
    s := (s * 1103515245 + 12345) % 2147483648
    let seqs := boolSeqs 3
    let xs := seqs[s / 7 % seqs.length]!
    let ys := seqs[s / 11 % seqs.length]!
    let brute := ((alignments xs ys).map h.alignProb).sum
    unless h.likelihood xs ys == brute do throw (IO.userError s!"likelihood {xs} {ys}")
    let bmax := ((alignments xs ys).map h.alignProb).foldl max 0
    unless h.viterbi xs ys == bmax do throw (IO.userError s!"viterbi {xs} {ys}")
  IO.println "40 random pair HMMs: sum and max recursions = brute force over alignments"

/-! ## Closed checks -/

example (h : PairHMM Bool ℚ) (xs ys : List Bool) :
    h.likelihood xs ys = ((alignments xs ys).map h.alignProb).sum :=
  h.likelihood_eq_sum xs ys

example : (alignmentsOf [true] [false]).length = 3 := by decide

/-- A nonnegative pair HMM over `ℚ` (non-vacuity of `PairHMM.Nonneg`). -/
def toyPair : PairHMM Bool ℚ where
  start _ := 1 / 4
  startStop := 1 / 4
  trans _ t := if t = .M then 1 / 2 else 1 / 8
  stop _ := 1 / 4
  emitM a b := if a = b then 3 / 8 else 1 / 8
  emitX _ := 1 / 2
  emitY _ := 1 / 2

theorem toyPair_nonneg : toyPair.Nonneg where
  start _ := by norm_num [toyPair]
  trans _ t := by simp only [toyPair]; split_ifs <;> norm_num
  emitM a b := by simp only [toyPair]; split_ifs <;> norm_num
  emitX _ := by norm_num [toyPair]
  emitY _ := by norm_num [toyPair]

/-- The Viterbi alignment of `[true]`, `[true]` is the match column. -/
example : toyPair.viterbi [true] [true] = toyPair.alignProb [(some true, some true)] := by
  decide +kernel

example {A : Alignment Bool} (hA : IsAlignment A [true, false] [true]) :
    toyPair.alignProb A ≤ toyPair.viterbi [true, false] [true] :=
  PairHMM.alignProb_le_viterbi toyPair_nonneg hA

/-! ## Non-vacuity of `LinearGapLogOdds` -/

/-- The match transition weight `(e + e⁻¹) / 8` of the witness. -/
noncomputable def πM : ℝ := (Real.exp 1 + Real.exp (-1)) / 8

/-- The witness's transition weights into each emitting state. -/
noncomputable def wπ : PairState → ℝ
  | .M => πM
  | .X => Real.exp (-1) / 2
  | .Y => Real.exp (-1) / 2

/-- The witness's transition weight into the end state. -/
noncomputable def wτ : ℝ := 1 - πM - Real.exp (-1)

/-- The integer substitution scores of the witness: `1` on the diagonal, `-1` off it. -/
def wσ (a b : Bool) : ℤ := if a = b then 1 else -1

/-- The witness: a memoryless pair HMM over `Bool` with uniform gap emissions. -/
noncomputable def witness : PairHMM Bool ℝ where
  start := wπ
  startStop := wτ
  trans _ := wπ
  stop _ := wτ
  emitM a b := Real.exp (wσ a b) / (16 * πM)
  emitX _ := 1 / 2
  emitY _ := 1 / 2

theorem πM_pos : 0 < πM := by unfold πM; positivity

theorem wτ_pos : 0 < wτ := by
  have h1 := Real.exp_one_lt_d9
  have h3 := Real.exp_one_gt_d9
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hu := Real.exp_pos (-1)
  have h4 : Real.exp (-1) < 0.371 := by nlinarith
  unfold wτ πM
  nlinarith

/-- The witness is probabilistic: each transition row sums to one. -/
example : wπ .M + wπ .X + wπ .Y + wτ = 1 := by simp only [wπ, wτ]; ring

/-- The witness's match emissions sum to one. -/
example : ∑ a : Bool, ∑ b : Bool, witness.emitM a b = 1 := by
  simp only [witness, wσ, Fintype.sum_bool, ite_true, Bool.true_eq_false, Bool.false_eq_true,
    ite_false]
  have := πM_pos
  field_simp
  unfold πM
  push_cast
  ring

/-- **Non-vacuity**: the witness satisfies the log-odds hypotheses with `σ = wσ`, `gap = -1`,
uniform background frequencies and `η = 1/2`. -/
theorem witness_linearGapLogOdds :
    witness.LinearGapLogOdds wπ wτ (fun _ => 1 / 2) (1 / 2) wσ (-1) where
  memoryless := ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  π_pos s := by
    cases s
    · exact πM_pos
    all_goals exact div_pos (Real.exp_pos _) two_pos
  τ_pos := wτ_pos
  q_pos _ := by norm_num
  η_pos := by norm_num
  η_lt_one := by norm_num
  emitM_pos _ _ := div_pos (Real.exp_pos _) (mul_pos (by norm_num) πM_pos)
  emitX_pos _ := by simp [witness]
  emitY_pos _ := by simp [witness]
  logOdds_M a b := by
    have := πM_pos
    rw [show wπ .M * witness.emitM a b / ((1 - 1 / 2) ^ 2 * (1 / 2) * (1 / 2)) =
        Real.exp (wσ a b) by simp only [wπ, witness]; field_simp; ring, Real.log_exp]
  logOdds_X a := by
    rw [show wπ .X * witness.emitX a / ((1 - 1 / 2) * (1 / 2)) = Real.exp (-1) by
      simp only [wπ, witness]; ring, Real.log_exp]
    norm_num
  logOdds_Y b := by
    rw [show wπ .Y * witness.emitY b / ((1 - 1 / 2) * (1 / 2)) = Real.exp (-1) by
      simp only [wπ, witness]; ring, Real.log_exp]
    norm_num

/-- The log-odds Viterbi score of the witness on `[true]`, `[true]` is the Needleman–Wunsch
score `1` (one match) plus `log (τ / η²)`. -/
example : Real.log (witness.viterbi [true] [true] /
      PairHMM.background (fun _ => 1 / 2) (1 / 2) [true] [true]) =
    1 + Real.log (wτ / (1 / 2) ^ 2) := by
  rw [PairHMM.log_viterbi_div_background witness_linearGapLogOdds]
  congr 1
  rw [show nwScore wσ (-1) [true] [true] = 1 by decide]
  norm_num

end Cslib.Bioinformatics.HMM
