/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős–Rényi law with shifts for the longest exact match

Arratia and Waterman (1985): let `X₁, X₂, …` and `Y₁, Y₂, …` be letters from a countable
alphabet, all of them independent and identically distributed, and let `p = P(X₁ = Y₁)` with
`0 < p < 1`. The longest exact match with shifts between the first `n` letters of the two
sequences is `M_n = max {m : X_{i+k} = Y_{j+k} for k = 1, …, m, for some 0 ≤ i, j ≤ n - m}`
(equation (2)). Write `log` for the logarithm to base `1 / p`. Theorem 2:
`P(M_n - 2 log n ≥ b) ≤ p ^ b` for every real `b` and every `n ≥ 1` (equation (6)), and for
every `ε > 0`, almost surely, eventually in `n`,
`-4 - ε < (M_n - 2 log n) / log log n < 1 + ε`. Hence `M_n / log n → 2` almost surely
(equation (3)).

Indices start at `1` as in the source; the letters at index `0` are not used, and the shared
`SequenceComparisonShared.IIDLetters` assumes nothing about them. Not recorded here:
Theorem 3 (independent irreducible aperiodic Markov chains, with `p` the largest eigenvalue of the
matrix of squared transition probabilities), and the extension (12) to sequences of different
lengths, whose proof the paper omits.

Sources: R. Arratia and M. S. Waterman, "An Erdős–Rényi law with shifts", Advances in Mathematics
55 (1985) 13–23, doi:10.1016/0001-8708(85)90003-9, equations (2), (3), (6) and Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.ComputationalBiology.SequenceComparisonShared
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.LongestMatchShiftsWanted

open MeasureTheory ProbabilityTheory Filter
open WantedExt.Biology.ComputationalBiology.SequenceComparisonShared (IIDLetters)

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The letters `X_{i+1}, …, X_{i+m}` and `Y_{j+1}, …, Y_{j+m}` agree. -/
def MatchAt (X Y : ℕ → α) (i j m : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ m → X (i + k) = Y (j + k)

/-- The **longest exact match with shifts** `M_n`: the largest `m` such that the letters
`X_{i+1}, …, X_{i+m}` and `Y_{j+1}, …, Y_{j+m}` agree for some `i, j` with `i + m ≤ n` and
`j + m ≤ n` (equation (2)). -/
noncomputable def longestMatch (X Y : ℕ → α) (n : ℕ) : ℕ :=
  sSup {m | ∃ i j, i + m ≤ n ∧ j + m ≤ n ∧ MatchAt X Y i j m}

/-- **Match probability.** `p = P(X₁ = Y₁)`: `P.real` of the set of outcomes at which the first
letters agree. When the first letters are measurable and the alphabet is countable with measurable
singletons, that set is an event, and under a probability measure this is its probability, as in
the theorems below (`IIDLetters` makes the letters measurable). Otherwise the set need not be
measurable, and `P.real` of a set that is not measurable is its outer measure, not the probability
of an event. -/
noncomputable def matchProb (P : Measure Ω) (Z : ℕ ⊕ ℕ → Ω → α) : ℝ :=
  P.real {ω | Z (Sum.inl 1) ω = Z (Sum.inr 1) ω}

/-- The longest match with shifts between the first `n` letters of `X` and `Y` at the outcome
`ω`. -/
noncomputable def M (Z : ℕ ⊕ ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℕ :=
  longestMatch (fun i => Z (Sum.inl i) ω) (fun j => Z (Sum.inr j) ω) n

/-- **Tail bound for the longest match** (Arratia and Waterman 1985, Theorem 2 and equation (6)):
for i.i.d. letters `X₁, X₂, …, Y₁, Y₂, …` from a countable alphabet with measurable singletons,
under a probability measure, with `p = P(X₁ = Y₁)` and `0 < p < 1`, for every real `b` and every
`n ≥ 1`, `P(M_n - 2 log_{1/p} n ≥ b) ≤ p ^ b`.

Source: Arratia and Waterman (1985), Theorem 2. -/
public theorem_wanted prob_longestMatch_sub_ge_le [Countable α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z)
    (hp₀ : 0 < matchProb P Z) (hp₁ : matchProb P Z < 1) (b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    P.real {ω | b ≤ (M Z n ω : ℝ) - 2 * Real.logb (matchProb P Z)⁻¹ n} ≤ matchProb P Z ^ b

/-- **The Erdős–Rényi law with shifts, second-order window** (Arratia and Waterman 1985,
Theorem 2): for i.i.d. letters from a countable alphabet with measurable singletons, under a
probability measure, with `0 < p = P(X₁ = Y₁) < 1`, for every `ε > 0`, almost surely, for all
large `n`, `-4 - ε < (M_n - 2 log n) / log log n < 1 + ε`, logarithms to base `1 / p`.

Source: Arratia and Waterman (1985), Theorem 2. -/
public theorem_wanted ae_eventually_longestMatch_window [Countable α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z)
    (hp₀ : 0 < matchProb P Z) (hp₁ : matchProb P Z < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      -4 - ε < ((M Z n ω : ℝ) - 2 * Real.logb (matchProb P Z)⁻¹ n) /
          Real.logb (matchProb P Z)⁻¹ (Real.logb (matchProb P Z)⁻¹ n) ∧
        ((M Z n ω : ℝ) - 2 * Real.logb (matchProb P Z)⁻¹ n) /
          Real.logb (matchProb P Z)⁻¹ (Real.logb (matchProb P Z)⁻¹ n) < 1 + ε

/-- **The Erdős–Rényi law with shifts** (Arratia and Waterman 1985, equation (3), a consequence of
Theorem 2): for i.i.d. letters from a countable alphabet with measurable singletons, under a
probability measure, with `0 < p = P(X₁ = Y₁) < 1`, almost surely
`M_n / log_{1/p} n → 2`.

Source: Arratia and Waterman (1985), equation (3) and Theorem 2. -/
public theorem_wanted ae_tendsto_longestMatch_div_log [Countable α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z)
    (hp₀ : 0 < matchProb P Z) (hp₁ : matchProb P Z < 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (M Z n ω : ℝ) / Real.logb (matchProb P Z)⁻¹ n) atTop
      (nhds 2)

end WantedExt.Biology.ComputationalBiology.LongestMatchShiftsWanted
