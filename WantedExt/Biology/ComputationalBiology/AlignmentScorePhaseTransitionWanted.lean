/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The linear–logarithmic phase transition for local alignment scores

Arratia and Waterman (1994): let `A₁, A₂, …` and `B₁, B₂, …` be letters from a finite or countable
alphabet, all independent and identically distributed. An alignment of two words matches some of
their letters in order; its score is the number of matched equal letters, minus `μ` times the
number of matched unequal letters, minus `δ` times the number of letters left unmatched
(deleted). `S(I, J)` is the best score of an alignment of `I` and `J`; `S_t = S(A₁…A_t, B₁…B_t)`
is the global score and `M_n` the best score over all pairs of contiguous regions of `A₁…A_n` and
`B₁…B_n` (p.201). By superadditivity `E S_t / t` converges to `a(μ, δ) = sup_t E S_t / t`, and
`S_t / t → a(μ, δ)` almost surely. With `r(q) = lim -(1/k) log P(S_k ≥ q k) = inf_k -(1/k) log
P(S_k ≥ q k)` (equation (7)) and `b = max_{q ≥ 0} q / r(q)` (equation (8)):

* Lemma 3: if `a(μ, δ) > 0` then `M_n / n → a(μ, δ)` and `S_n / n → a(μ, δ)` in probability;
* Lemma 2: if `a(μ, δ) < 0` then `P((1 - ε) b < M_n / log n < (2 + ε) b) → 1` for every `ε > 0`;
* Theorem 2: for `q > a(μ, δ)`, `r(q) > 0`.

Theorem 1 (a phase transition between linear growth for small penalties and logarithmic growth for
large ones) is the combination of these lemmas, as the paper says. Here the penalties are finite,
`0 ≤ μ, δ < ∞`; the paper also allows `∞` (forbidding mismatches or deletions). `r(q)` is used
for `q ≤ 1`: for `q > 1`, `P(S_k ≥ q k) = 0` and `r(q) = ∞`, which contributes `0` to `b`, and for
`0 ≤ q ≤ 1` the probability is at least `P(A₁ = B₁) ^ k > 0`. Not recorded here: Lemma 1 (the set
`{a = 0}` "defines a line" separating `{a < 0}` from `{a > 0}`), whose notion of line the paper
does not make precise, and the extensions to general scoring and Markov letters. Logarithms are
natural. As in `LongestMatchShiftsWanted`, letters are indexed from `1`, and the shared
`SequenceComparisonShared.IIDLetters` assumes nothing about the unused letters at index `0`.

Sources: R. Arratia and M. S. Waterman, "A phase transition for the score in matching random
sequences allowing deletions", Annals of Applied Probability 4 (1994) 200–225,
doi:10.1214/aoap/1177005208, pp. 201–210, equations (7)–(9), (14), Lemmas 2 and 3, Theorems 1 and
2.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.ComputationalBiology.SequenceComparisonShared
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.AlignmentScorePhaseTransitionWanted

open MeasureTheory ProbabilityTheory Filter Topology
open WantedExt.Biology.ComputationalBiology.SequenceComparisonShared (IIDLetters)

section Score

variable {α : Type*}

/-- `P` is an **alignment** of words of lengths `a` and `b`: a set of index pairs `(i, j)` with
`i < a`, `j < b`, strictly increasing in both coordinates (any two distinct pairs are ordered the
same way in both). -/
def IsAlignment (a b : ℕ) (P : Finset (ℕ × ℕ)) : Prop :=
  (∀ x ∈ P, x.1 < a ∧ x.2 < b) ∧
    ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (x.1 < y.1 ∧ x.2 < y.2) ∨ (y.1 < x.1 ∧ y.2 < x.2)

open Classical in
/-- The score of the alignment `P` of `I` and `J`: matched equal letters count `+1`, matched
unequal letters `-μ`, and each of the `|I| + |J| - 2 |P|` unmatched letters `-δ`. -/
noncomputable def alignScore (μ δ : ℝ) (I J : List α) (P : Finset (ℕ × ℕ)) : ℝ :=
  ((P.filter fun x => I[x.1]? = J[x.2]?).card : ℝ) -
    μ * (P.filter fun x => I[x.1]? ≠ J[x.2]?).card -
    δ * ((I.length + J.length : ℕ) - 2 * P.card : ℝ)

/-- **Optimal alignment score.** `S(I, J)`, the largest score of an alignment of `I` and `J` (a
finite, nonempty set of values; the empty alignment is allowed). `Cslib.Algorithms.Lean.nwScore`
is the integer-valued counterpart, over alignments written as column lists; here the penalties
`μ` and `δ` are real. -/
noncomputable def optScore (μ δ : ℝ) (I J : List α) : ℝ :=
  sSup (alignScore μ δ I J '' {P | IsAlignment I.length J.length P})

/-- The word `X_{i+1} … X_{i+len}`. -/
def window (X : ℕ → α) (i len : ℕ) : List α :=
  (List.range len).map fun k => X (i + 1 + k)

/-- **Local score.** `M_n`, the best optimal score over pairs of contiguous regions
`X_{i+1} … X_{i+l}` and `Y_{j+1} … Y_{j+l'}` of the first `n` letters (`i + l ≤ n`,
`j + l' ≤ n`). `Cslib.Algorithms.Lean.localScore` is the integer-valued counterpart, the largest
`nwScore` over pairs of infixes. -/
noncomputable def localScore (μ δ : ℝ) (X Y : ℕ → α) (n : ℕ) : ℝ :=
  sSup ((fun c : ℕ × ℕ × ℕ × ℕ => optScore μ δ (window X c.1 c.2.1) (window Y c.2.2.1 c.2.2.2)) ''
    {c | c.1 + c.2.1 ≤ n ∧ c.2.2.1 + c.2.2.2 ≤ n})

end Score

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The global score `S_t(ω) = S(A₁ … A_t, B₁ … B_t)`. -/
noncomputable def globalScore (μ δ : ℝ) (Z : ℕ ⊕ ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  optScore μ δ (window (fun i => Z (Sum.inl i) ω) 0 t) (window (fun j => Z (Sum.inr j) ω) 0 t)

/-- The local score `M_n(ω)` of the letters at the outcome `ω`. -/
noncomputable def M (μ δ : ℝ) (Z : ℕ ⊕ ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  localScore μ δ (fun i => Z (Sum.inl i) ω) (fun j => Z (Sum.inr j) ω) n

/-- **Growth constant.** `a(μ, δ) = sup_{t ≥ 1} E S_t / t`, with `E` the Bochner integral: the
ordinary expectation of an integrable `S_t`, and `0` otherwise. -/
noncomputable def growthConst (P : Measure Ω) (μ δ : ℝ) (Z : ℕ ⊕ ℕ → Ω → α) : ℝ :=
  ⨆ t : ℕ, (∫ ω, globalScore μ δ Z (t + 1) ω ∂P) / (t + 1)

/-- **Rate function.** `r(q) = inf_{k ≥ 1} -(1/k) log P(S_k ≥ q k)` (equation (7)), used for
`0 ≤ q ≤ 1`. For i.i.d. letters from a countable alphabet with measurable singletons, under a
probability measure, every probability in it is then at least `P(A₁ = B₁) ^ k > 0`. For `q > 1`
and `μ, δ ≥ 0` they vanish (`S_k ≤ k`), and `Real.log 0 = 0` makes `rate` `0` there instead of the
source's `∞`. -/
noncomputable def rate (P : Measure Ω) (μ δ : ℝ) (Z : ℕ ⊕ ℕ → Ω → α) (q : ℝ) : ℝ :=
  ⨅ k : ℕ, -Real.log (P.real {ω | q * (k + 1) ≤ globalScore μ δ Z (k + 1) ω}) / (k + 1)

/-- **Logarithmic coefficient.** `b = max_{q ≥ 0} q / r(q)` (equation (8)), the supremum over
`0 < q ≤ 1` (larger `q` have `r(q) = ∞`). With Lean's `x / 0 = 0`, a `q` with `r(q) = 0`
contributes `0`; when `a(μ, δ) < 0`, as in the logarithmic regime, `r(q) > 0` for these `q`
(Theorem 2). -/
noncomputable def logCoeff (P : Measure Ω) (μ δ : ℝ) (Z : ℕ ⊕ ℕ → Ω → α) : ℝ :=
  sSup ((fun q => q / rate P μ δ Z q) '' Set.Ioc 0 1)

/-- **The growth constant exists** (Arratia and Waterman 1994, p.201, by superadditivity): for
i.i.d. letters from a countable alphabet with measurable singletons, under a probability measure,
and finite penalties `0 ≤ μ`, `0 ≤ δ`, `E S_t / t → a(μ, δ)` and `S_t / t → a(μ, δ)` almost
surely.

Source: Arratia and Waterman (1994), p.201. -/
public theorem_wanted tendsto_globalScore_div [Countable α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z)
    (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) :
    Tendsto (fun t : ℕ => (∫ ω, globalScore μ δ Z t ω ∂P) / t) atTop
        (𝓝 (growthConst P μ δ Z)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => globalScore μ δ Z t ω / t) atTop
        (𝓝 (growthConst P μ δ Z))

/-- **Linear regime** (Arratia and Waterman 1994, Lemma 3): for i.i.d. letters from a countable
alphabet with measurable singletons, under a probability measure, and finite penalties
`0 ≤ μ`, `0 ≤ δ`, if `a(μ, δ) > 0` then `M_n / n → a(μ, δ)` and `S_n / n → a(μ, δ)` in
probability.

Source: Arratia and Waterman (1994), Lemma 3 and equation (14). -/
public theorem_wanted tendstoInMeasure_localScore_div [Countable α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z)
    (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) (ha : 0 < growthConst P μ δ Z) :
    TendstoInMeasure P (fun n ω => M μ δ Z n ω / n) atTop
        (fun _ => growthConst P μ δ Z) ∧
      TendstoInMeasure P (fun n ω => globalScore μ δ Z n ω / n) atTop
        (fun _ => growthConst P μ δ Z)

/-- **Logarithmic regime** (Arratia and Waterman 1994, Lemma 2): for i.i.d. letters from a
countable alphabet with measurable singletons, under a probability measure, and finite penalties
`0 ≤ μ`, `0 ≤ δ`, if `a(μ, δ) < 0` then for every `ε > 0`,
`P((1 - ε) b < M_n / log n < (2 + ε) b) → 1`, where `b = max_{q ≥ 0} q / r(q)`.

Source: Arratia and Waterman (1994), Lemma 2 and equation (9). -/
public theorem_wanted tendsto_prob_localScore_log_window [Countable α]
    [MeasurableSingletonClass α] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z) (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 ≤ δ)
    (ha : growthConst P μ δ Z < 0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P.real {ω | (1 - ε) * logCoeff P μ δ Z < M μ δ Z n ω / Real.log n ∧
        M μ δ Z n ω / Real.log n < (2 + ε) * logCoeff P μ δ Z}) atTop (𝓝 1)

/-- **Large-deviation rate** (Arratia and Waterman 1994, Theorem 2 and equation (7)): for i.i.d.
letters from a countable alphabet with measurable singletons, under a probability measure, and
finite penalties `0 ≤ μ`, `0 ≤ δ`, for every `q` with `a(μ, δ) < q ≤ 1` and `0 ≤ q`,
`-(1/k) log P(S_k ≥ q k)` converges to `r(q)` and `r(q) > 0`.

Source: Arratia and Waterman (1994), Theorem 2 and equation (7). -/
public theorem_wanted rate_pos [Countable α] [MeasurableSingletonClass α] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℕ ⊕ ℕ → Ω → α) (hZ : IIDLetters P Z) (μ δ : ℝ)
    (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hq : growthConst P μ δ Z < q) :
    Tendsto (fun k : ℕ => -Real.log (P.real {ω | q * (k + 1) ≤ globalScore μ δ Z (k + 1) ω}) /
        (k + 1)) atTop (𝓝 (rate P μ δ Z q)) ∧ 0 < rate P μ δ Z q

end WantedExt.Biology.ComputationalBiology.AlignmentScorePhaseTransitionWanted
