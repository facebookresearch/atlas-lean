/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Probability.PaleyZygmund

import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The first and second moment methods

The basic existence tools of probabilistic combinatorics, stated for a real random variable on a
probability space and for a count `X = ∑ᵢ 1_{Aᵢ}` of events:

* `measureReal_one_le_le_integral`: the **first moment method**, `P(X ≥ 1) ≤ E X` for `X ≥ 0`.
* `measureReal_eq_zero_le_variance_div_sq`: the **second moment method**,
  `P(X = 0) ≤ Var X / (E X)²` (Zhao, Lemma 4.8).
* `sq_integral_le_integral_sq_mul_measureReal_pos`: the sharper form
  `(E X)² ≤ E[X²] · P(X > 0)` for `X ≥ 0`, the case `θ = 0` of Paley–Zygmund.
* `variance_sum_indicator_le`: for a count of events with a dependency graph `G` (pairs that are
  not adjacent are independent), `Var X ≤ μ + Δ` with `μ = ∑ P(Aᵢ)` and
  `Δ = ∑_{(i, j) adjacent} P(Aᵢ ∩ Aⱼ)` over ordered pairs.
* `measureReal_forall_not_mem_le`: hence `P(no Aᵢ occurs) ≤ (μ + Δ) / μ²`, the estimate behind
  thresholds for subgraph containment in `G(n, p)` (Zhao, Corollary 4.13).

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Section 4 (https://yufeizhao.com/pm/sp19/pmnotes.pdf).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Probability.Combinatorics.SecondMomentMethod

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **First moment method.** If `X ≥ 0` is integrable, then `P(X ≥ 1) ≤ E X`. For a
nonnegative integer-valued count `X` this says `P(X ≠ 0) ≤ E X`, so `E X → 0` forces `X = 0`
with high probability. It is Mathlib's Markov inequality `mul_meas_ge_le_integral_of_nonneg` at
level `1`, named here as the first moment method (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, proof of Proposition 4.11, via Markov's inequality). -/
theorem measureReal_one_le_le_integral [IsFiniteMeasure μ] {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X)
    (hXi : Integrable X μ) : μ.real {ω | 1 ≤ X ω} ≤ ∫ ω, X ω ∂μ := by
  have h := mul_meas_ge_le_integral_of_nonneg hX0 hXi 1
  simpa using h

/-- **Second moment method.** If `X` is a square-integrable real random variable with
`E X ≠ 0`, then `P(X = 0) ≤ Var X / (E X)²`. The event `X = 0` forces `|X - E X| ≥ |E X|`, so
this is Chebyshev's inequality at distance `|E X|` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Lemma 4.8; the notes state it for nonnegative `X`, an
assumption the proof does not use). -/
theorem measureReal_eq_zero_le_variance_div_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hmean : μ[X] ≠ 0) :
    μ.real {ω | X ω = 0} ≤ variance X μ / (μ[X]) ^ 2 := by
  have hc : 0 < |μ[X]| := abs_pos.mpr hmean
  have hsub : {ω | X ω = 0} ⊆ {ω | |μ[X]| ≤ |X ω - μ[X]|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω, zero_sub, abs_neg]
  have hcheb := meas_ge_le_variance_div_sq hX hc
  rw [sq_abs] at hcheb
  calc μ.real {ω | X ω = 0} ≤ μ.real {ω | |μ[X]| ≤ |X ω - μ[X]|} := measureReal_mono hsub
    _ ≤ variance X μ / (μ[X]) ^ 2 := by
      rw [measureReal_def]
      have hnn : 0 ≤ variance X μ / (μ[X]) ^ 2 :=
        div_nonneg (variance_nonneg X μ) (sq_nonneg _)
      exact ENNReal.toReal_le_of_le_ofReal hnn hcheb

/-- **Second moment method, Cauchy–Schwarz form.** If `X ≥ 0` is square-integrable, then
`(E X)² ≤ E[X²] · P(X > 0)`; equivalently `P(X > 0) ≥ (E X)² / E[X²]` when `E[X²] > 0`. This is
the case `θ = 0` of the Paley–Zygmund inequality `ProbabilityTheory.paley_zygmund`, backported in
this repository from Mathlib PR #40835. -/
theorem sq_integral_le_integral_sq_mul_measureReal_pos [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX0 : 0 ≤ᵐ[μ] X) (hX : MemLp X 2 μ) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ (∫ ω, X ω ^ 2 ∂μ) * μ.real {ω | 0 < X ω} := by
  have h := paley_zygmund hX0 hX le_rfl zero_le_one
  simpa using h

section Counting

variable {ι : Type*} [Fintype ι]

/-- **Number of events that occur.** The count `X = ∑ᵢ 1_{Aᵢ}` of the events `Aᵢ` that occur at
`ω` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Section 4.2). -/
noncomputable def count (A : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω

/-- **Expected number of events.** `μ = ∑ᵢ P(Aᵢ)`, the expectation of the count
`X = ∑ᵢ 1_{Aᵢ}` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
Section 4.2). -/
noncomputable def expectedCount (μ : Measure Ω) (A : ι → Set Ω) : ℝ :=
  ∑ i, μ.real (A i)

/-- **Correlation sum over dependent pairs.** `Δ = ∑ P(Aᵢ ∩ Aⱼ)` over the ordered pairs `(i, j)`
that are adjacent in the dependency graph `G` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Section 4.2, where the sum is over unordered pairs). -/
noncomputable def dependentPairSum (μ : Measure Ω) (A : ι → Set Ω) (G : SimpleGraph ι)
    [DecidableRel G.Adj] : ℝ :=
  ∑ i, ∑ j, if G.Adj i j then μ.real (A i ∩ A j) else 0

private lemma memLp_indicator_one (A : Set Ω) (hA : MeasurableSet A) [IsFiniteMeasure μ] :
    MemLp (A.indicator (fun _ => (1 : ℝ))) 2 μ :=
  (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet

private lemma memLp_count [IsFiniteMeasure μ] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (count A) 2 μ := by
  unfold count
  exact memLp_finsetSum Finset.univ (fun i _ => memLp_indicator_one (μ := μ) (A i) (hA i))

private lemma integral_count [IsFiniteMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, count A ω ∂μ = expectedCount μ A := by
  unfold count expectedCount
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact integral_indicator_one (hA i)
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hA i)

private lemma count_sq (A : ι → Set Ω) :
    (count A) ^ 2 = fun ω => ∑ i, ∑ j, (A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω := by
  funext ω
  simp only [count, Pi.pow_apply, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have h := congrFun (Set.inter_indicator_one (s := A i) (t := A j) (M₀ := ℝ)) ω
  simpa [Pi.one_def] using h.symm

private lemma integral_count_sq [IsFiniteMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    μ[(count A) ^ 2] = ∑ i, ∑ j, μ.real (A i ∩ A j) := by
  rw [count_sq]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun j _ => integral_indicator_one ((hA i).inter (hA j)))
    · intro j _
      exact (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j))
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j)))

/-- **Variance of a count of events with a dependency graph.** Let `G` be a graph on the index
set such that `P(Aᵢ ∩ Aⱼ) = P(Aᵢ) P(Aⱼ)` whenever `i ≠ j` are not adjacent. Then the count
`X = ∑ᵢ 1_{Aᵢ}` satisfies `Var X ≤ μ + Δ`, where `μ = ∑ᵢ P(Aᵢ) = E X` and `Δ` is the sum of
`P(Aᵢ ∩ Aⱼ)` over ordered adjacent pairs (Y. Zhao, *The Probabilistic Method in Combinatorics*,
MIT 18.218 notes, 2019, Section 4.2, the computation `var(X) ≤ E[X] + Δ` before Corollary 4.13;
there `Δ` is written over unordered pairs, which undercounts the covariance sum by a factor `2`,
and the ordered-pair `Δ` used here is the one for which the bound holds). Only pairwise
independence of non-adjacent events is used. -/
theorem variance_sum_indicator_le [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hind : ∀ i j, i ≠ j → ¬ G.Adj i j → μ.real (A i ∩ A j) = μ.real (A i) * μ.real (A j)) :
    variance (count A) μ ≤ expectedCount μ A + dependentPairSum μ A G := by
  classical
  rw [variance_eq_sub (memLp_count A hA), integral_count_sq A hA, integral_count A hA]
  -- split each inner term according to `i = j`, adjacency, or independence
  have hterm : ∀ i j, μ.real (A i ∩ A j) ≤
      (if i = j then μ.real (A i) else 0) +
        (if G.Adj i j then μ.real (A i ∩ A j) else 0) + μ.real (A i) * μ.real (A j) := by
    intro i j
    have hpos : 0 ≤ μ.real (A i) * μ.real (A j) := mul_nonneg measureReal_nonneg measureReal_nonneg
    by_cases hij : i = j
    · subst hij
      simp only [Set.inter_self, ite_true, G.loopless.irrefl i, ite_false]
      linarith
    · by_cases hadj : G.Adj i j
      · simp only [hij, hadj, ite_true, ite_false]
        linarith
      · simp only [hij, hadj, ite_false]
        rw [hind i j hij hadj]
        linarith
  have hsum : ∑ i, ∑ j, μ.real (A i ∩ A j) ≤
      ∑ i, ∑ j, ((if i = j then μ.real (A i) else 0) +
        (if G.Adj i j then μ.real (A i ∩ A j) else 0) + μ.real (A i) * μ.real (A j)) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
  have hsplit : ∑ i, ∑ j, ((if i = j then μ.real (A i) else 0) +
        (if G.Adj i j then μ.real (A i ∩ A j) else 0) + μ.real (A i) * μ.real (A j)) =
      expectedCount μ A + dependentPairSum μ A G + expectedCount μ A ^ 2 := by
    simp only [Finset.sum_add_distrib, expectedCount, dependentPairSum, sq, Finset.sum_mul_sum]
    congr 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  linarith

/-- **Second moment method for counts of events.** Let `G` be a dependency graph for the
events `Aᵢ` in the pairwise sense of `variance_sum_indicator_le`, let `μ = ∑ᵢ P(Aᵢ) > 0` and let
`Δ` be the sum of `P(Aᵢ ∩ Aⱼ)` over ordered adjacent pairs. Then
`P(no Aᵢ occurs) ≤ (μ + Δ) / μ²`. In particular, along a sequence with `μ → ∞` and `Δ = o(μ²)`
some `Aᵢ` occurs with high probability (Y. Zhao, *The Probabilistic Method in Combinatorics*,
MIT 18.218 notes, 2019, Lemma 4.8 and Corollary 4.13). -/
theorem measureReal_forall_not_mem_le [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hind : ∀ i j, i ≠ j → ¬ G.Adj i j → μ.real (A i ∩ A j) = μ.real (A i) * μ.real (A j))
    (hμ : 0 < expectedCount μ A) :
    μ.real {ω | ∀ i, ω ∉ A i} ≤
      (expectedCount μ A + dependentPairSum μ A G) / expectedCount μ A ^ 2 := by
  have hmean : μ[count A] = expectedCount μ A := integral_count A hA
  have hset : {ω | ∀ i, ω ∉ A i} = {ω | count A ω = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, count]
    constructor
    · intro h
      exact Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (h i) _)
    · intro h i hi
      have hle : (A i).indicator (fun _ => (1 : ℝ)) ω ≤ ∑ j, (A j).indicator (fun _ => (1 : ℝ)) ω :=
        Finset.single_le_sum (f := fun j => (A j).indicator (fun _ => (1 : ℝ)) ω)
          (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) (Finset.mem_univ i)
      rw [h, Set.indicator_of_mem hi] at hle
      linarith
  rw [hset]
  have h2 := measureReal_eq_zero_le_variance_div_sq (memLp_count (μ := μ) A hA)
    (by rw [hmean]; exact hμ.ne')
  rw [hmean] at h2
  calc μ.real {ω | count A ω = 0} ≤ variance (count A) μ / expectedCount μ A ^ 2 := h2
    _ ≤ (expectedCount μ A + dependentPairSum μ A G) / expectedCount μ A ^ 2 :=
      div_le_div_of_nonneg_right (variance_sum_indicator_le A hA G hind) (sq_nonneg _)

end Counting

end MathlibExt.Probability.Combinatorics.SecondMomentMethod
