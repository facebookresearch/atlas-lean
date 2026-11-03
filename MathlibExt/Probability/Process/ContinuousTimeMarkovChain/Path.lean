/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProductMeasure
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Semigroup
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.StrongLaw
import MathlibExt.Probability.Distributions.ExponentialMoments

/-!
# Finite continuous-time Markov chains as path processes

For a rate matrix `Q` on a finite state space `ι`, with exit rates `q i = -Q i i`, this file
builds the continuous-time Markov chain with generator `Q` as an explicit path process, by the
jump chain / holding time construction of Norris (1997, §2.6).

The randomness is an i.i.d. sequence of *steps* `ω n = (ξ n, E n)`, under the product measure
`ctmcInputMeasure hQ` on `ℕ → (ι → ι) × ℝ`:

* `ξ n : ι → ι` is a random map whose coordinates are independent, with `ξ n i` distributed
  according to row `i` of the jump matrix `Π` (`ctmcJumpMatrix`): `Π i j = Q i j / q i` for
  `j ≠ i` when `q i ≠ 0`, and `Π i = δ_i` (the state is absorbing) when `q i = 0`;
* `E n` is an exponential clock of rate `1`, independent of `ξ n`.

From a starting state `i`, the jump chain is `Y 0 = i`, `Y (n + 1) = ξ n (Y n)`; the holding
times are `S n = E n / q (Y n)` (and `S n = ∞` when `q (Y n) = 0`), valued in `ℝ≥0∞`; the jump
times are `T n = S 0 + ⋯ + S (n - 1)`; and the path is `X t = Y n` for `T n ≤ t < T (n + 1)`.
Using one random map per step, rather than one jump per step, makes every `Y n` a measurable
function of the first `n` steps; since `ξ n` is independent of the first `n` steps, the next
state is drawn from row `Y n` of `Π`.

## Main definitions

* `ProbabilityTheory.ctmcJumpMatrix Q`: the jump matrix `Π` of `Q` (Norris 1997, §2.6).
* `ProbabilityTheory.ctmcInputMeasure hQ`: the law of the i.i.d. step sequence.
* `ProbabilityTheory.ctmcJumpChain`, `ctmcHoldingTime`, `ctmcJumpTime`: `Y`, `S` and `T`.
* `ProbabilityTheory.ctmcPath Q i ω t`: the state `X t` of the chain started at `i`.

## Main results

* `IsRateMatrix.ctmcJumpMatrix_mem_rowStochastic`: `Π` is a stochastic matrix.
* `ctmcPath_eq_ite`, `ctmcPath_jumpTime_add`: first-jump decomposition, and the path after a
  finite jump time `T n` is the path started at `Y n` driven by the shifted steps
  (deterministic identities).
* `measurable_ctmcPath_uncurry`: `(t, ω) ↦ X t` is jointly measurable.
* `IsRateMatrix.ae_tendsto_ctmcJumpTime`: **non-explosion**, `T n → ∞` almost surely.
* `IsRateMatrix.ctmcInputMeasure_ctmcPath_jumpTime_add`: the **strong Markov property at jump
  times**: given the first `n` steps (which determine `Y 0, …, Y n` and `S 0, …, S (n - 1)`),
  on `{T n < ∞, Y n = k}` the path after `T n` is distributed as the chain started at `k`.
* `IsRateMatrix.ctmcInputMeasure_real_ctmcPath_eq`: **Kolmogorov**,
  `P_i(X t = j) = exp (t Q) i j`.
* `IsRateMatrix.ctmcInputMeasure_real_ctmcPath_add`: the **restart law at a fixed time** `s`:
  `P_i(X s = k, X (s + ·) ∈ B) = exp (s Q) i k * P_k(X ∈ B)`. This is not the full Markov
  property: events of the path before `s` (the natural filtration at time `s`) are not covered,
  and no conditional-expectation form is stated.
* `IsRateMatrix.ctmcInputMeasure_real_ctmcPath_fdd`: the **finite-dimensional distributions**
  are products of transition matrices over the time increments.

## Proof outline

Both the Kolmogorov identity and the fixed-time restart law are proved by a renewal
argument. Conditioning on the first step (whose law is a product with the law of the remaining
steps) gives a renewal equation in the time variable; the matrix exponential satisfies the same
equation (integrate the Kolmogorov backward equation against the exponential density); and a
bounded solution of the homogeneous renewal equation vanishes, because each exit rate is at
most a fixed `c`, so a holding time is shorter than `1 / c` with probability at most `1 - e⁻¹`.
The memoryless property of the exponential clocks supplies the restart at a fixed time.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.6–2.8.
* T. M. Liggett, *Continuous Time Markov Processes: An Introduction*, AMS, 2010, ch. 2.
-/

@[expose] public section

open Finset MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **jump matrix** `Π` of a matrix `Q` (Norris 1997, §2.6): for a state with exit rate
`q i = -Q i i ≠ 0`, `Π i j = Q i j / q i` for `j ≠ i` and `Π i i = 0`; a state with `q i = 0`
is absorbing, `Π i j = δ i j`. -/
noncomputable def ctmcJumpMatrix (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ := fun i j =>
  if Q i i = 0 then (if i = j then 1 else 0) else if i = j then 0 else Q i j / -Q i i

namespace IsRateMatrix

variable {Q : Matrix ι ι ℝ}

/-- The entries of the jump matrix of a rate matrix are nonnegative. -/
theorem ctmcJumpMatrix_nonneg (hQ : IsRateMatrix Q) (i j : ι) : 0 ≤ ctmcJumpMatrix Q i j := by
  unfold ctmcJumpMatrix
  have hq : 0 ≤ -Q i i := neg_nonneg.mpr (hQ.diag_nonpos i)
  split_ifs with h0 hij hij
  · norm_num
  · norm_num
  · norm_num
  · exact div_nonneg (hQ.nonneg_of_ne hij) hq

/-- The rows of the jump matrix of a rate matrix sum to `1`. -/
theorem sum_ctmcJumpMatrix (hQ : IsRateMatrix Q) (i : ι) : ∑ j, ctmcJumpMatrix Q i j = 1 := by
  by_cases h0 : Q i i = 0
  · simp [ctmcJumpMatrix, h0]
  · have hne : -Q i i ≠ 0 := neg_ne_zero.mpr h0
    have hd := hQ.diag_eq i
    have hs : ∑ j ∈ univ.erase i, ctmcJumpMatrix Q i j = ∑ j ∈ univ.erase i, Q i j / -Q i i :=
      sum_congr rfl fun j hj => by simp [ctmcJumpMatrix, h0, (ne_of_mem_erase hj).symm]
    have hii : ctmcJumpMatrix Q i i = 0 := by simp [ctmcJumpMatrix, h0]
    rw [← add_sum_erase _ _ (mem_univ i), hs, ← sum_div, hii, zero_add, div_eq_one_iff_eq hne]
    linarith

/-- The jump matrix of a rate matrix is row-stochastic. -/
theorem ctmcJumpMatrix_mem_rowStochastic (hQ : IsRateMatrix Q) :
    ctmcJumpMatrix Q ∈ Matrix.rowStochastic ℝ ι :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨hQ.ctmcJumpMatrix_nonneg, hQ.sum_ctmcJumpMatrix⟩

/-- Row `i` of the jump matrix of a rate matrix, as a probability mass function on `ι`. -/
noncomputable def ctmcJumpPMF (hQ : IsRateMatrix Q) (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (ctmcJumpMatrix Q i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hQ.ctmcJumpMatrix_nonneg i j,
      hQ.sum_ctmcJumpMatrix i, ENNReal.ofReal_one])

end IsRateMatrix

section Measure

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] {Q : Matrix ι ι ℝ}

/-- The law of one step `(ξ, E)` of the construction: `ξ : ι → ι` has independent coordinates
with `ξ i ∼ Π i`, and `E` is an independent exponential clock of rate `1`. -/
noncomputable def ctmcStepMeasure (hQ : IsRateMatrix Q) : Measure ((ι → ι) × ℝ) :=
  (Measure.pi fun i => (hQ.ctmcJumpPMF i).toMeasure).prod (expMeasure 1)

/-- The step law is a probability measure. -/
instance (hQ : IsRateMatrix Q) : IsProbabilityMeasure (ctmcStepMeasure hQ) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  unfold ctmcStepMeasure
  infer_instance

/-- The law of the i.i.d. step sequence `ω : ℕ → (ι → ι) × ℝ` driving the chain. -/
noncomputable def ctmcInputMeasure (hQ : IsRateMatrix Q) : Measure (ℕ → (ι → ι) × ℝ) :=
  Measure.infinitePi fun _ => ctmcStepMeasure hQ

/-- The law of the step sequence is a probability measure. -/
instance (hQ : IsRateMatrix Q) : IsProbabilityMeasure (ctmcInputMeasure hQ) := by
  unfold ctmcInputMeasure
  infer_instance

end Measure

section Path

variable {ι : Type*} {Q : Matrix ι ι ℝ}

/-- The **jump chain** started at `i`: `Y 0 = i` and `Y (n + 1) = ξ n (Y n)`. -/
def ctmcJumpChain (i : ι) (ω : ℕ → (ι → ι) × ℝ) : ℕ → ι
  | 0 => i
  | n + 1 => (ω n).1 (ctmcJumpChain i ω n)

/-- The `n`-th **holding time** `S n = E n / q (Y n)`, where `q k = -Q k k`; it is `∞` when
`Y n` is absorbing (`q (Y n) = 0`). Negative clock values, a null event, give `S n = 0`. -/
noncomputable def ctmcHoldingTime (Q : Matrix ι ι ℝ) (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n : ℕ) :
    ℝ≥0∞ :=
  if Q (ctmcJumpChain i ω n) (ctmcJumpChain i ω n) = 0 then ∞
  else ENNReal.ofReal ((ω n).2 / -Q (ctmcJumpChain i ω n) (ctmcJumpChain i ω n))

/-- The `n`-th **jump time** `T n = S 0 + ⋯ + S (n - 1)`, with `T 0 = 0`. -/
noncomputable def ctmcJumpTime (Q : Matrix ι ι ℝ) (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n : ℕ) :
    ℝ≥0∞ :=
  ∑ k ∈ range n, ctmcHoldingTime Q i ω k

open scoped Classical in
/-- The **path** of the chain started at `i`: `X t = Y n` for the `n` with
`T n ≤ t < T (n + 1)`. If `t` is at or after the explosion time `sup T n` (a null event, by
`IsRateMatrix.ae_tendsto_ctmcJumpTime`), the value is an arbitrary state that does not depend
on `i`, `Q` or `ω`. -/
noncomputable def ctmcPath (Q : Matrix ι ι ℝ) (i : ι) (ω : ℕ → (ι → ι) × ℝ) (t : ℝ≥0) : ι :=
  haveI : Nonempty ι := ⟨i⟩
  if h : ∃ n, (t : ℝ≥0∞) < ctmcJumpTime Q i ω (n + 1) then ctmcJumpChain i ω (Nat.find h)
  else Classical.ofNonempty

/-- The shift of the step sequence by `n`: `(shift n ω) m = ω (n + m)`. -/
def ctmcShift (n : ℕ) (ω : ℕ → (ι → ι) × ℝ) : ℕ → (ι → ι) × ℝ := fun m => ω (n + m)

/-- The jump times are nondecreasing. -/
theorem ctmcJumpTime_mono (i : ι) (ω : ℕ → (ι → ι) × ℝ) : Monotone (ctmcJumpTime Q i ω) := by
  intro m n hmn
  exact sum_le_sum_of_subset (range_mono hmn)

/-- If `T n ≤ t < T (n + 1)`, then `X t = Y n`. -/
theorem ctmcPath_eq_of_mem (i : ι) (ω : ℕ → (ι → ι) × ℝ) {t : ℝ≥0} {n : ℕ}
    (h₁ : ctmcJumpTime Q i ω n ≤ t) (h₂ : (t : ℝ≥0∞) < ctmcJumpTime Q i ω (n + 1)) :
    ctmcPath Q i ω t = ctmcJumpChain i ω n := by
  classical
  have h : ∃ n, (t : ℝ≥0∞) < ctmcJumpTime Q i ω (n + 1) := ⟨n, h₂⟩
  simp only [ctmcPath, h, dite_true]
  congr 1
  refine le_antisymm (Nat.find_min' h h₂) (not_lt.mp fun hlt => ?_)
  have := Nat.find_spec h
  have hmono := ctmcJumpTime_mono (Q := Q) i ω (Nat.succ_le_of_lt hlt)
  exact absurd (lt_of_lt_of_le this hmono) (not_lt.mpr h₁)

/-- The jump chain of the shifted steps started at `Y n` is the jump chain after `n`. -/
theorem ctmcJumpChain_shift (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n m : ℕ) :
    ctmcJumpChain (ctmcJumpChain i ω n) (ctmcShift n ω) m = ctmcJumpChain i ω (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ctmcJumpChain, ih, ctmcShift]

/-- The holding times of the shifted steps started at `Y n` are the holding times after `n`. -/
theorem ctmcHoldingTime_shift (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n m : ℕ) :
    ctmcHoldingTime Q (ctmcJumpChain i ω n) (ctmcShift n ω) m =
      ctmcHoldingTime Q i ω (n + m) := by
  simp only [ctmcHoldingTime, ctmcJumpChain_shift, ctmcShift]

/-- `T (n + m) = T n + T' m`, where `T'` are the jump times of the shifted steps started at
`Y n`. -/
theorem ctmcJumpTime_add (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n m : ℕ) :
    ctmcJumpTime Q i ω (n + m) =
      ctmcJumpTime Q i ω n + ctmcJumpTime Q (ctmcJumpChain i ω n) (ctmcShift n ω) m := by
  simp only [ctmcJumpTime, sum_range_add, ctmcHoldingTime_shift]

/-- After a finite jump time `T n`, the path is the path started at `Y n` driven by the
shifted steps: `X (T n + s) = X' s` with `X'` built from `shift n ω` started at `Y n`. -/
theorem ctmcPath_jumpTime_add (i : ι) (ω : ℕ → (ι → ι) × ℝ) (n : ℕ)
    (hn : ctmcJumpTime Q i ω n ≠ ∞) (s : ℝ≥0) :
    ctmcPath Q i ω ((ctmcJumpTime Q i ω n).toNNReal + s) =
      ctmcPath Q (ctmcJumpChain i ω n) (ctmcShift n ω) s := by
  classical
  set a := ctmcJumpTime Q i ω n with ha
  set T' := ctmcJumpTime Q (ctmcJumpChain i ω n) (ctmcShift n ω) with hT'
  have hcoe : ((a.toNNReal + s : ℝ≥0) : ℝ≥0∞) = a + s := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hn]
  have key : ∀ k, (a + s < ctmcJumpTime Q i ω (k + 1)) ↔
      n ≤ k ∧ (s : ℝ≥0∞) < T' (k - n + 1) := by
    intro k
    constructor
    · intro hk
      have hnk : n ≤ k := by
        by_contra h
        have := ctmcJumpTime_mono (Q := Q) i ω (show k + 1 ≤ n by omega)
        exact absurd (lt_of_lt_of_le hk this) (not_lt.mpr le_self_add)
      refine ⟨hnk, ?_⟩
      rwa [show k + 1 = n + (k - n + 1) by omega, ctmcJumpTime_add,
        ENNReal.add_lt_add_iff_left hn] at hk
    · rintro ⟨hnk, hk⟩
      rwa [show k + 1 = n + (k - n + 1) by omega, ctmcJumpTime_add,
        ENNReal.add_lt_add_iff_left hn]
  unfold ctmcPath
  simp only [hcoe]
  by_cases h' : ∃ m, (s : ℝ≥0∞) < T' (m + 1)
  · have h : ∃ k, a + s < ctmcJumpTime Q i ω (k + 1) := by
      obtain ⟨m, hm⟩ := h'
      exact ⟨n + m, (key _).2 ⟨by omega, by simpa using hm⟩⟩
    rw [dite_eq_left h, dite_eq_left h']
    have hfind : Nat.find h = n + Nat.find h' := by
      rw [Nat.find_eq_iff]
      refine ⟨(key _).2 ⟨by omega, by simpa using Nat.find_spec h'⟩, fun k hk hP => ?_⟩
      obtain ⟨hnk, hP'⟩ := (key k).1 hP
      exact Nat.find_min h' (show k - n < Nat.find h' by omega) hP'
    rw [hfind, ctmcJumpChain_shift]
  · have h : ¬∃ k, a + s < ctmcJumpTime Q i ω (k + 1) := by
      rintro ⟨k, hk⟩
      exact h' ⟨k - n, ((key k).1 hk).2⟩
    rw [dite_eq_right h, dite_eq_right h']

/-- The holding time at the start state `i` as a function of one step `(ξ, E)`:
`E / q i`, or `∞` when `q i = 0`. -/
private noncomputable def firstHold (Q : Matrix ι ι ℝ) (i : ι) (a : (ι → ι) × ℝ) : ℝ≥0∞ :=
  if Q i i = 0 then ∞ else ENNReal.ofReal (a.2 / -Q i i)

/-- **First-jump decomposition** of the path: before the first holding time the chain is at
`i`; afterwards it is the chain started at `ξ 0 i` driven by the shifted steps. -/
theorem ctmcPath_eq_ite (i : ι) (ω : ℕ → (ι → ι) × ℝ) (t : ℝ≥0) :
    ctmcPath Q i ω t = if (t : ℝ≥0∞) < ctmcHoldingTime Q i ω 0 then i
      else ctmcPath Q ((ω 0).1 i) (ctmcShift 1 ω) (t - (ctmcHoldingTime Q i ω 0).toNNReal) := by
  have hT1 : ctmcJumpTime Q i ω 1 = ctmcHoldingTime Q i ω 0 := by simp [ctmcJumpTime]
  split_ifs with h
  · exact ctmcPath_eq_of_mem (n := 0) i ω (by simp [ctmcJumpTime]) (by rwa [hT1])
  · push Not at h
    have hfin : ctmcHoldingTime Q i ω 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    have hle : (ctmcHoldingTime Q i ω 0).toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact h
    have := ctmcPath_jumpTime_add (Q := Q) i ω 1 (by rwa [hT1])
      (t - (ctmcHoldingTime Q i ω 0).toNNReal)
    rw [hT1, add_tsub_cancel_of_le hle] at this
    exact this

/-- Prepend a step to a step sequence: `cons a ω 0 = a`, `cons a ω (n + 1) = ω n`. -/
private def ctmcCons (a : (ι → ι) × ℝ) (ω : ℕ → (ι → ι) × ℝ) : ℕ → (ι → ι) × ℝ
  | 0 => a
  | n + 1 => ω n

private lemma ctmcShift_one_ctmcCons (a : (ι → ι) × ℝ) (ω : ℕ → (ι → ι) × ℝ) :
    ctmcShift 1 (ctmcCons a ω) = ω := by
  funext m
  simp only [ctmcShift, Nat.add_comm 1 m]
  rfl

/-- Before the first jump, the path from time `s` on is the path driven by the same steps
with the first clock reduced by `q i * s` (the memoryless property of the construction). -/
private lemma ctmcPath_ctmcCons_add (i : ι) (a : (ι → ι) × ℝ) (ω : ℕ → (ι → ι) × ℝ)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < firstHold Q i a) (u : ℝ≥0) :
    ctmcPath Q i (ctmcCons a ω) (s + u) =
      ctmcPath Q i (ctmcCons (a.1, a.2 - -Q i i * s) ω) u := by
  set F := firstHold Q i a with hF
  have hF' : firstHold Q i (a.1, a.2 - -Q i i * s) = F - s := by
    by_cases h0 : Q i i = 0
    · simp [hF, firstHold, h0]
    · have hq : -Q i i ≠ 0 := neg_ne_zero.mpr h0
      simp only [hF, firstHold, h0, ite_false] at hs ⊢
      rw [← ENNReal.ofReal_coe_nnreal]
      have e : (a.2 - -Q i i * s) / -Q i i = a.2 / -Q i i - s := by field_simp; ring
      exact (congrArg ENNReal.ofReal e).trans (ENNReal.ofReal_sub _ s.2)
  rw [ctmcPath_eq_ite i (ctmcCons a ω) (s + u),
    ctmcPath_eq_ite i (ctmcCons (a.1, a.2 - -Q i i * s) ω) u]
  change (if ((s + u : ℝ≥0) : ℝ≥0∞) < F then i else ctmcPath Q (a.1 i) (ctmcShift 1 (ctmcCons a ω))
      (s + u - F.toNNReal)) = (if (u : ℝ≥0∞) < firstHold Q i (a.1, a.2 - -Q i i * s) then i
      else ctmcPath Q (a.1 i) (ctmcShift 1 (ctmcCons (a.1, a.2 - -Q i i * s) ω))
        (u - (firstHold Q i (a.1, a.2 - -Q i i * s)).toNNReal))
  rw [hF', ctmcShift_one_ctmcCons, ctmcShift_one_ctmcCons]
  have hsF : (s : ℝ≥0∞) ≤ F := hs.le
  have hiff : ((s + u : ℝ≥0) : ℝ≥0∞) < F ↔ (u : ℝ≥0∞) < F - s := by
    rw [ENNReal.coe_add, AddLECancellable.lt_tsub_iff_left ENNReal.cancel_coe]
  by_cases hlt : ((s + u : ℝ≥0) : ℝ≥0∞) < F
  · rw [ite_eq_left hlt, ite_eq_left (hiff.1 hlt)]
  · rw [ite_eq_right hlt, ite_eq_right (mt hiff.2 hlt)]
    have hfin : F ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (not_lt.mp hlt)
    congr 1
    have h1 : F.toNNReal ≤ s + u := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact not_lt.mp hlt
    have h2 : s ≤ F.toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact hsF
    rw [ENNReal.toNNReal_sub ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
    have h3 : F.toNNReal - s ≤ u := tsub_le_iff_left.mpr h1
    apply NNReal.eq
    rw [NNReal.coe_sub h1, NNReal.coe_sub h3, NNReal.coe_sub h2, NNReal.coe_add]
    ring

/-- After the first jump (at or before `s`), the path from time `s` on is the path of the chain
started at `ξ 0 i` driven by the shifted steps, from time `s - S 0` on. -/
private lemma ctmcPath_add_of_le (i : ι) (ω : ℕ → (ι → ι) × ℝ) {s : ℝ≥0}
    (hs : firstHold Q i (ω 0) ≤ s) (u : ℝ≥0) :
    ctmcPath Q i ω (s + u) =
      ctmcPath Q ((ω 0).1 i) (ctmcShift 1 ω) (s - (firstHold Q i (ω 0)).toNNReal + u) := by
  rw [ctmcPath_eq_ite]
  change (if ((s + u : ℝ≥0) : ℝ≥0∞) < firstHold Q i (ω 0) then i else _) = _
  have hnlt : ¬ ((s + u : ℝ≥0) : ℝ≥0∞) < firstHold Q i (ω 0) := by
    rw [not_lt]; exact hs.trans (by exact_mod_cast le_self_add)
  rw [ite_eq_right hnlt]
  have hfin : firstHold Q i (ω 0) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
  have h2 : (firstHold Q i (ω 0)).toNNReal ≤ s := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact hs
  congr 1
  rw [show ctmcHoldingTime Q i ω 0 = firstHold Q i (ω 0) from rfl, tsub_add_eq_add_tsub h2]

section Measurable

variable [Finite ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

/-- The jump chain `Y n` is a measurable function of the steps. -/
theorem measurable_ctmcJumpChain (i : ι) (n : ℕ) :
    Measurable fun ω => ctmcJumpChain i ω n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have he : Measurable fun p : (ι → ι) × ι => p.1 p.2 := Measurable.of_discrete
    exact he.comp (((measurable_pi_apply n).fst).prodMk ih)

/-- The holding time `S n` is a measurable function of the steps. -/
theorem measurable_ctmcHoldingTime (i : ι) (n : ℕ) :
    Measurable fun ω => ctmcHoldingTime Q i ω n := by
  have hY := measurable_ctmcJumpChain i n
  have hq : Measurable fun ω => -Q (ctmcJumpChain i ω n) (ctmcJumpChain i ω n) :=
    (Measurable.of_discrete (f := fun k : ι => -Q k k)).comp hY
  refine Measurable.ite ?_ measurable_const
    (ENNReal.measurable_ofReal.comp (((measurable_pi_apply n).snd).div hq))
  exact hY (DiscreteMeasurableSpace.forall_measurableSet {k : ι | Q k k = 0})

/-- The jump time `T n` is a measurable function of the steps. -/
theorem measurable_ctmcJumpTime (i : ι) (n : ℕ) :
    Measurable fun ω => ctmcJumpTime Q i ω n :=
  Finset.measurable_sum _ fun k _ => measurable_ctmcHoldingTime i k

/-- The path `(t, ω) ↦ X t` is jointly measurable in the time and the steps. -/
theorem measurable_ctmcPath_uncurry (i : ι) :
    Measurable fun p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) => ctmcPath Q i p.2 p.1 := by
  classical
  refine measurable_to_countable' fun j => ?_
  have : Nonempty ι := ⟨i⟩
  have hset : (fun p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) => ctmcPath Q i p.2 p.1) ⁻¹' {j} =
      (⋃ n, {p | ctmcJumpChain i p.2 n = j} ∩ {p | ctmcJumpTime Q i p.2 n ≤ p.1} ∩
        {p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) | (p.1 : ℝ≥0∞) < ctmcJumpTime Q i p.2 (n + 1)}) ∪
      ({p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) | ∀ n, ¬ (p.1 : ℝ≥0∞) < ctmcJumpTime Q i p.2 (n + 1)} ∩
        {_p | (Classical.ofNonempty : ι) = j}) := by
    ext ⟨t, ω⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hX
      by_cases h : ∃ n, (t : ℝ≥0∞) < ctmcJumpTime Q i ω (n + 1)
      · left
        refine ⟨Nat.find h, ⟨⟨?_, ?_⟩, Nat.find_spec h⟩⟩
        · rw [← hX, ctmcPath, dite_eq_left h]
        · rcases Nat.eq_zero_or_eq_succ_pred (Nat.find h) with h0 | h0
          · rw [h0]; simp [ctmcJumpTime]
          · have := Nat.find_min h (Nat.pred_lt_of_lt (Nat.pos_of_ne_zero (by omega)) :
              Nat.pred (Nat.find h) < Nat.find h)
            rw [h0]
            exact not_lt.mp (by simpa [Nat.succ_eq_add_one] using this)
      · right
        refine ⟨fun n hn => h ⟨n, hn⟩, ?_⟩
        rw [← hX, ctmcPath, dite_eq_right h]
    · rintro (⟨n, ⟨hY, h₁⟩, h₂⟩ | ⟨h, hj⟩)
      · rw [ctmcPath_eq_of_mem i ω h₁ h₂, hY]
      · rw [ctmcPath, dite_eq_right (fun ⟨n, hn⟩ => h n hn), ← hj]
  have hT (n : ℕ) : Measurable fun p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) => ctmcJumpTime Q i p.2 n :=
    (measurable_ctmcJumpTime i n).comp measurable_snd
  have ht : Measurable fun p : ℝ≥0 × (ℕ → (ι → ι) × ℝ) => (p.1 : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp measurable_fst
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => ?_) ?_
  · exact (((measurable_ctmcJumpChain i n).comp measurable_snd (measurableSet_singleton j)).inter
      (measurableSet_le (hT n) ht)).inter (measurableSet_lt ht (hT (n + 1)))
  · refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => (measurableSet_lt ht (hT (n + 1))).compl

/-- The state `X t` is a measurable function of the steps. -/
theorem measurable_ctmcPath (i : ι) (t : ℝ≥0) : Measurable fun ω => ctmcPath Q i ω t :=
  (measurable_ctmcPath_uncurry i).comp (measurable_const.prodMk measurable_id)

private lemma measurable_ctmcJumpChain_past (i : ι) (n : ℕ) :
    ∀ m ≤ n, Measurable[⨆ k ∈ Set.Iio n,
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance]
      (fun ω => ctmcJumpChain i ω m) := by
  intro m
  induction m with
  | zero => exact fun _ => measurable_const
  | succ m ih =>
    intro hm
    have hω : Measurable[⨆ k ∈ Set.Iio n,
        MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance]
        (fun ω : ℕ → (ι → ι) × ℝ => ω m) :=
      (comap_measurable (fun ω : ℕ → (ι → ι) × ℝ => ω m)).mono
        (le_iSup₂ (f := fun k (_ : k ∈ Set.Iio n) =>
          MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) m
          (Set.mem_Iio.mpr (by omega))) le_rfl
    have he : Measurable fun p : (ι → ι) × ι => p.1 p.2 := Measurable.of_discrete
    exact he.comp (hω.fst.prodMk (ih (by omega)))

end Measurable

section StepSigma

variable [MeasurableSpace ι]

private lemma measurable_ctmcShift (n : ℕ) :
    Measurable[⨆ k ∈ Set.Ici n,
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance] (ctmcShift n) := by
  rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun k (_ : k ∈ Set.Ici n) =>
    MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) (n + j)
    (Set.mem_Ici.mpr (Nat.le_add_right n j))

private lemma measurable_prefix (n : ℕ) :
    Measurable[⨆ k ∈ Set.Iio n,
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance]
      (fun ω : ℕ → (ι → ι) × ℝ => fun k : Fin n => ω k) := by
  rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun k => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun k (_ : k ∈ Set.Iio n) =>
    MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) k
    (Set.mem_Iio.mpr k.isLt)

end StepSigma

end Path

omit [Fintype ι] [DecidableEq ι] in
private lemma ofReal_sum_range_le (f : ℕ → ℝ) (n : ℕ) :
    ENNReal.ofReal (∑ k ∈ range n, f k) ≤ ∑ k ∈ range n, ENNReal.ofReal (f k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    exact ENNReal.ofReal_add_le.trans (add_le_add_left ih _)

private lemma hasDerivAt_ctmcTransition_apply (Q : Matrix ι ι ℝ) (i j : ι) (t : ℝ) :
    HasDerivAt (fun s => ctmcTransition Q s i j) (∑ k, Q i k * ctmcTransition Q t k j) t := by
  have h := hasDerivAt_ctmcTransition_backward Q t
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j

private lemma continuous_ctmcTransition_apply (Q : Matrix ι ι ℝ) (i j : ι) :
    Continuous fun s => ctmcTransition Q s i j :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ctmcTransition_apply Q i j t).continuousAt

private lemma ctmcTransition_eq_integral (Q : Matrix ι ι ℝ) (i j : ι) (t : ℝ) :
    ctmcTransition Q t i j = (if i = j then 1 else 0) * Real.exp (-(-Q i i * t)) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(-Q i i * s)) *
        ∑ k, (Q i k + if i = k then -Q i i else 0) * ctmcTransition Q (t - s) k j := by
  set q := -Q i i
  set g : ℝ → ℝ := fun u => ∑ k, (Q i k + if i = k then q else 0) * ctmcTransition Q u k j
  have hg : Continuous g := continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_ctmcTransition_apply Q k j)
  have hd : ∀ u, HasDerivAt (fun u => Real.exp (q * u) * ctmcTransition Q u i j)
      (Real.exp (q * u) * g u) u := by
    intro u
    have h1 : HasDerivAt (fun u => Real.exp (q * u)) (Real.exp (q * u) * q) u := by
      simpa using ((hasDerivAt_id u).const_mul q).exp
    convert h1.mul (hasDerivAt_ctmcTransition_apply Q i j u) using 1
    simp only [g, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun u _ => hd u) ((Continuous.mul (by fun_prop) hg).intervalIntegrable _ _)
  simp only [mul_zero, Real.exp_zero, ctmcTransition_zero, one_mul] at hftc
  have hsub : ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * g (t - s) =
      Real.exp (-(q * t)) * ∫ u in (0 : ℝ)..t, Real.exp (q * u) * g u := by
    set f : ℝ → ℝ := fun u => Real.exp (-(q * (t - u))) * g u
    calc ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * g (t - s)
        = ∫ s in (0 : ℝ)..t, f (t - s) := by
          congr 1; ext s; simp only [f, sub_sub_cancel]
      _ = ∫ u in (t - t)..(t - 0), f u := intervalIntegral.integral_comp_sub_left f t
      _ = ∫ u in (0 : ℝ)..t, f u := by rw [sub_self, sub_zero]
      _ = _ := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1; ext u
          simp only [f, ← mul_assoc, ← Real.exp_add]
          ring_nf
  have hexp : Real.exp (-(q * t)) * Real.exp (q * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hsub, hftc, Matrix.one_apply]
  have : Real.exp (-(q * t)) * (Real.exp (q * t) * ctmcTransition Q t i j - if i = j then 1 else 0)
      = ctmcTransition Q t i j - (if i = j then 1 else 0) * Real.exp (-(q * t)) := by
    rw [mul_sub, ← mul_assoc, hexp, one_mul, mul_comm]
  rw [this]
  ring

private lemma renewal_eq_zero {κ Ω₀ : Type*} [MeasurableSpace Ω₀] (ν : Measure Ω₀)
    [IsProbabilityMeasure ν] (S : κ → Ω₀ → ℝ≥0∞) (J : κ → Ω₀ → κ) (d : ℝ≥0 → κ → κ → ℝ)
    {B : ℝ} (hB : ∀ t i j, |d t i j| ≤ B) {h : ℝ≥0} (hh : 0 < h) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1) (hSm : ∀ i, MeasurableSet {ω | S i ω < h})
    (hS : ∀ i, ν.real {ω | S i ω < h} ≤ ρ)
    (heq : ∀ t i j, d t i j =
      ∫ ω, (if S i ω ≤ t then d (t - (S i ω).toNNReal : ℝ≥0) (J i ω) j else 0) ∂ν) :
    ∀ t i j, d t i j = 0 := by
  have main : ∀ N : ℕ, ∀ t : ℝ≥0, t < N * h → ∀ i j, d t i j = 0 := by
    intro N
    induction N with
    | zero => intro t ht; simp at ht
    | succ N ih =>
      have hbd : ∀ m : ℕ, ∀ t : ℝ≥0, t < (N + 1 : ℕ) * h → ∀ i j, |d t i j| ≤ B * ρ ^ m := by
        intro m
        induction m with
        | zero => intro t _ i j; simpa using hB t i j
        | succ m ihm =>
          intro t ht i j
          have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB t i j)
          have hK : 0 ≤ B * ρ ^ m := mul_nonneg hB0 (pow_nonneg hρ0 m)
          rw [heq t i j, ← Real.norm_eq_abs]
          have hg : Integrable ({ω | S i ω < h}.indicator fun _ => B * ρ ^ m) ν :=
            Integrable.indicator (integrable_const _) (hSm i)
          refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun ω => ?_)).trans ?_
          · split_ifs with hSt
            · set u := t - (S i ω).toNNReal
              have hfin : S i ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hSt
              have hSt' : (S i ω).toNNReal ≤ t := by
                rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact hSt
              by_cases hu : u < N * h
              · rw [ih u hu, norm_zero]
                exact Set.indicator_nonneg (fun _ _ => hK) ω
              · push Not at hu
                have hlt : S i ω < h := by
                  rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe]
                  have h1 : (N : ℝ≥0) * h + (S i ω).toNNReal ≤ t := by
                    calc (N : ℝ≥0) * h + (S i ω).toNNReal ≤ u + (S i ω).toNNReal := by gcongr
                      _ = t := tsub_add_cancel_of_le hSt'
                  have h2 : t < N * h + h := by
                    simpa [add_mul] using ht
                  by_contra hc
                  push Not at hc
                  exact absurd (lt_of_le_of_lt (h1.trans' (by gcongr)) h2) (lt_irrefl _)
                rw [Set.indicator_of_mem (show ω ∈ {ω | S i ω < h} from hlt), Real.norm_eq_abs]
                exact ihm u (lt_of_le_of_lt tsub_le_self ht) _ _
            · rw [norm_zero]
              exact Set.indicator_nonneg (fun _ _ => hK) ω
          · rw [integral_indicator_const _ (hSm i), smul_eq_mul]
            calc ν.real {ω | S i ω < h} * (B * ρ ^ m) ≤ ρ * (B * ρ ^ m) :=
                  mul_le_mul_of_nonneg_right (hS i) hK
              _ = B * ρ ^ (m + 1) := by ring
      intro t ht i j
      have hlim : Tendsto (fun m : ℕ => B * ρ ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).const_mul B
      have : |d t i j| ≤ 0 := ge_of_tendsto' hlim fun m => hbd m t ht i j
      exact abs_nonpos_iff.mp this
  intro t i j
  obtain ⟨N, hN⟩ := exists_nat_gt (t / h)
  refine main N t ?_ i j
  rwa [div_lt_iff₀ hh] at hN

open Set in
private lemma integral_expMeasure_renewal {q t c : ℝ} (hq : 0 < q) (ht : 0 ≤ t) {f g : ℝ → ℝ}
    (hg : Integrable g (expMeasure 1))
    (hgf : ∀ e, 0 < e → g e = if t < e / q then c else f (t - e / q)) :
    ∫ e, g e ∂expMeasure 1 =
      c * Real.exp (-(q * t)) + q * ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * f (t - s) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq.le ht
  rw [integral_expMeasure_eq_setIntegral one_pos]
  have hI := (integrable_expMeasure_iff one_pos).1 hg
  rw [← Ioc_union_Ioi_eq_Ioi hqt, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hqt))]
  have h2 : ∫ e in Ioi (q * t), 1 * Real.exp (-(1 * e)) * g e =
      ∫ e in Ioi (q * t), Real.exp (-e) * c := by
    refine setIntegral_congr_fun measurableSet_Ioi fun e he => ?_
    have he0 : 0 < e := lt_of_le_of_lt hqt he
    have : t < e / q := by rw [lt_div_iff₀ hq]; linarith [mem_Ioi.mp he]
    simp only [hgf e he0, this, ite_true, one_mul]
  have h1 : ∫ e in Ioc 0 (q * t), 1 * Real.exp (-(1 * e)) * g e =
      ∫ e in Ioc 0 (q * t), Real.exp (-e) * f (t - e / q) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun e he => ?_
    have : ¬ t < e / q := by
      rw [not_lt, div_le_iff₀ hq]; linarith [(mem_Ioc.mp he).2]
    simp only [hgf e (mem_Ioc.mp he).1, this, ite_false, one_mul]
  rw [h1, h2, integral_mul_const, integral_exp_neg_Ioi, ← intervalIntegral.integral_of_le hqt]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun e => Real.exp (-e) * f (t - e / q)) hq.ne' (a := 0) (b := t)
  simp only [mul_zero, smul_eq_mul] at hsub
  have hc : ∀ x, Real.exp (-(q * x)) * f (t - q * x / q) = Real.exp (-(q * x)) * f (t - x) := by
    intro x; rw [mul_div_cancel_left₀ x hq.ne']
  simp only [hc] at hsub
  rw [hsub, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul, mul_comm c]
  ring

private lemma integral_expMeasure_memoryless {c : ℝ} (hc : 0 ≤ c) (k : ℝ → ℝ) :
    ∫ e, (if c < e then k (e - c) else 0) ∂expMeasure 1 =
      Real.exp (-c) * ∫ e, k e ∂expMeasure 1 := by
  rw [integral_expMeasure_eq_setIntegral one_pos, integral_expMeasure_eq_setIntegral one_pos]
  have h1 : ∫ e in Set.Ioi 0, 1 * Real.exp (-(1 * e)) * (if c < e then k (e - c) else 0) =
      ∫ e, (Set.Ioi c).indicator (fun e => Real.exp (-e) * k (e - c)) e := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; ext e
    by_cases he : c < e
    · have he0 : 0 < e := lt_of_le_of_lt hc he
      simp [Set.indicator_of_mem (show e ∈ Set.Ioi 0 from he0), he]
    · simp only [Set.indicator, Set.mem_Ioi, he, ite_false, mul_zero]
      split_ifs <;> simp
  have h2 : ∫ e, (Set.Ioi c).indicator (fun e => Real.exp (-e) * k (e - c)) e =
      ∫ x, (Set.Ioi 0).indicator (fun x => Real.exp (-(x + c)) * k x) x := by
    rw [← integral_add_right_eq_self _ c]
    congr 1; ext x
    simp only [Set.indicator, Set.mem_Ioi, add_sub_cancel_right, lt_add_iff_pos_left]
  rw [h1, h2, integral_indicator measurableSet_Ioi, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [neg_add, Real.exp_add]
  simp only [one_mul]
  ring

namespace IsRateMatrix

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] {Q : Matrix ι ι ℝ}

omit [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private lemma ofReal_div_le_ctmcHoldingTime (hQ : IsRateMatrix Q) (i : ι)
    (ω : ℕ → (ι → ι) × ℝ) (n : ℕ) :
    ENNReal.ofReal ((ω n).2 / (1 + ∑ k, -Q k k)) ≤ ctmcHoldingTime Q i ω n := by
  unfold ctmcHoldingTime
  set y := ctmcJumpChain i ω n
  split_ifs with h0
  · exact le_top
  · have hq : 0 < -Q y y := lt_of_le_of_ne (neg_nonneg.mpr (hQ.diag_nonpos y))
      (fun h => h0 (by linarith))
    have hqc : -Q y y ≤ 1 + ∑ k, -Q k k := by
      have := single_le_sum (f := fun k => -Q k k)
        (fun k _ => neg_nonneg.mpr (hQ.diag_nonpos k)) (mem_univ y)
      linarith
    rcases le_or_gt 0 (ω n).2 with hE | hE
    · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hE hq hqc)
    · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hE.le (by linarith))]
      exact zero_le

omit [DiscreteMeasurableSpace ι] in
private lemma ae_tendsto_sum_clock (hQ : IsRateMatrix Q) :
    ∀ᵐ ω ∂ctmcInputMeasure hQ,
      Tendsto (fun n => ∑ k ∈ range n, (ω k).2) atTop atTop := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set μ := ctmcInputMeasure hQ
  have hmap : ∀ k, μ.map (fun ω : ℕ → (ι → ι) × ℝ => (ω k).2) = expMeasure 1 := by
    intro k
    have h1 : μ.map (fun ω : ℕ → (ι → ι) × ℝ => ω k) = ctmcStepMeasure hQ :=
      Measure.infinitePi_map_eval _ k
    rw [show (fun ω : ℕ → (ι → ι) × ℝ => (ω k).2) = Prod.snd ∘ (fun ω => ω k) from rfl,
      ← Measure.map_map measurable_snd (measurable_pi_apply k), h1, ctmcStepMeasure,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hmeas : ∀ k, Measurable fun ω : ℕ → (ι → ι) × ℝ => (ω k).2 :=
    fun k => (measurable_pi_apply k).snd
  have hint : Integrable (fun ω : ℕ → (ι → ι) × ℝ => (ω 0).2) μ := by
    have := integrable_id_expMeasure (r := 1) one_pos
    rw [← hmap 0] at this
    exact (integrable_map_measure (by fun_prop) (hmeas 0).aemeasurable).1 this
  have hindep : Pairwise fun a b =>
      IndepFun (fun ω : ℕ → (ι → ι) × ℝ => (ω a).2) (fun ω => (ω b).2) μ := by
    intro a b hab
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => ctmcStepMeasure hQ)
      (X := fun _ x => x.2) (fun _ => measurable_snd)).indepFun hab
  have hident : ∀ k, IdentDistrib (fun ω : ℕ → (ι → ι) × ℝ => (ω k).2)
      (fun ω => (ω 0).2) μ μ := fun k =>
    ⟨(hmeas k).aemeasurable, (hmeas 0).aemeasurable, by rw [hmap, hmap]⟩
  have hmean : μ[fun ω : ℕ → (ι → ι) × ℝ => (ω 0).2] = 1 := by
    have h := integral_map (μ := μ) (f := id) (hmeas 0).aemeasurable
      aestronglyMeasurable_id
    simp only [hmap 0, id] at h
    rw [integral_id_expMeasure one_pos, inv_one] at h
    exact h.symm
  filter_upwards [strong_law_ae _ hint hindep hident] with ω hω
  rw [hmean] at hω
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < (n : ℝ)⁻¹ • ∑ k ∈ range n, (ω k).2 :=
    hω.eventually (lt_mem_nhds (by norm_num))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  rw [smul_eq_mul, lt_inv_mul_iff₀ hnpos] at hn
  linarith

omit [DiscreteMeasurableSpace ι] in
/-- **Non-explosion** (Norris 1997, §2.7, for a finite state space): almost surely
the jump times of the chain started at `i` tend to `∞`, so `X t` is a genuine state of the
jump chain for every `t ≥ 0`. -/
theorem ae_tendsto_ctmcJumpTime (hQ : IsRateMatrix Q) (i : ι) :
    ∀ᵐ ω ∂ctmcInputMeasure hQ, Tendsto (ctmcJumpTime Q i ω) atTop (𝓝 ∞) := by
  set c : ℝ := 1 + ∑ k, -Q k k
  have hc : 0 < c := by
    have := sum_nonneg fun k (_ : k ∈ univ) => neg_nonneg.mpr (hQ.diag_nonpos k)
    linarith
  filter_upwards [ae_tendsto_sum_clock hQ] with ω hω
  have hlow : ∀ n, ENNReal.ofReal ((∑ k ∈ range n, (ω k).2) / c) ≤ ctmcJumpTime Q i ω n := by
    intro n
    calc ENNReal.ofReal ((∑ k ∈ range n, (ω k).2) / c)
        = ENNReal.ofReal (∑ k ∈ range n, (ω k).2 / c) := by rw [sum_div]
      _ ≤ ∑ k ∈ range n, ENNReal.ofReal ((ω k).2 / c) := ofReal_sum_range_le _ _
      _ ≤ ctmcJumpTime Q i ω n :=
        sum_le_sum fun k _ => ofReal_div_le_ctmcHoldingTime hQ i ω k
  refine tendsto_nhds_top_mono ?_ (Eventually.of_forall hlow)
  exact ENNReal.tendsto_ofReal_atTop.comp (hω.atTop_div_const hc)

omit [DiscreteMeasurableSpace ι] in
private lemma ctmc_indep (hQ : IsRateMatrix Q) (n : ℕ) :
    Indep (⨆ k ∈ Set.Iio n, MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance)
      (⨆ k ∈ Set.Ici n, MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance)
      (ctmcInputMeasure hQ) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => ctmcStepMeasure hQ)
    (X := fun _ x => x) (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at h
  refine indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le) h ?_
  exact Set.disjoint_left.mpr fun k hk hk' => absurd (Set.mem_Iio.mp hk) (not_lt.mpr hk')

omit [DiscreteMeasurableSpace ι] in
private lemma ctmc_map_shift (hQ : IsRateMatrix Q) (n : ℕ) :
    (ctmcInputMeasure hQ).map (ctmcShift n) = ctmcInputMeasure hQ :=
  Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ctmcStepMeasure hQ)
    (f := fun j => n + j) (add_right_injective n)

/-- **Strong Markov property at jump times** (Norris 1997, §2.6–2.7): let `A` be a
measurable set of histories of the first `n` steps such that `T n < ∞` whenever the history
lies in `A`; these histories determine `Y 0, …, Y n` and `S 0, …, S (n - 1)`. Then for every
state `k` and every measurable set `B` of paths, the path after `T n` is independent of the
event `{history ∈ A, Y n = k}` and distributed as the chain started at `k`. -/
theorem ctmcInputMeasure_ctmcPath_jumpTime_add (hQ : IsRateMatrix Q) (i : ι) (n : ℕ)
    {A : Set (Fin n → (ι → ι) × ℝ)} (hA : MeasurableSet A)
    (hAT : ∀ ω : ℕ → (ι → ι) × ℝ, (fun k : Fin n => ω k) ∈ A → ctmcJumpTime Q i ω n ≠ ∞)
    (k : ι) {B : Set (ℝ≥0 → ι)} (hB : MeasurableSet B) :
    ctmcInputMeasure hQ
        ({ω | (fun k : Fin n => ω k) ∈ A} ∩ {ω | ctmcJumpChain i ω n = k} ∩
          {ω | (fun s => ctmcPath Q i ω ((ctmcJumpTime Q i ω n).toNNReal + s)) ∈ B}) =
      ctmcInputMeasure hQ
          ({ω | (fun k : Fin n => ω k) ∈ A} ∩ {ω | ctmcJumpChain i ω n = k}) *
        ctmcInputMeasure hQ {ω | (fun s => ctmcPath Q k ω s) ∈ B} := by
  have hXk : Measurable fun ω : ℕ → (ι → ι) × ℝ => fun s => ctmcPath Q k ω s :=
    Measurable.of_eval fun s => measurable_ctmcPath (Q := Q) k s
  have hset : {ω | (fun k : Fin n => ω k) ∈ A} ∩ {ω | ctmcJumpChain i ω n = k} ∩
      {ω | (fun s => ctmcPath Q i ω ((ctmcJumpTime Q i ω n).toNNReal + s)) ∈ B} =
      ({ω | (fun k : Fin n => ω k) ∈ A} ∩ {ω | ctmcJumpChain i ω n = k}) ∩
        ctmcShift n ⁻¹' {ω | (fun s => ctmcPath Q k ω s) ∈ B} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hA', hY⟩, hBω⟩
      refine ⟨⟨hA', hY⟩, ?_⟩
      have := funext fun s => ctmcPath_jumpTime_add (Q := Q) i ω n (hAT ω hA') s
      rw [this, hY] at hBω
      exact hBω
    · rintro ⟨⟨hA', hY⟩, hBω⟩
      refine ⟨⟨hA', hY⟩, ?_⟩
      have := funext fun s => ctmcPath_jumpTime_add (Q := Q) i ω n (hAT ω hA') s
      rw [this, hY]
      exact hBω
  rw [hset]
  calc _ = ctmcInputMeasure hQ
          ({ω | (fun k : Fin n => ω k) ∈ A} ∩ {ω | ctmcJumpChain i ω n = k}) *
        ctmcInputMeasure hQ (ctmcShift n ⁻¹' {ω | (fun s => ctmcPath Q k ω s) ∈ B}) :=
        (Indep_iff _ _ _).1 (ctmc_indep hQ n) _ _
          ((measurable_prefix n hA).inter (measurable_ctmcJumpChain_past i n n le_rfl
            (measurableSet_singleton k)))
          (measurable_ctmcShift n (hXk hB))
    _ = _ := by
      congr 1
      have h := Measure.map_apply (μ := ctmcInputMeasure hQ) (f := ctmcShift n)
        (Measurable.of_eval fun j => measurable_pi_apply (n + j)) (hXk hB)
      rw [ctmc_map_shift] at h
      exact h.symm

omit [DiscreteMeasurableSpace ι] in
private lemma ctmc_map_first (hQ : IsRateMatrix Q) :
    (ctmcInputMeasure hQ).map (fun ω => (ω 0, ctmcShift 1 ω)) =
      (ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ) := by
  have hsh : Measurable (ctmcShift (ι := ι) 1) :=
    Measurable.of_eval fun j => measurable_pi_apply (1 + j)
  have hind : IndepFun (fun ω : ℕ → (ι → ι) × ℝ => ω 0) (ctmcShift 1) (ctmcInputMeasure hQ) := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (ctmc_indep hQ 1) ?_)
      (measurable_ctmcShift 1).comap_le
    exact le_iSup₂ (f := fun k (_ : k ∈ Set.Iio 1) =>
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) 0
      (Set.mem_Iio.mpr Nat.zero_lt_one)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    hsh.aemeasurable).1 hind, ctmc_map_shift]
  congr 1
  exact Measure.infinitePi_map_eval _ 0

omit [Fintype ι] [DecidableEq ι] [DiscreteMeasurableSpace ι] in
private lemma measurable_firstHold (i : ι) : Measurable (firstHold Q i) := by
  unfold firstHold
  split_ifs
  · exact measurable_const
  · exact ENNReal.measurable_ofReal.comp (measurable_snd.div_const _)

private lemma ctmc_renewal (hQ : IsRateMatrix Q) (i j : ι) (t : ℝ≥0) :
    (ctmcInputMeasure hQ).real {ω | ctmcPath Q i ω t = j} =
      ∫ a, (if (t : ℝ≥0∞) < firstHold Q i a then (if i = j then (1 : ℝ) else 0) else
        (ctmcInputMeasure hQ).real
          {ω | ctmcPath Q (a.1 i) ω (t - (firstHold Q i a).toNNReal) = j}) ∂ctmcStepMeasure hQ ∧
    Integrable (fun a => if (t : ℝ≥0∞) < firstHold Q i a then (if i = j then (1 : ℝ) else 0)
      else (ctmcInputMeasure hQ).real
        {ω | ctmcPath Q (a.1 i) ω (t - (firstHold Q i a).toNNReal) = j}) (ctmcStepMeasure hQ) := by
  classical
  set μ := ctmcInputMeasure hQ
  set ν := ctmcStepMeasure hQ
  have hS := measurable_firstHold (Q := Q) i
  have hτ : Measurable fun a : (ι → ι) × ℝ => t - (firstHold Q i a).toNNReal :=
    measurable_const.sub (ENNReal.measurable_toNNReal.comp hS)
  have hΦ : Measurable fun p : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) =>
      ctmcPath Q (p.1.1 i) p.2 (t - (firstHold Q i p.1).toNNReal) := by
    have hk : Measurable fun p : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) => (p, p.1.1 i) :=
      measurable_id.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
    have key : ∀ F : ι → ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) → ι, (∀ k, Measurable (F k)) →
        Measurable fun p => F (p.1.1 i) p := fun F hF =>
      (measurable_from_prod_countable_left (f := fun q => F q.2 q.1) hF).comp hk
    exact key (fun k p => ctmcPath Q k p.2 (t - (firstHold Q i p.1).toNNReal)) fun k =>
      (measurable_ctmcPath_uncurry k).comp ((hτ.comp measurable_fst).prodMk measurable_snd)
  set E : Set (((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ)) :=
    {p | (t : ℝ≥0∞) < firstHold Q i p.1 ∧ i = j} ∪
      {p | ¬ (t : ℝ≥0∞) < firstHold Q i p.1 ∧
        ctmcPath Q (p.1.1 i) p.2 (t - (firstHold Q i p.1).toNNReal) = j} with hEdef
  have hE : MeasurableSet E := by
    refine MeasurableSet.union ?_ ?_
    · exact (measurableSet_lt measurable_const (hS.comp measurable_fst)).inter
        (MeasurableSet.const _)
    · exact (measurableSet_lt measurable_const (hS.comp measurable_fst)).compl.inter
        (hΦ (measurableSet_singleton j))
  have hg : Measurable fun ω : ℕ → (ι → ι) × ℝ => (ω 0, ctmcShift 1 ω) :=
    (measurable_pi_apply 0).prodMk (Measurable.of_eval fun j => measurable_pi_apply (1 + j))
  have hpre : {ω | ctmcPath Q i ω t = j} = (fun ω => (ω 0, ctmcShift 1 ω)) ⁻¹' E := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hEdef, Set.mem_union]
    rw [ctmcPath_eq_ite, show ctmcHoldingTime Q i ω 0 = firstHold Q i (ω 0) from rfl]
    split_ifs with h <;> simp [h]
  have hslice : ∀ a, μ.real (Prod.mk a ⁻¹' E) =
      if (t : ℝ≥0∞) < firstHold Q i a then (if i = j then (1 : ℝ) else 0) else
        μ.real {ω | ctmcPath Q (a.1 i) ω (t - (firstHold Q i a).toNNReal) = j} := by
    intro a
    by_cases h : (t : ℝ≥0∞) < firstHold Q i a
    · by_cases hij : i = j
      · have : Prod.mk a ⁻¹' E = Set.univ := by
          ext ω
          simp only [hEdef, Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ,
            iff_true]
          exact Or.inl ⟨h, hij⟩
        rw [this, ite_eq_left h, ite_eq_left hij, probReal_univ]
      · have : Prod.mk a ⁻¹' E = ∅ := by
          ext ω
          simp only [hEdef, Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_or, not_and]
          exact ⟨fun _ => hij, fun h' => absurd h h'⟩
        rw [this, ite_eq_left h, ite_eq_right hij, measureReal_empty]
    · have : Prod.mk a ⁻¹' E =
          {ω | ctmcPath Q (a.1 i) ω (t - (firstHold Q i a).toNNReal) = j} := by
        ext ω
        simp only [hEdef, Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq]
        constructor
        · rintro (⟨h', _⟩ | ⟨_, h'⟩)
          · exact absurd h' h
          · exact h'
        · exact fun h' => Or.inr ⟨h, h'⟩
      rw [this, ite_eq_right h]
  have hint : Integrable
      (E.indicator (1 : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) → ℝ)) (ν.prod μ) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hin : ∀ a, ∫ ω, E.indicator (1 : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) → ℝ) (a, ω) ∂μ =
      μ.real (Prod.mk a ⁻¹' E) := by
    intro a
    rw [← integral_indicator_one (measurable_prodMk_left hE)]
    rfl
  have hfub := integral_prod _ hint
  rw [integral_indicator_one hE] at hfub
  simp only [hin, hslice] at hfub
  refine ⟨?_, ?_⟩
  · rw [hpre, ← hfub, ← ctmc_map_first hQ, measureReal_def, measureReal_def,
      Measure.map_apply hg hE]
  · have := hint.integral_prod_left
    simp only [hin, hslice] at this
    exact this

private lemma ctmcTransition_renewal (hQ : IsRateMatrix Q) (i j : ι) (t : ℝ≥0) :
    ctmcTransition Q t i j =
      ∫ a, (if (t : ℝ≥0∞) < firstHold Q i a then (if i = j then (1 : ℝ) else 0) else
        ctmcTransition Q (t - (firstHold Q i a).toNNReal : ℝ≥0) (a.1 i) j) ∂ctmcStepMeasure hQ ∧
    Integrable (fun a => if (t : ℝ≥0∞) < firstHold Q i a then (if i = j then (1 : ℝ) else 0)
      else ctmcTransition Q (t - (firstHold Q i a).toNNReal : ℝ≥0) (a.1 i) j)
      (ctmcStepMeasure hQ) := by
  classical
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set Φ : ι → ℝ → ℝ := fun k e => if (t : ℝ≥0∞) < firstHold Q i ((fun _ => i), e)
    then (if i = j then (1 : ℝ) else 0)
    else ctmcTransition Q (t - (firstHold Q i ((fun _ => i), e)).toNNReal : ℝ≥0) k j with hΦ
  have hfh : ∀ a : (ι → ι) × ℝ, firstHold Q i a = firstHold Q i ((fun _ => i), a.2) :=
    fun a => rfl
  have hPbd : ∀ (s : ℝ≥0) k, |ctmcTransition Q s k j| ≤ 1 := by
    intro s k
    have h0 := hQ.ctmcTransition_nonneg s.2 k j
    have h1 : ctmcTransition Q s k j ≤ 1 := by
      rw [← hQ.sum_ctmcTransition s k]
      exact single_le_sum (fun l _ => hQ.ctmcTransition_nonneg s.2 k l) (mem_univ j)
    exact abs_le.mpr ⟨le_trans (by norm_num) h0, h1⟩
  have hΦm : ∀ k, Measurable (Φ k) := by
    intro k
    have hS : Measurable fun e : ℝ => firstHold Q i ((fun _ => i), e) :=
      (measurable_firstHold i).comp (measurable_const.prodMk measurable_id)
    refine Measurable.ite (measurableSet_lt measurable_const hS) measurable_const ?_
    exact (continuous_ctmcTransition_apply Q k j).measurable.comp
      (measurable_coe_nnreal_real.comp (measurable_const.sub (ENNReal.measurable_toNNReal.comp hS)))
  have hΦb : ∀ k e, |Φ k e| ≤ 1 := by
    intro k e
    simp only [hΦ]
    split_ifs
    · simp
    · simp
    · exact hPbd _ _
  have hFm : Measurable fun a : (ι → ι) × ℝ => Φ (a.1 i) a.2 := by
    have hk : Measurable fun a : (ι → ι) × ℝ => (a, a.1 i) :=
      measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst)
    exact (measurable_from_prod_countable_left (f := fun q : ((ι → ι) × ℝ) × ι => Φ q.2 q.1.2)
      fun k => (hΦm k).comp measurable_snd).comp hk
  have hint : Integrable (fun a : (ι → ι) × ℝ => Φ (a.1 i) a.2) (ctmcStepMeasure hQ) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hΦb _ _)
  refine ⟨?_, hint⟩
  change _ = ∫ a, Φ (a.1 i) a.2 ∂ctmcStepMeasure hQ
  have hΦi : ∀ k, Integrable (Φ k) (expMeasure 1) := fun k =>
    Integrable.of_bound (hΦm k).aestronglyMeasurable 1
      (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact hΦb _ _)
  have hprod : ∫ a, Φ (a.1 i) a.2 ∂ctmcStepMeasure hQ =
      ∑ k, ctmcJumpMatrix Q i k * ∫ e, Φ k e ∂expMeasure 1 := by
    have hint' := hint
    unfold ctmcStepMeasure at hint' ⊢
    rw [integral_prod _ hint']
    have hmp := measurePreserving_eval (μ := fun i => (hQ.ctmcJumpPMF i).toMeasure) i
    have hmap := integral_map (μ := Measure.pi fun i => (hQ.ctmcJumpPMF i).toMeasure)
      (φ := fun ξ : ι → ι => ξ i) (f := fun k => ∫ e, Φ k e ∂expMeasure 1)
      hmp.measurable.aemeasurable Measurable.of_discrete.aestronglyMeasurable
    rw [hmp.map_eq, PMF.integral_eq_sum] at hmap
    rw [← hmap]
    refine sum_congr rfl fun k _ => ?_
    simp only [ctmcJumpPMF, PMF.ofFintype_apply, smul_eq_mul,
      ENNReal.toReal_ofReal (hQ.ctmcJumpMatrix_nonneg i k)]
  rw [hprod]
  by_cases h0 : Q i i = 0
  · have hfh0 : ∀ e : ℝ, firstHold Q i ((fun _ => i), e) = ∞ := fun e => by simp [firstHold, h0]
    have hG : ∀ k, ∫ e, Φ k e ∂expMeasure 1 = if i = j then 1 else 0 := by
      intro k
      simp only [hΦ, hfh0, ENNReal.coe_lt_top, ite_true, integral_const, probReal_univ,
        smul_eq_mul, one_mul]
    simp only [hG, ← sum_mul, hQ.sum_ctmcJumpMatrix, one_mul]
    have hrow : ∀ k, Q i k = 0 := by
      intro k
      have hnn : ∀ l ∈ univ, 0 ≤ Q i l := fun l _ => by
        by_cases hl : i = l
        · subst hl; exact h0.ge
        · exact hQ.nonneg_of_ne hl
      exact (sum_eq_zero_iff_of_nonneg hnn).1 (hQ.sum_row i) k (mem_univ k)
    rw [ctmcTransition_eq_integral]
    simp [hrow]
  · have hq : 0 < -Q i i := lt_of_le_of_ne (neg_nonneg.mpr (hQ.diag_nonpos i))
      (fun h => h0 (by linarith))
    have hG : ∀ k, ∫ e, Φ k e ∂expMeasure 1 = (if i = j then 1 else 0) *
        Real.exp (-(-Q i i * t)) + -Q i i *
          ∫ s in (0 : ℝ)..t, Real.exp (-(-Q i i * s)) * ctmcTransition Q (t - s) k j := by
      intro k
      refine integral_expMeasure_renewal (f := fun r => ctmcTransition Q r k j) hq t.2 (hΦi k)
        fun e he => ?_
      have hfe : firstHold Q i ((fun _ => i), e) = ENNReal.ofReal (e / -Q i i) := by
        simp [firstHold, h0]
      have hpos : 0 < e / -Q i i := div_pos he hq
      have hiff : ((t : ℝ≥0∞) < ENNReal.ofReal (e / -Q i i)) ↔ (t : ℝ) < e / -Q i i := by
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hpos]
      simp only [hΦ, hfe, hiff]
      by_cases hlt : (t : ℝ) < e / -Q i i
      · simp only [NNReal.val_eq_coe, hlt, ite_true]
      · simp only [NNReal.val_eq_coe, hlt, ite_false]
        push Not at hlt
        congr 2
        rw [show (ENNReal.ofReal (e / -Q i i)).toNNReal = (e / -Q i i).toNNReal from
          ENNReal.toNNReal_coe _, NNReal.coe_sub (by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos.le]; exact hlt),
          Real.coe_toNNReal _ hpos.le]
    have hw : ∀ k, ctmcJumpMatrix Q i k * -Q i i = Q i k + if i = k then -Q i i else 0 := by
      intro k
      by_cases hik : i = k
      · subst hik; simp [ctmcJumpMatrix, h0]
      · simp [ctmcJumpMatrix, h0, hik, div_mul_cancel₀ _ (neg_ne_zero.mpr h0)]
    simp only [hG]
    rw [ctmcTransition_eq_integral]
    have hcont : ∀ k, Continuous fun s : ℝ =>
        Real.exp (-(-Q i i * s)) * ctmcTransition Q (t - s) k j := fun k =>
      (by fun_prop : Continuous fun s : ℝ => Real.exp (-(-Q i i * s))).mul
        ((continuous_ctmcTransition_apply Q k j).comp (continuous_const.sub continuous_id))
    have hsplit : ∫ s in (0 : ℝ)..t, Real.exp (-(-Q i i * s)) *
        ∑ k, (Q i k + if i = k then -Q i i else 0) * ctmcTransition Q (t - s) k j =
        ∑ k, (Q i k + if i = k then -Q i i else 0) *
          ∫ s in (0 : ℝ)..t, Real.exp (-(-Q i i * s)) * ctmcTransition Q (t - s) k j := by
      calc _ = ∫ s in (0 : ℝ)..t, ∑ k, (Q i k + if i = k then -Q i i else 0) *
              (Real.exp (-(-Q i i * s)) * ctmcTransition Q (t - s) k j) :=
            intervalIntegral.integral_congr fun s _ => by
              simp only [mul_sum]
              exact sum_congr rfl fun k _ => by ring
        _ = ∑ k, ∫ s in (0 : ℝ)..t, (Q i k + if i = k then -Q i i else 0) *
              (Real.exp (-(-Q i i * s)) * ctmcTransition Q (t - s) k j) :=
            intervalIntegral.integral_finsetSum fun k _ =>
              ((hcont k).const_mul _).intervalIntegrable _ _
        _ = _ := sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
    rw [hsplit]
    simp only [mul_add, sum_add_distrib, ← sum_mul, hQ.sum_ctmcJumpMatrix, one_mul]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [← hw k]
    ring

omit [DiscreteMeasurableSpace ι] in
private lemma firstHold_small (hQ : IsRateMatrix Q) : ∃ h : ℝ≥0, 0 < h ∧
    ∀ k, (ctmcStepMeasure hQ).real {a | firstHold Q k a < h} ≤ 1 - Real.exp (-1) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set c : ℝ := 1 + ∑ k, -Q k k
  have hc : 0 < c := by
    have := sum_nonneg fun k (_ : k ∈ univ) => neg_nonneg.mpr (hQ.diag_nonpos k)
    linarith
  set h : ℝ≥0 := ⟨c⁻¹, (inv_pos.mpr hc).le⟩
  have hh : 0 < h := by rw [← NNReal.coe_pos]; exact inv_pos.mpr hc
  have hρ : (ctmcStepMeasure hQ).real {a | a.2 ≤ 1} = 1 - Real.exp (-1) := by
    have hmap : (ctmcStepMeasure hQ).map Prod.snd = expMeasure 1 := by
      rw [ctmcStepMeasure, Measure.map_snd_prod, measure_univ, one_smul]
    rw [show {a : (ι → ι) × ℝ | a.2 ≤ 1} = Prod.snd ⁻¹' Set.Iic 1 from rfl,
      ← map_measureReal_apply measurable_snd measurableSet_Iic, hmap, ← cdf_eq_real,
      cdf_expMeasure_eq one_pos]
    simp
  refine ⟨h, hh, ?_⟩
  intro k
  rw [← hρ]
  refine measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)
  simp only [Set.mem_ofPred_eq] at ha ⊢
  by_cases h0 : Q k k = 0
  · simp [firstHold, h0] at ha
  · have hq : 0 < -Q k k := lt_of_le_of_ne (neg_nonneg.mpr (hQ.diag_nonpos k))
      (fun h => h0 (by linarith))
    have hqc : -Q k k ≤ c := by
      have := single_le_sum (f := fun k => -Q k k)
        (fun k _ => neg_nonneg.mpr (hQ.diag_nonpos k)) (mem_univ k)
      simp only [c]; linarith
    simp only [firstHold, h0, ite_false] at ha
    rw [← ENNReal.ofReal_coe_nnreal] at ha
    have ha' := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 ha
    rcases le_or_gt a.2 0 with ha0 | ha0
    · linarith
    · have : a.2 / -Q k k < c⁻¹ := ha'
      rw [div_lt_iff₀ hq] at this
      have h2 : c⁻¹ * -Q k k ≤ 1 := by
        rw [inv_mul_le_iff₀ hc]; linarith
      linarith

/-- **Kolmogorov** (Norris 1997, §2.8, Theorem 2.8.2 for a finite state space): the chain
built from the jump chain and the holding times has transition function `exp (t • Q)`:
`P_i(X t = j) = exp (t Q) i j` for every `t ≥ 0`. -/
theorem ctmcInputMeasure_real_ctmcPath_eq (hQ : IsRateMatrix Q) (i j : ι) (t : ℝ≥0) :
    (ctmcInputMeasure hQ).real {ω | ctmcPath Q i ω t = j} = ctmcTransition Q t i j := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set d : ℝ≥0 → ι → ι → ℝ := fun t i j =>
    (ctmcInputMeasure hQ).real {ω | ctmcPath Q i ω t = j} - ctmcTransition Q t i j with hd
  have hPbd : ∀ (s : ℝ≥0) k l, 0 ≤ ctmcTransition Q s k l ∧ ctmcTransition Q s k l ≤ 1 := by
    intro s k l
    refine ⟨hQ.ctmcTransition_nonneg s.2 k l, ?_⟩
    rw [← hQ.sum_ctmcTransition s k]
    exact single_le_sum (fun l _ => hQ.ctmcTransition_nonneg s.2 k l) (mem_univ l)
  have hB : ∀ s k l, |d s k l| ≤ 2 := by
    intro s k l
    have h1 := measureReal_nonneg (μ := ctmcInputMeasure hQ) (s := {ω | ctmcPath Q k ω s = l})
    have h2 : (ctmcInputMeasure hQ).real {ω | ctmcPath Q k ω s = l} ≤ 1 := measureReal_le_one
    have h3 := hPbd s k l
    exact abs_le.mpr ⟨by simp only [hd]; linarith [h3.2], by simp only [hd]; linarith [h3.1]⟩
  obtain ⟨h, hh, hsmall⟩ := firstHold_small hQ
  have hzero := renewal_eq_zero (ctmcStepMeasure hQ) (firstHold Q) (fun i a => a.1 i) d hB hh
    (ρ := 1 - Real.exp (-1)) (by linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)])
    (by linarith [Real.exp_pos (-1)])
    (fun i => measurableSet_lt (measurable_firstHold i) measurable_const) hsmall ?_ t i j
  · simp only [hd] at hzero
    linarith
  · intro s k l
    obtain ⟨hp, hpi⟩ := ctmc_renewal hQ k l s
    obtain ⟨hP, hPi⟩ := ctmcTransition_renewal hQ k l s
    simp only [hd]
    rw [hp, hP, ← integral_sub hpi hPi]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    by_cases hlt : (s : ℝ≥0∞) < firstHold Q k a
    · simp [hlt, not_le.mpr hlt]
    · simp [hlt, not_lt.mp hlt]

omit [DiscreteMeasurableSpace ι] in
private lemma step_memoryless (hQ : IsRateMatrix Q) (i : ι) (s : ℝ≥0)
    {h : (ι → ι) × ℝ → ℝ} (hm : Measurable h) (hb : ∀ a, |h a| ≤ 1) :
    ∫ a, (if (s : ℝ≥0∞) < firstHold Q i a then h (a.1, a.2 - -Q i i * s) else 0)
        ∂ctmcStepMeasure hQ =
      (ctmcStepMeasure hQ).real {a | (s : ℝ≥0∞) < firstHold Q i a} *
        ∫ a, h a ∂ctmcStepMeasure hQ := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  by_cases h0 : Q i i = 0
  · have hS : ∀ a, firstHold Q i a = ∞ := fun a => by simp [firstHold, h0]
    simp [hS, h0]
  have hq : 0 < -Q i i := lt_of_le_of_ne (neg_nonneg.mpr (hQ.diag_nonpos i))
    (fun h => h0 (by linarith))
  have hc : 0 ≤ -Q i i * s := mul_nonneg hq.le s.2
  have hcond : ∀ a : (ι → ι) × ℝ, (s : ℝ≥0∞) < firstHold Q i a ↔ -Q i i * s < a.2 := by
    intro a
    simp only [firstHold, h0, ite_false]
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff', lt_div_iff₀ hq]
    constructor
    · exact fun h => by linarith [h.1]
    · intro h
      exact ⟨by linarith, div_pos (by linarith) hq⟩
  -- the general identity, for every bounded measurable `g`
  have key : ∀ g : (ι → ι) × ℝ → ℝ, Measurable g → (∀ a, |g a| ≤ 1) →
      ∫ a, (if (s : ℝ≥0∞) < firstHold Q i a then g (a.1, a.2 - -Q i i * s) else 0)
        ∂ctmcStepMeasure hQ = Real.exp (-(-Q i i * s)) * ∫ a, g a ∂ctmcStepMeasure hQ := by
    intro g hgm hgb
    have hgi : Integrable g (ctmcStepMeasure hQ) := Integrable.of_bound hgm.aestronglyMeasurable 1
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hgb a)
    have hFm : Measurable fun a : (ι → ι) × ℝ =>
        if (s : ℝ≥0∞) < firstHold Q i a then g (a.1, a.2 - -Q i i * s) else 0 :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_firstHold i))
        (hgm.comp (measurable_fst.prodMk (measurable_snd.sub_const _))) measurable_const
    have hFi : Integrable (fun a : (ι → ι) × ℝ =>
        if (s : ℝ≥0∞) < firstHold Q i a then g (a.1, a.2 - -Q i i * s) else 0)
        (ctmcStepMeasure hQ) := Integrable.of_bound hFm.aestronglyMeasurable 1
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs]; split_ifs
        · exact hgb _
        · simp)
    unfold ctmcStepMeasure at hgi hFi ⊢
    rw [integral_prod _ hFi, integral_prod _ hgi, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hcond]
    exact integral_expMeasure_memoryless hc (fun e => g (ξ, e))
  have h1 := key (fun _ => 1) measurable_const (fun _ => by simp)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  rw [← integral_indicator_one (measurableSet_lt measurable_const (measurable_firstHold i))]
  rw [key h hm hb]
  congr 1
  rw [← h1]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]

omit [DiscreteMeasurableSpace ι] in
private lemma ctmc_map_cons (hQ : IsRateMatrix Q) :
    ((ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ)).map (fun p => ctmcCons p.1 p.2) =
      ctmcInputMeasure hQ := by
  have hg : Measurable fun ω : ℕ → (ι → ι) × ℝ => (ω 0, ctmcShift 1 ω) :=
    (measurable_pi_apply 0).prodMk (Measurable.of_eval fun j => measurable_pi_apply (1 + j))
  have hc : Measurable fun p : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) => ctmcCons p.1 p.2 := by
    refine Measurable.of_eval fun n => ?_
    cases n with
    | zero => exact measurable_fst
    | succ n => exact (measurable_pi_apply n).comp measurable_snd
  rw [← ctmc_map_first hQ, Measure.map_map hc hg]
  convert Measure.map_id
  funext ω m
  cases m with
  | zero => rfl
  | succ m => simp [ctmcCons, ctmcShift, Nat.add_comm 1 m]

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private lemma integral_ite_split {α : Type*} [MeasurableSpace α] {ν : Measure α} {C : Set α}
    (hC : MeasurableSet C) [DecidablePred (· ∈ C)] {A B : α → ℝ}
    (hF : Integrable (fun a => if a ∈ C then A a else B a) ν) :
    ∫ a, (if a ∈ C then A a else B a) ∂ν =
        ∫ a, (if a ∈ C then A a else 0) ∂ν + ∫ a, (if a ∈ C then 0 else B a) ∂ν ∧
      Integrable (fun a => if a ∈ C then A a else 0) ν ∧
      Integrable (fun a => if a ∈ C then 0 else B a) ν := by
  have h1 : (fun a => if a ∈ C then A a else 0) =
      C.indicator (fun a => if a ∈ C then A a else B a) := by
    funext a; by_cases ha : a ∈ C <;> simp [ha]
  have h2 : (fun a => if a ∈ C then 0 else B a) =
      Cᶜ.indicator (fun a => if a ∈ C then A a else B a) := by
    funext a; by_cases ha : a ∈ C <;> simp [ha]
  have i1 : Integrable (fun a => if a ∈ C then A a else 0) ν := h1 ▸ hF.indicator hC
  have i2 : Integrable (fun a => if a ∈ C then 0 else B a) ν := h2 ▸ hF.indicator hC.compl
  refine ⟨?_, i1, i2⟩
  rw [← integral_add i1 i2]
  congr 1; funext a; by_cases ha : a ∈ C <;> simp [ha]

omit [DiscreteMeasurableSpace ι] in
private lemma prod_real_eq_integral (hQ : IsRateMatrix Q)
    {E : Set (((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ))} (hE : MeasurableSet E) :
    ((ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ)).real E =
        ∫ a, (ctmcInputMeasure hQ).real (Prod.mk a ⁻¹' E) ∂ctmcStepMeasure hQ ∧
      Integrable (fun a => (ctmcInputMeasure hQ).real (Prod.mk a ⁻¹' E))
        (ctmcStepMeasure hQ) := by
  have hint : Integrable (E.indicator (1 : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) → ℝ))
      ((ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ)) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hin : ∀ a, ∫ ω, E.indicator (1 : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) → ℝ) (a, ω)
      ∂ctmcInputMeasure hQ = (ctmcInputMeasure hQ).real (Prod.mk a ⁻¹' E) := by
    intro a
    rw [← integral_indicator_one (measurable_prodMk_left hE)]
    rfl
  have hfub := integral_prod _ hint
  rw [integral_indicator_one hE] at hfub
  simp only [hin] at hfub
  refine ⟨hfub, ?_⟩
  have := hint.integral_prod_left
  simp only [hin] at this
  exact this

omit [Fintype ι] [DecidableEq ι] [DiscreteMeasurableSpace ι] in
private lemma measurable_ctmcCons :
    Measurable fun p : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) => ctmcCons p.1 p.2 := by
  refine Measurable.of_eval fun n => ?_
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

omit [DiscreteMeasurableSpace ι] in
private lemma real_eq_prod_cons (hQ : IsRateMatrix Q) {A : Set (ℕ → (ι → ι) × ℝ)}
    (hA : MeasurableSet A) :
    (ctmcInputMeasure hQ).real A = ((ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ)).real
      ((fun p => ctmcCons p.1 p.2) ⁻¹' A) := by
  conv_lhs => rw [← ctmc_map_cons hQ]
  rw [map_measureReal_apply measurable_ctmcCons hA]

/-- **Restart law at a fixed time** (cf. the Markov property, Norris 1997, §2.8), for events of
`X s` and of the path after `s` only: for the chain started at `i`, the probability that
`X s = k` and that the path after `s` lies in a measurable set `B` is `exp (s Q) i k` times the
probability that the chain started at `k` lies in `B`. This is weaker than the Markov property
with respect to the natural filtration: arbitrary events of the path before `s` are not covered
(only through the finite-dimensional distributions, `ctmcInputMeasure_real_ctmcPath_fdd`). -/
theorem ctmcInputMeasure_real_ctmcPath_add (hQ : IsRateMatrix Q) (i k : ι) (s : ℝ≥0)
    {B : Set (ℝ≥0 → ι)} (hB : MeasurableSet B) :
    (ctmcInputMeasure hQ).real
        {ω | ctmcPath Q i ω s = k ∧ (fun u => ctmcPath Q i ω (s + u)) ∈ B} =
      ctmcTransition Q s i k *
        (ctmcInputMeasure hQ).real {ω | (fun u => ctmcPath Q k ω u) ∈ B} := by
  classical
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set β : ι → ℝ := fun k => (ctmcInputMeasure hQ).real {ω | (fun u => ctmcPath Q k ω u) ∈ B} with hβ
  set L : ℝ≥0 → ι → ι → ℝ := fun s i k =>
    (ctmcInputMeasure hQ).real
      {ω | ctmcPath Q i ω s = k ∧ (fun u => ctmcPath Q i ω (s + u)) ∈ B} with hL
  set p : ℝ≥0 → ι → ι → ℝ := fun s i k =>
    (ctmcInputMeasure hQ).real {ω | ctmcPath Q i ω s = k} with hp
  set g : ι → (ι → ι) × ℝ → ℝ := fun i a =>
    (ctmcInputMeasure hQ).real {ω | (fun u => ctmcPath Q i (ctmcCons a ω) u) ∈ B} with hg
  have hXm : ∀ k, Measurable fun ω : ℕ → (ι → ι) × ℝ => fun u => ctmcPath Q k ω u :=
    fun k => Measurable.of_eval fun u => measurable_ctmcPath k u
  have hXsm : ∀ (s : ℝ≥0) i,
      Measurable fun ω : ℕ → (ι → ι) × ℝ => fun u => ctmcPath Q i ω (s + u) :=
    fun s i => Measurable.of_eval fun u => measurable_ctmcPath i (s + u)
  have hLm : ∀ (s : ℝ≥0) i k, MeasurableSet
      {ω : ℕ → (ι → ι) × ℝ | ctmcPath Q i ω s = k ∧ (fun u => ctmcPath Q i ω (s + u)) ∈ B} :=
    fun s i k => (measurable_ctmcPath i s (measurableSet_singleton k)).inter (hXsm s i hB)
  have hEg : ∀ i, MeasurableSet
      {q : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) | (fun u => ctmcPath Q i (ctmcCons q.1 q.2) u) ∈ B} :=
    fun i => (hXm i).comp measurable_ctmcCons hB
  have hgβ : ∀ i, ∫ a, g i a ∂ctmcStepMeasure hQ = β i := fun i =>
    (prod_real_eq_integral hQ (hEg i)).1.symm.trans (real_eq_prod_cons hQ (hXm i hB)).symm
  have hgm : ∀ i, Measurable (g i) := fun i =>
    (measurable_measure_prodMk_left (hEg i)).ennreal_toReal
  have hgb : ∀ i a, |g i a| ≤ 1 := by
    intro i a
    have h1 := measureReal_nonneg (μ := ctmcInputMeasure hQ)
      (s := {ω | (fun u => ctmcPath Q i (ctmcCons a ω) u) ∈ B})
    have h2 : g i a ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith, h2⟩
  -- the renewal equation for `L`
  have hLren : ∀ (s : ℝ≥0) i k, L s i k =
      (if i = k then (ctmcStepMeasure hQ).real {a | (s : ℝ≥0∞) < firstHold Q i a} * β i else 0) +
        ∫ a, (if a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} then 0
          else L (s - (firstHold Q i a).toNNReal) (a.1 i) k) ∂ctmcStepMeasure hQ ∧
      Integrable (fun a => if a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} then 0
          else L (s - (firstHold Q i a).toNNReal) (a.1 i) k) (ctmcStepMeasure hQ) := by
    intro s i k
    have hE := measurable_ctmcCons (hLm s i k)
    have h1 := real_eq_prod_cons hQ (hLm s i k)
    obtain ⟨h2, h2i⟩ := prod_real_eq_integral hQ hE
    have hslice : ∀ a, (ctmcInputMeasure hQ).real
        (Prod.mk a ⁻¹' ((fun q : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) =>
        ctmcCons q.1 q.2) ⁻¹' {ω | ctmcPath Q i ω s = k ∧
          (fun u => ctmcPath Q i ω (s + u)) ∈ B})) =
        if a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} then
          (if i = k then g i (a.1, a.2 - -Q i i * s) else 0)
        else L (s - (firstHold Q i a).toNNReal) (a.1 i) k := by
      intro a
      by_cases hs : (s : ℝ≥0∞) < firstHold Q i a
      · have hX : ∀ ω, ctmcPath Q i (ctmcCons a ω) s = i := by
          intro ω
          rw [ctmcPath_eq_ite]
          exact ite_eq_left hs
        have hpath : ∀ ω, (fun u => ctmcPath Q i (ctmcCons a ω) (s + u)) =
            fun u => ctmcPath Q i (ctmcCons (a.1, a.2 - -Q i i * s) ω) u :=
          fun ω => funext fun u => ctmcPath_ctmcCons_add i a ω hs u
        rw [ite_eq_left (show a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} from hs)]
        by_cases hik : i = k
        · subst hik
          rw [ite_eq_left rfl]
          congr 1
          ext ω
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, hX, hpath, true_and]
        · rw [ite_eq_right hik]
          have : Prod.mk a ⁻¹' ((fun q : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) =>
              ctmcCons q.1 q.2) ⁻¹' {ω | ctmcPath Q i ω s = k ∧
                (fun u => ctmcPath Q i ω (s + u)) ∈ B}) = ∅ := by
            ext ω
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, hX, Set.mem_empty_iff_false,
              iff_false, not_and]
            exact fun h => absurd h hik
          rw [this, measureReal_empty]
      · have hS : firstHold Q i a ≤ s := not_lt.mp hs
        rw [ite_eq_right (show a ∉ {a | (s : ℝ≥0∞) < firstHold Q i a} from hs)]
        have hX : ∀ ω, ctmcPath Q i (ctmcCons a ω) s =
            ctmcPath Q (a.1 i) ω (s - (firstHold Q i a).toNNReal) := by
          intro ω
          rw [ctmcPath_eq_ite, show ctmcHoldingTime Q i (ctmcCons a ω) 0 = firstHold Q i a from rfl,
            ite_eq_right hs, ctmcShift_one_ctmcCons]
          rfl
        have hpath : ∀ ω, (fun u => ctmcPath Q i (ctmcCons a ω) (s + u)) =
            fun u => ctmcPath Q (a.1 i) ω (s - (firstHold Q i a).toNNReal + u) := by
          intro ω
          funext u
          have := ctmcPath_add_of_le (Q := Q) i (ctmcCons a ω) hS u
          rwa [ctmcShift_one_ctmcCons] at this
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hX, hpath]
    simp only [hslice] at h2 h2i
    obtain ⟨hsp, -, hi2⟩ := integral_ite_split
      (measurableSet_lt measurable_const (measurable_firstHold i)) h2i
    refine ⟨?_, hi2⟩
    change (ctmcInputMeasure hQ).real _ = _
    rw [h1, h2, hsp]
    congr 1
    by_cases hik : i = k
    · simp only [hik, ite_true]
      subst hik
      have := step_memoryless hQ i s (hgm i) (hgb i)
      rw [hgβ] at this
      rw [← this]
      rfl
    · simp [hik]
  -- the renewal equation for `p`
  have hpren : ∀ (s : ℝ≥0) i k, p s i k =
      (if i = k then (ctmcStepMeasure hQ).real {a | (s : ℝ≥0∞) < firstHold Q i a} else 0) +
        ∫ a, (if a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} then 0
          else p (s - (firstHold Q i a).toNNReal) (a.1 i) k) ∂ctmcStepMeasure hQ ∧
      Integrable (fun a => if a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} then 0
          else p (s - (firstHold Q i a).toNNReal) (a.1 i) k) (ctmcStepMeasure hQ) := by
    intro s i k
    obtain ⟨h1, h1i⟩ := ctmc_renewal hQ i k s
    obtain ⟨hsp, -, hi2⟩ := integral_ite_split (A := fun _ => if i = k then (1 : ℝ) else 0)
      (measurableSet_lt measurable_const (measurable_firstHold i)) h1i
    refine ⟨?_, hi2⟩
    change (ctmcInputMeasure hQ).real _ = _
    rw [h1]
    refine hsp.trans ?_
    congr 1
    by_cases hik : i = k
    · subst hik
      simp only [ite_true]
      rw [← integral_indicator_one (measurableSet_lt measurable_const (measurable_firstHold i))]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      by_cases ha : a ∈ {a | (s : ℝ≥0∞) < firstHold Q i a} <;> simp [ha]
    · simp [hik]
  obtain ⟨h, hh, hsmall⟩ := firstHold_small hQ
  set d : ℝ≥0 → ι → ι → ℝ := fun s i k => L s i k - p s i k * β k with hd
  have hbd : ∀ s i k, |d s i k| ≤ 2 := by
    intro s i k
    have a1 := measureReal_nonneg (μ := ctmcInputMeasure hQ)
      (s := {ω | ctmcPath Q i ω s = k ∧ (fun u => ctmcPath Q i ω (s + u)) ∈ B})
    have a2 : L s i k ≤ 1 := measureReal_le_one
    have a3 := measureReal_nonneg (μ := ctmcInputMeasure hQ) (s := {ω | ctmcPath Q i ω s = k})
    have a4 : p s i k ≤ 1 := measureReal_le_one
    have a5 := measureReal_nonneg (μ := ctmcInputMeasure hQ)
      (s := {ω | (fun u => ctmcPath Q k ω u) ∈ B})
    have a6 : β k ≤ 1 := measureReal_le_one
    have : 0 ≤ p s i k * β k := mul_nonneg a3 a5
    have : p s i k * β k ≤ 1 := by nlinarith
    exact abs_le.mpr ⟨by simp only [hd]; linarith, by simp only [hd]; linarith⟩
  have hzero := renewal_eq_zero (ctmcStepMeasure hQ) (firstHold Q) (fun i a => a.1 i) d hbd hh
    (ρ := 1 - Real.exp (-1)) (by linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)])
    (by linarith [Real.exp_pos (-1)])
    (fun i => measurableSet_lt (measurable_firstHold i) measurable_const) hsmall ?_ s i k
  · rw [← hQ.ctmcInputMeasure_real_ctmcPath_eq i k s]
    simp only [hd] at hzero
    change L s i k = p s i k * β k
    linarith
  · intro s i k
    obtain ⟨hL1, hL2⟩ := hLren s i k
    obtain ⟨hp1, hp2⟩ := hpren s i k
    simp only [hd]
    rw [hL1, hp1, add_mul, ← integral_mul_const]
    have hfirst :
        (if i = k then (ctmcStepMeasure hQ).real {a | (s : ℝ≥0∞) < firstHold Q i a} * β i
          else 0) =
        (if i = k then (ctmcStepMeasure hQ).real {a | (s : ℝ≥0∞) < firstHold Q i a} else 0) *
          β k := by
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik]
    rw [hfirst, add_sub_add_left_eq_sub, ← integral_sub hL2 (hp2.mul_const _)]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    by_cases hlt : (s : ℝ≥0∞) < firstHold Q i a
    · simp [hlt, not_le.mpr hlt]
    · simp [hlt, not_lt.mp hlt]

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private lemma sum_Iic_fin_eq {n : ℕ} (s : Fin n → ℝ≥0) (k : Fin n) :
    ∑ l ∈ Iic k, s l = ∑ l, if l ≤ k then s l else 0 := by
  rw [← sum_filter]
  congr 1
  ext l
  simp

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private lemma sum_Iic_zero {n : ℕ} (s : Fin (n + 1) → ℝ≥0) :
    ∑ l ∈ Iic (0 : Fin (n + 1)), s l = s 0 := by
  rw [sum_Iic_fin_eq, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
private lemma sum_Iic_succ {n : ℕ} (s : Fin (n + 1) → ℝ≥0) (k : Fin n) :
    ∑ l ∈ Iic k.succ, s l = s 0 + ∑ l ∈ Iic k, s l.succ := by
  rw [sum_Iic_fin_eq, sum_Iic_fin_eq, Fin.sum_univ_succ]
  simp [Fin.succ_le_succ_iff]

/-- **Finite-dimensional distributions** (Norris 1997, §2.8, Theorem 2.8.2 (c)): with
increments `s 0, …, s (n - 1) ≥ 0`, times `t k = s 0 + ⋯ + s k`, and states `j 0, …, j (n - 1)`,
`P_i(X (t k) = j k for all k) = ∏ₖ exp (s k Q) (j (k - 1)) (j k)`, where `j (-1) = i`. -/
theorem ctmcInputMeasure_real_ctmcPath_fdd (hQ : IsRateMatrix Q) (i : ι) {n : ℕ}
    (s : Fin n → ℝ≥0) (j : Fin n → ι) :
    (ctmcInputMeasure hQ).real {ω | ∀ k, ctmcPath Q i ω (∑ l ∈ Iic k, s l) = j k} =
      ∏ k, ctmcTransition Q (s k) ((Fin.cons i j : Fin (n + 1) → ι) k.castSucc) (j k) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    set B : Set (ℝ≥0 → ι) := {f | ∀ k : Fin n, f (∑ l ∈ Iic k, s l.succ) = j k.succ} with hBdef
    have hB : MeasurableSet B := by
      rw [hBdef, Set.ofPred_forall]
      exact MeasurableSet.iInter fun k =>
        measurableSet_eq_fun (measurable_pi_apply (∑ l ∈ Iic k, s l.succ)) measurable_const
    have hset : {ω | ∀ k, ctmcPath Q i ω (∑ l ∈ Iic k, s l) = j k} =
        {ω | ctmcPath Q i ω (s 0) = j 0 ∧ (fun u => ctmcPath Q i ω (s 0 + u)) ∈ B} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ, sum_Iic_zero, sum_Iic_succ, hBdef]
    rw [hset, hQ.ctmcInputMeasure_real_ctmcPath_add i (j 0) (s 0) hB]
    have hB' : {ω | (fun u => ctmcPath Q (j 0) ω u) ∈ B} =
        {ω | ∀ k : Fin n, ctmcPath Q (j 0) ω (∑ l ∈ Iic k, s (Fin.succ l)) = j (Fin.succ k)} := by
      ext ω; simp [hBdef]
    rw [hB', ih (j 0) (fun l => s l.succ) (fun l => j l.succ), Fin.prod_univ_succ]
    congr 1
    refine prod_congr rfl fun k _ => ?_
    congr 1
    rw [← Fin.succ_castSucc, Fin.cons_succ]
    exact congrFun (Fin.cons_self_tail j) k.castSucc

end IsRateMatrix

end ProbabilityTheory
