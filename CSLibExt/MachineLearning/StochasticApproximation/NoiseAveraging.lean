/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
public import MathlibExt.MeasureTheory.Function.ConditionalExpectation.LebesguePullOut
public import MathlibExt.Analysis.Series.AveragingRecursion
public import MathlibExt.Probability.SqMartingaleConvergence

/-!
# Noise averaging in stochastic approximation

A scalar process driven by step sizes `α t` and noise `w t` follows the recursion
`W (t + 1) = (1 - α t) * W t + α t * w t`. Tsitsiklis (1994), Lemma 1: if the noise is
conditionally centered given the past, with conditional second moment at most an envelope `B t`
that is bounded above along almost every path, and the step sizes lie in `[0, 1]`, have a
divergent sum and have square sums bounded by a deterministic constant, then `W t → 0` almost
surely, from any initial value. Lemma 2 of the same paper is the restarted form: almost surely,
for every `δ > 0`, the recursion restarted from `0` at any late enough time stays within `δ` of
`0` forever. Both are noise-averaging steps of that paper's convergence proofs for asynchronous
stochastic approximation and Q-learning.

## Setting and source conditions

`ℱ : Filtration ℕ m0` is a filtration on a probability space `(Ω, m0, μ)`. The step sizes `α t`
and the envelopes `B t` are real and `ℱ t`-measurable, and the noise `w t` is
`ℱ (t + 1)`-measurable (the source's `w(t - 1)` is `F(t)`-measurable). The conditions of
Tsitsiklis (1994), Lemma 1, are hypotheses of `ae_tendsto_zero`, each assumed almost surely:

* (a) `E[w t | ℱ t] = 0` and (b) `E[w t ^ 2 | ℱ t] ≤ B t`:
  `IsCenteredNoise (ℱ t) μ (w t) (B t)`, which reads a negative `B t` as `0` (see Encoding);
* (c) `α t ∈ [0, 1]`;
* (d) `∑ t, α t = ∞`: the partial sums `∑ t ∈ Finset.range n, α t` tend to infinity;
* (e) `∑ t, α t ^ 2 ≤ C` for a deterministic constant `C`: every partial sum of the squares is
  at most `C`;
* the sequence `B t` is bounded above.

The recursion is also assumed almost surely. Nothing is assumed about the initial value `W 0`,
not even integrability, and nothing about the sign of `B t`, which the source takes nonnegative.

## Encoding

The noise need not be integrable, so (a) and (b) use the conditional Lebesgue expectation
`μ⁻[· | m]` (`MeasureTheory.condLExp`) of `ℝ≥0∞`-valued functions. `IsCenteredNoise m μ w B`
consists of two statements about `μ⁻[· | m]`, each almost everywhere:
`μ⁻[ofReal (w ^ 2) | m] ≤ ofReal B` and `μ⁻[ofReal w | m] = μ⁻[ofReal (-w) | m]`. They are (b)
and (a), a conditional second moment at most `max B 0` and equal conditional expectations of the
positive and negative parts of `w`, when `w` is a.e.-measurable for the ambient σ-algebra `m0`,
`m ≤ m0` and `μ.trim` is σ-finite. In `ae_tendsto_zero` all three hold: `w t` is
`ℱ (t + 1)`-measurable, and every `ℱ t` is a sub-σ-algebra whose trim of a finite measure is
σ-finite. Since `ENNReal.ofReal` sends negative numbers to `0`, the first condition then bounds the
conditional second moment by `max B 0`: for a nonnegative envelope it is (b) itself, and where
`B < 0` it asks the conditional second moment to vanish. Both sides of the centering equality are
finite (`IsCenteredNoise.condLExp_abs_lt_top`), so in that setting it is a genuine centering
condition and not an equality `∞ = ∞`. Outside it the two statements need not mean this: if
`m ≤ m0` fails or `μ.trim` is not σ-finite, `μ⁻[· | m]` is `0` and every `w` satisfies the
contract, and for a `w` that is not a.e.-measurable the lower integrals behind `μ⁻[· | m]` see only
the measurable minorants of `ofReal w` and `ofReal (w ^ 2)`, so a nonnegative `w` that is not
almost everywhere `0` can satisfy it with envelope `0`. The Bochner conditional expectation
`μ[· | m]` is `0` for a non-integrable function, and a real `tsum` is `0` for a divergent series,
so neither is used to state (a), (b), (d) or (e).

## Main definitions

* `IsCenteredNoise m μ w B`: two conditions on `μ⁻[· | m]`; for an a.e.-measurable `w`, a
  sub-σ-algebra `m` and a σ-finite `μ.trim`, `w` is conditionally centered given `m` and its
  conditional second moment is at most `max B 0`.
* `restart α w t₀ n`: the recursion started from `0` at time `t₀`, at time `t₀ + n` (the source's
  `W(t₀ + n; t₀)`).

## Main results

* `IsCenteredNoise.condLExp_abs_lt_top`: `μ⁻[ofReal |w| | m]` is finite almost everywhere.
* `IsCenteredNoise.localize`: for a measurable `w`, a sub-σ-algebra `m` and a finite measure, on an
  `m`-measurable event on which `B ≤ k`, the localized noise is square integrable and
  conditionally centered, with conditional second moment at most `k`, for the Bochner conditional
  expectation.
* `IsCenteredNoise.of_memLp`: square-integrable noise with the usual conditional moment
  conditions satisfies the contract.
* `IsCenteredNoise.div`: dividing by an `m`-measurable `G ≥ G₀ > 0` gives noise with envelope
  `B / G ^ 2`.
* `ae_tendsto_zero`: Tsitsiklis (1994), Lemma 1.
* `ae_uniform_tail_restart`: Tsitsiklis (1994), Lemma 2, on one full-measure event.
* `ae_tendsto_zero_and_uniform_tail_fintype`: both conclusions for finitely many coordinates on
  one common event, with one restart threshold for all coordinates.

## Implementation notes

Fix a level `k`. The cutoff is applied at each step: the localized noise at time `t` is
`{B t ≤ k}.indicator (w t)`, and on this `ℱ t`-measurable event `IsCenteredNoise.localize` turns
the contract into Bochner moment bounds. So the partial sums of `α t * {B t ≤ k}.indicator (w t)`
form a square-integrable martingale whose predictable quadratic variation is at most `k * C`. It
converges almost surely by `MeasureTheory.Martingale.ae_tendsto_of_tendsto_predictableQuadVar`.
Where `B t ≤ k` for every `t`, this series is `∑ t, α t * w t`; intersecting over `k : ℕ` and
applying the deterministic lemma `MetaMathlibExt.tendsto_zero_of_averaging_of_tendsto_sum` path
by path gives Lemma 1.
Lemma 2 follows from Lemma 1 applied to `restart α w 0`, since
`restart α w t₀ n = W (t₀ + n) - (∏ s ∈ Finset.range n, (1 - α (t₀ + s))) * W t₀` for any `W`
that follows the recursion. No Robbins–Siegmund theorem is needed.

## References

* J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning 16
  (1994), 185–202: Assumptions 2 and 3 (p. 188), Lemma 1 (p. 190), the rescaled noise
  `w(t) / G(t)` (p. 191) and Lemma 2 with equation (15) (p. 192).
* T. Jaakkola, M. I. Jordan and S. P. Singh, *On the convergence of stochastic iterative dynamic
  programming algorithms*, MIT A.I. Memo No. 1441 (1993), Appendix, Lemma 1: a related lemma with
  separate gains for the iterate and the noise, a deterministic bound on the conditional variance
  and almost surely finite square sums of the gains. It is a topic reference, not the statement
  formalized here.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Cslib.MachineLearning.StochasticApproximation.NoiseAveraging

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Noise contract.** Two conditions on the conditional Lebesgue expectation `μ⁻[· | m]`,
which needs no integrability of `w`: `μ⁻[ofReal (w ^ 2) | m] ≤ ofReal B` and
`μ⁻[ofReal w | m] = μ⁻[ofReal (-w) | m]`, each almost everywhere. They are conditions (a) and (b)
of Tsitsiklis (1994), Lemma 1, for one step, when `w` is a.e.-measurable for the ambient
σ-algebra `m0`, `m ≤ m0` and `μ.trim` is σ-finite, as for a measurable noise and every σ-algebra
of a filtration under a finite measure. Then the conditional second moment of `w` given `m` is at
most `max B 0`, and the positive part `ofReal w` and the negative part `ofReal (-w)` have the same
conditional expectation. `ENNReal.ofReal` sends a negative `B` to `0`, so for a nonnegative
envelope `B` the bound is the bound by `B` itself, while where `B < 0` it asks the conditional
second moment to vanish, not to be at most `B`. Outside that setting the two conditions need not
mean this: if `m ≤ m0` fails or `μ.trim` is not σ-finite, `μ⁻[· | m]` is `0` and every `w`
satisfies the contract, and a nonnegative `w` that is not a.e.-measurable can satisfy it with
envelope `0` without being almost everywhere `0`. Square-integrable noise with the usual
conditions `μ[w | m] = 0` and `μ[w ^ 2 | m] ≤ B` satisfies it (`IsCenteredNoise.of_memLp`). -/
structure IsCenteredNoise (m : MeasurableSpace Ω) (μ : Measure[m0] Ω) (w B : Ω → ℝ) : Prop where
  /-- `μ⁻[ofReal (w ^ 2) | m] ≤ ofReal B` almost everywhere. In the setting above this is
  condition (b): the conditional second moment of `w` given `m` is at most `B` where `B ≥ 0` and
  `0` where `B < 0`. -/
  condLExp_sq_le : μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] ≤ᵐ[μ] fun ω => ENNReal.ofReal (B ω)
  /-- `μ⁻[ofReal w | m] = μ⁻[ofReal (-w) | m]` almost everywhere. In the setting above this is
  condition (a): the positive and negative parts of `w` have the same conditional expectation
  given `m`. -/
  condLExp_pos_eq_neg :
    μ⁻[fun ω => ENNReal.ofReal (w ω) | m] =ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (-w ω) | m]

/-- **Restarted recursion.** `restart α w t₀ n` is the recursion
`W (t + 1) = (1 - α t) * W t + α t * w t` started from `0` at time `t₀` and evaluated at time
`t₀ + n`: the process `W(t; t₀)` of Tsitsiklis (1994, p. 192) at `t = t₀ + n`. -/
noncomputable def restart (α w : ℕ → Ω → ℝ) (t₀ : ℕ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => (1 - α (t₀ + n) ω) * restart α w t₀ n ω + α (t₀ + n) ω * w (t₀ + n) ω

/-! ### Bridges between the contract and ordinary moment conditions -/

private theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1), abs_nonneg x, sq_abs x]

/-- **Finite conditional Lebesgue expectation of `|w|`.** If `w` satisfies the contract, then
`μ⁻[ofReal |w| | m] < ∞` almost surely, for every `m` and `μ`. Hence both sides of
`IsCenteredNoise.condLExp_pos_eq_neg` are finite almost surely. When `w` is a.e.-measurable,
`m ≤ m0` and `μ.trim` is σ-finite, `μ⁻[ofReal |w| | m]` is the conditional first moment of `w`,
and that equality is therefore a genuine centering condition. Outside that setting it need not
be: if `m ≤ m0` fails or `μ.trim` is not σ-finite, `μ⁻[· | m]` is `0` and every `w` satisfies the
contract, and a nonnegative `w` that is not a.e.-measurable can satisfy it with envelope `0`
without being almost everywhere `0`. -/
theorem IsCenteredNoise.condLExp_abs_lt_top {m : MeasurableSpace Ω} {w B : Ω → ℝ}
    (hw : IsCenteredNoise m μ w B) :
    ∀ᵐ ω ∂μ, μ⁻[fun ω => ENNReal.ofReal |w ω| | m] ω < ∞ := by
  by_cases hm : m ≤ m0
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  have hle : (fun ω => ENNReal.ofReal |w ω|) ≤ᵐ[μ]
      (fun ω => ENNReal.ofReal 1 + ENNReal.ofReal (w ω ^ 2)) := by
    filter_upwards with ω
    calc ENNReal.ofReal |w ω| ≤ ENNReal.ofReal (1 + w ω ^ 2) :=
            ENNReal.ofReal_le_ofReal (abs_le_one_add_sq _)
      _ = ENNReal.ofReal 1 + ENNReal.ofReal (w ω ^ 2) :=
            ENNReal.ofReal_add zero_le_one (sq_nonneg _)
  have hmono : μ⁻[fun ω => ENNReal.ofReal |w ω| | m] ≤ᵐ[μ]
      μ⁻[fun ω => ENNReal.ofReal 1 + ENNReal.ofReal (w ω ^ 2) | m] :=
    condLExp_mono hle
  have hconst : μ⁻[fun _ : Ω => ENNReal.ofReal 1 | m] = fun _ => ENNReal.ofReal 1 :=
    condLExp_const hm μ _
  have hadd : μ⁻[fun ω => ENNReal.ofReal 1 + ENNReal.ofReal (w ω ^ 2) | m]
      =ᵐ[μ] fun ω => ENNReal.ofReal 1 + μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] ω := by
    have h : μ⁻[(fun _ : Ω => ENNReal.ofReal 1) + (fun ω => ENNReal.ofReal (w ω ^ 2)) | m]
        =ᵐ[μ] μ⁻[fun _ : Ω => ENNReal.ofReal 1 | m] + μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] :=
      condLExp_add_left (fun ω => ENNReal.ofReal (w ω ^ 2)) (aemeasurable_const)
    rw [hconst] at h
    exact h
  have hle2 : μ⁻[fun ω => ENNReal.ofReal |w ω| | m] ≤ᵐ[μ]
      fun ω => ENNReal.ofReal 1 + ENNReal.ofReal (B ω) := by
    filter_upwards [hmono, hadd, hw.condLExp_sq_le] with ω h1 h2 h3
    calc μ⁻[fun ω => ENNReal.ofReal |w ω| | m] ω
          ≤ μ⁻[fun ω => ENNReal.ofReal 1 + ENNReal.ofReal (w ω ^ 2) | m] ω := h1
      _ = ENNReal.ofReal 1 + μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] ω := h2
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (B ω) := by gcongr
  filter_upwards [hle2] with ω h
  exact lt_of_le_of_lt h
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **Localized moment bridge.** Let `μ` be a finite measure and `m ≤ m0` a sub-σ-algebra, let
`w` be measurable and satisfy the contract, and let `A` be an `m`-measurable event on which
`B ≤ k`, for a constant `k ≥ 0`. Then the localized noise `A.indicator w` is square integrable,
its Bochner conditional expectation given `m` vanishes, and its Bochner conditional second moment
is at most `k`. Measurability of `w` is for the ambient σ-algebra `m0`. -/
theorem IsCenteredNoise.localize [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {w B : Ω → ℝ} (hwm : Measurable[m0] w)
    (hw : IsCenteredNoise m μ w B) {A : Set Ω} (hA : MeasurableSet[m] A) {k : ℝ} (hk : 0 ≤ k)
    (hBk : ∀ ω ∈ A, B ω ≤ k) :
    MemLp (A.indicator w) 2 μ ∧ μ[A.indicator w | m] =ᵐ[μ] 0 ∧
      μ[fun ω => A.indicator w ω ^ 2 | m] ≤ᵐ[μ] fun _ => k := by
  have hA0 : MeasurableSet[m0] A := hm _ hA
  have hw_ind : Measurable[m0] (A.indicator w) := hwm.indicator hA0
  have hXsq : AEMeasurable[m0] (fun ω => ENNReal.ofReal (w ω ^ 2)) μ :=
    (ENNReal.measurable_ofReal.comp (hwm.pow_const 2)).aemeasurable
  have hsq_congr : (fun ω => ENNReal.ofReal ((A.indicator w ω) ^ 2))
      = A.indicator (fun ω => ENNReal.ofReal (w ω ^ 2)) := by
    ext ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      have h00 : ((0 : ℝ) ^ 2) = 0 := by norm_num
      rw [h00, ENNReal.ofReal_zero]
  have hpull : μ⁻[A.indicator (fun ω => ENNReal.ofReal (w ω ^ 2)) | m]
      =ᵐ[μ] A.indicator (μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m]) :=
    condLExp_indicator hA hXsq
  have hle : μ⁻[A.indicator (fun ω => ENNReal.ofReal (w ω ^ 2)) | m] ≤ᵐ[μ]
      fun _ => ENNReal.ofReal k := by
    filter_upwards [hpull, hw.condLExp_sq_le] with ω hp hsq
    by_cases hω : ω ∈ A
    · rw [hp, Set.indicator_of_mem hω]
      exact hsq.trans (ENNReal.ofReal_le_ofReal (hBk ω hω))
    · rw [hp, Set.indicator_of_notMem hω]
      exact zero_le
  have hfin : ∫⁻ ω, ‖A.indicator w ω ^ 2‖ₑ ∂μ < ∞ := by
    have hcongr : (fun ω => ‖A.indicator w ω ^ 2‖ₑ) =ᵐ[μ]
        fun ω => ENNReal.ofReal ((A.indicator w ω) ^ 2) := by
      filter_upwards with ω
      exact Real.eNorm_eq_ofReal (sq_nonneg _)
    rw [lintegral_congr_ae hcongr, hsq_congr]
    calc ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (w ω ^ 2)) ω ∂μ
        = ∫⁻ ω, μ⁻[A.indicator (fun ω => ENNReal.ofReal (w ω ^ 2)) | m] ω ∂μ :=
          (lintegral_condLExp hm μ _).symm
      _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal k ∂μ := lintegral_mono_ae hle
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
  have hsq_int : Integrable (fun ω => A.indicator w ω ^ 2) μ :=
    ⟨(hw_ind.pow_const 2).aestronglyMeasurable, hfin⟩
  have hmem : MemLp (A.indicator w) 2 μ := by
    rw [memLp_two_iff_integrable_sq hw_ind.aestronglyMeasurable]
    exact hsq_int
  have hg_int : Integrable (A.indicator w) μ := hmem.integrable one_le_two
  have hcond0 : μ[A.indicator w | m] =ᵐ[μ] 0 := by
    have h0 : (0 : Ω → ℝ) =ᵐ[μ] μ[A.indicator w | m] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq hm hg_int ?_ ?_ ?_
      · intro s hs hμs
        exact (integrable_const (0 : ℝ)).integrableOn
      · intro s hs hμs
        have hzero : ∫ x in s, (0 : Ω → ℝ) x ∂μ = 0 := by
          simp only [Pi.zero_apply, setIntegral_const, smul_zero]
        rw [hzero]
        symm
        have hs0 : MeasurableSet[m0] s := hm _ hs
        have ht : MeasurableSet[m] (s ∩ A) := hs.inter hA
        have hu : Integrable (s.indicator (A.indicator w)) μ := hg_int.indicator hs0
        have huint := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu
        have hL1 : (fun x => ENNReal.ofReal (s.indicator (A.indicator w) x))
            = (s ∩ A).indicator (fun x => ENNReal.ofReal (w x)) := by
          ext x
          by_cases hxs : x ∈ s <;> by_cases hxA : x ∈ A
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxA,
              Set.indicator_of_mem ((⟨hxs, hxA⟩ : x ∈ s ∩ A))]
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxA,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxA h.2)]
            exact ENNReal.ofReal_zero
          · rw [Set.indicator_of_notMem hxs,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxs h.1)]
            exact ENNReal.ofReal_zero
          · rw [Set.indicator_of_notMem hxs,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxs h.1)]
            exact ENNReal.ofReal_zero
        have hL2 : (fun x => ENNReal.ofReal (-s.indicator (A.indicator w) x))
            = (s ∩ A).indicator (fun x => ENNReal.ofReal (-w x)) := by
          ext x
          by_cases hxs : x ∈ s <;> by_cases hxA : x ∈ A
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxA,
              Set.indicator_of_mem ((⟨hxs, hxA⟩ : x ∈ s ∩ A))]
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxA,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxA h.2)]
            rw [neg_zero, ENNReal.ofReal_zero]
          · rw [Set.indicator_of_notMem hxs,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxs h.1)]
            rw [neg_zero, ENNReal.ofReal_zero]
          · rw [Set.indicator_of_notMem hxs,
              Set.indicator_of_notMem (fun h : x ∈ s ∩ A => hxs h.1)]
            rw [neg_zero, ENNReal.ofReal_zero]
        have hAeq : ∫⁻ x, ENNReal.ofReal (s.indicator (A.indicator w) x) ∂μ
            = ∫⁻ x in s ∩ A, ENNReal.ofReal (w x) ∂μ := by
          rw [hL1, lintegral_indicator (hm _ ht)]
        have hBeq : ∫⁻ x, ENNReal.ofReal (-s.indicator (A.indicator w) x) ∂μ
            = ∫⁻ x in s ∩ A, ENNReal.ofReal (-w x) ∂μ := by
          rw [hL2, lintegral_indicator (hm _ ht)]
        have hAB : ∫⁻ x in s ∩ A, ENNReal.ofReal (w x) ∂μ
            = ∫⁻ x in s ∩ A, ENNReal.ofReal (-w x) ∂μ := by
          have e1 : ∫⁻ x in s ∩ A, ENNReal.ofReal (w x) ∂μ
              = ∫⁻ x in s ∩ A, μ⁻[fun ω => ENNReal.ofReal (w ω) | m] x ∂μ :=
            (setLIntegral_condLExp hm μ _ ht).symm
          have e2 : ∫⁻ x in s ∩ A, μ⁻[fun ω => ENNReal.ofReal (w ω) | m] x ∂μ
              = ∫⁻ x in s ∩ A, μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] x ∂μ := by
            apply setLIntegral_congr_fun_ae (hm _ ht)
            filter_upwards [hw.condLExp_pos_eq_neg] with x h _ using h
          have e3 : ∫⁻ x in s ∩ A, μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] x ∂μ
              = ∫⁻ x in s ∩ A, ENNReal.ofReal (-w x) ∂μ :=
            setLIntegral_condLExp hm μ _ ht
          exact e1.trans (e2.trans e3)
        have hss : ∫ x in s, A.indicator w x ∂μ = ∫ x, s.indicator (A.indicator w) x ∂μ :=
          (integral_indicator hs0).symm
        rw [hss, huint, hAeq, hBeq, hAB, sub_self]
      · exact aestronglyMeasurable_zero
    exact h0.symm
  have hcondle : μ[fun ω => A.indicator w ω ^ 2 | m] ≤ᵐ[μ] fun _ => k := by
    have hnonneg : 0 ≤ᵐ[μ] (fun ω => A.indicator w ω ^ 2) := by
      filter_upwards with ω
      exact sq_nonneg _
    have heq : μ⁻[fun ω => ENNReal.ofReal ((A.indicator w ω) ^ 2) | m] =ᵐ[μ]
        (fun ω => ENNReal.ofReal (μ[fun ω => A.indicator w ω ^ 2 | m] ω)) :=
      condLExp_ofReal m hsq_int hnonneg
    have hLHS : μ⁻[fun ω => ENNReal.ofReal ((A.indicator w ω) ^ 2) | m] ≤ᵐ[μ]
        fun _ => ENNReal.ofReal k := by
      rw [hsq_congr]
      exact hle
    have hle2 : (fun ω => ENNReal.ofReal (μ[fun ω => A.indicator w ω ^ 2 | m] ω)) ≤ᵐ[μ]
        fun _ => ENNReal.ofReal k :=
      heq.symm.trans_le hLHS
    filter_upwards [hle2] with ω h
    exact (ENNReal.ofReal_le_ofReal_iff hk).mp h
  exact ⟨hmem, hcond0, hcondle⟩

/-- **Square-integrable noise satisfies the contract.** Under a finite measure `μ`, if `w` is
square integrable with the usual conditional moment conditions, `μ[w | m] = 0` and
`μ[w ^ 2 | m] ≤ B` almost surely, then `IsCenteredNoise m μ w B`. -/
theorem IsCenteredNoise.of_memLp [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    {w B : Ω → ℝ} (hw2 : MemLp w 2 μ) (hmean : μ[w | m] =ᵐ[μ] 0)
    (hsq : μ[fun ω => w ω ^ 2 | m] ≤ᵐ[μ] B) :
    IsCenteredNoise m μ w B := by
  have hw_int : Integrable w μ := hw2.integrable one_le_two
  have hsq_int : Integrable (fun ω => w ω ^ 2) μ := hw2.integrable_sq
  have hwfin : ∫⁻ x, ‖w x‖ₑ ∂μ < ∞ := hw_int.2
  refine ⟨?_, ?_⟩
  · have hnonneg : 0 ≤ᵐ[μ] (fun ω => w ω ^ 2) := by
      filter_upwards with ω
      exact sq_nonneg _
    have heq : μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] =ᵐ[μ]
        (fun ω => ENNReal.ofReal (μ[fun ω => w ω ^ 2 | m] ω)) :=
      condLExp_ofReal m hsq_int hnonneg
    have hle : (fun ω => ENNReal.ofReal (μ[fun ω => w ω ^ 2 | m] ω)) ≤ᵐ[μ]
        (fun ω => ENNReal.ofReal (B ω)) := by
      filter_upwards [hsq] with ω h
      exact ENNReal.ofReal_le_ofReal h
    exact heq.trans_le hle
  · by_cases hm : m ≤ m0
    · have hY : Measurable[m] (μ⁻[fun ω => ENNReal.ofReal (-w ω) | m]) :=
        measurable_condLExp m μ _
      have hXY : ∀ s, MeasurableSet[m] s →
          ∫⁻ ω in s, μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] ω ∂μ
            = ∫⁻ ω in s, ENNReal.ofReal (w ω) ∂μ := by
        intro s hs
        rw [setLIntegral_condLExp hm μ _ hs]
        have hs0 : MeasurableSet[m0] s := hm _ hs
        have hv : Integrable (s.indicator w) μ := hw_int.indicator hs0
        have hset0 : ∫ x in s, w x ∂μ = 0 := by
          have h1 : ∫ x in s, w x ∂μ = ∫ x in s, μ[w | m] x ∂μ :=
            (setIntegral_condExp hm hw_int hs).symm
          have h2 : ∫ x in s, μ[w | m] x ∂μ = ∫ x in s, (0 : Ω → ℝ) x ∂μ := by
            apply setIntegral_congr_ae (hm _ hs)
            filter_upwards [hmean] with x hx _ using hx
          rw [h1, h2]
          simp only [Pi.zero_apply, setIntegral_const, smul_zero]
        have hC1 : (fun x => ENNReal.ofReal (s.indicator w x))
            = s.indicator (fun x => ENNReal.ofReal (w x)) := by
          ext x
          by_cases hxs : x ∈ s
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs]
          · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]
            exact ENNReal.ofReal_zero
        have hC2 : (fun x => ENNReal.ofReal (-s.indicator w x))
            = s.indicator (fun x => ENNReal.ofReal (-w x)) := by
          ext x
          by_cases hxs : x ∈ s
          · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs]
          · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]
            rw [neg_zero, ENNReal.ofReal_zero]
        have hL1eq : ∫⁻ x, ENNReal.ofReal (s.indicator w x) ∂μ
            = ∫⁻ x in s, ENNReal.ofReal (w x) ∂μ := by
          rw [hC1, lintegral_indicator (hm _ hs)]
        have hL2eq : ∫⁻ x, ENNReal.ofReal (-s.indicator w x) ∂μ
            = ∫⁻ x in s, ENNReal.ofReal (-w x) ∂μ := by
          rw [hC2, lintegral_indicator (hm _ hs)]
        have hv_eq : ∫ x in s, w x ∂μ = ∫ x, s.indicator w x ∂μ :=
          (integral_indicator hs0).symm
        rw [hv_eq, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hv, hL1eq, hL2eq] at hset0
        have hAf : ∫⁻ x in s, ENNReal.ofReal (w x) ∂μ ≠ ∞ := by
          have h1 : ∫⁻ x in s, ENNReal.ofReal (w x) ∂μ ≤ ∫⁻ x, ‖w x‖ₑ ∂μ :=
            (setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae (by
              filter_upwards with x
              calc ENNReal.ofReal (w x) ≤ ENNReal.ofReal |w x| :=
                      ENNReal.ofReal_le_ofReal (le_abs_self _)
                _ = ‖w x‖ₑ := (Real.eNorm_eq_ofReal_abs _).symm))
          exact ne_of_lt (lt_of_le_of_lt h1 hwfin)
        have hBf : ∫⁻ x in s, ENNReal.ofReal (-w x) ∂μ ≠ ∞ := by
          have h1 : ∫⁻ x in s, ENNReal.ofReal (-w x) ∂μ ≤ ∫⁻ x, ‖w x‖ₑ ∂μ :=
            (setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae (by
              filter_upwards with x
              calc ENNReal.ofReal (-w x) ≤ ENNReal.ofReal |w x| :=
                      ENNReal.ofReal_le_ofReal (neg_le_abs _)
                _ = ‖w x‖ₑ := (Real.eNorm_eq_ofReal_abs _).symm))
          exact ne_of_lt (lt_of_le_of_lt h1 hwfin)
        have htoReal : (∫⁻ x in s, ENNReal.ofReal (w x) ∂μ).toReal
            = (∫⁻ x in s, ENNReal.ofReal (-w x) ∂μ).toReal :=
          sub_eq_zero.mp hset0
        exact ((ENNReal.toReal_eq_toReal_iff' hAf hBf).mp htoReal).symm
      have heq : μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] =ᵐ[μ]
          μ⁻[fun ω => ENNReal.ofReal (w ω) | m] :=
        ae_eq_condLExp hm μ _ hY hXY
      exact heq.symm
    · have e1 : μ⁻[fun ω => ENNReal.ofReal (w ω) | m] = 0 := condLExp_of_not_le hm
      have e2 : μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] = 0 := condLExp_of_not_le hm
      rw [e1, e2]

/-- **Predictable positive-scaling bridge.** If `w` is measurable and satisfies the contract with
envelope `B`, and `G` is `m`-measurable with `G ≥ G₀` almost surely for a constant `G₀ > 0`, then
`w / G` satisfies the contract with envelope `B / G ^ 2`. This is the rescaled noise
`w(t) / G(t)` of Tsitsiklis (1994, pp. 191–192, proof of Theorem 1). Measurability of `w` is for
the ambient σ-algebra `m0`. -/
theorem IsCenteredNoise.div {m : MeasurableSpace Ω}
    {w B G : Ω → ℝ} {G₀ : ℝ} (hwm : Measurable[m0] w) (hGm : StronglyMeasurable[m] G)
    (hG₀ : 0 < G₀) (hG : ∀ᵐ ω ∂μ, G₀ ≤ G ω) (hw : IsCenteredNoise m μ w B) :
    IsCenteredNoise m μ (fun ω => w ω / G ω) (fun ω => B ω / G ω ^ 2) := by
  have hGne : ∀ᵐ ω ∂μ, G ω ≠ 0 := by
    filter_upwards [hG] with ω h
    exact ne_of_gt (lt_of_lt_of_le hG₀ h)
  have hGnn : ∀ᵐ ω ∂μ, 0 ≤ 1 / G ω := by
    filter_upwards [hG] with ω h
    exact one_div_nonneg.mpr (le_trans hG₀.le h)
  have hGmeas : Measurable[m] G := hGm.measurable
  have hInv : Measurable[m] (fun ω => 1 / G ω) := measurable_const.div hGmeas
  have hInv2 : Measurable[m] (fun ω => 1 / G ω ^ 2) :=
    measurable_const.div (hGmeas.pow_const 2)
  have hInvE : Measurable[m] (fun ω => ENNReal.ofReal (1 / G ω)) :=
    ENNReal.measurable_ofReal.comp hInv
  have hInv2E : Measurable[m] (fun ω => ENNReal.ofReal (1 / G ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp hInv2
  have hXsq : AEMeasurable[m0] (fun ω => ENNReal.ofReal (w ω ^ 2)) μ :=
    (ENNReal.measurable_ofReal.comp (hwm.pow_const 2)).aemeasurable
  have hXpos : AEMeasurable[m0] (fun ω => ENNReal.ofReal (w ω)) μ :=
    (ENNReal.measurable_ofReal.comp hwm).aemeasurable
  have hXneg : AEMeasurable[m0] (fun ω => ENNReal.ofReal (-w ω)) μ :=
    (ENNReal.measurable_ofReal.comp hwm.neg).aemeasurable
  refine ⟨?_, ?_⟩
  · show μ⁻[fun ω => ENNReal.ofReal ((w ω / G ω) ^ 2) | m] ≤ᵐ[μ]
        fun ω => ENNReal.ofReal (B ω / G ω ^ 2)
    have hG2nn : ∀ᵐ ω ∂μ, 0 ≤ 1 / G ω ^ 2 := by
      filter_upwards with ω
      exact one_div_nonneg.mpr (sq_nonneg _)
    have hcongr1 : (fun ω => ENNReal.ofReal ((w ω / G ω) ^ 2)) =ᵐ[μ]
        ((fun ω => ENNReal.ofReal (1 / G ω ^ 2)) * (fun ω => ENNReal.ofReal (w ω ^ 2))) := by
      filter_upwards [hGne, hG2nn] with ω hne hnn
      have halb : (w ω / G ω) ^ 2 = (1 / G ω ^ 2) * w ω ^ 2 := by
        rw [div_pow, div_eq_mul_one_div, mul_comm]
      rw [halb, ENNReal.ofReal_mul hnn, Pi.mul_apply]
    have hpull1 :
        μ⁻[(fun ω => ENNReal.ofReal (1 / G ω ^ 2)) * (fun ω => ENNReal.ofReal (w ω ^ 2)) | m]
        =ᵐ[μ] (fun ω => ENNReal.ofReal (1 / G ω ^ 2)) * μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] :=
      condLExp_mul_of_measurable_left hInv2E hXsq
    have heq1 : μ⁻[fun ω => ENNReal.ofReal ((w ω / G ω) ^ 2) | m] =ᵐ[μ]
        (fun ω => ENNReal.ofReal (1 / G ω ^ 2)) * μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] :=
      (condLExp_congr_ae hcongr1).trans hpull1
    filter_upwards [heq1, hw.condLExp_sq_le, hGne] with ω he hsq hne
    have hG2nn' : (0 : ℝ) ≤ 1 / G ω ^ 2 := one_div_nonneg.mpr (sq_nonneg _)
    calc μ⁻[fun ω => ENNReal.ofReal ((w ω / G ω) ^ 2) | m] ω
        = ENNReal.ofReal (1 / G ω ^ 2) * μ⁻[fun ω => ENNReal.ofReal (w ω ^ 2) | m] ω := he
      _ ≤ ENNReal.ofReal (1 / G ω ^ 2) * ENNReal.ofReal (B ω) := by gcongr
      _ ≤ ENNReal.ofReal (B ω / G ω ^ 2) := by
          by_cases hB : 0 ≤ B ω
          · have halb : (1 / G ω ^ 2) * B ω = B ω / G ω ^ 2 := by
              conv_rhs => rw [div_eq_mul_one_div]
              rw [mul_comm]
            have heq : ENNReal.ofReal (1 / G ω ^ 2) * ENNReal.ofReal (B ω)
                = ENNReal.ofReal (B ω / G ω ^ 2) := by
              calc ENNReal.ofReal (1 / G ω ^ 2) * ENNReal.ofReal (B ω)
                  = ENNReal.ofReal ((1 / G ω ^ 2) * B ω) := (ENNReal.ofReal_mul hG2nn').symm
                _ = ENNReal.ofReal (B ω / G ω ^ 2) := by rw [halb]
            exact le_of_eq heq
          · have hB0 : ENNReal.ofReal (B ω) = 0 :=
              ENNReal.ofReal_of_nonpos (le_of_lt (lt_of_not_ge hB))
            rw [hB0, mul_zero]
            exact zero_le
  · show μ⁻[fun ω => ENNReal.ofReal (w ω / G ω) | m] =ᵐ[μ]
        μ⁻[fun ω => ENNReal.ofReal (-(w ω / G ω)) | m]
    have hcongrL : (fun ω => ENNReal.ofReal (w ω / G ω)) =ᵐ[μ]
        ((fun ω => ENNReal.ofReal (1 / G ω)) * (fun ω => ENNReal.ofReal (w ω))) := by
      filter_upwards [hGnn] with ω hnn
      have halb : w ω / G ω = (1 / G ω) * w ω := by
        rw [div_eq_mul_one_div, mul_comm]
      rw [halb, ENNReal.ofReal_mul hnn, Pi.mul_apply]
    have hcongrR : (fun ω => ENNReal.ofReal (-(w ω / G ω))) =ᵐ[μ]
        ((fun ω => ENNReal.ofReal (1 / G ω)) * (fun ω => ENNReal.ofReal (-w ω))) := by
      filter_upwards [hGnn] with ω hnn
      have halb : -(w ω / G ω) = (1 / G ω) * (-w ω) := by
        rw [div_eq_mul_one_div]
        ring
      rw [halb, ENNReal.ofReal_mul hnn, Pi.mul_apply]
    have hpullL : μ⁻[(fun ω => ENNReal.ofReal (1 / G ω)) * (fun ω => ENNReal.ofReal (w ω)) | m]
        =ᵐ[μ] (fun ω => ENNReal.ofReal (1 / G ω)) * μ⁻[fun ω => ENNReal.ofReal (w ω) | m] :=
      condLExp_mul_of_measurable_left hInvE hXpos
    have hpullR : μ⁻[(fun ω => ENNReal.ofReal (1 / G ω)) * (fun ω => ENNReal.ofReal (-w ω)) | m]
        =ᵐ[μ] (fun ω => ENNReal.ofReal (1 / G ω)) * μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] :=
      condLExp_mul_of_measurable_left hInvE hXneg
    calc μ⁻[fun ω => ENNReal.ofReal (w ω / G ω) | m]
        =ᵐ[μ] (fun ω => ENNReal.ofReal (1 / G ω)) * μ⁻[fun ω => ENNReal.ofReal (w ω) | m] :=
          (condLExp_congr_ae hcongrL).trans hpullL
      _ =ᵐ[μ] (fun ω => ENNReal.ofReal (1 / G ω)) * μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] := by
          filter_upwards [hw.condLExp_pos_eq_neg] with ω h
          change ENNReal.ofReal (1 / G ω) * μ⁻[fun ω => ENNReal.ofReal (w ω) | m] ω
            = ENNReal.ofReal (1 / G ω) * μ⁻[fun ω => ENNReal.ofReal (-w ω) | m] ω
          rw [h]
      _ =ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (-(w ω / G ω)) | m] :=
          ((condLExp_congr_ae hcongrR).trans hpullR).symm

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {α w B W : ℕ → Ω → ℝ} {C : ℝ}

private noncomputable def localizedNoise (B w : ℕ → Ω → ℝ) (k : ℝ) (t : ℕ) : Ω → ℝ :=
  {ω | B t ω ≤ k}.indicator (w t)

private noncomputable def localizedSum (α B w : ℕ → Ω → ℝ) (k : ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ t ∈ Finset.range n, (α t * localizedNoise B w k t)

private theorem localizedSum_succ_sub (α B w : ℕ → Ω → ℝ) (k : ℝ) (i : ℕ) :
    localizedSum α B w k (i + 1) - localizedSum α B w k i
      = α i * localizedNoise B w k i := by
  funext ω
  simp only [localizedSum, Pi.sub_apply, Finset.sum_apply, Finset.sum_range_succ,
    Pi.mul_apply, Pi.add_apply]
  ring

private theorem measurableSet_envelope_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m0} {B : ℕ → Ω → ℝ}
    (hB_adapted : StronglyAdapted ℱ B) (t : ℕ) (k : ℕ) :
    MeasurableSet[ℱ t] {ω | B t ω ≤ (k : ℝ)} :=
  measurableSet_le (hB_adapted t).measurable measurable_const

private theorem localizedNoise_moments {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {w B : ℕ → Ω → ℝ}
    (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (t : ℕ) (k : ℕ) :
    MemLp (localizedNoise B w ↑k t) 2 μ
      ∧ μ[localizedNoise B w ↑k t | ℱ t] =ᵐ[μ] 0
      ∧ μ[fun ω => localizedNoise B w ↑k t ω ^ 2 | ℱ t] ≤ᵐ[μ] fun _ => (k : ℝ) := by
  have hA := measurableSet_envelope_le hB_adapted t k
  have hw0 : Measurable[m0] (w t) := ((hw_meas t).mono (ℱ.le (t + 1))).measurable
  exact (hw t).localize (ℱ.le t) hw0 hA (Nat.cast_nonneg k) (fun ω h => h)

private theorem stepSize_bounds {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {α : ℕ → Ω → ℝ}
    (hα_adapted : StronglyAdapted ℱ α)
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    AEStronglyMeasurable (α t) μ ∧ (∀ᵐ ω ∂μ, ‖α t ω‖ ≤ (1 : ℝ))
      ∧ AEStronglyMeasurable ((α t) ^ 2) μ
      ∧ (∀ᵐ ω ∂μ, ‖((α t) ^ 2) ω‖ ≤ (1 : ℝ)) := by
  have hm0 : StronglyMeasurable[m0] (α t) := (hα_adapted t).mono (ℱ.le t)
  have h01 : ∀ᵐ ω ∂μ, α t ω ∈ Set.Icc (0 : ℝ) 1 := hα01.mono (fun ω h => h t)
  refine ⟨hm0.aestronglyMeasurable, ?_, (hm0.pow 2).aestronglyMeasurable, ?_⟩
  · filter_upwards [h01] with ω h
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  · filter_upwards [h01] with ω h
    have h2 : (α t ω) ^ 2 ≤ 1 := pow_le_one₀ h.1 h.2
    rw [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (α t ω))]
    exact h2

private theorem martingale_localizedSum {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {α w B : ℕ → Ω → ℝ}
    (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    Martingale (localizedSum α B w ↑k) ℱ μ := by
  have hmem : ∀ t, MemLp (localizedNoise B w ↑k t) 2 μ :=
    fun t => (localizedNoise_moments hB_adapted hw_meas hw t k).1
  have hmean : ∀ t, μ[localizedNoise B w ↑k t | ℱ t] =ᵐ[μ] 0 :=
    fun t => (localizedNoise_moments hB_adapted hw_meas hw t k).2.1
  have hα := fun t => stepSize_bounds hα_adapted hα01 t
  have hwk_int : ∀ t, Integrable (localizedNoise B w ↑k t) μ :=
    fun t => (hmem t).integrable (by norm_num)
  have hterm_int : ∀ t, Integrable (α t * localizedNoise B w ↑k t) μ := fun t =>
    Integrable.bdd_mul (hwk_int t) (hα t).1 (hα t).2.1
  have hadp : StronglyAdapted ℱ (localizedSum α B w ↑k) := fun n => by
    change StronglyMeasurable[ℱ n]
      (∑ t ∈ Finset.range n, (α t * localizedNoise B w ↑k t))
    refine Finset.stronglyMeasurable_sum _ (fun t ht => ?_)
    have htn : t < n := Finset.mem_range.mp ht
    have hαn : StronglyMeasurable[ℱ n] (α t) :=
      (hα_adapted t).mono (ℱ.mono (Nat.le_of_lt htn))
    have hwn : StronglyMeasurable[ℱ n] (w t) :=
      (hw_meas t).mono (ℱ.mono (Nat.succ_le_of_lt htn))
    have hBtn : StronglyMeasurable[ℱ n] (B t) :=
      (hB_adapted t).mono (ℱ.mono (Nat.le_of_lt htn))
    have hAn : MeasurableSet[ℱ n] {ω | B t ω ≤ (k : ℝ)} :=
      measurableSet_le hBtn.measurable measurable_const
    exact hαn.mul (hwn.indicator hAn)
  have hint : ∀ n, Integrable (localizedSum α B w ↑k n) μ := fun n => by
    change Integrable (∑ t ∈ Finset.range n, (α t * localizedNoise B w ↑k t)) μ
    exact integrable_finsetSum' _ (fun t _ => hterm_int t)
  have hsub : ∀ i, μ[localizedSum α B w ↑k (i + 1) - localizedSum α B w ↑k i
      | ℱ i] =ᵐ[μ] 0 := fun i => by
    rw [localizedSum_succ_sub]
    calc μ[α i * localizedNoise B w ↑k i | ℱ i]
        =ᵐ[μ] α i * μ[localizedNoise B w ↑k i | ℱ i] :=
          condExp_mul_of_stronglyMeasurable_left (hα_adapted i) (hterm_int i)
            (hwk_int i)
      _ =ᵐ[μ] α i * 0 := (hmean i).mul_left
      _ = 0 := by simp
  exact martingale_of_condExp_sub_eq_zero_nat hadp hint hsub

private theorem ae_exists_tendsto_localizedSum {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {α w B : ℕ → Ω → ℝ} {C : ℝ}
    (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C)
    (k : ℕ) :
    ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun n => localizedSum α B w ↑k n ω) atTop (𝓝 l) := by
  have hmem : ∀ t, MemLp (localizedNoise B w ↑k t) 2 μ :=
    fun t => (localizedNoise_moments hB_adapted hw_meas hw t k).1
  have hsqc : ∀ t, μ[fun ω => localizedNoise B w ↑k t ω ^ 2 | ℱ t] ≤ᵐ[μ]
      fun _ => (k : ℝ) :=
    fun t => (localizedNoise_moments hB_adapted hw_meas hw t k).2.2
  have hα := fun t => stepSize_bounds hα_adapted hα01 t
  have hwk2_int : ∀ t, Integrable (fun ω => localizedNoise B w ↑k t ω ^ 2) μ :=
    fun t => (memLp_two_iff_integrable_sq (hmem t).aestronglyMeasurable).mp (hmem t)
  have hprod_int : ∀ t,
      Integrable ((α t) ^ 2 * (fun ω => localizedNoise B w ↑k t ω ^ 2)) μ :=
    fun t => by
      change Integrable (fun ω => ((α t) ^ 2) ω * localizedNoise B w ↑k t ω ^ 2) μ
      exact Integrable.bdd_mul (hwk2_int t) (hα t).2.2.1 (hα t).2.2.2
  have hQeq : ∀ t, (fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2)
      = (α t) ^ 2 * (fun ω => localizedNoise B w ↑k t ω ^ 2) := fun t => by
    funext ω'
    have h := congrFun (localizedSum_succ_sub α B w ↑k t) ω'
    simp only [Pi.sub_apply, Pi.mul_apply] at h
    rw [h, mul_pow, Pi.mul_apply, Pi.pow_apply]
  have hpull2 : ∀ t, μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]
      =ᵐ[μ] (α t) ^ 2 * μ[fun ω => localizedNoise B w ↑k t ω ^ 2 | ℱ t] :=
    fun t => by
      rw [hQeq t]
      exact condExp_mul_of_stronglyMeasurable_left ((hα_adapted t).pow 2)
        (hprod_int t) (hwk2_int t)
  have hQ : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω
        ∧ (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
          - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω
          ≤ (α t ω) ^ 2 * (k : ℝ) := fun t => by
    have hnn : ∀ᵐ ω ∂μ, 0 ≤ (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω :=
      condExp_nonneg (Eventually.of_forall (fun ω' => sq_nonneg _))
    have hle : ∀ᵐ ω ∂μ, (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω
        ≤ (α t ω) ^ 2 * (k : ℝ) := by
      filter_upwards [hpull2 t, hsqc t] with ω heqω hsqω
      rw [heqω, Pi.mul_apply, Pi.pow_apply]
      exact mul_le_mul_of_nonneg_left hsqω (sq_nonneg _)
    exact hnn.and hle
  have hQall : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
        - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω
        ∧ (μ[fun ω' => (localizedSum α B w ↑k (t + 1) ω'
          - localizedSum α B w ↑k t ω') ^ 2 | ℱ t]) ω
          ≤ (α t ω) ^ 2 * (k : ℝ) :=
    ae_all_iff.mpr hQ
  have hquad : ∀ᵐ ω ∂μ, ∃ l, Tendsto
      (fun n => predictableQuadraticVariation μ ℱ (localizedSum α B w ↑k) n ω)
      atTop (𝓝 l) := by
    filter_upwards [hQall, hα_sq] with ω hQω hsqω
    refine ⟨_, tendsto_atTop_ciSup ?_ ?_⟩
    · apply monotone_nat_of_le_succ
      intro n
      have h0 := (hQω n).1
      simp only [predictableQuadraticVariation, Finset.sum_range_succ]
      linarith
    · refine ⟨(k : ℝ) * C, ?_⟩
      rintro _ ⟨n, rfl⟩
      simp only [predictableQuadraticVariation]
      calc ∑ j ∈ Finset.range n, (μ[fun ω' => (localizedSum α B w ↑k (j + 1) ω'
              - localizedSum α B w ↑k j ω') ^ 2 | ℱ j]) ω
            ≤ ∑ j ∈ Finset.range n, ((α j ω) ^ 2 * (k : ℝ)) :=
              Finset.sum_le_sum (fun j _ => (hQω j).2)
        _ = (∑ j ∈ Finset.range n, (α j ω) ^ 2) * (k : ℝ) := by
              rw [← Finset.sum_mul]
        _ ≤ C * (k : ℝ) :=
              mul_le_mul_of_nonneg_right (hsqω n) (Nat.cast_nonneg k)
        _ = (k : ℝ) * C := mul_comm _ _
  have hmem2 : ∀ t, MemLp (α t * localizedNoise B w ↑k t) 2 μ := fun t => by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · have hαm0 : StronglyMeasurable[m0] (α t) := (hα_adapted t).mono (ℱ.le t)
      have hwm0 : StronglyMeasurable[m0] (w t) := (hw_meas t).mono (ℱ.le (t + 1))
      have hBm0 : StronglyMeasurable[m0] (B t) := (hB_adapted t).mono (ℱ.le t)
      have hAm0 : MeasurableSet[m0] {ω | B t ω ≤ (k : ℝ)} :=
        measurableSet_le hBm0.measurable measurable_const
      have hwkm0 : StronglyMeasurable[m0] (localizedNoise B w ↑k t) :=
        hwm0.indicator hAm0
      exact (hαm0.mul hwkm0).aestronglyMeasurable
    · have hfeq : (fun ω => ((α t * localizedNoise B w ↑k t) ω) ^ 2)
          = fun ω => ((α t) ^ 2) ω * localizedNoise B w ↑k t ω ^ 2 := by
        funext ω
        simp only [Pi.mul_apply, Pi.pow_apply, mul_pow]
      rw [hfeq]
      exact Integrable.bdd_mul (hwk2_int t) (hα t).2.2.1 (hα t).2.2.2
  have hMmem : ∀ n, MemLp (localizedSum α B w ↑k n) 2 μ := fun n => by
    change MemLp (∑ t ∈ Finset.range n, (α t * localizedNoise B w ↑k t)) 2 μ
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact MemLp.zero
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (hmem2 n)
  have hinteg : ∀ n, Integrable (fun ω => (localizedSum α B w ↑k n ω) ^ 2) μ :=
    fun n => (memLp_two_iff_integrable_sq (hMmem n).aestronglyMeasurable).mp
      (hMmem n)
  have hmart := martingale_localizedSum hα_adapted hB_adapted hw_meas hw hα01 k
  have hprov := MeasureTheory.Martingale.ae_tendsto_of_tendsto_predictableQuadVar
    hmart hinteg
  filter_upwards [hprov, hquad] with ω h1 h2
  exact h1 h2

/-- **Tsitsiklis (1994), Lemma 1.** On a probability space with a filtration `ℱ` indexed by `ℕ`,
let `W (t + 1) = (1 - α t) * W t + α t * w t` almost surely, where the step sizes `α t` and the
envelopes `B t` are `ℱ t`-measurable and the noise `w t` is `ℱ (t + 1)`-measurable. Suppose that
(a), (b) for every `t` the noise `w t` is conditionally centered given `ℱ t`, with conditional
second moment at most `max (B t) 0` (`IsCenteredNoise`), and that almost surely (c) `α t ∈ [0, 1]`
for every `t`, (d) `∑ t, α t = ∞`, (e) every partial sum of `α t ^ 2` is at most the
deterministic constant `C`, and the sequence `B t` is bounded above. Then `W t → 0` almost
surely, for any initial value `W 0`. -/
theorem ae_tendsto_zero
    (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t)) -- (a), (b)
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) -- (c)
    (hα_div : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop) -- (d)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C) -- (e)
    (hB_bdd : ∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω))
    (hW : ∀ᵐ ω ∂μ, ∀ t, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => W t ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ l,
      Tendsto (fun n => localizedSum α B w ↑k n ω) atTop (𝓝 l) :=
    ae_all_iff.mpr
      (fun k => ae_exists_tendsto_localizedSum hα_adapted hB_adapted hw_meas hw hα01 hα_sq k)
  filter_upwards [hall, hα01, hα_div, hW, hB_bdd] with ω hallω hα01ω hαdivω hWω
    hBddω
  obtain ⟨K, hK⟩ := hBddω
  have hKt : ∀ t, B t ω ≤ K := fun t => hK (Set.mem_range_self t)
  have hkle : ∀ t, B t ω ≤ ((Nat.ceil (max K 0) : ℕ) : ℝ) := fun t =>
    le_trans (hKt t) (le_trans (le_max_left K 0) (Nat.le_ceil _))
  obtain ⟨l, hl⟩ := hallω (Nat.ceil (max K 0))
  have hMeq : ∀ n, localizedSum α B w ↑(Nat.ceil (max K 0)) n ω
      = ∑ t ∈ Finset.range n, α t ω * w t ω := fun n => by
    change (∑ t ∈ Finset.range n, (α t * localizedNoise B w ↑(Nat.ceil (max K 0)) t)) ω
      = _
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    show (α t * localizedNoise B w ↑(Nat.ceil (max K 0)) t) ω = α t ω * w t ω
    rw [Pi.mul_apply]
    congr 1
    show localizedNoise B w ↑(Nat.ceil (max K 0)) t ω = w t ω
    change ({ω | B t ω ≤ ↑(Nat.ceil (max K 0))}.indicator (w t)) ω = w t ω
    exact Set.indicator_of_mem (hkle t) _
  have hS : Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω * w t ω) atTop (𝓝 l) :=
    Tendsto.congr hMeq hl
  exact MetaMathlibExt.tendsto_zero_of_averaging_of_tendsto_sum hα01ω hαdivω hS hWω

private theorem restart_zero_add {Ω : Type*} (α w : ℕ → Ω → ℝ) (ω : Ω) (t₀ n : ℕ) :
    restart α w 0 (t₀ + n) ω
      = (∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω)) * restart α w 0 t₀ ω
        + restart α w t₀ n ω := by
  induction n with
  | zero =>
    have hzero : ∀ t₀' : ℕ, restart α w t₀' 0 ω = 0 := fun t₀' => rfl
    simp only [Finset.prod_range_zero, hzero, one_mul, add_zero]
  | succ n ih =>
    have hadd : t₀ + (n + 1) = (t₀ + n) + 1 := by omega
    have hsucc : ∀ t₀' n' : ℕ, restart α w t₀' (n' + 1) ω
        = (1 - α (t₀' + n') ω) * restart α w t₀' n' ω + α (t₀' + n') ω * w (t₀' + n') ω :=
      fun t₀' n' => rfl
    rw [hadd, hsucc, hsucc, Nat.zero_add, ih, Finset.prod_range_succ]
    ring

private theorem abs_restart_le {Ω : Type*} (α w : ℕ → Ω → ℝ) (ω : Ω) (t₀ n : ℕ)
    (h01 : ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1) :
    |restart α w t₀ n ω| ≤ |restart α w 0 (t₀ + n) ω| + |restart α w 0 t₀ ω| := by
  have hdecomp := restart_zero_add α w ω t₀ n
  have hfac : ∀ k ∈ Finset.range n, 0 ≤ 1 - α (t₀ + k) ω ∧ 1 - α (t₀ + k) ω ≤ 1 :=
    fun k _ => ⟨sub_nonneg.mpr (h01 (t₀ + k)).2, sub_le_self _ (h01 (t₀ + k)).1⟩
  have hP0 : 0 ≤ ∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω) :=
    Finset.prod_nonneg fun k hk => (hfac k hk).1
  have hP1 : ∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω) ≤ 1 :=
    Finset.prod_le_one₀ (fun k hk => (hfac k hk).1) fun k hk => (hfac k hk).2
  have heq : restart α w t₀ n ω = restart α w 0 (t₀ + n) ω
      - (∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω)) * restart α w 0 t₀ ω := by
    linarith
  rw [heq]
  have hPabs : |(∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω))| ≤ 1 := by
    rw [abs_of_nonneg hP0]
    exact hP1
  have hmul : |(∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω)) * restart α w 0 t₀ ω|
      ≤ |restart α w 0 t₀ ω| := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right hPabs (abs_nonneg (restart α w 0 t₀ ω))
    simpa using h
  calc |restart α w 0 (t₀ + n) ω
          - (∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω)) * restart α w 0 t₀ ω|
        ≤ |restart α w 0 (t₀ + n) ω|
          + |(∏ k ∈ Finset.range n, (1 - α (t₀ + k) ω)) * restart α w 0 t₀ ω| :=
          abs_sub _ _
      _ ≤ |restart α w 0 (t₀ + n) ω| + |restart α w 0 t₀ ω| :=
          add_le_add_right hmul _

/-- **Tsitsiklis (1994), Lemma 2.** The restarted recursion has a uniform tail: under the
hypotheses of `ae_tendsto_zero` on `α`, `w` and `B`, almost surely, for every `δ > 0` there is a
time `T` such that the recursion restarted from `0` at any time `t₀ ≥ T` stays in `[-δ, δ]`
forever, that is, `|W(t; t₀)| ≤ δ` whenever `T ≤ t₀ ≤ t`. One full-measure event serves every
`δ`. -/
theorem ae_uniform_tail_restart
    (hα_adapted : StronglyAdapted ℱ α) (hB_adapted : StronglyAdapted ℱ B)
    (hw_meas : ∀ t, StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw : ∀ t, IsCenteredNoise (ℱ t) μ (w t) (B t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_div : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, α t ω) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ n, ∑ t ∈ Finset.range n, α t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂μ, BddAbove (Set.range fun t => B t ω)) :
    ∀ᵐ ω ∂μ, ∀ δ > 0, ∃ T, ∀ t₀ ≥ T, ∀ n, |restart α w t₀ n ω| ≤ δ := by
  have hW : ∀ᵐ ω ∂μ, ∀ t, restart α w 0 (t + 1) ω
      = (1 - α t ω) * restart α w 0 t ω + α t ω * w t ω := by
    filter_upwards with ω t
    have hdef : restart α w 0 (t + 1) ω
        = (1 - α (0 + t) ω) * restart α w 0 t ω + α (0 + t) ω * w (0 + t) ω := rfl
    rw [hdef, Nat.zero_add]
  have hlim := ae_tendsto_zero (W := restart α w 0) hα_adapted hB_adapted hw_meas hw
    hα01 hα_div hα_sq hB_bdd hW
  filter_upwards [hlim, hα01] with ω hlimω h01ω
  intro δ hδ
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hlimω) (δ / 2) hδ2
  refine ⟨T, fun t₀ ht₀ n => ?_⟩
  have hle := abs_restart_le α w ω t₀ n h01ω
  have habs : ∀ t ≥ T, |restart α w 0 t ω| ≤ δ / 2 := by
    intro t ht
    have h := hT t ht
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  have h2 := habs (t₀ + n) (by omega)
  have h3 := habs t₀ ht₀
  linarith

/-- **Finitely many coordinates.** If each coordinate `i : ι` of a finite family satisfies the
hypotheses of `ae_tendsto_zero`, with one constant `C` for all coordinates, then on one
full-measure event every coordinate `W i t` tends to `0`, and for every `δ > 0` one restart
threshold `T` serves all coordinates. This is the form used in equation (15) of
Tsitsiklis (1994). -/
theorem ae_tendsto_zero_and_uniform_tail_fintype {ι : Type*} [Finite ι]
    {α w B W : ι → ℕ → Ω → ℝ} {C : ℝ}
    (hα_adapted : ∀ i, StronglyAdapted ℱ (α i)) (hB_adapted : ∀ i, StronglyAdapted ℱ (B i))
    (hw_meas : ∀ i t, StronglyMeasurable[ℱ (t + 1)] (w i t))
    (hw : ∀ i t, IsCenteredNoise (ℱ t) μ (w i t) (B i t))
    (hα01 : ∀ᵐ ω ∂μ, ∀ i t, α i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hα_div : ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => ∑ t ∈ Finset.range n, α i t ω) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂μ, ∀ i n, ∑ t ∈ Finset.range n, α i t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂μ, ∀ i, BddAbove (Set.range fun t => B i t ω))
    (hW : ∀ᵐ ω ∂μ, ∀ i t, W i (t + 1) ω = (1 - α i t ω) * W i t ω + α i t ω * w i t ω) :
    ∀ᵐ ω ∂μ, (∀ i, Tendsto (fun t => W i t ω) atTop (𝓝 0)) ∧
      ∀ δ > 0, ∃ T, ∀ i, ∀ t₀ ≥ T, ∀ n, |restart (α i) (w i) t₀ n ω| ≤ δ := by
  have htend : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun t => W i t ω) atTop (𝓝 0) := by
    intro i
    apply ae_tendsto_zero (α := α i) (w := w i) (B := B i) (W := W i) (C := C)
    · exact hα_adapted i
    · exact hB_adapted i
    · exact hw_meas i
    · exact hw i
    · filter_upwards [hα01] with ω h using fun t => h i t
    · filter_upwards [hα_div] with ω h using h i
    · filter_upwards [hα_sq] with ω h using fun n => h i n
    · filter_upwards [hB_bdd] with ω h using h i
    · filter_upwards [hW] with ω h using fun t => h i t
  have htail : ∀ i, ∀ᵐ ω ∂μ, ∀ δ > 0, ∃ T, ∀ t₀ ≥ T, ∀ n,
      |restart (α i) (w i) t₀ n ω| ≤ δ := by
    intro i
    apply ae_uniform_tail_restart (α := α i) (w := w i) (B := B i) (C := C)
    · exact hα_adapted i
    · exact hB_adapted i
    · exact hw_meas i
    · exact hw i
    · filter_upwards [hα01] with ω h using fun t => h i t
    · filter_upwards [hα_div] with ω h using h i
    · filter_upwards [hα_sq] with ω h using fun n => h i n
    · filter_upwards [hB_bdd] with ω h using h i
  have htend_all : ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun t => W i t ω) atTop (𝓝 0) :=
    ae_all_iff.mpr htend
  have htail_all : ∀ᵐ ω ∂μ, ∀ i, ∀ δ > 0, ∃ T, ∀ t₀ ≥ T, ∀ n,
      |restart (α i) (w i) t₀ n ω| ≤ δ :=
    ae_all_iff.mpr htail
  filter_upwards [htend_all, htail_all] with ω h1 h2
  refine ⟨h1, fun δ hδ => ?_⟩
  choose T hT using fun i => h2 i δ hδ
  refine ⟨(@Finset.univ ι (Fintype.ofFinite ι)).sup T, fun i t₀ ht₀ n => hT i t₀ ?_ n⟩
  exact le_trans (Finset.le_sup (@Finset.mem_univ ι (Fintype.ofFinite ι) i)) ht₀

end Cslib.MachineLearning.StochasticApproximation.NoiseAveraging
