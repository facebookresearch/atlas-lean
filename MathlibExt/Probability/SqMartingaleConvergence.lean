/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.BorelCantelli
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Square-integrable martingale convergence on `{A_∞ < ∞}`

For a square-integrable martingale `f`, let `A_n` be its predictable
quadratic variation, the predictable part of `f²` in Doob's decomposition:
`A_n = ∑_{k < n} E[(f_{k+1} - f_k)² | ℱ_k]`. Then `f_n` converges almost
surely on the event that `A_n` converges (in particular, on `{A_∞ < ∞}`):
the martingale cannot oscillate forever if its accumulated conditional
variance stays finite.

## Source

This formalizes the target "Theorem (Square integrable martingale
convergence)" (Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`:

* "Suppose `X_n` is a martingale with `EX_n² < ∞` for all `n`. Then
  `lim_{n → ∞} X_n` exists and is finite a.s. on `{A_∞ < ∞}`."

The v1 formalization is
`v1/Atlas/TheoryOfProbability/code/SqMartingaleConvergence.lean`. Its main
theorem there rests on the unproved helper
`stopped_martingale_L1_bound` (the stopped process is `L¹`-bounded). This
file proves that helper from scratch: stopping at the first time
`A_{n+1}` exceeds `M + 1` keeps the `L²` norm of the stopped process
bounded by `E[f_0²] + (M + 1)`, via the telescoping identity
`E[A_n] = E[f_n²] - E[f_0²]` applied to the stopped martingale, and the
`L¹` bound follows from the `L²` bound on a probability space.

## Notes on scope

This file is self-contained with respect to the batch base: it does not
import the Doob maximal-inequality file from an earlier batch, which is
not present in that base. Its `predictableQuadVar` is the same object as
that file's `predictableQuadraticVariation` (same formula, `μ ℱ f`
argument order) under the v1 name; the two should be unified when the
batches are rebased onto a common base.

## Main results

* `MeasureTheory.predictableQuadVar`: the predictable quadratic
  variation `A_n = ∑_{k < n} E[(f_{k+1} - f_k)² | ℱ_k]`.
* `MeasureTheory.Martingale.ae_tendsto_of_tendsto_predictableQuadVar`:
  if `A_n(ω)` converges, then `f_n(ω)` converges, almost surely.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

/-- The **predictable quadratic variation** of a process `f` with respect to
a filtration `ℱ` and a measure `μ`, defined pointwise by
`A_n(ω) = ∑_{k=0}^{n-1} E[(f_{k+1} - f_k)² | ℱ_k] (ω)`. For a
square-integrable martingale this is the predictable part of `f²` in
Doob's decomposition. -/
noncomputable def predictableQuadVar (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun k =>
    (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω)

/-- The predictable quadratic variation is integrable. -/
private theorem integrable_predictableQuadVar [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (predictableQuadVar μ ℱ f n) μ := by
  have h : Integrable (fun ω => ∑ k ∈ Finset.range n,
      (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω) μ :=
    integrable_finsetSum _ (fun k _ => integrable_condExp)
  have hEq : predictableQuadVar μ ℱ f n =
      fun ω => ∑ k ∈ Finset.range n,
        (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω := by
    funext ω
    simp [predictableQuadVar]
  rw [hEq]
  exact h

/-- Orthogonality of a martingale increment against the current value:
`∫ f_{k+1} * f_k = ∫ f_k²`, since `E[f_{k+1} | ℱ_k] = f_k` a.e. -/
private theorem Martingale.integral_mul_succ_eq [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (k : ℕ) :
    ∫ ω, f (k + 1) ω * f k ω ∂μ = ∫ ω, (f k ω) ^ 2 ∂μ := by
  have hprod_int : Integrable (f (k + 1) * f k) μ :=
    (hL2 (k + 1)).integrable_mul (hL2 k)
  have hcond : μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k] =ᵐ[μ] fun ω => (f k ω) ^ 2 := by
    calc μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k]
        =ᵐ[μ] μ[f (k + 1) | ℱ k] * f k :=
          condExp_mul_of_stronglyMeasurable_right (hmart.stronglyMeasurable k)
            hprod_int (hmart.integrable (k + 1))
      _ =ᵐ[μ] f k * f k :=
          (hmart.condExp_ae_eq (Nat.le_succ k)).mul (EventuallyEq.refl (ae μ) (f k))
      _ =ᵐ[μ] fun ω => (f k ω) ^ 2 := by
          filter_upwards with ω
          simp [Pi.mul_apply, pow_two]
  calc ∫ ω, f (k + 1) ω * f k ω ∂μ
      = ∫ ω, μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k] ω ∂μ :=
        (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, (f k ω) ^ 2 ∂μ := integral_congr_ae hcond

/-- The expectation of the predictable quadratic variation telescopes:
`E[A_n] = E[f_n²] - E[f_0²]`, by orthogonality of martingale increments. -/
private theorem Martingale.integral_predictableQuadVar [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) :
    ∫ ω, predictableQuadVar μ ℱ f n ω ∂μ =
      ∫ ω, (f n ω) ^ 2 ∂μ - ∫ ω, (f 0 ω) ^ 2 ∂μ := by
  have hsum : ∫ ω, predictableQuadVar μ ℱ f n ω ∂μ =
      ∑ k ∈ Finset.range n, ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ := by
    simp only [predictableQuadVar]
    rw [integral_finsetSum _ (fun k _ => integrable_condExp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_condExp (ℱ.le k)]
  have hdiff : ∀ k, ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ =
      ∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, (f k ω) ^ 2 ∂μ := by
    intro k
    have h1 : Integrable (fun ω => (f (k + 1) ω) ^ 2) μ := (hL2 _).integrable_sq
    have h2 : Integrable (fun ω => (f k ω) ^ 2) μ := (hL2 _).integrable_sq
    have hprod_int : Integrable (fun ω => f (k + 1) ω * f k ω) μ :=
      (hL2 (k + 1)).integrable_mul (hL2 k)
    have hprod2_int : Integrable (fun ω => 2 * (f (k + 1) ω * f k ω)) μ :=
      hprod_int.const_mul 2
    have hA : Integrable (fun ω =>
        (f (k + 1) ω) ^ 2 - 2 * (f (k + 1) ω * f k ω)) μ :=
      h1.sub hprod2_int
    calc ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ
        = ∫ ω, ((f (k + 1) ω) ^ 2 - 2 * (f (k + 1) ω * f k ω) + (f k ω) ^ 2) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
      _ = (∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, 2 * (f (k + 1) ω * f k ω) ∂μ) +
            ∫ ω, (f k ω) ^ 2 ∂μ := by
          rw [integral_add hA h2, integral_sub h1 hprod2_int]
      _ = ∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, (f k ω) ^ 2 ∂μ := by
          rw [integral_const_mul, hmart.integral_mul_succ_eq hL2 k]
          ring
  rw [hsum, Finset.sum_congr rfl (fun k _ => hdiff k)]
  exact Finset.sum_range_sub (fun k => ∫ ω, (f k ω) ^ 2 ∂μ) n

/-- The shifted predictable quadratic variation `n ↦ A_{n+1}` is adapted:
each summand `E[(f_{k+1} - f_k)² | ℱ_k]` is `ℱ_k`-measurable, hence
`ℱ_n`-measurable for `k ≤ n`. -/
private theorem stronglyAdapted_predictableQuadVar_succ :
    StronglyAdapted ℱ (fun n => predictableQuadVar μ ℱ f (n + 1)) := by
  intro n
  show StronglyMeasurable[ℱ n] (predictableQuadVar μ ℱ f (n + 1))
  have hEq : predictableQuadVar μ ℱ f (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) := by
    funext ω
    simp [predictableQuadVar]
  rw [hEq]
  apply Finset.stronglyMeasurable_sum
  intro k hk
  have hkn : k ≤ n := by
    have hmem := Finset.mem_range.mp hk
    omega
  exact stronglyMeasurable_condExp.mono (ℱ.mono hkn)

/-- The stopped process at the first time `A_{n+1}` reaches `M + 1` is
uniformly bounded in `L²`: `E[(f^τ_n)²] ≤ E[f_0²] + (M + 1)`. This is the
helper left unproved in v1 (`stopped_martingale_L1_bound`, `L¹` form).
The proof applies the telescoping identity to the stopped martingale,
whose predictable quadratic variation is the sum of the conditional
variances over the indices `k < τ`, and bounds that sum by `M + 1`
using that `τ` is the first hitting time of `M + 1`. -/
private theorem integral_sq_stoppedProcess_le [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (M : ℕ) (n : ℕ) :
    ∫ ω, (stoppedProcess f
      (leastGE (fun i => predictableQuadVar μ ℱ f (i + 1)) ((M : ℝ) + 1)) n ω) ^ 2 ∂μ ≤
      ∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1) := by
  classical
  set τ : Ω → WithTop ℕ :=
    leastGE (fun i => predictableQuadVar μ ℱ f (i + 1)) ((M : ℝ) + 1) with hτ_def
  set g : ℕ → Ω → ℝ := stoppedProcess f τ with hg_def
  have hτ : IsStoppingTime ℱ τ :=
    stronglyAdapted_predictableQuadVar_succ.isStoppingTime_leastGE _
  have hg_mart : Martingale g ℱ μ := by
    refine martingale_iff.mpr ⟨?_, ?_⟩
    · have h1 := hmart.neg.submartingale.stoppedProcess hτ
      have hEq : stoppedProcess (-f) τ = -g := by
        funext i ω
        simp [hg_def, stoppedProcess, Pi.neg_apply]
      rw [hEq] at h1
      simpa using h1.neg
    · exact hmart.submartingale.stoppedProcess hτ
  have hg_L2 : ∀ n, MemLp (g n) 2 μ := fun n => memLp_stoppedProcess hτ hL2 n
  have hg0 : g 0 = f 0 := by
    funext ω
    simp [hg_def, stoppedProcess]
  have htele := hg_mart.integral_predictableQuadVar hg_L2 n
  rw [hg0] at htele
  have hA_bound : ∫ ω, predictableQuadVar μ ℱ g n ω ∂μ ≤ (M : ℝ) + 1 := by
    -- Expand the expectation of the stopped quadratic variation as a sum of
    -- set integrals over `{k < τ}`.
    have hdiff_sq : ∀ k : ℕ, (fun ω => (g (k + 1) ω - g k ω) ^ 2) =
        Set.indicator {ω | (k : WithTop ℕ) < τ ω}
          (fun ω => (f (k + 1) ω - f k ω) ^ 2) := by
      intro k
      funext ω
      by_cases h : (k : WithTop ℕ) < τ ω
      · have hmem : ω ∈ {ω | (k : WithTop ℕ) < τ ω} := h
        have hk : (k : WithTop ℕ) ≤ τ ω := le_of_lt h
        have hk1 : ((k + 1 : ℕ) : WithTop ℕ) ≤ τ ω := by
          rcases eq_or_ne (τ ω) ⊤ with htop | hne
          · rw [htop]
            exact le_top
          · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
            rw [← ht]
            have hlt : k < t := WithTop.coe_lt_coe.mp (ht ▸ h)
            exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hlt)
        have e1 := stoppedProcess_eq_of_le (u := f) (τ := τ) (i := k) (ω := ω) hk
        have e2 := stoppedProcess_eq_of_le (u := f) (τ := τ) (i := k + 1) (ω := ω) hk1
        rw [hg_def]
        rw [Set.indicator_of_mem hmem, e1, e2]
      · have hnotmem : ω ∉ {ω | (k : WithTop ℕ) < τ ω} := h
        have hle : τ ω ≤ (k : WithTop ℕ) := not_lt.mp h
        have hle1 : τ ω ≤ ((k + 1 : ℕ) : WithTop ℕ) :=
          le_trans hle (WithTop.coe_le_coe.mpr (Nat.le_succ k))
        have e1 := stoppedProcess_eq_of_ge (u := f) (τ := τ) (i := k) (ω := ω) hle
        have e2 := stoppedProcess_eq_of_ge (u := f) (τ := τ) (i := k + 1) (ω := ω) hle1
        rw [hg_def]
        rw [Set.indicator_of_notMem hnotmem, e1, e2]
        simp
    have hset_meas : ∀ k : ℕ, MeasurableSet {ω | (k : WithTop ℕ) < τ ω} := by
      intro k
      have hle : MeasurableSet {ω | τ ω ≤ (k : WithTop ℕ)} :=
        (ℱ.le k) _ (hτ.measurableSet_le k)
      have hEq : {ω | (k : WithTop ℕ) < τ ω} = {ω | τ ω ≤ (k : WithTop ℕ)}ᶜ := by
        ext ω
        simp [not_le]
      rw [hEq]
      exact hle.compl
    have hset_meas_F : ∀ k : ℕ,
        MeasurableSet[ℱ k] {ω | (k : WithTop ℕ) < τ ω} := by
      intro k
      have hEq : {ω | (k : WithTop ℕ) < τ ω} = {ω | τ ω ≤ (k : WithTop ℕ)}ᶜ := by
        ext ω
        simp [not_le]
      rw [hEq]
      exact (hτ.measurableSet_le k).compl
    have hsum : ∫ ω, predictableQuadVar μ ℱ g n ω ∂μ =
        ∑ k ∈ Finset.range n,
          ∫ ω in {ω | (k : WithTop ℕ) < τ ω}, (f (k + 1) ω - f k ω) ^ 2 ∂μ := by
      have hstep : ∀ k : ℕ, ∫ ω, (μ[(fun ω' => (g (k + 1) ω' - g k ω') ^ 2) | ℱ k]) ω ∂μ =
          ∫ ω in {ω | (k : WithTop ℕ) < τ ω}, (f (k + 1) ω - f k ω) ^ 2 ∂μ := by
        intro k
        rw [hdiff_sq k]
        rw [integral_condExp (ℱ.le k)]
        rw [← integral_indicator (hset_meas k)]
      simp only [predictableQuadVar]
      rw [integral_finsetSum _ (fun k _ => integrable_condExp)]
      apply Finset.sum_congr rfl
      intro k _
      exact hstep k
    rw [hsum]
    -- Rewrite each set integral of a square as a set integral of the
    -- corresponding conditional expectation, then collect the sum into
    -- one integral of a truncated quadratic variation.
    have hset_int : ∀ k : ℕ,
        ∫ ω in {ω | (k : WithTop ℕ) < τ ω}, (f (k + 1) ω - f k ω) ^ 2 ∂μ =
        ∫ ω in {ω | (k : WithTop ℕ) < τ ω},
          (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω ∂μ := by
      intro k
      have hint : Integrable (fun ω => (f (k + 1) ω - f k ω) ^ 2) μ :=
        ((hL2 (k + 1)).sub (hL2 k)).integrable_sq
      rw [setIntegral_condExp (ℱ.le k) hint (hset_meas_F k)]
    rw [Finset.sum_congr rfl (fun k _ => hset_int k)]
    -- The truncated sum.
    set B : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n,
      Set.indicator {ω | (k : WithTop ℕ) < τ ω}
        (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω with hB_def
    have hB_eq : ∑ k ∈ Finset.range n,
        ∫ ω in {ω | (k : WithTop ℕ) < τ ω},
          (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω ∂μ =
        ∫ ω, B ω ∂μ := by
      rw [hB_def]
      rw [integral_finsetSum _ (fun k _ =>
        Integrable.indicator integrable_condExp (hset_meas k))]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_indicator (hset_meas k)]
    rw [hB_eq]
    have hB_int : Integrable B μ := by
      rw [hB_def]
      exact integrable_finsetSum _ (fun k _ =>
        Integrable.indicator integrable_condExp (hset_meas k))
    have hB_le : B ≤ᵐ[μ] fun _ => (M : ℝ) + 1 := by
      have hG : ∀ᵐ ω ∂μ, ∀ k : ℕ, 0 ≤
          (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω :=
        ae_all_iff.mpr fun k =>
          condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      filter_upwards [hG] with ω hω
      -- Write the truncated sum as a sum over the filtered index set.
      have hBsum : B ω = ∑ k ∈ (Finset.range n).filter
          (fun k : ℕ => ((k : WithTop ℕ) < τ ω)),
            (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω := by
        rw [hB_def]
        dsimp only
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [Finset.sum_filter]
      -- The truncated sum is bounded by the full sum up to `τ ω` (or up
      -- to `n` when `τ ω = ⊤`), and the first hitting time forces that
      -- full sum below `M + 1`.
      rcases eq_or_ne (τ ω) ⊤ with htop | hne
      · have hfilter : (Finset.range n).filter (fun k : ℕ => ((k : WithTop ℕ) < τ ω)) =
            Finset.range n := by
          apply Finset.filter_true_of_mem
          intro k _
          rw [htop]
          exact WithTop.coe_lt_top k
        rw [hBsum, hfilter]
        by_cases hn : n = 0
        · subst hn
          simp only [Finset.range_zero, Finset.sum_empty]
          positivity
        · have hlt : (↑(n - 1) : WithTop ℕ) < τ ω := by
            rw [htop]
            exact WithTop.coe_lt_top _
          have hlt' : (↑(n - 1) : WithTop ℕ) <
              hittingAfter (fun i => predictableQuadVar μ ℱ f (i + 1))
                (Set.Ici ((M : ℝ) + 1)) ⊥ ω := hlt
          have hnot : predictableQuadVar μ ℱ f ((n - 1) + 1) ω ∉
              Set.Ici ((M : ℝ) + 1) :=
            notMem_of_lt_hittingAfter (u := fun i => predictableQuadVar μ ℱ f (i + 1))
              (s := Set.Ici ((M : ℝ) + 1)) (n := ⊥) (k := n - 1) hlt' bot_le
          rw [Set.mem_Ici, not_le] at hnot
          have hn1 : (n - 1) + 1 = n := by omega
          rw [hn1] at hnot
          exact le_of_lt hnot
      · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [hBsum]
        by_cases ht0 : t = 0
        · subst ht0
          have hempty : (Finset.range n).filter
              (fun k : ℕ => ((k : WithTop ℕ) < τ ω)) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro k hk
            rw [Finset.mem_filter] at hk
            have hk2 : k < 0 := by
              have hmem := hk.2
              rw [← ht] at hmem
              exact WithTop.coe_lt_coe.mp hmem
            omega
          rw [hempty, Finset.sum_empty]
          positivity
        · have hfilter_le : (Finset.range n).filter
              (fun k : ℕ => ((k : WithTop ℕ) < τ ω)) ⊆ Finset.range t := by
            intro k hk
            rw [Finset.mem_filter] at hk
            rw [← ht] at hk
            rw [Finset.mem_range]
            exact WithTop.coe_lt_coe.mp hk.2
          have hle_sum : ∑ k ∈ (Finset.range n).filter
                (fun k : ℕ => ((k : WithTop ℕ) < τ ω)),
              (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω ≤
            ∑ k ∈ Finset.range t,
              (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hfilter_le
            intro k _ _
            exact hω k
          have htlt : t - 1 < t := by omega
          have hlt : (↑(t - 1) : WithTop ℕ) < τ ω := by
            rw [← ht]
            exact WithTop.coe_lt_coe.mpr htlt
          have hlt' : (↑(t - 1) : WithTop ℕ) <
              hittingAfter (fun i => predictableQuadVar μ ℱ f (i + 1))
                (Set.Ici ((M : ℝ) + 1)) ⊥ ω := hlt
          have hnot : predictableQuadVar μ ℱ f ((t - 1) + 1) ω ∉
              Set.Ici ((M : ℝ) + 1) :=
            notMem_of_lt_hittingAfter (u := fun i => predictableQuadVar μ ℱ f (i + 1))
              (s := Set.Ici ((M : ℝ) + 1)) (n := ⊥) (k := t - 1) hlt' bot_le
          rw [Set.mem_Ici, not_le] at hnot
          have ht1 : (t - 1) + 1 = t := by omega
          rw [ht1] at hnot
          have hAt : ∑ k ∈ Finset.range t,
              (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω =
            predictableQuadVar μ ℱ f t ω := by
            simp [predictableQuadVar]
          rw [hAt] at hle_sum
          exact le_trans hle_sum (le_of_lt hnot)
    have hconst : ∫ _ : Ω, ((M : ℝ) + 1) ∂μ = (M : ℝ) + 1 := by
      simp [integral_const]
    rw [← hconst]
    exact integral_mono_ae hB_int (integrable_const _) hB_le
  linarith [htele, hA_bound]

/-- If the predictable quadratic variation is bounded by `M` along the
trajectory of `ω`, then `f_n(ω)` converges. The stopping time above is
then identically `⊤` on that trajectory, so the stopped process agrees
with `f` there, and the stopped process converges a.e. by the
`L¹`-bounded submartingale convergence theorem. -/
private theorem exists_ae_tendsto_of_forall_quadVar_le [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (M : ℕ) :
    ∀ᵐ ω ∂μ, (∀ n, predictableQuadVar μ ℱ f n ω ≤ (M : ℝ)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by
  classical
  set τ : Ω → WithTop ℕ :=
    leastGE (fun i => predictableQuadVar μ ℱ f (i + 1)) ((M : ℝ) + 1) with hτ_def
  set g : ℕ → Ω → ℝ := stoppedProcess f τ with hg_def
  have hτ : IsStoppingTime ℱ τ :=
    stronglyAdapted_predictableQuadVar_succ.isStoppingTime_leastGE _
  have hg_mart : Martingale g ℱ μ := by
    refine martingale_iff.mpr ⟨?_, ?_⟩
    · have h1 := hmart.neg.submartingale.stoppedProcess hτ
      have hEq : stoppedProcess (-f) τ = -g := by
        funext i ω
        simp [hg_def, stoppedProcess, Pi.neg_apply]
      rw [hEq] at h1
      simpa using h1.neg
    · exact hmart.submartingale.stoppedProcess hτ
  have hg_L1 : ∃ R : NNReal, ∀ n, eLpNorm (g n) 1 μ ≤ (R : ENNReal) := by
    refine ⟨Real.toNNReal (Real.sqrt
      (∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1))), fun n => ?_⟩
    have hC_nonneg : 0 ≤ ∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1) := by
      have h1 : 0 ≤ ∫ ω, (f 0 ω) ^ 2 ∂μ :=
        integral_nonneg (fun ω => sq_nonneg _)
      positivity
    have hg_L2 : MemLp (g n) 2 μ := memLp_stoppedProcess hτ hL2 n
    have h1 : eLpNorm (g n) 1 μ ≤ eLpNorm (g n) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    have h2 : eLpNorm (g n) 2 μ ≤
        ENNReal.ofReal (Real.sqrt (∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1))) := by
      rw [hg_L2.eLpNorm_eq_integral_rpow_norm
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      apply ENNReal.ofReal_le_ofReal
      have h_int_eq : (∫ a, ‖g n a‖ ^ (2 : ℝ≥0∞).toReal ∂μ) =
          ∫ ω, (g n ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp [Real.norm_eq_abs, sq_abs]
      rw [h_int_eq]
      have h_le : ∫ ω, (g n ω) ^ 2 ∂μ ≤
          ∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1) :=
        integral_sq_stoppedProcess_le hmart hL2 M n
      have h_pow : (∫ ω, (g n ω) ^ 2 ∂μ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ ≤
          Real.sqrt (∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1)) := by
        have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        rw [h2r, show ((2 : ℝ))⁻¹ = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt h_le
      exact h_pow
    have hR_eq : ((Real.toNNReal (Real.sqrt
        (∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1)))) : ℝ≥0∞) =
        ENNReal.ofReal (Real.sqrt (∫ ω, (f 0 ω) ^ 2 ∂μ + ((M : ℝ) + 1))) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _),
        Real.toNNReal_of_nonneg (Real.sqrt_nonneg _)]
    rw [hR_eq]
    exact h1.trans h2
  obtain ⟨R, hR⟩ := hg_L1
  have hg_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => g n ω) atTop (𝓝 c) :=
    hg_mart.submartingale.exists_ae_tendsto_of_bdd hR
  filter_upwards [hg_conv] with ω hω hbnd
  have hτ_top : τ ω = ⊤ := by
    rw [hτ_def]
    simp only [leastGE, hittingAfter_eq_top_iff]
    intro j _
    simp only [Set.mem_Ici, not_le]
    have hle := hbnd (j + 1)
    linarith
  have hgf : ∀ n, g n ω = f n ω := by
    intro n
    have hle : ((n : ℕ) : WithTop ℕ) ≤ τ ω := by
      rw [hτ_top]
      exact le_top
    have hEq := stoppedProcess_eq_of_le (u := f) (τ := τ) (i := n) (ω := ω) hle
    rw [hg_def]
    exact hEq
  obtain ⟨c, hc⟩ := hω
  exact ⟨c, by rwa [show (fun n => f n ω) = (fun n => g n ω) from
    funext (fun n => (hgf n).symm)]⟩

/-- **Square-integrable martingale convergence.** Suppose `X_n` is a
martingale with `E[X_n²] < ∞` for all `n` and let `A_n` be its
predictable quadratic variation. Then `lim_{n → ∞} X_n` exists and is
finite almost surely on the event that `A_n` converges (in particular,
on `{A_∞ < ∞}`). -/
theorem Martingale.ae_tendsto_of_tendsto_predictableQuadVar [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ) :
    ∀ᵐ ω ∂μ, (∃ l, Tendsto (fun n => predictableQuadVar μ ℱ f n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by
  have hL2 : ∀ n, MemLp (f n) 2 μ := fun n =>
    (memLp_two_iff_integrable_sq
      ((hmart.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).mpr (hinteg n)
  have key : ∀ᵐ ω ∂μ, ∀ M : ℕ, (∀ n, predictableQuadVar μ ℱ f n ω ≤ (M : ℝ)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by
    rw [ae_all_iff]
    intro M
    exact exists_ae_tendsto_of_forall_quadVar_le hmart hL2 M
  filter_upwards [key] with ω hω hconv
  obtain ⟨l, hl⟩ := hconv
  have hbdd : ∃ M : ℕ, ∀ n, predictableQuadVar μ ℱ f n ω ≤ (M : ℝ) := by
    obtain ⟨B, hB⟩ := hl.isBoundedUnder_le.bddAbove_range
    obtain ⟨M, hM⟩ := exists_nat_gt B
    exact ⟨M, fun n =>
      le_trans (hB (Set.mem_range_self n)) (le_of_lt (by exact_mod_cast hM))⟩
  obtain ⟨M, hM⟩ := hbdd
  exact hω M hM

end MeasureTheory
