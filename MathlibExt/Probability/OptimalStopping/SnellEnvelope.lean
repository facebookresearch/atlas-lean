/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SupermartingaleOptionalStopping
public import MathlibExt.Probability.BoundedOptionalStopping
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.HittingTime

/-!
# The Snell envelope of a finite-horizon optimal stopping problem

Let `G = (G n)` be an integrable reward sequence adapted to a filtration `𝒢` on a finite measure
space, and fix a horizon `N`. The *Snell envelope* is built by backward induction,
`S N = G N` and `S n = max (G n) (E[S (n + 1) | 𝒢 n])` for `n < N` (Peskir and Shiryaev,
*Optimal Stopping and Free-Boundary Problems*, Birkhäuser 2006, Chapter I, equations
(1.1.6)–(1.1.7)). This file proves Peskir–Shiryaev Theorem 1.2 (finite horizon):
(1.1.9)–(1.1.10) at every time `n ≤ N`, and (1.1.11)–(1.1.14) at `n = 0`. In detail:

* the envelope is a supermartingale dominating the reward up to the horizon, and it is the
  smallest such sequence (statement (1.1.13));
* for every stopping time `τ ≤ N`, `E[G τ] ≤ E[S 0]` (the expectation of (1.1.9) at `n = 0`);
* the first time `τ*` at which `S = G` (equation (1.1.8) at `n = 0`) satisfies
  `E[G τ*] = E[S 0]`, so `τ*` is optimal and the value of the problem is `E[S 0]`
  (statements (1.1.10)–(1.1.11) in expectation form);
* `τ*` is the smallest optimal stopping time (statement (1.1.12)), and the envelope stopped at
  `τ*` is a martingale (statement (1.1.14)), both for `n = 0`;
* the conditional statements (1.1.9)–(1.1.10) at every time `n ≤ N`:
  `E[G τ | 𝒢 n] ≤ S n` for every stopping time `n ≤ τ ≤ N`, with equality almost everywhere for
  the first time `τₙ ≥ n` at which `S = G`.

The infinite-horizon theory (Theorems 1.4 and 1.6, essential suprema) is not formalised here.

The integrability condition (1.1.3) of the book, `E sup_{k ≤ N} |G k| < ∞`, is equivalent for a
finite horizon to the integrability of every `G k` with `k ≤ N`; it is assumed here for all `k`
for simplicity (the values after the horizon do not enter the envelope).

## Main definitions

* `MeasureTheory.snellEnvelope 𝒢 μ G N`: the Snell envelope, frozen at `G N` after the horizon.
* `MeasureTheory.snellStoppingTime 𝒢 μ G N`: the first time in `[0, N]` at which the envelope
  equals the reward.

## Main statements

* `MeasureTheory.supermartingale_snellEnvelope`
* `MeasureTheory.le_snellEnvelope`, `MeasureTheory.snellEnvelope_ae_le`
* `MeasureTheory.integral_stoppedValue_le_integral_snellEnvelope_zero`
* `MeasureTheory.integral_stoppedValue_snellStoppingTime`
* `MeasureTheory.snellStoppingTime_optimal`
* `MeasureTheory.snellStoppingTime_le_of_optimal`
* `MeasureTheory.martingale_stoppedProcess_snellEnvelope`
* `MeasureTheory.condExp_stoppedValue_le_snellEnvelope`
* `MeasureTheory.snellEnvelope_ae_eq_condExp_stoppedValue`
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {G : ℕ → Ω → ℝ} {N n : ℕ}

/-- **Snell envelope by backward induction.** For a reward sequence `G`, a filtration `𝒢`, a
measure `μ` and a horizon `N`, the Snell envelope is `S N = G N` and, for `n < N`,
`S n = max (G n) (E[S (n + 1) | 𝒢 n])` (Peskir and Shiryaev, *Optimal Stopping and
Free-Boundary Problems*, Birkhäuser 2006, Chapter I, equations (1.1.6)–(1.1.7)). After the
horizon the sequence is frozen at `G N`, which keeps it a supermartingale on all of `ℕ`; the book
only defines it for `0 ≤ n ≤ N`. -/
noncomputable def snellEnvelope (𝒢 : Filtration ℕ m0) (μ : Measure Ω) (G : ℕ → Ω → ℝ)
    (N : ℕ) : ℕ → Ω → ℝ
  | n => if h : N ≤ n then G N
      else fun ω => max (G n ω) (μ[snellEnvelope 𝒢 μ G N (n + 1) | 𝒢 n] ω)
termination_by n => N - n
decreasing_by omega

/-- **The Snell envelope equals the final reward from the horizon on.** If `N ≤ n` then
`S n = G N` (Peskir–Shiryaev, equation (1.1.6)). -/
theorem snellEnvelope_of_le (h : N ≤ n) : snellEnvelope 𝒢 μ G N n = G N := by
  rw [snellEnvelope]
  simp [h]

/-- **Wald–Bellman recursion for the Snell envelope.** Before the horizon,
`S n = max (G n) (E[S (n + 1) | 𝒢 n])` (Peskir–Shiryaev, equation (1.1.7)). -/
theorem snellEnvelope_of_lt (h : n < N) :
    snellEnvelope 𝒢 μ G N n =
      fun ω => max (G n ω) (μ[snellEnvelope 𝒢 μ G N (n + 1) | 𝒢 n] ω) := by
  rw [snellEnvelope]
  simp [Nat.not_le.mpr h]

/-- **The Snell envelope is adapted.** If the reward is strongly adapted, each `S n` is strongly
measurable with respect to `𝒢 n`. -/
theorem stronglyMeasurable_snellEnvelope (hG : StronglyAdapted 𝒢 G) (n : ℕ) :
    StronglyMeasurable[𝒢 n] (snellEnvelope 𝒢 μ G N n) := by
  rcases le_or_gt N n with h | h
  · rw [snellEnvelope_of_le h]
    exact (hG N).mono (𝒢.mono h)
  · rw [snellEnvelope_of_lt h]
    exact ((hG n).measurable.max stronglyMeasurable_condExp.measurable).stronglyMeasurable

/-- **The Snell envelope is integrable.** If every reward `G k` is integrable, so is every
`S n`. -/
theorem integrable_snellEnvelope (hint : ∀ k, Integrable (G k) μ) (n : ℕ) :
    Integrable (snellEnvelope 𝒢 μ G N n) μ := by
  induction h : N - n generalizing n with
  | zero =>
    rw [snellEnvelope_of_le (by omega)]
    exact hint N
  | succ k ih =>
    have hn : n < N := by omega
    rw [snellEnvelope_of_lt hn]
    exact (hint n).sup integrable_condExp

/-- **The Snell envelope is a supermartingale** (Peskir–Shiryaev, Theorem 1.2, part (1.1.13)):
for a strongly adapted reward with integrable values on a finite measure space, the Snell
envelope is a supermartingale with respect to `𝒢`. -/
theorem supermartingale_snellEnvelope [IsFiniteMeasure μ] (hG : StronglyAdapted 𝒢 G)
    (hint : ∀ k, Integrable (G k) μ) :
    Supermartingale (snellEnvelope 𝒢 μ G N) 𝒢 μ := by
  refine supermartingale_nat (fun n => stronglyMeasurable_snellEnvelope hG n)
    (integrable_snellEnvelope hint) fun i => ?_
  rcases lt_or_ge i N with h | h
  · refine Eventually.of_forall fun ω => ?_
    rw [snellEnvelope_of_lt (G := G) (μ := μ) (𝒢 := 𝒢) h]
    exact le_max_right _ _
  · rw [snellEnvelope_of_le (Nat.le_succ_of_le h), snellEnvelope_of_le h,
      condExp_of_stronglyMeasurable (𝒢.le i) ((hG N).mono (𝒢.mono h)) (hint N)]

/-- **The Snell envelope dominates the reward up to the horizon** (Peskir–Shiryaev,
Theorem 1.2, part (1.1.13)): `G n ≤ S n` everywhere for `n ≤ N`. -/
theorem le_snellEnvelope (hn : n ≤ N) (ω : Ω) : G n ω ≤ snellEnvelope 𝒢 μ G N n ω := by
  rcases lt_or_eq_of_le hn with h | rfl
  · rw [snellEnvelope_of_lt h]
    exact le_max_left _ _
  · rw [snellEnvelope_of_le le_rfl]

/-- **The Snell envelope is the smallest supermartingale dominating the reward**
(Peskir–Shiryaev, Theorem 1.2, part (1.1.13)). Let `Y` be integrable with
`E[Y (n + 1) | 𝒢 n] ≤ Y n` almost everywhere for `n < N` and `G n ≤ Y n` almost everywhere for
`n ≤ N`. Then `S n ≤ Y n` almost everywhere for every `n ≤ N`. Adaptedness of `Y` is not
needed. -/
theorem snellEnvelope_ae_le [IsFiniteMeasure μ] (hint : ∀ k, Integrable (G k) μ)
    {Y : ℕ → Ω → ℝ} (hYint : ∀ k, Integrable (Y k) μ)
    (hY : ∀ k < N, μ[Y (k + 1) | 𝒢 k] ≤ᵐ[μ] Y k) (hGY : ∀ k ≤ N, G k ≤ᵐ[μ] Y k)
    (hn : n ≤ N) : snellEnvelope 𝒢 μ G N n ≤ᵐ[μ] Y n := by
  induction h : N - n generalizing n with
  | zero =>
    have : n = N := by omega
    subst this
    rw [snellEnvelope_of_le le_rfl]
    exact hGY n le_rfl
  | succ k ih =>
    have hlt : n < N := by omega
    have hrec := ih (n := n + 1) (by omega) (by omega)
    have hce : μ[snellEnvelope 𝒢 μ G N (n + 1) | 𝒢 n] ≤ᵐ[μ] μ[Y (n + 1) | 𝒢 n] :=
      condExp_mono (integrable_snellEnvelope hint _) (hYint _) hrec
    filter_upwards [hce, hY n hlt, hGY n hn] with ω h1 h2 h3
    rw [snellEnvelope_of_lt hlt]
    exact max_le h3 (h1.trans h2)

/-- **First time the Snell envelope meets the reward.** The stopping time
`τ* = min {k ∈ [0, N] : S k = G k}` (Peskir–Shiryaev, equation (1.1.8) with `n = 0`); the set is
nonempty because `S N = G N`. -/
noncomputable def snellStoppingTime (𝒢 : Filtration ℕ m0) (μ : Measure Ω) (G : ℕ → Ω → ℝ)
    (N : ℕ) : Ω → ℕ :=
  hittingBtwn (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) {0} 0 N

/-- **The first meeting time is at most the horizon.** -/
theorem snellStoppingTime_le (ω : Ω) : snellStoppingTime 𝒢 μ G N ω ≤ N :=
  hittingBtwn_le ω

/-- **At the first meeting time the envelope equals the reward.** `S τ* = G τ*` pointwise
(Peskir–Shiryaev, equation (1.1.8)). -/
theorem snellEnvelope_snellStoppingTime (ω : Ω) :
    snellEnvelope 𝒢 μ G N (snellStoppingTime 𝒢 μ G N ω) ω =
      G (snellStoppingTime 𝒢 μ G N ω) ω := by
  have hex : ∃ j ∈ Set.Icc 0 N, (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) j ω ∈
      ({0} : Set ℝ) :=
    ⟨N, ⟨Nat.zero_le _, le_rfl⟩, by simp [snellEnvelope_of_le le_rfl]⟩
  have := hittingBtwn_mem_set (u := fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω)
    (s := {0}) (n := 0) (m := N) (ω := ω) hex
  simpa [sub_eq_zero, snellStoppingTime] using this

/-- **Before the first meeting time the envelope exceeds the reward.** If `k < τ* ω` then
`S k ω ≠ G k ω`. -/
theorem snellEnvelope_ne_of_lt_snellStoppingTime {k : ℕ} {ω : Ω}
    (hk : k < snellStoppingTime 𝒢 μ G N ω) : snellEnvelope 𝒢 μ G N k ω ≠ G k ω := by
  intro heq
  have hkN : k ≤ N := (hk.trans_le (snellStoppingTime_le ω)).le
  have : snellStoppingTime 𝒢 μ G N ω ≤ k :=
    hittingBtwn_le_of_mem (Nat.zero_le _) hkN (by simp [heq])
  omega

/-- **Before the first meeting time the envelope is the continuation value.** If `k < τ* ω` then
`S k ω = E[S (k + 1) | 𝒢 k] ω`. -/
theorem snellEnvelope_eq_condExp_of_lt_snellStoppingTime {k : ℕ} {ω : Ω}
    (hk : k < snellStoppingTime 𝒢 μ G N ω) :
    snellEnvelope 𝒢 μ G N k ω = μ[snellEnvelope 𝒢 μ G N (k + 1) | 𝒢 k] ω := by
  have hkN : k < N := hk.trans_le (snellStoppingTime_le ω)
  have hne := snellEnvelope_ne_of_lt_snellStoppingTime hk
  rw [snellEnvelope_of_lt hkN] at hne ⊢
  rcases max_choice (G k ω) (μ[snellEnvelope 𝒢 μ G N (k + 1) | 𝒢 k] ω) with hm | hm
  · exact absurd hm hne
  · exact hm

/-- **The first meeting time is a stopping time.** For a strongly adapted reward, `τ*` is a
stopping time with respect to `𝒢`. -/
theorem isStoppingTime_snellStoppingTime (hG : StronglyAdapted 𝒢 G) :
    IsStoppingTime 𝒢 (fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ)) := by
  have hadp : Adapted 𝒢 (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) := fun k =>
    ((stronglyMeasurable_snellEnvelope hG k).sub (hG k)).measurable
  exact hadp.isStoppingTime_hittingBtwn (measurableSet_singleton 0)

private theorem untopA_le_of_le {x : WithTop ℕ} (h : x ≤ N) : x.untopA ≤ N := by
  induction x using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    have : a ≤ N := WithTop.coe_le_coe.mp h
    exact this

/-- **Every bounded stopping time earns at most the expected envelope at time zero**
(Peskir–Shiryaev, Theorem 1.2: the expectation of (1.1.9) at `n = 0`). For a strongly adapted,
integrable reward on a finite measure space and any stopping time `τ ≤ N`,
`E[G τ] ≤ E[S 0]`. -/
theorem integral_stoppedValue_le_integral_snellEnvelope_zero [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue G τ] ≤ μ[snellEnvelope 𝒢 μ G N 0] := by
  have hS := supermartingale_snellEnvelope (N := N) hG hint
  refine le_trans (integral_mono (integrable_stoppedValue ℕ hτ hint hbdd)
    (integrable_stoppedValue ℕ hτ (integrable_snellEnvelope hint) hbdd) fun ω => ?_)
    (hS.expected_stoppedValue_le hτ hbdd)
  exact le_snellEnvelope (untopA_le_of_le (hbdd ω)) ω

/-- **The first meeting time attains the expected envelope at time zero** (Peskir–Shiryaev,
Theorem 1.2: the expectation of (1.1.10) at `n = 0`). For a strongly adapted, integrable reward
on a finite measure space, `E[G τ*] = E[S 0]`. -/
theorem integral_stoppedValue_snellStoppingTime [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) :
    μ[stoppedValue G (fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ))] =
      μ[snellEnvelope 𝒢 μ G N 0] := by
  set S := snellEnvelope 𝒢 μ G N with hSdef
  set π : Ω → WithTop ℕ := fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ) with hπdef
  set τ : Ω → WithTop ℕ := fun _ => ((0 : ℕ) : WithTop ℕ) with hτdef
  have hπ : IsStoppingTime 𝒢 π := isStoppingTime_snellStoppingTime hG
  have hτ : IsStoppingTime 𝒢 τ := isStoppingTime_const 𝒢 0
  have hle : τ ≤ π := fun ω => by simp [hτdef, hπdef]
  have hbdd : ∀ ω, π ω ≤ N := fun ω => by simpa [hπdef] using snellStoppingTime_le ω
  have hSint : ∀ k, Integrable (S k) μ := integrable_snellEnvelope hint
  have hGS : stoppedValue G π = stoppedValue S π := by
    funext ω
    simp only [stoppedValue, hπdef]
    exact (snellEnvelope_snellStoppingTime ω).symm
  have hS0 : stoppedValue S τ = S 0 := by
    funext ω
    simp [stoppedValue, hτdef]
  rw [hGS, ← hS0, ← sub_eq_zero, ← integral_sub' (integrable_stoppedValue ℕ hπ hSint hbdd)
    (integrable_stoppedValue ℕ hτ hSint fun ω => (hle ω).trans (hbdd ω)),
    stoppedValue_sub_eq_sum' hle hbdd]
  simp only [Finset.sum_apply]
  have hmeas : ∀ i, MeasurableSet[𝒢 i] {ω | τ ω ≤ i ∧ i < π ω} := by
    intro i
    simp_rw [Set.ofPred_and, ← not_le, ← Set.compl_ofPred]
    exact (hτ i).inter (hπ i).compl
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_indicator (𝒢.le _ _ (hmeas i)),
      integral_sub' (hSint _).integrableOn (hSint _).integrableOn, sub_eq_zero,
      ← setIntegral_condExp (𝒢.le i) (hSint (i + 1)) (hmeas i)]
    refine setIntegral_congr_fun (𝒢.le _ _ (hmeas i)) fun ω hω => ?_
    have hiπ : i < snellStoppingTime 𝒢 μ G N ω := by
      have := hω.2
      simpa [hπdef] using this
    exact (snellEnvelope_eq_condExp_of_lt_snellStoppingTime hiπ).symm
  · intro i _
    exact ((hSint _).sub (hSint _)).indicator (𝒢.le _ _ (hmeas i))

/-- **Optimality of the first meeting time** (Peskir–Shiryaev, Theorem 1.2, part (1.1.11) with
`n = 0`). For a strongly adapted, integrable reward on a finite measure space and every
stopping time `τ ≤ N`, `E[G τ] ≤ E[G τ*]`; hence `τ*` is optimal and the value
`sup_{τ ≤ N} E[G τ]` equals `E[S 0]`. -/
theorem snellStoppingTime_optimal [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue G τ] ≤
      μ[stoppedValue G (fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ))] := by
  rw [integral_stoppedValue_snellStoppingTime hG hint]
  exact integral_stoppedValue_le_integral_snellEnvelope_zero hG hint hτ hbdd

/-- **The Snell envelope stopped at the first meeting time is a martingale** (Peskir–Shiryaev,
Theorem 1.2, part (1.1.14) with `n = 0`). For a strongly adapted, integrable reward on a finite
measure space, `(S (k ∧ τ*))_k` is a martingale with respect to `𝒢`. -/
theorem martingale_stoppedProcess_snellEnvelope [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) :
    Martingale (stoppedProcess (snellEnvelope 𝒢 μ G N)
      (fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ))) 𝒢 μ := by
  set S := snellEnvelope 𝒢 μ G N with hSdef
  set π : Ω → WithTop ℕ := fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ) with hπdef
  have hπ : IsStoppingTime 𝒢 π := isStoppingTime_snellStoppingTime hG
  have hSint : ∀ k, Integrable (S k) μ := integrable_snellEnvelope hint
  have hSadp : StronglyAdapted 𝒢 S := fun k => stronglyMeasurable_snellEnvelope hG k
  have hMint : ∀ i, Integrable (stoppedProcess S π i) μ := integrable_stoppedProcess hπ hSint
  refine martingale_of_setIntegral_eq_succ (hSadp.stoppedProcess_of_discrete hπ) hMint
    fun i s hs => ?_
  set A : Set Ω := {ω | (i : WithTop ℕ) < π ω} with hAdef
  have hA : MeasurableSet[𝒢 i] A := by
    have := (hπ i).compl
    simpa [hAdef, Set.compl_ofPred, not_le] using this
  have hdiff : stoppedProcess S π (i + 1) =
      stoppedProcess S π i + A.indicator (S (i + 1) - S i) := by
    funext ω
    by_cases h : (i : WithTop ℕ) < π ω
    · have hiτ : i < snellStoppingTime 𝒢 μ G N ω := WithTop.coe_lt_coe.mp h
      rw [stoppedProcess_eq_of_le (u := S) (τ := π) (i := i + 1)
          (WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hiτ)),
        Pi.add_apply, stoppedProcess_eq_of_le (u := S) (τ := π) (i := i) h.le,
        Set.indicator_of_mem (show ω ∈ A from h)]
      simp
    · have hτi : snellStoppingTime 𝒢 μ G N ω ≤ i :=
        WithTop.coe_le_coe.mp (le_of_not_gt h)
      rw [stoppedProcess_eq_of_ge (u := S) (τ := π) (i := i + 1)
          (WithTop.coe_le_coe.mpr (hτi.trans (Nat.le_succ i))),
        Pi.add_apply, stoppedProcess_eq_of_ge (u := S) (τ := π) (i := i)
          (WithTop.coe_le_coe.mpr hτi),
        Set.indicator_of_notMem (show ω ∉ A from h)]
      simp
  have hsA : MeasurableSet[𝒢 i] (s ∩ A) := hs.inter hA
  rw [hdiff, integral_add' (hMint i).integrableOn
    (((hSint _).sub (hSint _)).indicator (𝒢.le _ _ hA)).integrableOn,
    setIntegral_indicator (𝒢.le _ _ hA), left_eq_add,
    integral_sub' (hSint _).integrableOn (hSint _).integrableOn, sub_eq_zero,
    ← setIntegral_condExp (𝒢.le i) (hSint (i + 1)) hsA]
  refine setIntegral_congr_fun (𝒢.le _ _ hsA) fun ω hω => ?_
  have hiπ : i < snellStoppingTime 𝒢 μ G N ω := by
    have := hω.2
    simpa [hAdef, hπdef] using this
  exact (snellEnvelope_eq_condExp_of_lt_snellStoppingTime hiπ).symm

/-- **The first meeting time is the smallest optimal stopping time** (Peskir–Shiryaev,
Theorem 1.2, part (1.1.12) with `n = 0`). For a strongly adapted, integrable reward on a finite
measure space, if a stopping time `τ ≤ N` is optimal, `E[G τ*] ≤ E[G τ]`, then `τ* ≤ τ` almost
everywhere. -/
theorem snellStoppingTime_le_of_optimal [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) (hbdd : ∀ ω, τ ω ≤ N)
    (hopt : μ[stoppedValue G (fun ω => (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ))] ≤
      μ[stoppedValue G τ]) :
    ∀ᵐ ω ∂μ, (snellStoppingTime 𝒢 μ G N ω : WithTop ℕ) ≤ τ ω := by
  set S := snellEnvelope 𝒢 μ G N with hSdef
  have hS := supermartingale_snellEnvelope (N := N) hG hint
  have hSint : ∀ k, Integrable (S k) μ := integrable_snellEnvelope hint
  have hiS := integrable_stoppedValue ℕ hτ hSint hbdd
  have hiG := integrable_stoppedValue ℕ hτ hint hbdd
  have hnonneg : 0 ≤ stoppedValue S τ - stoppedValue G τ := fun ω => by
    simp only [Pi.sub_apply, Pi.zero_apply, sub_nonneg]
    exact le_snellEnvelope (untopA_le_of_le (hbdd ω)) ω
  have hzero : ∫ ω, (stoppedValue S τ - stoppedValue G τ) ω ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg hnonneg)
    rw [integral_sub' hiS hiG]
    have h1 := hS.expected_stoppedValue_le hτ hbdd
    have h2 := integral_stoppedValue_snellStoppingTime (N := N) hG hint
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg (hiS.sub hiG)).mp hzero
  filter_upwards [hae] with ω hω
  have hkN := untopA_le_of_le (hbdd ω)
  have hτω : τ ω = ((τ ω).untopA : WithTop ℕ) := by
    have : τ ω ≠ ⊤ := fun h => by simpa [h] using hbdd ω
    lift τ ω to ℕ using this with k
    rfl
  have heq : S (τ ω).untopA ω = G (τ ω).untopA ω := by
    simpa [stoppedValue, sub_eq_zero] using hω
  have hle : snellStoppingTime 𝒢 μ G N ω ≤ (τ ω).untopA :=
    hittingBtwn_le_of_mem (u := fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) (s := {0})
      (Nat.zero_le _) hkN (Set.mem_singleton_iff.mpr (sub_eq_zero.mpr heq))
  rw [hτω]
  exact_mod_cast hle

/-- **First time from `n` on that the Snell envelope meets the reward.** For `n ≤ N`,
`τₙ = min {k ∈ [n, N] : S k = G k}` (Peskir–Shiryaev, equation (1.1.8)); for `n = 0` it is
`snellStoppingTime`. -/
noncomputable def snellStoppingTimeFrom (𝒢 : Filtration ℕ m0) (μ : Measure Ω) (G : ℕ → Ω → ℝ)
    (N n : ℕ) : Ω → ℕ :=
  hittingBtwn (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) {0} n N

theorem snellStoppingTimeFrom_zero :
    snellStoppingTimeFrom 𝒢 μ G N 0 = snellStoppingTime 𝒢 μ G N := rfl

private theorem snellStoppingTimeFrom_mem (hn : n ≤ N) (ω : Ω) :
    snellStoppingTimeFrom 𝒢 μ G N n ω ∈ Set.Icc n N :=
  hittingBtwn_mem_Icc hn ω

private theorem snellEnvelope_snellStoppingTimeFrom (hn : n ≤ N) (ω : Ω) :
    snellEnvelope 𝒢 μ G N (snellStoppingTimeFrom 𝒢 μ G N n ω) ω =
      G (snellStoppingTimeFrom 𝒢 μ G N n ω) ω := by
  have hex : ∃ j ∈ Set.Icc n N, (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) j ω ∈
      ({0} : Set ℝ) :=
    ⟨N, ⟨hn, le_rfl⟩, by simp [snellEnvelope_of_le le_rfl]⟩
  have := hittingBtwn_mem_set (u := fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω)
    (s := {0}) (n := n) (m := N) (ω := ω) hex
  simpa [sub_eq_zero, snellStoppingTimeFrom] using this

private theorem snellEnvelope_eq_condExp_of_lt_snellStoppingTimeFrom {k : ℕ} {ω : Ω}
    (hnk : n ≤ k) (hk : k < snellStoppingTimeFrom 𝒢 μ G N n ω) :
    snellEnvelope 𝒢 μ G N k ω = μ[snellEnvelope 𝒢 μ G N (k + 1) | 𝒢 k] ω := by
  have hkN : k < N := hk.trans_le (hittingBtwn_le ω)
  have hne : snellEnvelope 𝒢 μ G N k ω ≠ G k ω := by
    intro heq
    have : snellStoppingTimeFrom 𝒢 μ G N n ω ≤ k :=
      hittingBtwn_le_of_mem hnk hkN.le (by simp [heq])
    omega
  rw [snellEnvelope_of_lt hkN] at hne ⊢
  rcases max_choice (G k ω) (μ[snellEnvelope 𝒢 μ G N (k + 1) | 𝒢 k] ω) with hm | hm
  · exact absurd hm hne
  · exact hm

/-- **The first meeting time from `n` on is a stopping time.** -/
theorem isStoppingTime_snellStoppingTimeFrom (hG : StronglyAdapted 𝒢 G) (n : ℕ) :
    IsStoppingTime 𝒢 (fun ω => (snellStoppingTimeFrom 𝒢 μ G N n ω : WithTop ℕ)) := by
  have hadp : Adapted 𝒢 (fun k ω => snellEnvelope 𝒢 μ G N k ω - G k ω) := fun k =>
    ((stronglyMeasurable_snellEnvelope hG k).sub (hG k)).measurable
  exact hadp.isStoppingTime_hittingBtwn (measurableSet_singleton 0)

/-- **The Snell envelope dominates every conditional stopped reward** (Peskir–Shiryaev,
Theorem 1.2, (1.1.9)). For a strongly adapted, integrable reward on a finite measure space,
`n ≤ N` and every stopping time `τ` with `n ≤ τ ≤ N`, `E[G τ | 𝒢 n] ≤ S n` almost everywhere. -/
theorem condExp_stoppedValue_le_snellEnvelope [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) (hnτ : ∀ ω, (n : WithTop ℕ) ≤ τ ω) (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue G τ | 𝒢 n] ≤ᵐ[μ] snellEnvelope 𝒢 μ G N n := by
  have hS := supermartingale_snellEnvelope (N := N) hG hint
  have hc : IsStoppingTime 𝒢 (fun _ : Ω => ((n : ℕ) : ℕ∞)) := isStoppingTime_const 𝒢 n
  have h := hS.condExp_stoppedValue_le_stoppedValue hc hτ hnτ hbdd
  rw [IsStoppingTime.measurableSpace_const] at h
  have hmono : μ[stoppedValue G τ | 𝒢 n] ≤ᵐ[μ]
      μ[stoppedValue (snellEnvelope 𝒢 μ G N) τ | 𝒢 n] :=
    condExp_mono (integrable_stoppedValue ℕ hτ hint hbdd)
      (integrable_stoppedValue ℕ hτ (integrable_snellEnvelope hint) hbdd)
      (Eventually.of_forall fun ω => le_snellEnvelope (untopA_le_of_le (hbdd ω)) ω)
  filter_upwards [hmono, h] with ω h1 h2
  exact h1.trans (by simpa [stoppedValue] using h2)

/-- **The first meeting time from `n` on attains the envelope conditionally** (Peskir–Shiryaev,
Theorem 1.2, (1.1.10)). For a strongly adapted, integrable reward on a finite measure space and
`n ≤ N`, `S n = E[G τₙ | 𝒢 n]` almost everywhere, where `τₙ` is the first time in `[n, N]` at
which `S = G`. -/
theorem snellEnvelope_ae_eq_condExp_stoppedValue [IsFiniteMeasure μ]
    (hG : StronglyAdapted 𝒢 G) (hint : ∀ k, Integrable (G k) μ) (hn : n ≤ N) :
    snellEnvelope 𝒢 μ G N n =ᵐ[μ]
      μ[stoppedValue G (fun ω => (snellStoppingTimeFrom 𝒢 μ G N n ω : WithTop ℕ)) | 𝒢 n] := by
  set S := snellEnvelope 𝒢 μ G N with hSdef
  set π : Ω → WithTop ℕ := fun ω => (snellStoppingTimeFrom 𝒢 μ G N n ω : WithTop ℕ) with hπdef
  set τ : Ω → WithTop ℕ := fun _ => ((n : ℕ) : WithTop ℕ) with hτdef
  have hπ : IsStoppingTime 𝒢 π := isStoppingTime_snellStoppingTimeFrom hG n
  have hτ : IsStoppingTime 𝒢 τ := isStoppingTime_const 𝒢 n
  have hle : τ ≤ π := fun ω => by
    simpa [hτdef, hπdef] using (snellStoppingTimeFrom_mem (𝒢 := 𝒢) (μ := μ) (G := G) hn ω).1
  have hbdd : ∀ ω, π ω ≤ N := fun ω => by
    simpa [hπdef] using (snellStoppingTimeFrom_mem (𝒢 := 𝒢) (μ := μ) (G := G) hn ω).2
  have hSint : ∀ k, Integrable (S k) μ := integrable_snellEnvelope hint
  have hGS : stoppedValue G π = stoppedValue S π := by
    funext ω
    simp only [stoppedValue, hπdef]
    exact (snellEnvelope_snellStoppingTimeFrom hn ω).symm
  have hSn : stoppedValue S τ = S n := by
    funext ω
    rfl
  have hiπ := integrable_stoppedValue ℕ hπ hSint hbdd
  rw [hGS]
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le n) hiπ
    (fun s _ _ => (hSint n).integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_snellEnvelope hG n).aestronglyMeasurable
  have hA : ∀ i, MeasurableSet[𝒢 i] {ω | τ ω ≤ i ∧ i < π ω} := by
    intro i
    simp_rw [Set.ofPred_and, ← not_le, ← Set.compl_ofPred]
    exact (hτ i).inter (hπ i).compl
  have hmeas : ∀ i, MeasurableSet[𝒢 i] (s ∩ {ω | τ ω ≤ i ∧ i < π ω}) := by
    intro i
    rcases le_or_gt n i with hni | hin
    · exact (𝒢.mono hni _ hs).inter (hA i)
    · have hempty : s ∩ {ω | τ ω ≤ i ∧ i < π ω} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and, hτdef]
        intro _ h
        have : n ≤ i := by exact_mod_cast h
        omega
      rw [hempty]
      exact @MeasurableSet.empty _ (𝒢 i)
  rw [eq_comm, ← sub_eq_zero, ← integral_sub (hiπ.integrableOn) (hSint n).integrableOn]
  have hsum : (fun ω => stoppedValue S π ω - S n ω) = fun ω =>
      ∑ i ∈ Finset.range (N + 1),
        Set.indicator {ω | τ ω ≤ i ∧ i < π ω} (S (i + 1) - S i) ω := by
    have := stoppedValue_sub_eq_sum' (u := S) hle hbdd
    rw [hSn] at this
    funext ω
    have h := congrFun this ω
    simpa using h
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [setIntegral_indicator (𝒢.le _ _ (hA i)),
      integral_sub' (hSint _).integrableOn (hSint _).integrableOn, sub_eq_zero,
      ← setIntegral_condExp (𝒢.le i) (hSint (i + 1)) (hmeas i)]
    refine setIntegral_congr_fun (𝒢.le _ _ (hmeas i)) fun ω hω => ?_
    have h2 := hω.2
    simp only [Set.mem_ofPred_eq, hτdef, hπdef] at h2
    exact (snellEnvelope_eq_condExp_of_lt_snellStoppingTimeFrom
      (by exact_mod_cast h2.1) (by exact_mod_cast h2.2)).symm
  · intro i _
    exact (((hSint _).sub (hSint _)).indicator (𝒢.le _ _ (hA i))).integrableOn

end MeasureTheory
