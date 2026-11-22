/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CompensatorUniqueness
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Uniqueness of càdlàg compensators for a single-jump history

`MathlibExt/Probability/Statistics/Survival/CompensatorUniqueness.lean` proves that compensators
of a counting process are unique for a single-jump history, assuming each compensator is
*stopped at exit*, `A t = A (t ∧ X)`. Its Scope section shows that some path condition is needed
(a left-continuous, unstopped, predictable martingale of finite variation exists) and records the
textbook version, with càdlàg paths in place of the stopping hypothesis, as not proved there.
This file proves that textbook version: right-continuous paths replace stopping at exit.

## Source receipt

* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section II.3.1: the compensator is the unique predictable,
  càdlàg, finite-variation process with `A(0) = 0` making `N - A` a (local) martingale.
* T. R. Fleming and D. P. Harrington, *Counting Processes and Survival Analysis*, Wiley (1991),
  Theorem 1.4.1 (uniqueness of the compensator) and Section 1.3 (the single-jump process under
  random censorship).

Reused, not reproved: the whole uniqueness argument for stopped compensators,
`ae_forall_eq_of_isCompensator`, and its model-level corollary `ae_forall_eq_compensator`.
Proved here: the reduction from càdlàg compensators to stopped ones.

## Hypotheses

As in `ae_forall_eq_of_isCompensator` (`hX`, `hpast`, predictability, finite variation,
normalization at `-∞`), with stopping at exit replaced by

* `hcont`: every path of the compensator is right-continuous;
* `hfut`: nothing is learned after exit, `B ∩ {X ≤ s} ∈ ℱ s` for `B ∈ ℱ t`, `s ≤ t`.

`hfut` is the counterpart, after exit, of `hpast`. For T56's history filtration both hold
(`history_inter_obsTime_le`, `history_inter_or_subset`).

## Main results

* `ae_stopped_of_martingale`: under `hX` and `hfut`, a martingale with almost surely
  right-continuous paths is almost surely stopped at `X`.
* `measurable_stopped_strictPast`: if `A` is predictable with right-continuous paths, the stopped
  process `A (t ∧ X)` is predictable.
* `ae_forall_eq_of_isCompensator_cadlag`: two predictable, càdlàg, finite-variation, normalized
  compensators of the same `N` are indistinguishable.
* `ae_forall_eq_of_isCompensator_cadlag_history`: the same for T56's history filtration.
* `ae_forall_eq_compensator_cadlag`: under independent censoring every predictable, càdlàg,
  finite-variation, normalized compensator equals `A(t) = Λ((-∞, t ∧ X])` up to
  indistinguishability. Unlike the competitor, `A` need not be right-continuous on every path
  (only stopping is used for it).

## Proof

For `s ≤ t`, `hfut` makes `1{X ≤ s} M t` an `ℱ s`-measurable function, so the martingale
identity gives `M t = M s` almost surely on `{X ≤ s}`. Over rational pairs this holds
simultaneously, and right-continuity extends it to `M t = M (t ∧ X)` for all `t`. Applied to
`D = A - A'` this stops `D`. The stopped processes `Ā t = A (t ∧ X)`, `Ā' t = A' (t ∧ X)` are
predictable (dyadic approximation of `t ∧ X` from above, then right-continuity), stopped, of
finite variation, normalized, and `Ā - Ā'` is a martingale (it equals `D` almost surely). The
merged theorem, applied with `N := Ā`, gives `Ā = Ā'`, hence `A = A'`.

## Scope

* Right-continuity is assumed for **every** path of `A` and `A'` (as in the textbook definition
  of a càdlàg process), not only almost every path. It is used to show that the stopped process
  `A (t ∧ X)` is exactly `ℱ_{t-}`-measurable; the filtration is not assumed complete (and
  generally cannot be: `hpast` forbids proper nonempty subsets of `{X > s}`, null or not). Left
  limits are not used.
* The version with almost-everywhere right-continuous paths is not proved here (deferred).
* Finite variation and normalization remain almost-sure hypotheses, as in the merged theorem.

## Reused API

* `ae_forall_eq_of_isCompensator`, `ae_forall_eq_compensator`
  (`MathlibExt/Probability/Statistics/Survival/CompensatorUniqueness.lean`).
* `historyFiltration`, `measurable_observedProcess_history`, `measurableSet_obsTime_le_history`,
  `history_inter_or_subset`, `countingProcess_of_obsTime_le`, `measurable_countingProcess_history`,
  `strictPast_le_history` (`MathlibExt/Probability/Statistics/Survival/CountingProcess.lean`).
* `MeasureTheory.condExp_indicator`, `condExp_of_stronglyMeasurable`, `Martingale.condExp_ae_eq`;
  `measurable_of_tendsto_metrizable`; `eVariationOn.comp_le_of_monotoneOn`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ### Dyadic approximation from above -/

/-- The dyadic point `(⌊x 2ⁿ⌋ + 1) / 2ⁿ`, strictly above `x` and within `2⁻ⁿ` of it. -/
private noncomputable def dyadicUp (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ + 1) / 2 ^ n

private theorem lt_dyadicUp (n : ℕ) (x : ℝ) : x < dyadicUp n x := by
  unfold dyadicUp
  rw [lt_div_iff₀ (by positivity)]
  exact Int.lt_floor_add_one _

private theorem dyadicUp_le (n : ℕ) (x : ℝ) : dyadicUp n x ≤ x + 1 / 2 ^ n := by
  unfold dyadicUp
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  have := Int.floor_le (x * 2 ^ n)
  linarith

private theorem tendsto_dyadicUp (x : ℝ) :
    Tendsto (fun n => dyadicUp n x) atTop (𝓝[≥] x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (lt_dyadicUp n x).le⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => (lt_dyadicUp n x).le) (fun n => dyadicUp_le n x)
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa using (tendsto_const_nhds (x := x)).add h

/-! ### Stopped processes -/

section Stopping

variable {ℱ : Filtration ℝ m0} {X : Ω → ℝ}

/-- If `{X > s} ∈ ℱ s` for all `s`, the strict past `ℱ_{t-}` determines `t ∧ X`. -/
theorem measurable_min_strictPast (hX : ∀ s, MeasurableSet[ℱ s] {ω | s < X ω}) (t : ℝ) :
    Measurable[⨆ s < t, ℱ s] fun ω => min t (X ω) := by
  refine measurable_of_Iic fun x => ?_
  by_cases hx : t ≤ x
  · have : (fun ω => min t (X ω)) ⁻¹' Iic x = univ :=
      eq_univ_of_forall fun ω => (min_le_left _ _).trans hx
    rw [this]; exact MeasurableSet.univ
  · have : (fun ω => min t (X ω)) ⁻¹' Iic x = {ω | x < X ω}ᶜ := by
      ext ω; simp [min_le_iff, hx]
    rw [this]
    exact le_iSup₂ (f := fun s (_ : s < t) => ℱ s) x (not_le.1 hx) _ (hX x).compl

/-- **Stopping preserves predictability.** If `A t` is `ℱ_{t-}`-measurable for every `t` and every
path of `A` is right-continuous, then `A (t ∧ X)` is `ℱ_{t-}`-measurable. -/
theorem measurable_stopped_strictPast (hX : ∀ s, MeasurableSet[ℱ s] {ω | s < X ω})
    {A : ℝ → Ω → ℝ} (hApred : ∀ t, Measurable[⨆ s < t, ℱ s] (A t))
    (hAcont : ∀ ω t, ContinuousWithinAt (fun s => A s ω) (Ici t) t) (t : ℝ) :
    Measurable[⨆ s < t, ℱ s] fun ω => A (min t (X ω)) ω := by
  have hg : ∀ (n : ℕ) (k : ℤ), Measurable[⨆ s < t, ℱ s] (A (min t ((k + 1) / 2 ^ n))) := by
    intro n k
    by_cases h : ((k : ℝ) + 1) / 2 ^ n < t
    · rw [min_eq_right h.le]
      exact (hApred _).mono (iSup₂_le fun s hs =>
        le_iSup₂ (f := fun s (_ : s < t) => ℱ s) s (hs.trans h)) le_rfl
    · rw [min_eq_left (not_lt.1 h)]
      exact hApred t
  have hf : ∀ n : ℕ, Measurable[⨆ s < t, ℱ s]
      fun ω => A (min t (dyadicUp n (min t (X ω)))) ω := by
    intro n S hS
    have hk : Measurable[⨆ s < t, ℱ s] fun ω => ⌊min t (X ω) * 2 ^ n⌋ :=
      Int.measurable_floor.comp ((measurable_min_strictPast hX t).mul_const _)
    have : (fun ω => A (min t (dyadicUp n (min t (X ω)))) ω) ⁻¹' S =
        ⋃ k : ℤ, (fun ω => ⌊min t (X ω) * 2 ^ n⌋) ⁻¹' {k} ∩
          A (min t ((k + 1) / 2 ^ n)) ⁻¹' S := by
      ext ω
      simp [dyadicUp]
    rw [this]
    exact MeasurableSet.iUnion fun k => (hk (measurableSet_singleton k)).inter (hg n k hS)
  refine @measurable_of_tendsto_metrizable Ω ℝ (⨆ s < t, ℱ s) _ _ _ _ _ _ hf
    (tendsto_pi_nhds.2 fun ω => ?_)
  have hm : min t (X ω) ≤ t := min_le_left _ _
  have hτ : Tendsto (fun n => min t (dyadicUp n (min t (X ω)))) atTop
      (𝓝[≥] (min t (X ω))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      le_min hm (lt_dyadicUp n _).le⟩
    have h := ((continuous_const (y := t)).min continuous_id).tendsto (min t (X ω)) |>.comp
      ((tendsto_dyadicUp (min t (X ω))).mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def, min_eq_right hm] using h
  exact (hAcont ω _).tendsto.comp hτ

/-- A stopped path of locally bounded variation has locally bounded variation. -/
theorem locallyBoundedVariationOn_stopped {f : ℝ → ℝ} (hf : LocallyBoundedVariationOn f univ)
    (x : ℝ) : LocallyBoundedVariationOn (fun t => f (min t x)) univ := by
  intro a b _ _
  refine ne_top_of_le_ne_top (hf (min a x) (min b x) trivial trivial) ?_
  exact eVariationOn.comp_le_of_monotoneOn f (fun t => min t x)
    (fun _ _ _ _ h => min_le_min_right x h)
    (fun t ht => ⟨trivial, min_le_min_right x ht.2.1, min_le_min_right x ht.2.2⟩)

/-- A stopped path that tends to `0` at `-∞` still tends to `0` at `-∞`. -/
theorem tendsto_stopped_atBot {f : ℝ → ℝ} (hf : Tendsto f atBot (𝓝 0)) (x : ℝ) :
    Tendsto (fun t => f (min t x)) atBot (𝓝 0) :=
  hf.congr' ((eventually_le_atBot x).mono fun t ht => by
    change f t = f (min t x); rw [min_eq_left ht])

variable {P : Measure Ω}

/-- A process that agrees almost surely, along whole paths, with a martingale and is adapted is
a martingale. -/
private theorem martingale_of_ae_eq {M M' : ℝ → Ω → ℝ} (hM : Martingale M ℱ P)
    (hadapt : ∀ t, StronglyMeasurable[ℱ t] (M' t)) (heq : ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω) :
    Martingale M' ℱ P := by
  have heq' : ∀ t, M t =ᵐ[P] M' t := fun t => heq.mono fun ω h => h t
  exact ⟨hadapt, fun i j hij =>
    (condExp_congr_ae (heq' j)).symm.trans ((hM.condExp_ae_eq hij).trans (heq' i))⟩

variable [IsFiniteMeasure P]

/-- **A right-continuous martingale is stopped at exit.** If `{X > s} ∈ ℱ s` and nothing is
learned after exit (`B ∩ {X ≤ s} ∈ ℱ s` for `B ∈ ℱ t`, `s ≤ t`), a martingale with almost surely
right-continuous paths satisfies `M t = M (t ∧ X)` for all `t`, almost surely. -/
theorem ae_stopped_of_martingale (hX : ∀ s, MeasurableSet[ℱ s] {ω | s < X ω})
    (hfut : ∀ s t (B : Set Ω), s ≤ t → MeasurableSet[ℱ t] B →
      MeasurableSet[ℱ s] (B ∩ {ω | X ω ≤ s}))
    {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ P)
    (hMcont : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ici t) t) :
    ∀ᵐ ω ∂P, ∀ t, M t ω = M (min t (X ω)) ω := by
  -- For fixed `s ≤ t`, `M t = M s` almost surely on `{X ≤ s}`.
  have hpair : ∀ s t : ℝ, s ≤ t → ∀ᵐ ω ∂P, X ω ≤ s → M t ω = M s ω := by
    intro s t hst
    set E : Set Ω := {ω | X ω ≤ s} with hE_def
    have hE : MeasurableSet[ℱ s] E := by
      have h := (hX s).compl
      simpa only [compl_ofPred, not_lt] using h
    have hmeas : Measurable[ℱ s] (E.indicator (M t)) := by
      intro S hS
      rw [indicator_preimage]
      exact (hfut s t _ hst ((hM.1 t).measurable hS)).union
        ((measurable_const (a := (0 : ℝ)) hS).diff hE)
    have h1 : P[E.indicator (M t) | ℱ s] = E.indicator (M t) :=
      condExp_of_stronglyMeasurable (ℱ.le s) hmeas.stronglyMeasurable
        ((hM.integrable t).indicator (ℱ.le s _ hE))
    have h2 : P[E.indicator (M t) | ℱ s] =ᵐ[P] E.indicator (P[M t | ℱ s]) :=
      condExp_indicator (hM.integrable t) hE
    have h3 : P[M t | ℱ s] =ᵐ[P] M s := hM.condExp_ae_eq hst
    rw [h1] at h2
    filter_upwards [h2, h3] with ω hω hω' hXs
    have hmem : ω ∈ E := hXs
    rw [indicator_of_mem hmem, indicator_of_mem hmem] at hω
    rw [hω, hω']
  -- Simultaneously for all rational pairs.
  have hq : ∀ᵐ ω ∂P, ∀ s t : ℚ, (s : ℝ) ≤ t → X ω ≤ s → M t ω = M s ω := by
    rw [ae_all_iff]; intro s; rw [ae_all_iff]; intro t
    by_cases hst : (s : ℝ) ≤ t
    · filter_upwards [hpair s t hst] with ω hω _ h using hω h
    · exact ae_of_all _ fun ω h => absurd h hst
  filter_upwards [hq, hMcont] with ω hω hc t
  rcases le_or_gt t (X ω) with h | h
  · rw [min_eq_left h]
  rw [min_eq_right h.le]
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt (X ω)
  have hK : ∀ q : ℚ, X ω < q → M q ω = M q₀ ω := by
    intro q hq
    rcases le_total (q : ℝ) q₀ with h' | h'
    · exact (hω q q₀ h' hq.le).symm
    · exact hω q₀ q h' hq₀.le
  have hR : ∀ r, X ω ≤ r → M r ω = M q₀ ω := by
    intro r hr
    have hseq : ∀ n : ℕ, ∃ q : ℚ, r < q ∧ (q : ℝ) < r + 1 / ((n : ℝ) + 1) := fun n =>
      exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                          linarith)
    choose q hq using hseq
    have hτ : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[≥] r) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds ?_ (fun n => (hq n).1.le) (fun n => (hq n).2.le),
        Eventually.of_forall fun n => (hq n).1.le⟩
      simpa using (tendsto_const_nhds (x := r)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim := (hc r).tendsto.comp hτ
    have hconst : (fun s => M s ω) ∘ (fun n => (q n : ℝ)) = fun _ => M q₀ ω :=
      funext fun n => hK _ (hr.trans_lt (hq n).1)
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  exact (hR t h.le).trans (hR (X ω) le_rfl).symm

/-! ### Uniqueness of càdlàg compensators -/

/-- **Uniqueness of càdlàg compensators for a single-jump history.**

Let `ℱ` be a filtration on `ℝ` and `X` a random time such that `{X > s} ∈ ℱ s`, every `ℱ s`-event
contains `{X > s}` or misses it (nothing is learned before exit), and `B ∩ {X ≤ s} ∈ ℱ s` for
every `ℱ t`-event `B`, `s ≤ t` (nothing is learned after exit). Let `A` and `A'` be two
compensators of the same process `N`: both are predictable (`A t` is `ℱ_{t-}`-measurable), every
path is right-continuous, almost every path is of finite variation on compact intervals and tends
to `0` at `-∞`, and `N - A`, `N - A'` are martingales. Then `A` and `A'` are indistinguishable.
No stopping at exit is assumed. -/
theorem ae_forall_eq_of_isCompensator_cadlag {N A A' : ℝ → Ω → ℝ}
    (hX : ∀ s, MeasurableSet[ℱ s] {ω | s < X ω})
    (hpast : ∀ s (B : Set Ω), MeasurableSet[ℱ s] B →
      B ∩ {ω | s < X ω} = ∅ ∨ {ω | s < X ω} ⊆ B)
    (hfut : ∀ s t (B : Set Ω), s ≤ t → MeasurableSet[ℱ t] B →
      MeasurableSet[ℱ s] (B ∩ {ω | X ω ≤ s}))
    (hA : Martingale (fun t => N t - A t) ℱ P) (hA' : Martingale (fun t => N t - A' t) ℱ P)
    (hApred : ∀ t, Measurable[⨆ s < t, ℱ s] (A t))
    (hA'pred : ∀ t, Measurable[⨆ s < t, ℱ s] (A' t))
    (hAcont : ∀ ω t, ContinuousWithinAt (fun s => A s ω) (Ici t) t)
    (hA'cont : ∀ ω t, ContinuousWithinAt (fun s => A' s ω) (Ici t) t)
    (hAfv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t => A t ω) univ)
    (hA'fv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hAlim : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atBot (𝓝 0))
    (hA'lim : ∀ᵐ ω ∂P, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω := by
  set D : ℝ → Ω → ℝ := fun t ω => A t ω - A' t ω with hD_def
  have hD : Martingale D ℱ P := by
    have : D = (fun t => N t - A' t) - fun t => N t - A t := by
      funext t ω; simp only [hD_def, Pi.sub_apply]; ring
    rw [this]; exact hA'.sub hA
  have hDstop := ae_stopped_of_martingale hX hfut hD
    (ae_of_all _ fun ω t => (hAcont ω t).sub (hA'cont ω t))
  set Ab : ℝ → Ω → ℝ := fun t ω => A (min t (X ω)) ω with hAb_def
  set Ab' : ℝ → Ω → ℝ := fun t ω => A' (min t (X ω)) ω with hAb'_def
  have hAbpred : ∀ t, Measurable[⨆ s < t, ℱ s] (Ab t) :=
    measurable_stopped_strictPast hX hApred hAcont
  have hAb'pred : ∀ t, Measurable[⨆ s < t, ℱ s] (Ab' t) :=
    measurable_stopped_strictPast hX hA'pred hA'cont
  have hle : ∀ t, (⨆ s < t, ℱ s) ≤ ℱ t := fun t => iSup₂_le fun s hs => ℱ.mono hs.le
  have hmart : Martingale (fun t => Ab t - Ab' t) ℱ P :=
    martingale_of_ae_eq hD
      (fun t => (((hAbpred t).sub (hAb'pred t)).mono (hle t) le_rfl).stronglyMeasurable)
      (hDstop.mono fun ω h t => h t)
  have hzero : Martingale (fun t => Ab t - Ab t) ℱ P := by
    have : (fun t => Ab t - Ab t) = 0 := by funext t; simp
    rw [this]; exact martingale_zero _ ℱ P
  have h := ae_forall_eq_of_isCompensator (N := Ab) (A := Ab) (A' := Ab') hX hpast hzero hmart
    hAbpred hAb'pred (fun t ω => by simp only [hAb_def, min_assoc, min_self])
    (fun t ω => by simp only [hAb'_def, min_assoc, min_self])
    (hAfv.mono fun ω h => locallyBoundedVariationOn_stopped h (X ω))
    (hA'fv.mono fun ω h => locallyBoundedVariationOn_stopped h (X ω))
    (hAlim.mono fun ω h => tendsto_stopped_atBot h (X ω))
    (hA'lim.mono fun ω h => tendsto_stopped_atBot h (X ω))
  filter_upwards [h, hDstop] with ω hω hs t
  have h1 : A t ω - A' t ω = A (min t (X ω)) ω - A' (min t (X ω)) ω := hs t
  have h2 : A (min t (X ω)) ω = A' (min t (X ω)) ω := hω t
  linarith

end Stopping

/-! ### The censoring model -/

section History

variable {T C : Ω → ℝ}

/-- The observed process is frozen after exit: `(N(u), Nᶜ(u)) = (N(s), Nᶜ(s))` for
`X ≤ s ≤ u`. -/
theorem observedProcess_of_obsTime_le {s u : ℝ} {ω : Ω} (hs : obsTime T C ω ≤ s) (hsu : s ≤ u) :
    observedProcess T C u ω = observedProcess T C s ω := by
  simp only [observedProcess, countingProcess, censoringProcess, obsTime] at hs ⊢
  rcases le_or_gt (T ω) (C ω) with h | h
  · rw [min_eq_left h] at hs
    simp [h, hs, hs.trans hsu, not_lt.2 h]
  · rw [min_eq_right h.le] at hs
    simp [h, hs, hs.trans hsu, not_le.2 h]

/-- Every path of the counting process is right-continuous. -/
theorem continuousWithinAt_countingProcess (ω : Ω) (t : ℝ) :
    ContinuousWithinAt (fun s => countingProcess T C s ω) (Ici t) t := by
  have key : ∀ᶠ s in 𝓝[≥] t, countingProcess T C s ω = countingProcess T C t ω := by
    by_cases h : T ω ≤ C ω ∧ T ω ≤ t
    · filter_upwards [self_mem_nhdsWithin] with s (hs : t ≤ s)
      simp [countingProcess, h, h.2.trans hs]
    · by_cases hTC : T ω ≤ C ω
      · have ht : t < T ω := not_le.1 fun h' => h ⟨hTC, h'⟩
        filter_upwards [Ico_mem_nhdsGE ht] with s hs
        simp [countingProcess, not_le.2 hs.2, not_le.2 ht]
      · filter_upwards with s
        simp [countingProcess, hTC]
  exact continuousWithinAt_const.congr_of_eventuallyEq key rfl

/-- The σ-algebra of sets whose trace on `E` is `m`-measurable. -/
@[instance_reducible]
private def traceOn (m : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet[m] E) :
    MeasurableSpace Ω where
  MeasurableSet' B := MeasurableSet[m] (B ∩ E)
  measurableSet_empty := by rw [empty_inter]; exact @MeasurableSet.empty _ m
  measurableSet_compl B hB := by
    have : Bᶜ ∩ E = E \ (B ∩ E) := by
      ext; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [this]; exact hE.diff hB
  measurableSet_iUnion f hf := by rw [iUnion_inter]; exact MeasurableSet.iUnion hf

variable (hT : Measurable T) (hC : Measurable C)

/-- **Nothing is learned after exit**: for any `s`, `u`, the trace on `{X ≤ s}` of an event
observed by time `u` is already observed at time `s`. -/
theorem history_inter_obsTime_le {s u : ℝ} {B : Set Ω}
    (hB : MeasurableSet[historyFiltration hT hC u] B) :
    MeasurableSet[historyFiltration hT hC s] (B ∩ {ω | obsTime T C ω ≤ s}) := by
  have hE := measurableSet_obsTime_le_history hT hC (le_refl s)
  suffices h : historyFiltration hT hC u ≤ traceOn (historyFiltration hT hC s) _ hE from h B hB
  refine iSup₂_le fun j _ => ?_
  rintro _ ⟨B', hB', rfl⟩
  change MeasurableSet[historyFiltration hT hC s]
    (observedProcess T C j ⁻¹' B' ∩ {ω | obsTime T C ω ≤ s})
  rcases le_total j s with hjs | hsj
  · exact (measurable_observedProcess_history hT hC hjs hB').inter hE
  · have : observedProcess T C j ⁻¹' B' ∩ {ω | obsTime T C ω ≤ s} =
        observedProcess T C s ⁻¹' B' ∩ {ω | obsTime T C ω ≤ s} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [← observedProcess_of_obsTime_le h2 hsj], h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [observedProcess_of_obsTime_le h2 hsj], h2⟩
    rw [this]
    exact (measurable_observedProcess_history hT hC le_rfl hB').inter hE

/-- `{X > s}` is observed at time `s`. -/
theorem measurableSet_lt_obsTime_history (s : ℝ) :
    MeasurableSet[historyFiltration hT hC s] {ω | s < obsTime T C ω} := by
  have h := (measurableSet_obsTime_le_history hT hC (le_refl s)).compl
  simpa only [compl_ofPred, not_le] using h

variable {P : Measure Ω}

include hT hC in
/-- **Càdlàg compensator uniqueness in the censoring model.** For the history filtration
`ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)` of one subject, two predictable compensators `A`, `A'` of `N` with
right-continuous paths (almost every path of finite variation with `A(-∞) = 0`, and `N - A`,
`N - A'` martingales) are indistinguishable. No stopping at exit is assumed. -/
theorem ae_forall_eq_of_isCompensator_cadlag_history [IsFiniteMeasure P] {A A' : ℝ → Ω → ℝ}
    (hA : Martingale (fun t => countingProcess T C t - A t) (historyFiltration hT hC) P)
    (hA' : Martingale (fun t => countingProcess T C t - A' t) (historyFiltration hT hC) P)
    (hApred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A t))
    (hA'pred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A' t))
    (hAcont : ∀ ω t, ContinuousWithinAt (fun s => A s ω) (Ici t) t)
    (hA'cont : ∀ ω t, ContinuousWithinAt (fun s => A' s ω) (Ici t) t)
    (hAfv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t => A t ω) univ)
    (hA'fv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hAlim : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atBot (𝓝 0))
    (hA'lim : ∀ᵐ ω ∂P, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω :=
  ae_forall_eq_of_isCompensator_cadlag (X := obsTime T C)
    (measurableSet_lt_obsTime_history hT hC) (fun _ _ hB => history_inter_or_subset hT hC hB)
    (fun _ _ _ _ hB => history_inter_obsTime_le hT hC hB) hA hA' hApred hA'pred
    hAcont hA'cont hAfv hA'fv hAlim hA'lim

include hT hC in
/-- **The model compensator is the unique càdlàg one.** Under independent censoring, every
predictable compensator `A'` of `N` with right-continuous paths, almost every path of finite
variation and tending to `0` at `-∞`, is indistinguishable from `A(t) = Λ((-∞, t ∧ X])`, `Λ` the
hazard measure of the law of `T`. No stopping at exit is assumed for `A'`, and no condition is
put on the law of `T`. -/
theorem ae_forall_eq_compensator_cadlag [IsProbabilityMeasure P] (hind : IndepFun T C P)
    {A' : ℝ → Ω → ℝ}
    (hA' : Martingale (fun t => countingProcess T C t - A' t) (historyFiltration hT hC) P)
    (hA'pred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A' t))
    (hA'cont : ∀ ω t, ContinuousWithinAt (fun s => A' s ω) (Ici t) t)
    (hA'fv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hA'lim : ∀ᵐ ω ∂P, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A' t ω = compensator T C (hazardMeasure (P.map T)) t ω := by
  have hX := measurableSet_lt_obsTime_history hT hC
  have hstop := ae_stopped_of_martingale hX
    (fun _ _ _ _ hB => history_inter_obsTime_le hT hC hB) hA'
    (ae_of_all _ fun ω t => (continuousWithinAt_countingProcess ω t).sub (hA'cont ω t))
  have hN : ∀ t ω, countingProcess T C t ω =
      countingProcess T C (min t (obsTime T C ω)) ω := fun t ω => by
    rcases le_total t (obsTime T C ω) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, countingProcess_of_obsTime_le h]
  have hA'stop : ∀ᵐ ω ∂P, ∀ t, A' t ω = A' (min t (obsTime T C ω)) ω :=
    hstop.mono fun ω h t => by
      have h1 : countingProcess T C t ω - A' t ω =
          countingProcess T C (min t (obsTime T C ω)) ω -
            A' (min t (obsTime T C ω)) ω := h t
      have h2 := hN t ω
      linarith
  set Ab : ℝ → Ω → ℝ := fun t ω => A' (min t (obsTime T C ω)) ω with hAb_def
  have hAbpred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (Ab t) :=
    measurable_stopped_strictPast hX hA'pred hA'cont
  have hmart : Martingale (fun t => countingProcess T C t - Ab t) (historyFiltration hT hC) P :=
    martingale_of_ae_eq hA'
      (fun t => ((measurable_countingProcess_history hT hC le_rfl).sub
        ((hAbpred t).mono (strictPast_le_history hT hC t) le_rfl)).stronglyMeasurable)
      (hA'stop.mono fun ω h t => by simp only [Pi.sub_apply, hAb_def]; rw [← h t])
  have h := ae_forall_eq_compensator hT hC hind hmart hAbpred
    (fun t ω => by simp only [hAb_def, min_assoc, min_self])
    (hA'fv.mono fun ω h => locallyBoundedVariationOn_stopped h (obsTime T C ω))
    (hA'lim.mono fun ω h => tendsto_stopped_atBot h (obsTime T C ω))
  filter_upwards [h, hA'stop] with ω h1 h2 t
  rw [h2 t]
  exact h1 t

end History

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
