/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CountingProcess
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Uniqueness of compensators for a single-jump history

A **compensator** of a counting process `N` is a predictable process `A` of finite variation,
normalized by `A(-∞) = 0`, such that `N - A` is a martingale. This file proves that the compensator
is unique (up to indistinguishability) for filtrations in which nothing is learned before a random
exit time `X`, in particular for the history filtration of the censoring model of
`MathlibExt/Probability/Statistics/Survival/CountingProcess.lean`, whose compensator
`A(t) = Λ((-∞, t ∧ X])` is therefore *the* compensator.

## Source receipt

* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section II.3.1: the compensator in the Doob–Meyer decomposition
  `N = M + A` is the unique predictable increasing process with `A(0) = 0` making `N - A` a
  (local) martingale; uniqueness rests on "a predictable martingale of finite variation is
  constant".
* T. R. Fleming and D. P. Harrington, *Counting Processes and Survival Analysis*, Wiley (1991),
  Theorem 1.4.1 (Doob–Meyer, uniqueness of the compensator) and Section 1.3 (the single-jump
  process under random censorship).

## Hypotheses (T56's model, restated minimally)

Time is `ℝ` with a filtration `ℱ`, and `X : Ω → ℝ` is a random time with

* `hX`: `{X > s}` is an `ℱ s`-event (`X` is observed when it happens);
* `hpast`: every `ℱ s`-event contains `{X > s}` or misses it (the history before exit is trivial).

For T56's `historyFiltration` these are `measurableSet_obsTime_le_history` and
`history_inter_or_subset`. A compensator candidate `A` is assumed

* **predictable**: `A t` is `ℱ_{t-} = ⨆_{s < t} ℱ s`-measurable (T56's notion; Mathlib's
  `IsStronglyPredictable` needs an `OrderBot` time index, which `ℝ` lacks);
* **stopped at exit**: `A t = A (t ∧ X)` (see Scope);
* **of finite variation**: each path has `LocallyBoundedVariationOn` on `ℝ`;
* **normalized**: each path tends to `0` at `-∞` (the analogue of `A(0) = 0` on `[0, ∞)`).

No hypothesis is put on `N` beyond `N - A` and `N - A'` being martingales.

## Main results

* `ae_forall_eq_of_isCompensator`: two such compensators of the same `N` are indistinguishable,
  `∀ᵐ ω, ∀ t, A t ω = A' t ω`.
* `ae_forall_eq_of_isCompensator_history`: the same for T56's history filtration.
* `ae_forall_eq_compensator`: under independent censoring, with the hazard measure `Λ` of the law
  of `T` finite on half-lines, every such compensator equals T56's `compensator`
  `A(t) = Λ((-∞, t ∧ X])` up to indistinguishability. Its inputs `compensator_min_obsTime`,
  `monotone_compensator` and `tendsto_compensator_atBot` show that T56's compensator is in the
  class; `hazardMeasure_Iic_ne_top` gives the finiteness hypothesis when `F[s, ∞) > 0`.

## Proof

`D = A - A'` is a predictable, stopped martingale. By `hpast`, `D t` is constant, `= d t`, on
`{X ≥ t}`, and stopping gives `D t = d (t ∧ X)`. The martingale identity on `{X > s}` reads
`d t · P(X ≥ t) = d s · P(X > s) - E[d X; s < X < t]`, which yields the Grönwall-type inequality
`|d t| P(X ≥ t) ≤ |d s| P(X > s) + sup_{(s,t)} |d| · P(s < X < t)`. A contraction argument on a left
tail, followed by a supremum argument, gives `d = 0` on `(-∞, u]` whenever `P(X ≥ u) > 0`; almost
every exit time has `P(X ≥ X ω) > 0` (`ae_measure_Ici_ne_zero`), so `D = 0` along a.e. path.

## Scope

* **Stopping at exit is assumed, not derived.** With predictability meaning
  `ℱ_{t-}`-measurability at each fixed `t`, some path condition beyond finite variation is needed:
  if the law of `X` is atomless and charges every `[t, ∞)`, then
  `D(t) = 1{X < t} - 1{X ≥ t} · P(X < t) / P(X ≥ t)` is `ℱ_{t-}`-measurable, has finite-variation
  paths tending to `0` at `-∞`, and is a martingale for the history (on `{X > s}` both sides of
  the martingale identity equal `-P(X ≤ s)`), yet `D ≠ 0`, so `A + D` is a second compensator in
  this weak sense. `D` is left-continuous at `X` and not stopped. (This is an informal remark; it
  is not formalized here.) The textbook statement
  excludes it by asking for càdlàg paths; the càdlàg variant (deriving `A t = A (t ∧ X)` a.s. from
  right-continuity) is not proved here.
* The general Doob–Meyer uniqueness for arbitrary filtrations (predictable σ-algebra on `ℝ × Ω`,
  Stieltjes integration of predictable integrands) is not built. In discrete time it is Mathlib's
  `MeasureTheory.Martingale.eq_zero_of_predictable`.

## Reused API

* `MeasureTheory.Martingale.setIntegral_eq`, `Martingale.sub`
  (`Mathlib/Probability/Martingale/Basic.lean`).
* `eVariationOn.edist_le`, `MonotoneOn.locallyBoundedVariationOn`
  (`Mathlib/Topology/EMetricSpace/BoundedVariation.lean`).
* `MeasureTheory.tendsto_measure_iInter_atTop`, `tendsto_measure_iInter_atBot`
  (`Mathlib/MeasureTheory/Measure/Continuity.lean`).
* `historyFiltration`, `history_inter_or_subset`, `measurableSet_obsTime_le_history`,
  `measurable_compensator_strictPast`, `martingale_compensatedProcess`, `compensator_eq`,
  `ae_measure_Ici_ne_zero` (`MathlibExt/Probability/Statistics/Survival/CountingProcess.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal


variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ### The strict past is trivial on `{t ≤ X}` -/

/-- The σ-algebra of sets that either contain `E` or miss it. -/
@[instance_reducible]
private def trivialOn (E : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' B := B ∩ E = ∅ ∨ E ⊆ B
  measurableSet_empty := Or.inl (empty_inter E)
  measurableSet_compl B hB := by
    rcases hB with h | h
    · exact Or.inr fun x hx hxB => (h.subset ⟨hxB, hx⟩ : x ∈ (∅ : Set Ω))
    · exact Or.inl (eq_empty_of_forall_notMem fun x hx => hx.1 (h hx.2))
  measurableSet_iUnion f hf := by
    by_cases h : ∃ i, E ⊆ f i
    · obtain ⟨i, hi⟩ := h
      exact Or.inr (hi.trans (subset_iUnion f i))
    · push Not at h
      left
      rw [iUnion_inter]
      exact iUnion_eq_empty.2 fun i => (hf i).resolve_right (h i)

/-- If every `ℱ s`-event contains or misses `{s < X}`, then a real random variable determined by
the strict past `ℱ_{t-}` takes one value on `{t ≤ X}`. -/
private theorem eq_of_strictPast {ℱ : Filtration ℝ m0} {X : Ω → ℝ}
    (hpast : ∀ s (B : Set Ω), MeasurableSet[ℱ s] B →
      B ∩ {ω | s < X ω} = ∅ ∨ {ω | s < X ω} ⊆ B)
    {t : ℝ} {f : Ω → ℝ} (hf : Measurable[⨆ s < t, ℱ s] f) {ω₁ ω₂ : Ω}
    (h₁ : t ≤ X ω₁) (h₂ : t ≤ X ω₂) : f ω₁ = f ω₂ := by
  have hle : (⨆ s < t, ℱ s) ≤ trivialOn {ω | t ≤ X ω} := by
    refine iSup₂_le fun s hs B hB => ?_
    rcases hpast s B hB with h | h
    · exact Or.inl (eq_empty_of_forall_notMem fun ω hω =>
        (h.subset ⟨hω.1, hs.trans_le hω.2⟩ : ω ∈ (∅ : Set Ω)))
    · exact Or.inr fun ω hω => h (hs.trans_le hω)
  have hB : MeasurableSet[trivialOn {ω | t ≤ X ω}] (f ⁻¹' {f ω₁}) :=
    hle _ (hf (measurableSet_singleton _))
  rcases hB with h | h
  · exact absurd (h.subset ⟨rfl, h₁⟩ : ω₁ ∈ (∅ : Set Ω)) (notMem_empty ω₁)
  · exact (h h₂ : f ω₂ = f ω₁).symm

/-! ### A contraction principle -/

/-- If a bounded function on `S` satisfies `sup |g| ≤ θ · sup |g|` with `θ < 1`, it vanishes. -/
private theorem eq_zero_of_contract {S : Set ℝ} {g : ℝ → ℝ} {M θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hM : ∀ w ∈ S, |g w| ≤ M)
    (h : ∀ B, (∀ w ∈ S, |g w| ≤ B) → ∀ w ∈ S, |g w| ≤ θ * B) : ∀ w ∈ S, g w = 0 := by
  have hn : ∀ n : ℕ, ∀ w ∈ S, |g w| ≤ θ ^ n * M := by
    intro n
    induction n with
    | zero => simpa using hM
    | succ n ih => intro w hw; rw [pow_succ', mul_assoc]; exact h _ ih w hw
  intro w hw
  have hlim : Tendsto (fun n : ℕ => θ ^ n * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).mul_const M
  exact abs_eq_zero.1 (le_antisymm (ge_of_tendsto' hlim fun n => hn n w hw) (abs_nonneg _))

/-! ### The renewal-type inequality forces the deterministic part to vanish -/

/-- Continuity from above, in real form: a decreasing sequence of measurable sets with empty
intersection eventually has measure below any `ε > 0`. -/
private theorem exists_measureReal_lt {P : Measure Ω} [IsFiniteMeasure P] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n)) (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) {ε : ℝ}
    (hε : 0 < ε) : ∃ n, P.real (s n) < ε := by
  have h := tendsto_measure_iInter_atTop (μ := P) (fun n => (hs n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rw [hempty, measure_empty] at h
  have h' : Tendsto (fun n => P.real (s n)) atTop (𝓝 0) := by
    simpa [Function.comp_def, measureReal_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  exact ((tendsto_order.1 h').2 ε hε).exists

variable {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ}

/-- **The analytic core.** Let `d : ℝ → ℝ` tend to `0` at `-∞`, be bounded on `(-∞, u]`, and
satisfy, for `s < t` and every bound `B` of `|d|` on `(s, t)`,
`|d t| P(X ≥ t) ≤ |d s| P(X > s) + B P(s < X < t)`.
If `P(X ≥ u) > 0` then `d = 0` on `(-∞, u]`. -/
private theorem eq_zero_of_ineq (hXm : Measurable X) {d : ℝ → ℝ}
    (hineq : ∀ s t B, s < t → (∀ w ∈ Ioo s t, |d w| ≤ B) →
      |d t| * P.real {ω | t ≤ X ω} ≤
        |d s| * P.real {ω | s < X ω} + B * P.real {ω | s < X ω ∧ X ω < t})
    (hlim : Tendsto d atBot (𝓝 0)) {u M : ℝ} (hu : 0 < P.real {ω | u ≤ X ω})
    (hbdd : ∀ w ≤ u, |d w| ≤ M) : ∀ w ≤ u, d w = 0 := by
  set c := P.real {ω | u ≤ X ω} with hc_def
  have hc : ∀ t ≤ u, c ≤ P.real {ω | t ≤ X ω} := fun t ht =>
    measureReal_mono (fun ω (h : u ≤ X ω) => (ht.trans h : t ≤ X ω))
  -- Step A: `d` vanishes on a left tail `(-∞, v₀]`.
  obtain ⟨n, hn⟩ := exists_measureReal_lt (P := P) (s := fun n : ℕ => {ω | X ω < -(n : ℝ)})
    (fun n => measurableSet_lt hXm measurable_const)
    (fun m n hmn ω (h : X ω < -(n : ℝ)) => (show X ω < -(m : ℝ) by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith))
    (eq_empty_of_forall_notMem fun ω hω => by
      obtain ⟨k, hk⟩ := exists_nat_gt (-X ω)
      have := mem_iInter.1 hω k
      simp only [mem_ofPred_eq] at this
      linarith) (half_pos hu)
  set v₀ := min u (-(n : ℝ)) with hv₀
  have hA : ∀ w ∈ Iic v₀, d w = 0 := by
    refine eq_zero_of_contract (θ := 1 / 2) (by norm_num) (by norm_num) (M := M)
      (fun w hw => hbdd w (hw.trans (min_le_left _ _))) fun B hB t ht => ?_
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB t ht)
    have htu : t ≤ u := ht.trans (min_le_left _ _)
    have key : ∀ s < t, |d t| * c - B * (c / 2) ≤ |d s| * P.real (univ : Set Ω) := by
      intro s hst
      have h1 := hineq s t B hst fun w hw => hB w (hw.2.le.trans ht)
      have h2 : P.real {ω | s < X ω ∧ X ω < t} ≤ c / 2 :=
        (measureReal_mono (fun ω (h : s < X ω ∧ X ω < t) =>
          (show X ω < -(n : ℝ) from h.2.trans_le (ht.trans (min_le_right _ _))))).trans hn.le
      have h3 : P.real {ω | s < X ω} ≤ P.real (univ : Set Ω) := measureReal_mono (subset_univ _)
      have h4 := mul_le_mul_of_nonneg_left (hc t htu) (abs_nonneg (d t))
      nlinarith [abs_nonneg (d s), mul_le_mul_of_nonneg_left h2 hB0,
        mul_le_mul_of_nonneg_left h3 (abs_nonneg (d s))]
    have hlim' : Tendsto (fun s => |d s| * P.real (univ : Set Ω)) atBot (𝓝 0) := by
      simpa using (hlim.abs).mul_const (P.real (univ : Set Ω))
    have h5 : |d t| * c - B * (c / 2) ≤ 0 :=
      ge_of_tendsto hlim' ((eventually_lt_atBot t).mono key)
    nlinarith
  -- Step B: the supremum of the vanishing region is `u`.
  set S₀ : Set ℝ := {v | v ≤ u ∧ ∀ w ≤ v, d w = 0} with hS₀
  have hv₀S : v₀ ∈ S₀ := ⟨min_le_left _ _, fun w hw => hA w hw⟩
  have hbdd₀ : BddAbove S₀ := ⟨u, fun v hv => hv.1⟩
  set ts := sSup S₀ with hts_def
  have htsu : ts ≤ u := csSup_le ⟨v₀, hv₀S⟩ fun v hv => hv.1
  have hbelow : ∀ w < ts, d w = 0 := fun w hw => by
    obtain ⟨v, hv, hwv⟩ := exists_lt_of_lt_csSup ⟨v₀, hv₀S⟩ hw
    exact hv.2 w hwv.le
  have hat : d ts = 0 := by
    have h1 := hineq (ts - 1) ts 0 (by linarith) fun w hw => by simp [hbelow w hw.2]
    rw [hbelow (ts - 1) (by linarith), abs_zero, zero_mul, zero_mul, add_zero] at h1
    have h2 := mul_le_mul_of_nonneg_left (hc ts htsu) (abs_nonneg (d ts))
    have h3 : |d ts| * c ≤ 0 := h2.trans h1
    exact abs_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_left h3 hu) (abs_nonneg _))
  have hmem : ts ∈ S₀ := ⟨htsu, fun w hw => hw.lt_or_eq.elim (hbelow w) (· ▸ hat)⟩
  rcases htsu.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨k, hk⟩ := exists_measureReal_lt (P := P)
      (s := fun k : ℕ => {ω | ts < X ω ∧ X ω < ts + 1 / ((k : ℝ) + 1)})
      (fun k => (measurableSet_lt measurable_const hXm).inter
        (measurableSet_lt hXm measurable_const))
      (fun m k hmk ω (h : ts < X ω ∧ X ω < ts + 1 / ((k : ℝ) + 1)) => (show
          ts < X ω ∧ X ω < ts + 1 / ((m : ℝ) + 1) from ⟨h.1, h.2.trans_le (by
            have : (m : ℝ) ≤ k := by exact_mod_cast hmk
            gcongr)⟩))
      (eq_empty_of_forall_notMem fun ω hω => by
        have h0 := mem_iInter.1 hω 0
        simp only [mem_ofPred_eq] at h0
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h0.1)
        have := (mem_iInter.1 hω k).2
        linarith) (half_pos hu)
    set v := min u (ts + 1 / ((k : ℝ) + 1)) with hv
    have htv : ts < v := lt_min hlt (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                        linarith)
    have hB : ∀ w ∈ Ioc ts v, d w = 0 := by
      refine eq_zero_of_contract (θ := 1 / 2) (by norm_num) (by norm_num) (M := M)
        (fun w hw => hbdd w (hw.2.trans (min_le_left _ _))) fun B hB t ht => ?_
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB t ht)
      have htu : t ≤ u := ht.2.trans (min_le_left _ _)
      have h1 := hineq ts t B ht.1 fun w hw => hB w ⟨hw.1, hw.2.le.trans ht.2⟩
      rw [hat, abs_zero, zero_mul, zero_add] at h1
      have h2 : P.real {ω | ts < X ω ∧ X ω < t} ≤ c / 2 :=
        (measureReal_mono (fun ω (h : ts < X ω ∧ X ω < t) =>
          (show ts < X ω ∧ X ω < ts + 1 / ((k : ℝ) + 1) from
            ⟨h.1, h.2.trans_le (ht.2.trans (min_le_right _ _))⟩))).trans hk.le
      have h4 := mul_le_mul_of_nonneg_left (hc t htu) (abs_nonneg (d t))
      nlinarith [mul_le_mul_of_nonneg_left h2 hB0]
    have hvS : v ∈ S₀ := ⟨min_le_left _ _, fun w hw => by
      rcases le_or_gt w ts with h | h
      · exact hmem.2 w h
      · exact hB w ⟨h, hw⟩⟩
    exact absurd (le_csSup hbdd₀ hvS) (not_le.2 htv)
  · exact fun w hw => hmem.2 w (heq ▸ hw)

/-! ### Finite-variation paths are bounded on left half-lines -/

/-- A path of locally bounded variation that tends to `0` at `-∞` is bounded on `(-∞, u]`. -/
private theorem exists_bound_Iic {f : ℝ → ℝ} (hf : LocallyBoundedVariationOn f univ)
    (hlim : Tendsto f atBot (𝓝 0)) (u : ℝ) : ∃ M, ∀ w ≤ u, |f w| ≤ M := by
  obtain ⟨a, ha⟩ := eventually_atBot.1 ((tendsto_order.1 hlim.norm).2 1 (by simp))
  set a' := min a u
  have hfin := hf a' u trivial trivial
  refine ⟨1 + (eVariationOn f (univ ∩ Icc a' u)).toReal, fun w hw => ?_⟩
  have ha' : |f a'| < 1 := by simpa [Real.norm_eq_abs] using ha a' (min_le_left _ _)
  rcases le_or_gt w a' with h | h
  · have : |f w| < 1 := by simpa [Real.norm_eq_abs] using ha w (h.trans (min_le_left _ _))
    have := ENNReal.toReal_nonneg (a := eVariationOn f (univ ∩ Icc a' u))
    linarith
  · have hE := eVariationOn.edist_le f (s := univ ∩ Icc a' u) ⟨trivial, h.le, hw⟩
      ⟨trivial, le_rfl, min_le_right _ _⟩
    have hd : dist (f w) (f a') ≤ (eVariationOn f (univ ∩ Icc a' u)).toReal := by
      rw [dist_edist]; exact ENNReal.toReal_mono hfin hE
    rw [Real.dist_eq] at hd
    have := abs_sub_abs_le_abs_sub (f w) (f a')
    linarith

/-! ### Uniqueness of compensators -/

/-- **Uniqueness of compensators for a single-jump history.**

Let `ℱ` be a filtration on `ℝ` and `X` a random time such that `{X > s}` is an `ℱ s`-event and
every `ℱ s`-event either contains `{X > s}` or misses it (nothing is learned before exit; for the
censoring model these are `measurableSet_obsTime_le_history` and `history_inter_or_subset`). Let
`A` and `A'` be two compensators of the same process `N`: both are predictable (`A t` is
`ℱ_{t-}`-measurable), stopped at `X`, of finite variation on compact intervals and normalized by
`A(-∞) = 0`, and both `N - A`, `N - A'` are martingales. Then `A` and `A'` are indistinguishable. -/
theorem ae_forall_eq_of_isCompensator {ℱ : Filtration ℝ m0} {N A A' : ℝ → Ω → ℝ}
    (hX : ∀ s, MeasurableSet[ℱ s] {ω | s < X ω})
    (hpast : ∀ s (B : Set Ω), MeasurableSet[ℱ s] B →
      B ∩ {ω | s < X ω} = ∅ ∨ {ω | s < X ω} ⊆ B)
    (hA : Martingale (fun t => N t - A t) ℱ P) (hA' : Martingale (fun t => N t - A' t) ℱ P)
    (hApred : ∀ t, Measurable[⨆ s < t, ℱ s] (A t))
    (hA'pred : ∀ t, Measurable[⨆ s < t, ℱ s] (A' t))
    (hAstop : ∀ t ω, A t ω = A (min t (X ω)) ω) (hA'stop : ∀ t ω, A' t ω = A' (min t (X ω)) ω)
    (hAfv : ∀ ω, LocallyBoundedVariationOn (fun t => A t ω) univ)
    (hA'fv : ∀ ω, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hAlim : ∀ ω, Tendsto (fun t => A t ω) atBot (𝓝 0))
    (hA'lim : ∀ ω, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω := by
  classical
  set D : ℝ → Ω → ℝ := fun t ω => A t ω - A' t ω with hD_def
  have hD : Martingale D ℱ P := by
    have : D = (fun t => N t - A' t) - fun t => N t - A t := by
      funext t ω; simp only [hD_def, Pi.sub_apply]; ring
    rw [this]; exact hA'.sub hA
  have hXm : Measurable X := measurable_of_Ioi fun s => ℱ.le s _ (hX s)
  -- `D t` is constant on `{t ≤ X}`.
  set d : ℝ → ℝ := fun t => if h : ∃ ω, t ≤ X ω then D t h.choose else 0 with hd_def
  have hd : ∀ t ω, t ≤ X ω → D t ω = d t := fun t ω h => by
    have hex : ∃ ω, t ≤ X ω := ⟨ω, h⟩
    simp only [hd_def, dite_eq_left hex]
    exact eq_of_strictPast hpast ((hApred t).sub (hA'pred t)) h hex.choose_spec
  have hrep : ∀ t ω, D t ω = d (min t (X ω)) := fun t ω => by
    simp only [hD_def]; rw [hAstop, hA'stop]
    exact hd _ ω (min_le_right _ _)
  -- The martingale identity on `{X > s}` gives the renewal-type inequality.
  have hineq : ∀ s t B, s < t → (∀ w ∈ Ioo s t, |d w| ≤ B) →
      |d t| * P.real {ω | t ≤ X ω} ≤
        |d s| * P.real {ω | s < X ω} + B * P.real {ω | s < X ω ∧ X ω < t} := by
    intro s t B hst hB
    have hms : MeasurableSet {ω | s < X ω} := measurableSet_lt measurable_const hXm
    have hmt : MeasurableSet {ω | t ≤ X ω} := measurableSet_le measurable_const hXm
    have hmst : MeasurableSet {ω | s < X ω ∧ X ω < t} :=
      hms.inter (measurableSet_lt hXm measurable_const)
    have hmart := hD.setIntegral_eq hst.le (hX s)
    have hL : ∫ ω in {ω | s < X ω}, D s ω ∂P = P.real {ω | s < X ω} * d s := by
      rw [setIntegral_congr_fun hms fun ω (hω : s < X ω) => hd s ω hω.le, setIntegral_const,
        smul_eq_mul]
    have hsplit : {ω | s < X ω} = {ω | s < X ω ∧ X ω < t} ∪ {ω | t ≤ X ω} := by
      ext ω; simp only [mem_ofPred_eq, mem_union]
      constructor
      · intro h; by_cases h' : X ω < t
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (not_lt.1 h')
      · rintro (h | h)
        · exact h.1
        · exact hst.trans_le h
    have hdisj : Disjoint {ω | s < X ω ∧ X ω < t} {ω | t ≤ X ω} :=
      disjoint_left.2 fun ω h1 h2 => absurd h1.2 (not_lt.2 h2)
    have hR : ∫ ω in {ω | s < X ω}, D t ω ∂P =
        ∫ ω in {ω | s < X ω ∧ X ω < t}, D t ω ∂P + P.real {ω | t ≤ X ω} * d t := by
      rw [hsplit, setIntegral_union hdisj hmt (hD.integrable t).integrableOn
        (hD.integrable t).integrableOn,
        setIntegral_congr_fun hmt fun ω (hω : t ≤ X ω) => hd t ω hω, setIntegral_const,
        smul_eq_mul]
    have hI : ‖∫ ω in {ω | s < X ω ∧ X ω < t}, D t ω ∂P‖ ≤
        B * P.real {ω | s < X ω ∧ X ω < t} :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun ω hω => by
        rw [Real.norm_eq_abs, hrep, min_eq_right hω.2.le]
        exact hB _ ⟨hω.1, hω.2⟩
    rw [Real.norm_eq_abs] at hI
    have h1 : |d t| * P.real {ω | t ≤ X ω} = |P.real {ω | t ≤ X ω} * d t| := by
      rw [abs_mul, abs_of_nonneg measureReal_nonneg, mul_comm]
    have h2 : |d s| * P.real {ω | s < X ω} = |P.real {ω | s < X ω} * d s| := by
      rw [abs_mul, abs_of_nonneg measureReal_nonneg, mul_comm]
    have hkey : P.real {ω | t ≤ X ω} * d t =
        P.real {ω | s < X ω} * d s - ∫ ω in {ω | s < X ω ∧ X ω < t}, D t ω ∂P := by
      linarith
    rw [h1, h2, hkey]
    exact (abs_sub _ _).trans (by linarith)
  -- Almost every exit time `u = X ω` has `P(X ≥ u) > 0`; there `d = 0` on `(-∞, u]`.
  have hae : ∀ᵐ ω ∂P, (P.map X) (Ici (X ω)) ≠ 0 :=
    ae_of_ae_map hXm.aemeasurable (ae_measure_Ici_ne_zero (P.map X))
  filter_upwards [hae] with ω hω
  rw [Measure.map_apply hXm measurableSet_Ici] at hω
  have hu : 0 < P.real {ω' | X ω ≤ X ω'} := ENNReal.toReal_pos hω (measure_ne_top _ _)
  obtain ⟨M₁, hM₁⟩ := exists_bound_Iic (hAfv ω) (hAlim ω) (X ω)
  obtain ⟨M₂, hM₂⟩ := exists_bound_Iic (hA'fv ω) (hA'lim ω) (X ω)
  have hbdd : ∀ w ≤ X ω, |d w| ≤ M₁ + M₂ := fun w hw => by
    rw [← hd w ω hw]
    exact (abs_sub _ _).trans (add_le_add (hM₁ w hw) (hM₂ w hw))
  have hlim : Tendsto d atBot (𝓝 0) := by
    have h := (hAlim ω).sub (hA'lim ω)
    rw [sub_zero] at h
    exact h.congr' ((eventually_le_atBot (X ω)).mono fun w hw => hd w ω hw)
  have hzero := eq_zero_of_ineq hXm hineq hlim hu hbdd
  intro t
  have := hrep t ω
  rw [hzero _ (min_le_right _ _)] at this
  exact sub_eq_zero.1 this

/-! ### The censoring model: uniqueness for the history filtration -/

section History

variable {T C : Ω → ℝ} (hT : Measurable T) (hC : Measurable C)

include hT hC in
/-- **Compensator uniqueness in the censoring model.** For the history filtration
`ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)` of one subject, two predictable, stopped-at-exit, finite-variation
compensators `A`, `A'` of the counting process `N` (normalized by `A(-∞) = 0`, with `N - A` and
`N - A'` martingales) are indistinguishable. -/
theorem ae_forall_eq_of_isCompensator_history {A A' : ℝ → Ω → ℝ}
    (hA : Martingale (fun t => countingProcess T C t - A t) (historyFiltration hT hC) P)
    (hA' : Martingale (fun t => countingProcess T C t - A' t) (historyFiltration hT hC) P)
    (hApred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A t))
    (hA'pred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A' t))
    (hAstop : ∀ t ω, A t ω = A (min t (obsTime T C ω)) ω)
    (hA'stop : ∀ t ω, A' t ω = A' (min t (obsTime T C ω)) ω)
    (hAfv : ∀ ω, LocallyBoundedVariationOn (fun t => A t ω) univ)
    (hA'fv : ∀ ω, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hAlim : ∀ ω, Tendsto (fun t => A t ω) atBot (𝓝 0))
    (hA'lim : ∀ ω, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = A' t ω :=
  ae_forall_eq_of_isCompensator (X := obsTime T C)
    (fun s => by
      have h := (measurableSet_obsTime_le_history hT hC (le_refl s)).compl
      simpa only [compl_ofPred, not_le] using h)
    (fun _ _ hB => history_inter_or_subset hT hC hB) hA hA' hApred hA'pred hAstop hA'stop
    hAfv hA'fv hAlim hA'lim

/-- The compensator `A(t) = Λ((-∞, t ∧ X])` is stopped at the exit time `X`. -/
theorem compensator_min_obsTime (Λ : Measure ℝ) (t : ℝ) (ω : Ω) :
    compensator T C Λ t ω = compensator T C Λ (min t (obsTime T C ω)) ω := by
  rw [compensator_eq, compensator_eq, min_assoc, min_self]

/-- If the hazard measure is finite on half-lines, every compensator path is monotone. -/
theorem monotone_compensator {Λ : Measure ℝ} (hΛ : ∀ s, Λ (Iic s) ≠ ∞) (ω : Ω) :
    Monotone fun t => compensator T C Λ t ω := fun a b hab => by
  simp only [compensator_eq]
  exact ENNReal.toReal_mono (hΛ _) (measure_mono (Iic_subset_Iic.2 (min_le_min_right _ hab)))

/-- If the hazard measure is finite on half-lines, every compensator path tends to `0` at `-∞`. -/
theorem tendsto_compensator_atBot {Λ : Measure ℝ} (hΛ : ∀ s, Λ (Iic s) ≠ ∞) (ω : Ω) :
    Tendsto (fun t => compensator T C Λ t ω) atBot (𝓝 0) := by
  have h := tendsto_measure_iInter_atBot (μ := Λ) (s := fun t : ℝ => Iic t)
    (fun _ => measurableSet_Iic.nullMeasurableSet) (fun _ _ h => Iic_subset_Iic.2 h) ⟨0, hΛ 0⟩
  have hI : (⋂ t : ℝ, Iic t) = ∅ :=
    eq_empty_of_forall_notMem fun x hx => by
      have := mem_iInter.1 hx (x - 1)
      simp only [mem_Iic] at this
      linarith
  rw [hI, measure_empty] at h
  have h' : Tendsto (fun t => (Λ (Iic t)).toReal) atBot (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  refine h'.congr' ((eventually_le_atBot (obsTime T C ω)).mono fun t ht => ?_)
  simp only [compensator_eq, min_eq_left ht]

/-- The hazard measure of a finite law `F` is finite on `(-∞, s]` whenever `F[s, ∞) > 0`:
there `dΛ = dF / F[x, ∞) ≤ dF / F[s, ∞)`. -/
theorem hazardMeasure_Iic_ne_top {F : Measure ℝ} [IsFiniteMeasure F] {s : ℝ}
    (hs : F (Ici s) ≠ 0) : hazardMeasure F (Iic s) ≠ ∞ := by
  rw [hazardMeasure, withDensity_apply _ measurableSet_Iic]
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in Iic s, (F (Ici s))⁻¹ ∂F) ?_ ?_
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hs) (measure_ne_top _ _)
  · refine setLIntegral_mono measurable_const fun x (hx : x ≤ s) => ?_
    exact ENNReal.inv_le_inv.2 (measure_mono (Ici_subset_Ici.2 hx))

include hT hC in
/-- **The model compensator is the unique one.** Under independent censoring, with the hazard
measure `Λ` of the law of `T` finite on half-lines, every predictable, stopped-at-exit,
finite-variation compensator `A'` of `N` with `A'(-∞) = 0` is indistinguishable from
`A(t) = Λ((-∞, t ∧ X])`. -/
theorem ae_forall_eq_compensator [IsProbabilityMeasure P] (hind : IndepFun T C P)
    (hΛ : ∀ s, hazardMeasure (P.map T) (Iic s) ≠ ∞) {A' : ℝ → Ω → ℝ}
    (hA' : Martingale (fun t => countingProcess T C t - A' t) (historyFiltration hT hC) P)
    (hA'pred : ∀ t, Measurable[⨆ s < t, historyFiltration hT hC s] (A' t))
    (hA'stop : ∀ t ω, A' t ω = A' (min t (obsTime T C ω)) ω)
    (hA'fv : ∀ ω, LocallyBoundedVariationOn (fun t => A' t ω) univ)
    (hA'lim : ∀ ω, Tendsto (fun t => A' t ω) atBot (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ t, A' t ω = compensator T C (hazardMeasure (P.map T)) t ω := by
  have h := ae_forall_eq_of_isCompensator_history hT hC
    (martingale_compensatedProcess hT hC hind) hA'
    (measurable_compensator_strictPast hT hC _) hA'pred (compensator_min_obsTime _) hA'stop
    (fun ω => ((monotone_compensator hΛ ω).monotoneOn univ).locallyBoundedVariationOn) hA'fv
    (tendsto_compensator_atBot hΛ) hA'lim
  filter_upwards [h] with ω hω t
  exact (hω t).symm

end History

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
