/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic
public import MathlibExt.Probability.Statistics.Sequential.Ville
public import MathlibExt.Probability.BernoulliSumPmf
public import MathlibExt.Probability.Statistics.ConfidenceSet

open MeasureTheory Filter
open scoped ProbabilityTheory
open scoped Topology

universe u

/-!
# Anytime-valid confidence sequences by e-process inversion

For each null value `t` with null law `P t`, let `E t n` be a nonnegative test
supermartingale with expected initial value at most 1. Ville's maximal inequality bounds
the chance each process ever reaches `1 / α` by `α`; inverting the family of null tests
gives confidence sets trapping the true parameter at all times simultaneously with
probability at least `1 - α`.

A simultaneous-in-time confidence sequence traps the parameter at any almost-surely
finite data-chosen stopping time: on the finite-time event the stopped index is defined,
and the stopped event contains the simultaneous section.

## Main statements

* `MathlibExt.Probability.Statistics.confSeqOfEProcess`
* `MathlibExt.Probability.Statistics.anytime_coverage_of_eProcess`
* `MathlibExt.Probability.Statistics.stopped_confSeq_coverage`
* `MathlibExt.Probability.Statistics.bernoulliLik`
* `MathlibExt.Probability.Statistics.bernoulliNullLR`
* `MathlibExt.Probability.Statistics.bernoulli_null_lr_eProcess`
* `MathlibExt.Probability.Statistics.bernoulli_anytime_coverage`
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics

/-- Confidence sequence by e-process inversion: keep the parameter values whose null
test supermartingale stays below `1 / α` at time `n`. -/
noncomputable def confSeqOfEProcess {Θ X : Type*} (E : Θ → ℕ → X → ℝ) (α : ℝ) (n : ℕ)
    (x : X) : Set Θ :=
  {t : Θ | E t n x < 1 / α}

/-- **Anytime-valid coverage by e-process inversion.** Each null `t` carries a probability
law, a nonnegative test supermartingale with initial mean at most 1 (hypotheses `hsup`,
`hnonneg`, `hE0`). By Ville's maximal
inequality applied to each null process, the inverted sets trap `t` at all times
simultaneously with probability at least `1 - α`. -/
theorem anytime_coverage_of_eProcess
    {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (μ θ)]
    {𝒢 : Θ → Filtration ℕ m0} {E : Θ → ℕ → X → ℝ} {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hsup : ∀ t, Supermartingale (E t) (𝒢 t) (μ t))
    (hnonneg : ∀ t, 0 ≤ E t)
    (hE0 : ∀ t, ∫ x, E t 0 x ∂(μ t) ≤ 1) :
    ∀ t, (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≥ 1 - α := by
  intro t
  have ha : (0 : ℝ) < 1 / α := one_div_pos.mpr hα.1
  have hV := Supermartingale.ville_maximal_ineq (hsup t) (hnonneg t) ha
  have hEmeas : ∀ n, Measurable (E t n) := fun n =>
    Measurable.mono (((hsup t).1 n).measurable) ((𝒢 t).le n) le_rfl
  have hmeas : MeasurableSet {x | ∃ n, (1 : ℝ) / α ≤ E t n x} := by
    rw [show {x | ∃ n, (1 : ℝ) / α ≤ E t n x}
        = ⋃ n, {x | (1 : ℝ) / α ≤ E t n x} from by ext x; simp]
    exact MeasurableSet.iUnion fun n => measurableSet_le measurable_const (hEmeas n)
  have hcross : (μ t).real {x | ∃ n, (1 : ℝ) / α ≤ E t n x} ≤ α := by
    have h1 : (1 / α) * (μ t).real {x | ∃ n, (1 : ℝ) / α ≤ E t n x} ≤ 1 :=
      le_trans hV (hE0 t)
    have h2 : (1 / α) * (μ t).real {x | ∃ n, (1 : ℝ) / α ≤ E t n x} ≤ (1 / α) * α := by
      rw [one_div_mul_cancel (ne_of_gt hα.1)]
      exact h1
    exact le_of_mul_le_mul_left h2 ha
  have hcompl : {x | ∀ n, t ∈ confSeqOfEProcess E α n x}
      = {x | ∃ n, (1 : ℝ) / α ≤ E t n x}ᶜ := by
    ext x
    simp [confSeqOfEProcess, not_le]
  rw [hcompl, probReal_compl_eq_one_sub hmeas]
  linarith

/-- **Stopped coverage at a finite-a.s. time.** The simultaneous guarantee `hcover`
implies coverage at any almost-surely finite stopping time: the stopped event contains
the simultaneous section on the finite-time event, whose complement is null. The
measurability of the simultaneous, finite-time and stopped sections is established from
the per-time measurability of the processes and the stopping-time property, so the
conclusion is a genuine probability statement rather than an outer-measure inequality. -/
theorem stopped_confSeq_coverage
    {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X} [∀ θ, IsProbabilityMeasure (μ θ)]
    {E : Θ → ℕ → X → ℝ} {α : ℝ}
    (hEmeas : ∀ t n, Measurable (E t n))
    (hcover : ∀ t, (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≥ 1 - α)
    {𝒢 : Θ → Filtration ℕ m0}
    {τ : Θ → X → WithTop ℕ}
    (hstop : ∀ t, IsStoppingTime (𝒢 t) (τ t))
    (hfin : ∀ t, ∀ᵐ x ∂(μ t), τ t x < ⊤) :
    ∀ t, (μ t).real {x | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} ≥ 1 - α := by
  intro t
  -- The simultaneous section is measurable.
  have hsec : ∀ n, MeasurableSet {x | t ∈ confSeqOfEProcess E α n x} :=
    fun n => measurableSet_lt (hEmeas t n) measurable_const
  have hAmeas : MeasurableSet {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} := by
    have hAeq : {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x}
        = ⋂ n, {x | t ∈ confSeqOfEProcess E α n x} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hAeq]
    exact MeasurableSet.iInter hsec
  -- The finite-time event is measurable, from the stopping-time property.
  have hFinmeas : MeasurableSet {x : X | τ t x < ⊤} := by
    have hFin : {x : X | τ t x < ⊤} = ⋃ n : ℕ, {x | τ t x ≤ (↑n : WithTop ℕ)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hx)
        exact ⟨n, le_of_eq hn.symm⟩
      · rintro ⟨n, hn⟩
        exact lt_of_le_of_lt hn (WithTop.coe_lt_top n)
    rw [hFin]
    exact MeasurableSet.iUnion fun n => ((𝒢 t).le n) _ (hstop t n)
  -- The stopped section is measurable, so the conclusion is a genuine probability statement.
  have hBmeas :
      MeasurableSet {x : X | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} := by
    have hPmeas : ∀ n : ℕ, MeasurableSet {x : X | τ t x = (↑n : WithTop ℕ)} := by
      intro n
      have hPeq : {x : X | τ t x = (↑n : WithTop ℕ)}
          = {x | τ t x ≤ (↑n : WithTop ℕ)} ∩ {x | τ t x < (↑n : WithTop ℕ)}ᶜ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
        exact eq_iff_le_not_lt
      have hlt : MeasurableSet {x : X | τ t x < (↑n : WithTop ℕ)} := by
        have hltEq : {x : X | τ t x < (↑n : WithTop ℕ)}
            = ⋃ (m : Fin n), {x | τ t x ≤ ((↑(m : ℕ) : WithTop ℕ))} := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
          constructor
          · intro hx
            have hne : τ t x ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp (lt_of_lt_of_le hx le_top)
            obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
            have hmlt : m < n := WithTop.coe_lt_coe.mp (by rwa [hm])
            exact ⟨⟨m, hmlt⟩, le_of_eq hm.symm⟩
          · rintro ⟨⟨m, hmn⟩, hmle⟩
            exact lt_of_le_of_lt hmle (WithTop.coe_lt_coe.mpr hmn)
        rw [hltEq]
        exact MeasurableSet.iUnion fun m => ((𝒢 t).le (m : ℕ)) _ (hstop t (m : ℕ))
      rw [hPeq]
      exact (((𝒢 t).le n) _ (hstop t n)).inter hlt.compl
    have hBeq : {x : X | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x}
        = ⋃ n : ℕ, ({x | τ t x = (↑n : WithTop ℕ)} ∩ {x | t ∈ confSeqOfEProcess E α n x}) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨hxF, hxC⟩
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hxF)
        have huntop : (τ t x).untopD 0 = n := by rw [← hn]; exact WithTop.untopD_coe _ _
        refine ⟨n, hn.symm, ?_⟩
        rw [huntop] at hxC
        exact hxC
      · rintro ⟨n, hn, hCn⟩
        have huntop : (τ t x).untopD 0 = n := by rw [hn]; exact WithTop.untopD_coe _ _
        refine ⟨?_, ?_⟩
        · rw [hn]
          exact WithTop.coe_lt_top n
        · rwa [huntop]
    rw [hBeq]
    exact MeasurableSet.iUnion fun n => (hPmeas n).inter (hsec n)
  -- The finite-time complement is null.
  have hnull : μ t {x : X | τ t x < ⊤}ᶜ = 0 := ae_iff.mp (hfin t)
  -- The simultaneous section keeps full measure on the finite-time event.
  have hAeq : μ t {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x}
      = μ t ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}) := by
    have hsubU : {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x}
        ⊆ ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
          ∪ ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}ᶜ) := by
      intro x hx
      exact Or.elim (Classical.em (τ t x < ⊤)) (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
    have hdisj : Disjoint
        ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
        ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}ᶜ) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hF⟩ hcon
      exact absurd hF hcon.2
    have hle1 : μ t {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x}
        ≤ μ t ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}) := by
      have hunion : μ t (({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
          ∪ ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}ᶜ))
          = μ t ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
            + μ t ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}ᶜ) :=
        measure_union hdisj (hAmeas.inter hFinmeas.compl)
      have hzero : μ t ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}ᶜ) = 0 :=
        le_antisymm (le_trans (measure_mono Set.inter_subset_right) hnull.le) zero_le
      have h1 := le_trans (measure_mono hsubU) (le_of_eq hunion)
      rwa [hzero, add_zero] at h1
    exact le_antisymm hle1 (measure_mono Set.inter_subset_left)
  -- Restrict the simultaneous guarantee to the finite-time event.
  have hsubAB : ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
      ⊆ {x | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} := by
    intro x hx
    obtain ⟨hxA, hxF⟩ := hx
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hxF)
    have huntop : (τ t x).untopD 0 = n := by rw [← hn]; exact WithTop.untopD_coe _ _
    refine ⟨hxF, ?_⟩
    rw [huntop]
    exact hxA n
  have hmono2 : (μ t).real ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
      ≤ (μ t).real {x | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} :=
    measureReal_mono hsubAB (measure_ne_top _ _)
  have hAeqR : (μ t).real ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤})
      = (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} := by
    have h := congrArg ENNReal.toReal hAeq.symm
    simpa only [measureReal_def] using h
  calc (μ t).real {x : X | τ t x < ⊤ ∧ t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x}
      ≥ (μ t).real ({x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ∩ {x | τ t x < ⊤}) := hmono2
    _ = (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} := hAeqR
    _ ≥ 1 - α := hcover t

/-- Bernoulli likelihood: `p` at `x = 1`, `1 - p` at `x = 0`, and `0` otherwise. This is
the likelihood of Mathlib's Nat-valued Bernoulli law, which assigns no mass outside
`{0, 1}`; treating every non-`1` observation as a failure would be wrong off the support. -/
noncomputable def bernoulliLik (p : ℝ) (x : ℕ) : ℝ :=
  if x = 1 then p else if x = 0 then 1 - p else 0

/-- A Bernoulli likelihood value is nonnegative. -/
private theorem bernoulliLik_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) :
    0 ≤ bernoulliLik p x := by
  unfold bernoulliLik
  by_cases h1 : x = 1
  · simp [h1, hp]
  · by_cases h0 : x = 0
    · simp [h0, sub_nonneg.mpr hp1]
    · simp [h1, h0]

/-- Null likelihood-ratio process for testing success probability `q` against the fixed
reference alternative `p0`: product of per-observation alternative-over-null ratios over
observations `X_0..X_n` (inclusive product over `range (n + 1)`, matching the inclusive
`Filtration.natural`; an exclusive product over `range n` would be one step ahead of the
filtration and is unsound here). -/
noncomputable def bernoulliNullLR {Ω : Type u} (X : ℕ → Ω → ℕ) (p0 q : ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range (n + 1), bernoulliLik p0 (X i ω) / bernoulliLik q (X i ω)

/-- Finite-horizon Bernoulli null-LR products are integrable: each factor takes two
finite values (hence is bounded and measurable), so every finite product is bounded and
measurable under the interior probability law. -/
private theorem integrable_bernoulliNullLR_prod
    {Ω : Type u} {m0 : MeasurableSpace Ω} {X : ℕ → Ω → ℕ} {p0 : ℝ}
    {μ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1} → Measure Ω} [∀ θ, IsProbabilityMeasure (μ θ)]
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (θ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1}) (n : ℕ) :
    Integrable (fun ω => bernoulliNullLR X p0 θ.val n ω) (μ θ) := by
  have hfactor_meas : ∀ i, Measurable
      (fun ω => bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω)) := by
    intro i
    have h1 : Measurable (fun x : ℕ => bernoulliLik p0 x / bernoulliLik θ.val x) :=
      Measurable.of_discrete
    exact h1.comp (hXstrong i).measurable
  set B : ℝ := ‖p0 / θ.val‖ + ‖(1 - p0) / (1 - θ.val)‖ + 1 with hB
  have hfactor_bdd : ∀ i, ∀ ω, ‖bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω)‖ ≤ B := by
    intro i ω
    by_cases h : X i ω = 1
    · simp only [h, bernoulliLik]
      rw [hB]
      exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_right zero_le_one)
    · by_cases h0 : X i ω = 0
      · simp only [h, h0, bernoulliLik]
        rw [hB]
        exact le_trans (le_add_of_nonneg_left (norm_nonneg _))
          (le_add_of_nonneg_right zero_le_one)
      · have hzero : bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω) = 0 := by
          simp [bernoulliLik, h, h0]
        rw [hzero, norm_zero, hB]
        positivity
  have hsm : StronglyMeasurable (fun ω => bernoulliNullLR X p0 θ.val n ω) := by
    unfold bernoulliNullLR
    apply Finset.stronglyMeasurable_fun_prod
    intro i hi
    have hmeas : Measurable (fun x : ℕ => bernoulliLik p0 x / bernoulliLik θ.val x) :=
      Measurable.of_discrete
    exact (hmeas.comp (hXstrong i).measurable).stronglyMeasurable
  have hBnn : (0:ℝ) ≤ B := by
    simp only [hB]
    positivity
  have hprod_le : ∀ ω, ∀ s : Finset ℕ,
      ∏ i ∈ s, ‖bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω)‖ ≤ B ^ s.card := by
    intro ω s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
      calc ‖bernoulliLik p0 (X a ω) / bernoulliLik θ.val (X a ω)‖
            * ∏ i ∈ s, ‖bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω)‖
          ≤ B * B ^ s.card := by
            apply mul_le_mul (hfactor_bdd a ω) ih
              (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hBnn
        _ = B ^ (s.card + 1) := by rw [pow_succ, mul_comm]
  apply Integrable.of_bound hsm.aestronglyMeasurable (B ^ (n + 1))
  filter_upwards with ω
  unfold bernoulliNullLR
  calc ‖∏ i ∈ Finset.range (n + 1), (bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω))‖
      ≤ ∏ i ∈ Finset.range (n + 1), ‖bernoulliLik p0 (X i ω) / bernoulliLik θ.val (X i ω)‖ :=
        Finset.norm_prod_le _ _
    _ ≤ B ^ (n + 1) := by
        have h := hprod_le ω (Finset.range (n + 1))
        rwa [Finset.card_range] at h

/-- **Bernoulli null LR family is a mean-1 nonnegative e-process under each null.**
For fixed reference `p0 ∈ (0,1)`, every interior null `θ` with iid Bernoulli(`θ.val`)
data carries a `Filtration.natural`-supermartingale that is pointwise nonnegative with
initial mean exactly 1. The family is parameterized by the interior subtype, so no laws
outside `(0,1)` are required. The filtration is the natural filtration of the observations
(a general adapted filtration does NOT suffice: with the constant full filtration the
conditional-expectation step fails). -/
theorem bernoulli_null_lr_eProcess
    {Ω : Type u} {m0 : MeasurableSpace Ω} {X : ℕ → Ω → ℕ} {p0 : ℝ}
    (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1)
    {μ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1} → Measure Ω} [∀ θ, IsProbabilityMeasure (μ θ)]
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX_indep : ∀ θ, ProbabilityTheory.iIndepFun X (μ θ))
    (hXbern : ∀ θ, ∀ i, ProbabilityTheory.IsBernoulliRV (X i) (μ θ) θ.val) :
    ∀ θ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1},
      Supermartingale (bernoulliNullLR X p0 θ.val) (Filtration.natural X hXstrong) (μ θ) ∧
        0 ≤ bernoulliNullLR X p0 θ.val ∧
        ∫ ω, bernoulliNullLR X p0 θ.val 0 ω ∂(μ θ) = 1 := by
  intro θ
  have hq : θ.val ∈ Set.Ioo (0 : ℝ) 1 := θ.property
  have hX01 : ∀ i, μ θ {ω | X i ω = 0 ∨ X i ω = 1} = 1 := by
    intro i
    have hset : {ω | X i ω = 0 ∨ X i ω = 1} =
        (X i ⁻¹' {0}) ∪ (X i ⁻¹' {1}) := by
      ext ω
      simp [Set.mem_preimage]
    have hdisj : Disjoint (X i ⁻¹' {0}) (X i ⁻¹' {1}) :=
      Set.disjoint_left.mpr (fun ω h0 h1 => by simp [Set.mem_preimage] at h0 h1; omega)
    have hmeas1 : MeasurableSet (X i ⁻¹' {1}) :=
      (hXstrong i).measurable (measurableSet_singleton 1)
    rw [hset, measure_union hdisj hmeas1, (hXbern θ i).measure_zero,
      (hXbern θ i).measure_one,
      ← ENNReal.ofReal_add (sub_nonneg.mpr hq.2.le) hq.1.le, sub_add_cancel]
    exact ENNReal.ofReal_one
  have hX1 : ∀ i, ((μ θ {ω | X i ω = 1}).toReal) = θ.val := by
    intro i
    have h := (hXbern θ i).measure_one
    have hset : {ω | X i ω = 1} = X i ⁻¹' {1} := by
      ext ω
      simp
    rw [hset, h, ENNReal.toReal_ofReal hq.1.le]
  have hae : ∀ i, ∀ᵐ ω ∂(μ θ), X i ω = 0 ∨ X i ω = 1 := by
    intro i
    rw [ae_iff]
    have hmeas : MeasurableSet {ω | X i ω = 0 ∨ X i ω = 1} := by
      have h0 : MeasurableSet {ω | X i ω = 0} :=
        (hXstrong i).measurable (measurableSet_singleton 0)
      have h1 : MeasurableSet {ω | X i ω = 1} :=
        (hXstrong i).measurable (measurableSet_singleton 1)
      exact h0.union h1
    have hcompl : μ θ {ω | X i ω = 0 ∨ X i ω = 1}ᶜ = 0 := by
      rw [measure_compl hmeas (measure_ne_top _ _), hX01 i, measure_univ]
      simp
    have hset : {ω | ¬ (X i ω = 0 ∨ X i ω = 1)} =
        {ω | X i ω = 0 ∨ X i ω = 1}ᶜ := by
      ext ω
      simp
    rw [hset]
    exact hcompl
  have hnonneg : 0 ≤ bernoulliNullLR X p0 θ.val := by
    intro n ω
    unfold bernoulliNullLR
    apply Finset.prod_nonneg
    intro i hi
    exact div_nonneg (bernoulliLik_nonneg hp0.1.le hp0.2.le _)
      (bernoulliLik_nonneg hq.1.le hq.2.le _)
  have hadp : StronglyAdapted (Filtration.natural X hXstrong) (bernoulliNullLR X p0 θ.val) := by
    intro n
    unfold bernoulliNullLR
    apply Finset.stronglyMeasurable_fun_prod
    intro i hi
    simp only [Finset.mem_range] at hi
    have hij : i ≤ n := Nat.lt_succ_iff.mp hi
    have hXi : StronglyMeasurable[(Filtration.natural X hXstrong) n] (X i) := by
      have h := (Filtration.stronglyAdapted_natural hXstrong) i
      exact h.mono ((Filtration.natural X hXstrong).mono hij)
    have hmeas : Measurable (fun x : ℕ => bernoulliLik p0 x / bernoulliLik θ.val x) :=
      Measurable.of_discrete
    exact (hmeas.comp hXi.measurable).stronglyMeasurable
  have hint : ∀ n, Integrable (bernoulliNullLR X p0 θ.val n) (μ θ) := by
    intro n
    have h : Integrable (fun ω => bernoulliNullLR X p0 θ.val n ω) (μ θ) :=
      integrable_bernoulliNullLR_prod hXstrong θ n
    simpa using h
  have hmart_eq : ∀ n, (bernoulliNullLR X p0 θ.val n) =ᵐ[μ θ]
      (μ θ)[bernoulliNullLR X p0 θ.val (n+1) | (Filtration.natural X hXstrong) n] := by
    intro n
    set F : Filtration ℕ m0 := Filtration.natural X hXstrong with hF
    set M : ℕ → Ω → ℝ := bernoulliNullLR X p0 θ.val with hM
    set Z : Ω → ℝ := fun ω => bernoulliLik p0 (X (n+1) ω) / bernoulliLik θ.val (X (n+1) ω) with hZ
    have hsplit : ∀ ω, M (n+1) ω = M n ω * Z ω := by
      intro ω
      simp only [hM, hZ, bernoulliNullLR]
      rw [Finset.prod_range_succ]
    have hMmeas : StronglyMeasurable[F n] (M n) := by
      have := hadp n
      simpa [hM, hF] using this
    have hmeasX : Measurable (X (n+1)) := (hXstrong (n+1)).measurable
    have hs_meas : MeasurableSet {ω : Ω | X (n+1) ω = 1} := hmeasX (measurableSet_singleton 1)
    set a : ℝ := p0 / θ.val with ha
    set b : ℝ := (1 - p0) / (1 - θ.val) with hb
    have hZ_eq : Z =ᵐ[μ θ] fun ω => {ω | X (n+1) ω = 1}.indicator (fun _ => a) ω
        + {ω | X (n+1) ω = 1}ᶜ.indicator (fun _ => b) ω := by
      filter_upwards [hae (n + 1)] with ω hω
      simp only [hZ, Set.indicator]
      rcases hω with h | h
      · simp [h, bernoulliLik, hb]
      · simp [h, bernoulliLik, ha]
    have h1 : Integrable ({ω | X (n+1) ω = 1}.indicator (fun _ : Ω => a)) (μ θ) :=
      (integrableOn_const (C := a)).integrable_indicator hs_meas
    have h2 : Integrable ({ω | X (n+1) ω = 1}ᶜ.indicator (fun _ : Ω => b)) (μ θ) :=
      (integrableOn_const (C := b)).integrable_indicator hs_meas.compl
    have hZint : Integrable Z (μ θ) := (h1.add h2).congr hZ_eq.symm
    have hZmean : ∫ ω, Z ω ∂(μ θ) = 1 := by
      rw [integral_congr_ae hZ_eq, integral_add h1 h2, integral_indicator_const a hs_meas,
        integral_indicator_const b hs_meas.compl]
      simp only [smul_eq_mul]
      have hq_real : (μ θ).real {ω | X (n+1) ω = 1} = θ.val := by
        have := hX1 (n+1)
        simp [Measure.real, this]
      have hcompl : (μ θ).real {ω | X (n+1) ω = 1}ᶜ = 1 - θ.val := by
        rw [probReal_compl_eq_one_sub hs_meas, hq_real]
      rw [hq_real, hcompl]
      simp only [ha, hb]
      have hq0 : (0:ℝ) < θ.val := hq.1
      have h1qne : (1:ℝ) - θ.val ≠ 0 := by linarith [hq.2]
      have hqne : (θ.val:ℝ) ≠ 0 := ne_of_gt hq0
      field_simp
      ring
    have hfg : Integrable (M n * Z) (μ θ) := by
      have h : Integrable (bernoulliNullLR X p0 θ.val (n + 1)) (μ θ) :=
        integrable_bernoulliNullLR_prod hXstrong θ (n + 1)
      have heq2 : (bernoulliNullLR X p0 θ.val (n+1)) =ᵐ[μ θ] (M n * Z) := by
        filter_upwards with ω
        show bernoulliNullLR X p0 θ.val (n+1) ω = (M n * Z) ω
        simp only [Pi.mul_apply, hM, hZ]
        exact hsplit ω
      have hMfold : bernoulliNullLR X p0 θ.val (n+1) = M (n+1) := by simp [hM]
      rw [hMfold] at h heq2
      exact h.congr heq2
    have hpull : (μ θ)[M n * Z | F n] =ᵐ[μ θ] M n * (μ θ)[Z | F n] :=
      condExp_mul_of_stronglyMeasurable_left (m := F n) (μ := μ θ) (f := M n) (g := Z)
        hMmeas hfg hZint
    have hindep_X : ProbabilityTheory.Indep
        (MeasurableSpace.comap (X (n+1)) inferInstance) (F n) (μ θ) := by
      have hdis : Disjoint ({n+1} : Set ℕ) {k | k ≤ n} := by
        rw [Set.disjoint_singleton_left]
        intro h
        simp only [Set.mem_ofPred_eq] at h
        omega
      have hfull : ProbabilityTheory.Indep
          (⨆ k ∈ ({n+1} : Set ℕ), MeasurableSpace.comap (X k) inferInstance)
          (⨆ k ∈ {k | k ≤ n}, MeasurableSpace.comap (X k) inferInstance) (μ θ) :=
        ProbabilityTheory.indep_iSup_of_disjoint
          (fun k => (hXstrong k).measurable.comap_le) (hX_indep θ) hdis
      rwa [iSup_singleton] at hfull
    have hZ_meas_m1 : StronglyMeasurable[MeasurableSpace.comap (X (n+1)) inferInstance] Z := by
      have hmeas : Measurable (fun x : ℕ => bernoulliLik p0 x / bernoulliLik θ.val x) :=
        Measurable.of_discrete
      have hXmeas : Measurable[MeasurableSpace.comap (X (n+1)) inferInstance] (X (n+1)) :=
        comap_measurable (X (n+1))
      have : Measurable[MeasurableSpace.comap (X (n+1)) inferInstance] Z := by
        simp only [hZ]
        exact hmeas.comp hXmeas
      exact this.stronglyMeasurable
    have hcondZ : (μ θ)[Z | F n] =ᵐ[μ θ] fun _ => ∫ ω, Z ω ∂(μ θ) := by
      have hle1 : MeasurableSpace.comap (X (n+1)) inferInstance ≤ m0 :=
        (hXstrong (n+1)).measurable.comap_le
      have hle2 : F n ≤ m0 := by
        simp only [hF]
        exact (Filtration.natural X hXstrong).le n
      have := condExp_indep_eq (m₁ := MeasurableSpace.comap (X (n+1)) inferInstance)
        (m₂ := F n) (m := m0) (μ := μ θ) (f := Z) hle1 hle2 hZ_meas_m1 hindep_X
      simpa using this
    have hcondZ1 : (μ θ)[Z | F n] =ᵐ[μ θ] fun _ => (1:ℝ) := by
      simpa [hZmean] using hcondZ
    have hMnext_cond : (μ θ)[M (n+1) | F n] =ᵐ[μ θ] (μ θ)[M n * Z | F n] := by
      apply condExp_congr_ae
      filter_upwards with ω
      show M (n+1) ω = (M n * Z) ω
      simp only [Pi.mul_apply]
      exact hsplit ω
    have hfinal : (μ θ)[M (n+1) | F n] =ᵐ[μ θ] M n := by
      calc (μ θ)[M (n+1) | F n] =ᵐ[μ θ] (μ θ)[M n * Z | F n] := hMnext_cond
        _ =ᵐ[μ θ] M n * (μ θ)[Z | F n] := hpull
        _ =ᵐ[μ θ] M n * 1 := by
              have hmul : M n * (μ θ)[Z | F n] =ᵐ[μ θ] M n * 1 := by
                filter_upwards [hcondZ1] with ω hω
                show (M n * (μ θ)[Z | F n]) ω = (M n * 1) ω
                simp only [Pi.mul_apply, Pi.one_apply, hω]
              exact hmul
        _ =ᵐ[μ θ] M n := by
              filter_upwards with ω
              show (M n * 1) ω = M n ω
              simp
    have hfinal_symm : M n =ᵐ[μ θ] (μ θ)[M (n+1) | F n] := hfinal.symm
    simpa [hM, hF] using hfinal_symm
  have hmart : Martingale (bernoulliNullLR X p0 θ.val) (Filtration.natural X hXstrong) (μ θ) :=
    martingale_nat hadp hint hmart_eq
  have hsup : Supermartingale (bernoulliNullLR X p0 θ.val) (Filtration.natural X hXstrong) (μ θ) :=
    hmart.supermartingale
  have hmean : ∫ ω, bernoulliNullLR X p0 θ.val 0 ω ∂(μ θ) = 1 := by
    have hM0_eq : (bernoulliNullLR X p0 θ.val 0)
        = fun ω => bernoulliLik p0 (X 0 ω) / bernoulliLik θ.val (X 0 ω) := by
      funext ω
      unfold bernoulliNullLR
      simp
    have hmeasX0 : Measurable (X 0) := (hXstrong 0).measurable
    have hs_meas0 : MeasurableSet {ω : Ω | X 0 ω = 1} := hmeasX0 (measurableSet_singleton 1)
    set a0 : ℝ := p0 / θ.val with ha0
    set b0 : ℝ := (1 - p0) / (1 - θ.val) with hb0
    have hZ0_eq : (fun ω => bernoulliLik p0 (X 0 ω) / bernoulliLik θ.val (X 0 ω))
        =ᵐ[μ θ] fun ω => {ω | X 0 ω = 1}.indicator (fun _ => a0) ω
          + {ω | X 0 ω = 1}ᶜ.indicator (fun _ => b0) ω := by
      filter_upwards [hae 0] with ω hω
      simp only [Set.indicator]
      rcases hω with h | h
      · simp [h, bernoulliLik, hb0]
      · simp [h, bernoulliLik, ha0]
    have h10 : Integrable ({ω | X 0 ω = 1}.indicator (fun _ : Ω => a0)) (μ θ) :=
      (integrableOn_const (C := a0)).integrable_indicator hs_meas0
    have h20 : Integrable ({ω | X 0 ω = 1}ᶜ.indicator (fun _ : Ω => b0)) (μ θ) :=
      (integrableOn_const (C := b0)).integrable_indicator hs_meas0.compl
    have hZ0mean : ∫ ω, (bernoulliLik p0 (X 0 ω) / bernoulliLik θ.val (X 0 ω)) ∂(μ θ) = 1 := by
      rw [integral_congr_ae hZ0_eq, integral_add h10 h20, integral_indicator_const a0 hs_meas0,
        integral_indicator_const b0 hs_meas0.compl]
      simp only [smul_eq_mul]
      have hq_real : (μ θ).real {ω | X 0 ω = 1} = θ.val := by
        have := hX1 0
        simp [Measure.real, this]
      have hcompl : (μ θ).real {ω | X 0 ω = 1}ᶜ = 1 - θ.val := by
        rw [probReal_compl_eq_one_sub hs_meas0, hq_real]
      rw [hq_real, hcompl]
      simp only [ha0, hb0]
      have hq0 : (0:ℝ) < θ.val := hq.1
      have h1qne : (1:ℝ) - θ.val ≠ 0 := by linarith [hq.2]
      have hqne : (θ.val:ℝ) ≠ 0 := ne_of_gt hq0
      field_simp
      ring
    calc ∫ ω, bernoulliNullLR X p0 θ.val 0 ω ∂(μ θ)
        = ∫ ω, (bernoulliLik p0 (X 0 ω) / bernoulliLik θ.val (X 0 ω)) ∂(μ θ) := by
          simp only [hM0_eq]
      _ = 1 := hZ0mean
  exact ⟨hsup, hnonneg, hmean⟩

/-- **Explicit Bernoulli anytime-valid confidence sequence, self-contained.** For fixed
reference `p0 ∈ (0,1)`, every interior null `θ` with iid Bernoulli(`θ.val`) data carries
coverage `≥ 1 - α` through the inverted family. The family e-process property is derived
internally by exact application of `bernoulli_null_lr_eProcess`, then composed through
the sibling `anytime_coverage_of_eProcess` on the interior subtype (no `hE`/`hville`
premises, no duplicated Ville/inversion machinery). The conclusion is a confidence
sequence over the interior subtype, not a claimed real-line interval. -/
theorem bernoulli_anytime_coverage
    {Ω : Type u} {m0 : MeasurableSpace Ω} {X : ℕ → Ω → ℕ} {p0 : ℝ}
    (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1)
    {μ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1} → Measure Ω} [∀ θ, IsProbabilityMeasure (μ θ)]
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX_indep : ∀ θ, ProbabilityTheory.iIndepFun X (μ θ))
    (hXbern : ∀ θ, ∀ i, ProbabilityTheory.IsBernoulliRV (X i) (μ θ) θ.val)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ θ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1},
      (μ θ).real {ω | ∀ n, θ ∈ confSeqOfEProcess
        (fun s m w => bernoulliNullLR X p0 s.val m w) α n ω} ≥ 1 - α := by
  have hE := fun θ => bernoulli_null_lr_eProcess hp0 hXstrong hX_indep hXbern θ
  exact anytime_coverage_of_eProcess hα (fun θ => (hE θ).1) (fun θ => (hE θ).2.1)
    (fun θ => le_of_eq (hE θ).2.2)
end MathlibExt.Probability.Statistics
