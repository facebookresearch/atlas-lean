/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-!
# Stopped coverage for confidence sequences

The simultaneous confidence sequence traps the parameter at any almost-surely finite
data-chosen stopping time: on the finite-time event the stopped index is defined, and
the stopped event contains the simultaneous section.

## Main statements

* `MathlibExt.Probability.Statistics.confSeqOfEProcess`
* `MathlibExt.Probability.Statistics.stopped_confSeq_coverage`
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MathlibExt.Probability.Statistics

/-- Confidence sequence by e-process inversion: keep the parameter values whose null
test supermartingale stays below `1 / α` at time `n`. -/
noncomputable def confSeqOfEProcess {Θ X : Type*} (E : Θ → ℕ → X → ℝ) (α : ℝ) (n : ℕ)
    (x : X) : Set Θ :=
  {t : Θ | E t n x < 1 / α}

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

end MathlibExt.Probability.Statistics
