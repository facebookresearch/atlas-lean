/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Sequences
public import Mathlib.Order.LiminfLimsup

/-!
# Prokhorov's theorem, sequential form on `ℝ`

A sequence of probability measures on `ℝ` is tight if and only if every
subsequence has a further subsequence converging weakly to a probability
measure.

## Source

This formalizes `v1/Atlas/TheoryOfProbability/code/TightnessCompactness.lean`
(`prokhorov_theorem`, left unproved there), for the target "Theorem
(tightness and compactness)" (Lecture 12, Compactness section) in
`v1/Atlas/TheoryOfProbability/targets.yaml`: "Every subsequential limit
of the `Fₙ` is the distribution function of a probability measure if and
only if the `Fₙ` are tight."

## Scope

In: the sequential form of Prokhorov's theorem for sequences of
probability measures on `ℝ`, proved from Mathlib's compactness form
(`isCompact_closure_of_isTightMeasureSet`,
`isTightMeasureSet_of_isCompact_closure`) plus the Portmanteau theorem.

Out: the compactness form itself (already in Mathlib), Helly's selection
theorem (Batch 6), the Portmanteau theorem (already in Mathlib), and
any statement about tightness on a general space.
-/

@[expose] public section

open MeasureTheory Filter Set Topology ENNReal

namespace MathlibExt.Probability.ProkhorovSequential

/-- The complements of the centered intervals `[-M, M]` shrink to the empty
set, and their masses under any probability measure tend to `0`. -/
private theorem tendsto_measure_compl_Icc (ν : ProbabilityMeasure ℝ) :
    Tendsto (fun M : ℕ => (ν : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ) atTop
      (𝓝 0) := by
  have hant : Antitone (fun M : ℕ => (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ) := by
    intro a b hab
    exact Set.compl_subset_compl.mpr (Set.Icc_subset_Icc
      (neg_le_neg (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab))
      (by exact_mod_cast hab))
  have hinter : ⋂ M : ℕ, (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false]
    push Not at *
    exact ⟨⌈|x|⌉₊, by
      constructor
      · exact le_trans (neg_le_neg (Nat.le_ceil |x|)) (abs_le.mp (le_refl |x|)).1
      · exact le_trans (le_abs_self x) (Nat.le_ceil |x|)⟩
  have hmeas : ∀ M : ℕ, NullMeasurableSet (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ
      (ν : Measure ℝ) :=
    fun M => isCompact_Icc.measurableSet.compl.nullMeasurableSet
  have hfin : ∃ M : ℕ, (ν : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ ≠ ∞ :=
    ⟨0, by simp⟩
  have h := tendsto_measure_iInter_atTop hmeas hant hfin
  rw [hinter, measure_empty] at h
  exact h

/-- The masses of the sets `{x | M ≤ |x|}` under any probability measure
tend to `0` as `M → ∞`. -/
private theorem tendsto_measure_abs_ge (ν : ProbabilityMeasure ℝ) :
    Tendsto (fun M : ℕ => (ν : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|}) atTop
      (𝓝 0) := by
  have hant : Antitone (fun M : ℕ => {x : ℝ | (M : ℝ) ≤ |x|}) := by
    intro a b hab x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_trans (by exact_mod_cast hab) hx
  have hinter : ⋂ M : ℕ, {x : ℝ | (M : ℝ) ≤ |x|} = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    push Not at *
    exact ⟨⌈|x|⌉₊ + 1, by
      have h1 : |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈|x|⌉₊ : ℝ) < (⌈|x|⌉₊ + 1 : ℕ) := by
        exact_mod_cast Nat.lt_succ_self _
      linarith⟩
  have hmeas : ∀ M : ℕ, NullMeasurableSet {x : ℝ | (M : ℝ) ≤ |x|}
      (ν : Measure ℝ) :=
    fun M => (isClosed_Ici.preimage continuous_abs).measurableSet.nullMeasurableSet
  have hfin : ∃ M : ℕ, (ν : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|} ≠ ∞ :=
    ⟨0, by simp⟩
  have h := tendsto_measure_iInter_atTop hmeas hant hfin
  rw [hinter, measure_empty] at h
  exact h

/-- If a sequence of extended reals is eventually strictly above `c`, then
`c` is at most its limsup. -/
private theorem le_limsup_of_ev_lt {a : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, c < a n) : c ≤ Filter.limsup a atTop := by
  refine le_limsup_of_le (by isBoundedDefault) ?_
  intro b hb
  obtain ⟨j, hj1, hj2⟩ := (hb.and h).exists
  exact hj2.le.trans hj1

/-- Diagonal state sequence for the non-tightness argument: starting from
`next 0 0`, each step moves to a larger index whose measure escapes the
interval of radius equal to the new step number. -/
private noncomputable def diagSeq (next : ℕ → ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (next 0 0, 0)
  | (k + 1) => (next (k + 1) (diagSeq next k).1, k + 1)

/-- The second coordinate of `diagSeq next j` is `j`. -/
private theorem diagSeq_snd (next : ℕ → ℕ → ℕ) (j : ℕ) : (diagSeq next j).2 = j := by
  induction j with
  | zero => rfl
  | succ k _ => rfl

/-- The first coordinate of `diagSeq next (k + 1)` is the chosen index
`next (k + 1)` applied to the previous first coordinate. -/
private theorem diagSeq_fst_succ (next : ℕ → ℕ → ℕ) (k : ℕ) :
    (diagSeq next (k + 1)).1 = next (k + 1) (diagSeq next k).1 :=
  rfl

/-- Every step of `diagSeq` satisfies the escape property: the measure at
the chosen index gives mass more than `ε` to the complement of
`[-j, j]`. -/
private theorem diagSeq_property {ε : ℝ≥0∞} {μ : ℕ → ProbabilityMeasure ℝ}
    {next : ℕ → ℕ → ℕ}
    (hnext : ∀ k B, B < next k B ∧
      ε < (μ (next k B) : Measure ℝ) (Set.Icc (-(k : ℝ)) (k : ℝ))ᶜ)
    (j : ℕ) :
    ε < (μ (diagSeq next j).1 : Measure ℝ)
      (Set.Icc (-(j : ℝ)) (j : ℝ))ᶜ := by
  induction j with
  | zero => exact (hnext 0 0).2
  | succ k _ => exact (hnext (k + 1) (diagSeq next k).1).2

/-- **Prokhorov's theorem, sequential form on $\mathbb{R}$.** A sequence $(\mu_n)$ of probability
measures on $\mathbb{R}$ is tight if and only if every subsequence of $(\mu_n)$ has a further
subsequence converging weakly to a probability measure on $\mathbb{R}$. -/
theorem prokhorov_sequential (μ : ℕ → ProbabilityMeasure ℝ) :
    IsTightMeasureSet {((μ n : ProbabilityMeasure ℝ) : Measure ℝ) | n} ↔
      ∀ f : ℕ → ℕ, StrictMono f →
        ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ ν : ProbabilityMeasure ℝ,
          Tendsto (μ ∘ f ∘ g) atTop (𝓝 ν) := by
  constructor
  · -- Tightness implies relative sequential compactness, via Mathlib's
    -- compactness form of Prokhorov's theorem.
    intro h f hf
    have hcomp : IsCompact (closure (Set.range μ)) :=
      isCompact_closure_of_isTightMeasureSet (by simpa using h)
    obtain ⟨a, _, g, hg, hlim⟩ :=
      hcomp.tendsto_subseq (fun n => subset_closure ⟨f n, rfl⟩)
    exact ⟨g, hg, a, hlim⟩
  · -- If the sequence is not tight, some `ε > 0` defeats every compact
    -- set; the diagonal subsequence built from those defeats escapes
    -- every closed tail set, contradicting the Portmanteau theorem.
    intro Hseq
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    by_contra hnot
    push Not at hnot
    obtain ⟨ε, hε, hK⟩ := hnot
    have key : ∀ M : ℕ, ∃ n : ℕ,
        ε < (μ n : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ := by
      intro M
      obtain ⟨ν, hν, hgt⟩ := hK _ isCompact_Icc
      obtain ⟨n, hn⟩ := hν
      exact ⟨n, by rw [hn]; exact hgt⟩
    choose n hn using key
    -- Step 1: for each radius `k` and each bound `B`, there is an index
    -- beyond `B` whose measure escapes `[-k, k]`.
    have step1 : ∀ k : ℕ, ∀ B : ℕ, ∃ n : ℕ, B < n ∧
        ε < (μ n : Measure ℝ) (Set.Icc (-(k : ℝ)) (k : ℝ))ᶜ := by
      intro k B
      by_contra hcon
      push Not at hcon
      have hle : ∀ M : ℕ, k ≤ M → n M ≤ B := by
        intro M hMk
        by_contra hgt
        push Not at hgt
        have hmono : (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ ⊆
            (Set.Icc (-(k : ℝ)) (k : ℝ))ᶜ :=
          Set.compl_subset_compl.mpr (Set.Icc_subset_Icc
            (neg_le_neg (show (k : ℝ) ≤ (M : ℝ) by exact_mod_cast hMk))
            (by exact_mod_cast hMk))
        have h1 := hn M
        have h2 := hcon (n M) hgt
        have h3 : (μ (n M) : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ ≤
            (μ (n M) : Measure ℝ) (Set.Icc (-(k : ℝ)) (k : ℝ))ᶜ :=
          measure_mono hmono
        exact (not_lt_of_ge (le_trans h3 h2)) h1
      have hthr : ∀ m : ℕ, ∃ T : ℕ, ∀ M : ℕ, T ≤ M →
          (μ m : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ < ε := by
        intro m
        have hev : ∀ᶠ (M : ℕ) in atTop,
            (μ m : Measure ℝ) (Set.Icc (-(M : ℝ)) (M : ℝ))ᶜ < ε :=
          (tendsto_measure_compl_Icc (μ m)).eventually (Iio_mem_nhds hε)
        rw [Filter.eventually_atTop] at hev
        exact hev
      choose T hT using hthr
      set Tmax := (Finset.range (B + 1)).sup T with hTmax
      obtain ⟨M, hMk, hMT⟩ : ∃ M, k ≤ M ∧ Tmax < M :=
        ⟨max k (Tmax + 1), le_max_left _ _,
          lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩
      have hnM_le : n M ≤ B := hle M hMk
      have hTle : T (n M) ≤ Tmax :=
        Finset.le_sup (Finset.mem_range.mpr (by omega))
      have hTM : T (n M) ≤ M := le_trans hTle (by omega)
      have hlt := hT (n M) M hTM
      exact (not_lt_of_ge hlt.le) (hn M)
    -- Step 2: diagonalize Step 1 into a strictly monotone subsequence
    -- whose `j`-th term escapes `[-j, j]`.
    choose next hnext using step1
    set f : ℕ → ℕ := fun j => (diagSeq next j).1 with hf_def
    have hf : StrictMono f :=
      strictMono_nat_of_lt_succ fun j => by
        show (diagSeq next j).1 < (diagSeq next (j + 1)).1
        rw [diagSeq_fst_succ]
        exact (hnext (j + 1) (diagSeq next j).1).1
    have hfp : ∀ j, ε < (μ (f j) : Measure ℝ)
        (Set.Icc (-(j : ℝ)) (j : ℝ))ᶜ :=
      fun j => diagSeq_property hnext j
    obtain ⟨g, hg, ν, hlim⟩ := Hseq f hf
    -- Step 3: Portmanteau contradiction. For every `M`, the limit
    -- measure gives mass at least `ε` to `{x | M ≤ |x|}`, but those
    -- masses tend to `0`.
    have hnu : ∀ M : ℕ, ε ≤ (ν : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|} := by
      intro M
      have hlim' : Tendsto (fun j => μ (f (g j))) atTop (𝓝 ν) := hlim
      have hlimsup : Filter.limsup
          (fun j => (μ (f (g j)) : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|}) atTop
          ≤ (ν : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|} :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim'
          (isClosed_Ici.preimage continuous_abs)
      have hev : ∀ᶠ j in atTop,
          ε < (μ (f (g j)) : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|} := by
        have hgj : ∀ᶠ j in atTop, M ≤ g j :=
          hg.tendsto_atTop.eventually (eventually_ge_atTop M)
        filter_upwards [hgj] with j hj
        have h1 := hfp (g j)
        have hsub : (Set.Icc (-((g j : ℝ))) ((g j : ℝ)))ᶜ ⊆
            {x : ℝ | (M : ℝ) ≤ |x|} := by
          intro x hx
          have habs : ((g j : ℝ)) < |x| := by
            simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le] at hx
            by_cases hxc : -((g j : ℝ)) ≤ x
            · have h2 := hx hxc
              have hx0 : 0 ≤ x := by linarith
              rw [abs_of_nonneg hx0]
              exact h2
            · push Not at hxc
              have habsx : |x| = -x := abs_of_neg (by linarith)
              linarith
          simp only [Set.mem_ofPred_eq]
          exact le_trans (by exact_mod_cast hj) habs.le
        exact lt_of_lt_of_le h1 (measure_mono hsub)
      exact le_trans (le_limsup_of_ev_lt hev) hlimsup
    have htend := tendsto_measure_abs_ge ν
    have hev2 : ∀ᶠ (M : ℕ) in atTop, (ν : Measure ℝ) {x : ℝ | (M : ℝ) ≤ |x|} < ε :=
      htend.eventually (Iio_mem_nhds hε)
    obtain ⟨M, hM1, hM2⟩ :=
      (hev2.and (Filter.Eventually.of_forall (fun M => hnu M))).exists
    exact (not_le_of_gt hM1) hM2

end MathlibExt.Probability.ProkhorovSequential
