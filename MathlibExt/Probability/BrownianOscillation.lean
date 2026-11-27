/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import MathlibExt.Probability.Distributions.GaussianTail
import MathlibExt.Probability.BlumenthalZeroOne
import MathlibExt.Probability.BrownianQuadraticVariation

/-!
# Brownian motion oscillates immediately after time zero

If `B` is a real Brownian motion, then almost surely, for every `ε > 0`, the path takes both
strictly positive and strictly negative values on `(0, ε]`. In particular `sup_{s ≤ ε} B s > 0`
and `inf_{s ≤ ε} B s < 0` for every `ε > 0`, and `0` is an accumulation point of the zero set.
This is the first application of Blumenthal's zero–one law in Le Gall's ENS notes
(*Intégration, Probabilités et Processus Aléatoires*, Corollaire 14.4.3, first assertion).

The proof follows the notes. The event `A = ⋂_n {∃ m ≥ n, B (1/(m+1)) > 0}` belongs to the
germ σ-algebra `⋂_{t > 0} σ(B_u : u ≤ t)`, so it has probability `0` or `1` by the repository's
zero–one law for continuous processes with independent increments
(`MathlibExt.Probability.BlumenthalZeroOne.zero_one_naturalGerm`). It is the decreasing limit of
events of probability at least `P(B_{1/(n+1)} > 0) = 1/2` (the half-line mass
`ProbabilityTheory.gaussianReal_Ioi_zero` from `MathlibExt.Probability.Distributions.GaussianTail`),
so `P(A) ≥ 1/2`, hence `P(A) = 1`. The same argument applied to `-B` gives the negative values.

## Main results

* `ProbabilityTheory.IsBrownianReal.ae_exists_pos_and_neg`: **immediate oscillation of Brownian
  motion at time `0`**.

## References

* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Théorème 14.4.2 (Blumenthal) and Corollaire 14.4.3.
* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- For a Brownian motion with measurable coordinates, the event "for every `n`, `B` is
strictly positive at some time `1/(m+1)` with `m ≥ n`" has probability one. -/
private lemma ae_forall_exists_pos {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ 0 < B (1 / ((m : ℝ≥0) + 1)) ω := by
  have hP : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- the natural filtration of the repository's zero-one law
  set 𝓕 := MathlibExt.Probability.BlumenthalZeroOne.naturalFiltration B hBm with h𝓕
  have hproc : MathlibExt.Probability.BlumenthalZeroOne.IsContinuousIndependentIncrementProcess
      B 𝓕 P 0 := by
    refine ⟨hP, hB.eval_zero_ae_eq_zero, fun t ↦ ?_, fun s t hst ↦ ?_, hB.cont⟩
    · exact MathlibExt.Probability.BlumenthalZeroOne.measurable_naturalFiltration hBm le_rfl
    · have h := (hB.toIsPreBrownianReal.indep_natural hBm s t hst.le).symm
      refine indep_of_indep_of_le_left h ?_
      refine iSup₂_le fun u hu ↦ ?_
      exact le_iSup₂_of_le (f := fun (j : ℝ≥0) (_ : j ≤ s) ↦
        MeasurableSpace.comap (B j) inferInstance) u hu le_rfl
  -- the events
  set A : ℕ → Set Ω := fun n ↦
    ⋃ m : ℕ, ⋃ (_ : n ≤ m), {ω | 0 < B (1 / ((m : ℝ≥0) + 1)) ω} with hA
  have hinv : ∀ n m : ℕ, n ≤ m → 1 / ((m : ℝ≥0) + 1) ≤ 1 / ((n : ℝ≥0) + 1) := by
    intro n m hnm
    gcongr
  have hA_meas_le : ∀ (n : ℕ) (t : ℝ≥0), 1 / ((n : ℝ≥0) + 1) ≤ t →
      MeasurableSet[𝓕 t] (A n) := by
    intro n t hnt
    refine MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun hm ↦ ?_
    exact measurableSet_lt measurable_const
      (MathlibExt.Probability.BlumenthalZeroOne.measurable_naturalFiltration hBm
        ((hinv n m hm).trans hnt))
  have hA_anti : Antitone A := by
    intro k n hkn ω hω
    simp only [hA, Set.mem_iUnion] at hω ⊢
    obtain ⟨m, hm, hpos⟩ := hω
    exact ⟨m, hkn.trans hm, hpos⟩
  have hsmall : ∀ t : ℝ≥0, 0 < t → ∃ N : ℕ, 1 / ((N : ℝ≥0) + 1) ≤ t := by
    intro t ht
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (t : ℝ))
    refine ⟨N, ?_⟩
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ ht'] at hN
    nlinarith
  have hgerm : MeasurableSet[MathlibExt.Probability.BlumenthalZeroOne.naturalGerm B hBm]
      (⋂ n, A n) := by
    change MeasurableSet[⨅ t > (0 : ℝ≥0), 𝓕 t] _
    simp only [MeasurableSpace.measurableSet_iInf]
    intro t ht
    obtain ⟨N, hN⟩ := hsmall t ht
    have heq : (⋂ n, A n) = ⋂ n, A (n + N) := by
      ext ω
      simp only [Set.mem_iInter]
      exact ⟨fun h n ↦ h _, fun h n ↦ hA_anti (Nat.le_add_right n N) (h n)⟩
    rw [heq]
    exact MeasurableSet.iInter fun n ↦ hA_meas_le _ _
      ((hinv N (n + N) (Nat.le_add_left N n)).trans hN)
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n ↦
    (𝓕.le 1) _ (hA_meas_le n 1 ((hinv 0 n (Nat.zero_le n)).trans (by simp)))
  -- lower bound
  have hlow : ∀ n, (1 / 2 : ℝ≥0∞) ≤ P (A n) := by
    intro n
    have hsub : {ω | 0 < B (1 / ((n : ℝ≥0) + 1)) ω} ⊆ A n := by
      intro ω hω
      simp only [hA, Set.mem_iUnion]
      exact ⟨n, le_rfl, hω⟩
    have hlaw := hB.hasLaw_eval (1 / ((n : ℝ≥0) + 1))
    have hne : (1 / ((n : ℝ≥0) + 1)) ≠ 0 := by positivity
    calc (1 / 2 : ℝ≥0∞) = gaussianReal 0 (1 / ((n : ℝ≥0) + 1)) (Set.Ioi 0) :=
          (gaussianReal_Ioi_zero hne).symm
      _ = P {ω | 0 < B (1 / ((n : ℝ≥0) + 1)) ω} := by
        rw [hlaw.measure_eq (p := fun x : ℝ ↦ 0 < x) measurableSet_Ioi]
        rfl
      _ ≤ P (A n) := measure_mono hsub
  have hlim : (1 / 2 : ℝ≥0∞) ≤ P (⋂ n, A n) := by
    rw [hA_anti.measure_iInter (fun n ↦ (hA_meas n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    exact le_iInf hlow
  rcases MathlibExt.Probability.BlumenthalZeroOne.zero_one_naturalGerm hproc hBm hgerm with
    h0 | h1
  · rw [h0] at hlim
    norm_num at hlim
  · have hmeas : MeasurableSet (⋂ n, A n) := MeasurableSet.iInter hA_meas
    have hc : P (⋂ n, A n)ᶜ = 0 := by
      rw [measure_compl hmeas (measure_ne_top _ _), h1, measure_univ, tsub_self]
    have hae : ∀ᵐ ω ∂P, ω ∈ ⋂ n, A n := by
      rw [ae_iff]
      exact hc
    filter_upwards [hae] with ω hω n
    have := Set.mem_iInter.1 hω n
    simp only [hA, Set.mem_iUnion] at this
    obtain ⟨m, hm, hpos⟩ := this
    exact ⟨m, hm, hpos⟩

/-- **Brownian motion oscillates immediately after time zero.** If `B` is a real Brownian motion
with measurable coordinates, then almost surely, for every `ε > 0`, there are times `s, s'` in
`(0, ε]` with `B s ω > 0` and `B s' ω < 0`; in particular `sup_{0 ≤ s ≤ ε} B s > 0` and
`inf_{0 ≤ s ≤ ε} B s < 0`. Le Gall, ENS notes *Intégration, Probabilités et Processus
Aléatoires*, Corollaire 14.4.3 (first assertion), a consequence of Blumenthal's zero–one law
(Théorème 14.4.2). -/
theorem IsBrownianReal.ae_exists_pos_and_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      (∃ s ∈ Set.Ioc 0 ε, 0 < B s ω) ∧ (∃ s ∈ Set.Ioc 0 ε, B s ω < 0) := by
  have hpos := ae_forall_exists_pos hB hBm
  have hneg := ae_forall_exists_pos hB.neg (fun t ↦ (hBm t).neg)
  filter_upwards [hpos, hneg] with ω hp hn ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε : ℝ))
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hNε : ∀ m : ℕ, N ≤ m → 1 / ((m : ℝ≥0) + 1) ≤ ε := by
    intro m hm
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε'] at hN
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  obtain ⟨m, hm, hBm'⟩ := hp N
  obtain ⟨m', hm', hBm''⟩ := hn N
  refine ⟨⟨_, ⟨by positivity, hNε m hm⟩, hBm'⟩, ⟨_, ⟨by positivity, hNε m' hm'⟩, ?_⟩⟩
  simpa using hBm''

end ProbabilityTheory
