/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sequential.ConfidenceSequence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for anytime-valid confidence sequences

The constant process `E = 1` gives the whole space at every time, and a process taking a
negative value is rejected by the nonnegativity hypothesis. A finite deterministic time
recovers fixed-time coverage through the stopped-coverage theorem, and the infinite time
is outside the almost-sure-finiteness hypothesis. Bernoulli null likelihood ratios give
a concrete e-process family with anytime coverage, wide-nonempty all-zero sets, and a
repeated-testing counterexample.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

universe u

namespace MathlibExt.Probability.Statistics

-- Positive: the constant process E = 1 gives the whole space at every time.
example {Θ X : Type*} (E : Θ → ℕ → X → ℝ) (α : ℝ) (n : ℕ) (x : X)
    (hE : ∀ t m, E t m x = 1) (t : Θ) :
    t ∈ confSeqOfEProcess E α n x ↔ (1 : ℝ) < 1 / α := by
  simp [confSeqOfEProcess, hE]

-- Boundary: a process taking a negative value is rejected by the nonnegativity hypothesis.
example : ¬ (0 : ℝ → ℕ → ℝ) ≤ (fun _ _ => (-1 : ℝ)) := by
  intro h
  have h0 : (0 : ℝ) ≤ (-1 : ℝ) := h 0 0
  norm_num at h0

-- Positive: a finite deterministic time recovers fixed-time coverage through the main
-- theorem. The two-argument constant family is a stopping time (via
-- isStoppingTime_const) and is a.s. finite (every constant is below top); the
-- conclusion follows by applying stopped_confSeq_coverage to that exact tau.
example {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (μ θ)]
    {E : Θ → ℕ → X → ℝ} {α : ℝ}
    (hEmeas : ∀ t n, Measurable (E t n))
    (hcover : ∀ t, (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≥ 1 - α)
    {𝒢 : Θ → Filtration ℕ m0} (n : ℕ) :
    ∀ t, (μ t).real {x | ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x) < ⊤ ∧ t ∈ confSeqOfEProcess E α (((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x).untopD 0) x} ≥ 1 - α := by
  have hstop : ∀ t, IsStoppingTime (𝒢 t) ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t) :=
    fun t => isStoppingTime_const (𝒢 t) n
  have hfin : ∀ t, ∀ᵐ x ∂(μ t), ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x) < ⊤ :=
    fun t => ae_of_all _ fun _ => WithTop.coe_lt_top n
  exact stopped_confSeq_coverage hEmeas hcover hstop hfin

-- Positive/use: the constant-one e-process derives simultaneous coverage through the
-- main theorem. The constant process is a martingale for the constant filtration, hence
-- a supermartingale, and its initial mean is 1.
example {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (μ θ)]
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (t : Θ) :
    (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess (fun _ _ _ => 1) α n x} ≥ 1 - α := by
  have hsup : ∀ s, Supermartingale (fun (_ : ℕ) (_ : X) => (1 : ℝ))
      (Filtration.const ℕ m0 le_rfl) (μ s) :=
    fun s => (martingale_const _ _ 1).supermartingale
  have hnonneg : ∀ s : Θ, (0 : ℕ → X → ℝ) ≤ fun _ _ => (1 : ℝ) := by
    intro s i x
    exact zero_le_one
  have hE0 : ∀ s, ∫ x, (fun (_ : ℕ) (_ : X) => (1 : ℝ)) 0 x ∂(μ s) ≤ 1 := by
    intro s
    simp
  exact anytime_coverage_of_eProcess hα hsup hnonneg hE0 t

-- Positive/use: the Bernoulli likelihood computes at both atoms.
example (p : ℝ) : bernoulliLik p 1 = p ∧ bernoulliLik p 0 = 1 - p := by
  constructor
  · simp [bernoulliLik]
  · simp [bernoulliLik]

-- Boundary: the LR process is nonnegative for every observation path (degenerate
-- all-zero data stay valid), using only p0, q ∈ (0,1), no distributional assumption.
example {Ω : Type*} (X : ℕ → Ω → ℕ) {p0 q : ℝ}
    (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (ω : Ω) : 0 ≤ bernoulliNullLR X p0 q n ω := by
  unfold bernoulliNullLR
  apply Finset.prod_nonneg
  intro i hi
  apply div_nonneg
  · unfold bernoulliLik
    by_cases h : X i ω = 1
    · simp [h, hp0.1.le]
    · simp [h]
      linarith [hp0.2]
  · unfold bernoulliLik
    by_cases h : X i ω = 1
    · simp [h, hq.1.le]
    · simp [h]
      linarith [hq.2]

/-- Fair-coin anytime coverage use case: for the fair null `q = 1/2` against the fixed
reference alternative `p0 = 1/4`, the inverted confidence sequence traps `1/2` at every
time with probability at least `1 - α`. Invokes the self-contained coverage theorem
directly with the data hypotheses. -/
example {Ω : Type u} {m0 : MeasurableSpace Ω} {X : ℕ → Ω → ℕ}
    {μ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1} → Measure Ω} [∀ θ, IsProbabilityMeasure (μ θ)]
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX_indep : ∀ θ, ProbabilityTheory.iIndepFun X (μ θ))
    (hX01 : ∀ θ, ∀ i, μ θ {ω | X i ω = 0 ∨ X i ω = 1} = 1)
    (hX1 : ∀ θ, ∀ i, ((μ θ {ω | X i ω = 1}).toReal) = θ.val)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (μ ⟨(1/2 : ℝ), by norm_num⟩).real {ω | ∀ n,
      (⟨(1/2 : ℝ), by norm_num⟩ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1}) ∈
      confSeqOfEProcess (fun t m w => bernoulliNullLR X (1/4 : ℝ) t.val m w) α n ω} ≥ 1 - α := by
  have hp0 : (1/4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hq : (1/2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  exact bernoulli_anytime_coverage (p0 := (1/4 : ℝ)) hp0 hXstrong hX_indep hX01 hX1 hα ⟨1/2, hq⟩

/-- All-zero degenerate data: the inverted confidence sets stay wide and nonempty.
For the constant-zero path, every null `q` below the reference `p0` stays in the set
at every horizon (the likelihood ratio over the `n + 1` inclusive factors is `((1-p0)/(1-q))^(n+1) ≤ 1 < 1/α`), so the
degenerate path yields a valid confidence set containing the whole `(0, p0]`, never an empty
set. Validity (coverage) is the main theorems' content; this pins the non-collapse. -/
example {Ω : Type u} {p0 : ℝ} (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (ω : Ω) :
    ∀ θ : {q : ℝ // q ∈ Set.Ioo (0 : ℝ) 1}, θ.val ≤ p0 →
      θ ∈ confSeqOfEProcess (fun s m _ => bernoulliNullLR (fun _ _ => (0 : ℕ)) p0 s.val m ω) α n ω := by
  intro θ hθp0
  have hq : θ.val ∈ Set.Ioo (0 : ℝ) 1 := θ.property
  show bernoulliNullLR (fun _ _ => (0 : ℕ)) p0 θ.val n ω < 1 / α
  have hlik0 : ∀ (p : ℝ), bernoulliLik p 0 = 1 - p := by
    intro p; simp [bernoulliLik]
  have hLR : bernoulliNullLR (fun _ _ => (0 : ℕ)) p0 θ.val n ω = ((1 - p0) / (1 - θ.val)) ^ (n + 1) := by
    unfold bernoulliNullLR
    simp only [hlik0]
    rw [Finset.prod_const, Finset.card_range]
  rw [hLR]
  have h1q : (0:ℝ) < 1 - θ.val := by linarith [hq.2]
  have hbase_nonneg : (0:ℝ) ≤ (1 - p0) / (1 - θ.val) := by
    apply div_nonneg
    · linarith [hp0.2]
    · linarith [hq.2]
  have hbase_le : (1 - p0) / (1 - θ.val) ≤ 1 := by
    rw [div_le_one h1q]
    linarith
  have hpow : ((1 - p0) / (1 - θ.val)) ^ (n + 1) ≤ 1 := pow_le_one₀ hbase_nonneg hbase_le
  have hα1 : (1:ℝ) < 1 / α := by
    rw [lt_div_iff₀ hα.1]
    simp only [one_mul]
    linarith [hα.2]
  linarith

/-- Naive repeated fixed-n testing counterexample: the joint false-rejection probability
of `k ≥ 2` independent fixed-n tests, each of exact size `α`, is `1 - (1-α)^k`, which
strictly exceeds the nominal `α`. Pointwise level-`α` control does not compose across
looks; this is the quantitative gap the anytime-valid construction closes. -/
example {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {k : ℕ} (hk : 2 ≤ k) :
    α < 1 - (1 - α) ^ k := by
  have h0 : (0:ℝ) ≤ 1 - α := by linarith [hα.1, hα.2]
  have h1 : (1:ℝ) - α ≤ 1 := by linarith [hα.1]
  have hpow : (1 - α) ^ k ≤ (1 - α) ^ 2 := pow_le_pow_of_le_one h0 h1 hk
  have h2 : (1 - α) ^ 2 = 1 - 2 * α + α ^ 2 := by ring
  have hsq : (1 - α) ^ k < 1 - α := by
    calc (1 - α) ^ k ≤ (1 - α) ^ 2 := hpow
      _ = 1 - 2 * α + α ^ 2 := h2
      _ < 1 - α := by nlinarith [hα.1, hα.2, sq_nonneg α]
  linarith

end MathlibExt.Probability.Statistics
