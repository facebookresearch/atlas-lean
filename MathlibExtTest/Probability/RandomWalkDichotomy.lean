/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkDichotomy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Topology
open MathlibExt.Probability.RandomWalkDichotomy
open MathlibExt.Probability.RandomWalkTailMeasurability (randomWalkPartialSum)

namespace MathlibExtTest.Probability.RandomWalkDichotomy

private theorem gaussian_ne_zero_ae : ∀ᵐ x ∂gaussianReal 0 1, x ≠ 0 := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by simp)
  rw [ae_iff]
  simp

/-- The source conclusion includes zero partial sums at every time. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ZeroWalk μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X :=
  random_walk_dichotomy_zero μ X hindep hident

/-- The product-space theorem has the same all-times zero alternative. -/
example (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ZeroWalk (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToTop (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToBot (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    Oscillates (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq :=
  dichotomy_product_zero ρ

/-- The actual product law with zero increments gives a zero walk at all times. -/
example : ZeroWalk (Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))) coordSeq := by
  rw [zeroWalk_iff_ae_forall_eq_zero, ae_all_iff]
  intro i
  have hmap : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => Measure.dirac (0 : ℝ))).map
      (fun ω => ω i), x = 0 := by
    rw [Measure.infinitePi_map_eval]
    simp
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable (measurableSet_singleton 0)).mp hmap

/-- A nonconstant Gaussian i.i.d. walk cannot take the all-times zero alternative. -/
example :
    DriftsToTop (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) coordSeq ∨
    DriftsToBot (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) coordSeq ∨
    Oscillates (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) coordSeq := by
  let ν := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
  have hindep : iIndepFun coordSeq ν :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
      (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have hident : ∀ i, IdentDistrib (coordSeq i) (coordSeq 0) ν ν := by
    intro i
    refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
    exact (Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) i).trans
      (Measure.infinitePi_map_eval (fun _ : ℕ => gaussianReal 0 1) 0).symm
  have hmap : ∀ᵐ x ∂ν.map (fun ω => ω 0), x ≠ 0 := by
    rw [Measure.infinitePi_map_eval]
    exact gaussian_ne_zero_ae
  have hnonzero : ∀ᵐ ω ∂ν, ω 0 ≠ 0 :=
    (ae_map_iff (measurable_pi_apply 0).aemeasurable (measurableSet_singleton 0).compl).mp hmap
  have hnotzero : ¬ ZeroWalk ν coordSeq := by
    intro hzero
    have hzero' : ∀ᵐ ω ∂ν, ∀ i, ω i = 0 := zeroWalk_iff_ae_forall_eq_zero.mp hzero
    obtain ⟨ω, hz, hne⟩ := (hzero'.and hnonzero).exists
    exact hne (hz 0)
  exact (random_walk_dichotomy_zero ν coordSeq hindep hident).resolve_left hnotzero

/-- Finite convergence can have a nonzero limit that depends on the path. -/
example :
    ConvergesFinite (gaussianReal 0 1) (fun i ω => if i = 0 then ω else 0) ∧
    ¬ ZeroWalk (gaussianReal 0 1) (fun i ω => if i = 0 then ω else 0) := by
  constructor
  · apply Filter.Eventually.of_forall
    intro ω
    refine ⟨ω, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < n := by omega
    simp [randomWalkPartialSum, hn0]
  · intro hzero
    have hall := zeroWalk_iff_ae_forall_eq_zero.mp hzero
    obtain ⟨ω, hz, hne⟩ := (hall.and gaussian_ne_zero_ae).exists
    exact hne (by simpa using hz 0)

/-- Tending to zero still permits a nonzero excursion at the first step. -/
example : ∃ X : ℕ → ℝ → ℝ,
    (∀ᵐ ω ∂gaussianReal 0 1, Tendsto (fun n => randomWalkPartialSum X n ω)
      atTop (𝓝 0)) ∧ ¬ ZeroWalk (gaussianReal 0 1) X := by
  refine ⟨fun i ω => (if i = 0 then ω else 0) - (if i = 1 then ω else 0), ?_, ?_⟩
  · apply Filter.Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : 0 < n := by omega
    have hn1 : 1 < n := by omega
    simp [randomWalkPartialSum, Finset.sum_sub_distrib, hn0, hn1]
  · intro hzero
    have hall := zeroWalk_iff_ae_forall_eq_zero.mp hzero
    obtain ⟨ω, hz, hne⟩ := (hall.and gaussian_ne_zero_ae).exists
    exact hne (by simpa using hz 0)

/-- The finite-convergence corollary retains the original public conclusion. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConvergesFinite μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X :=
  random_walk_dichotomy μ X hindep hident

/-- The constant-`1` walk drifts to `+∞`: its partial sums are
`Sₙ = n`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    DriftsToTop μ (fun _ _ => (1 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (1 : ℝ)) n ω = (n : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [hsum] using tendsto_natCast_atTop_atTop

/-- The constant-`-1` walk drifts to `-∞`: its partial sums are
`Sₙ = -n`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    DriftsToBot μ (fun _ _ => (-1 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (-1 : ℝ)) n ω = -(n : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [Function.comp_def, hsum] using
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop

/-- The zero walk converges finitely: its partial sums are identically `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ConvergesFinite μ (fun _ _ => (0 : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro ω
  refine ⟨0, ?_⟩
  have hsum : ∀ n, randomWalkPartialSum (fun _ _ => (0 : ℝ)) n ω = (0 : ℝ) := by
    intro n
    simp [randomWalkPartialSum]
  simpa only [hsum] using tendsto_const_nhds

/-- Drifting to `+∞` and to `-∞` are mutually exclusive: at a point where
both hold, the partial sums would eventually be `≥ 1` and `≤ 0` at once. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hTop : DriftsToTop μ X) (hBot : DriftsToBot μ X) :
    False := by
  obtain ⟨ω, h1, h2⟩ := (hTop.and hBot).exists
  have e1 : ∀ᶠ n in Filter.atTop, (1 : ℝ) ≤ randomWalkPartialSum X n ω :=
    h1.eventually (eventually_ge_atTop (1 : ℝ))
  have e2 : ∀ᶠ n in Filter.atTop, randomWalkPartialSum X n ω ≤ (0 : ℝ) :=
    h2.eventually (eventually_le_atBot (0 : ℝ))
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  linarith

end MathlibExtTest.Probability.RandomWalkDichotomy
