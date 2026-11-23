/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TimeSeries.AR1MovingAverage
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for the causal AR(1) moving-average representation

The finite-truncation theorems applied at exact values (`ρ = 1/2`, `N = 2`, and the block
`1 ≤ k < 3`), and a satisfiability check for `ar1MA_representation`: coordinates of the
product of standard Gaussian measures on `ℤ → ℝ` are iid, mean zero and square integrable,
so they meet every hypothesis of the main theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExtTest.Probability.TimeSeries.AR1MovingAverage

open MathlibExt.Probability.TimeSeries.AR1MovingAverage

/-- Finite variance formula at exact values `ρ = 1/2`, `N = 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (hLp : ∀ t, MemLp (ε t) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ) (t : ℤ) :
    variance (ar1MAPartial ε (1 / 2 : ℝ) t 2) μ
      = variance (ε 0) μ * (1 - (1 / 2 : ℝ) ^ 4) / (1 - (1 / 2 : ℝ) ^ 2) := by
  have hρ : ((1 / 2 : ℝ) ^ 2) ≠ 1 := by norm_num
  have h := ar1MA_partial_variance ε hρ hLp hIndep hVar t 2
  have h2 : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h2] at h
  exact h

/-- One-step identity at `ρ = 1/2`, `N = 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (t : ℤ) :
    ar1MAPartial ε (1 / 2 : ℝ) t (2 + 1)
      = fun ω => ε t ω + (1 / 2 : ℝ) * ar1MAPartial ε (1 / 2 : ℝ) (t - 1) 2 ω :=
  ar1MA_partial_succ ε (1 / 2 : ℝ) t 2

/-- Remainder recursion at `ρ = 1/2`, `N = 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (t : ℤ) :
    ar1MAPartial ε (1 / 2 : ℝ) t 2
      = fun ω => (1 / 2 : ℝ) * ar1MAPartial ε (1 / 2 : ℝ) (t - 1) 2 ω + ε t ω
        - (1 / 2 : ℝ) ^ 2 * ε (t - ((2 : ℕ) : ℤ)) ω :=
  ar1MA_partial_recursion ε (1 / 2 : ℝ) t 2

/-- Block variance between `N = 1` and `M = 3` at `ρ = 1/2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (hLp : ∀ t, MemLp (ε t) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ) (t : ℤ) :
    variance (fun ω => ar1MAPartial ε (1 / 2 : ℝ) t 3 ω
        - ar1MAPartial ε (1 / 2 : ℝ) t 1 ω) μ
      = variance (ε 0) μ * ∑ k ∈ Finset.Ico 1 3, (1 / 2 : ℝ) ^ (2 * k) :=
  ar1MA_partial_sub_variance ε hLp hIndep hVar t (by norm_num)

/-- Satisfiability: i.i.d. Gaussian product innovations meet every limit-theorem
hypothesis, so the MA representation applies to them. -/
example (t : ℤ) :
    (∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)),
      Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * ω (t - (k : ℤ)))) ∧
      (∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)),
        ar1MA (fun s (ω : ℤ → ℝ) => ω s) (1 / 2) t ω
          = (1 / 2) * ar1MA (fun s (ω : ℤ → ℝ) => ω s) (1 / 2) (t - 1) ω + ω t) ∧
      ((∫ ω, ar1MA (fun s (ω : ℤ → ℝ) => ω s) (1 / 2) t ω
          ∂(Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1))) = 0) ∧
      variance (ar1MA (fun s (ω : ℤ → ℝ) => ω s) (1 / 2) t)
          (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1))
        = variance ((fun s (ω : ℤ → ℝ) => ω s) 0)
            (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1))
          / (1 - (1 / 2 : ℝ) ^ 2) := by
  have hρ : |(1 / 2 : ℝ)| < 1 := by norm_num
  have hLp : MemLp ((fun s (ω : ℤ → ℝ) => ω s) 0) 2
      (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) := by
    have h1 : MemLp id ((2 : NNReal) : ℝ≥0∞) (gaussianReal 0 1) :=
      memLp_id_gaussianReal 2
    have hmp : MeasurePreserving (Function.eval (0 : ℤ))
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) (gaussianReal 0 1) :=
      measurePreserving_eval_infinitePi _ 0
    have h2 := h1.comp_measurePreserving hmp
    have hcoe : ((2 : NNReal) : ℝ≥0∞) = 2 := by simp
    rw [hcoe] at h2
    exact h2
  have hIndep : iIndepFun (fun s (ω : ℤ → ℝ) => ω s)
      (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hIdent : ∀ s, IdentDistrib ((fun s (ω : ℤ → ℝ) => ω s) s)
      ((fun s (ω : ℤ → ℝ) => ω s) 0)
      (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1))
      (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) := by
    intro s
    have hφs : AEMeasurable ((fun s (ω : ℤ → ℝ) => ω s) s)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) :=
      (measurable_pi_apply s).aemeasurable
    have hφ0 : AEMeasurable ((fun s (ω : ℤ → ℝ) => ω s) 0)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) :=
      (measurable_pi_apply 0).aemeasurable
    have e1 : Measure.map ((fun s (ω : ℤ → ℝ) => ω s) s)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) = gaussianReal 0 1 :=
      Measure.infinitePi_map_eval _ s
    have e0 : Measure.map ((fun s (ω : ℤ → ℝ) => ω s) 0)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) = gaussianReal 0 1 :=
      Measure.infinitePi_map_eval _ 0
    exact ⟨hφs, hφ0, e1.trans e0.symm⟩
  have hMean : (∫ ω, (fun s (ω : ℤ → ℝ) => ω s) 0 ω
      ∂(Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1))) = 0 := by
    have hφ : AEMeasurable (fun ω : ℤ → ℝ => ω 0)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) :=
      (measurable_pi_apply 0).aemeasurable
    have hmap0 : Measure.map (fun ω : ℤ → ℝ => ω 0)
        (Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)) = gaussianReal 0 1 :=
      Measure.infinitePi_map_eval _ 0
    have heq := integral_map hφ aestronglyMeasurable_id
    rw [hmap0] at heq
    have hgauss : (∫ y, id y ∂(gaussianReal 0 1)) = (0 : ℝ) :=
      integral_id_gaussianReal
    exact heq.symm.trans hgauss
  exact ar1MA_representation (fun s (ω : ℤ → ℝ) => ω s) hρ hLp hIndep hIdent hMean t

end MathlibExtTest.Probability.TimeSeries.AR1MovingAverage
