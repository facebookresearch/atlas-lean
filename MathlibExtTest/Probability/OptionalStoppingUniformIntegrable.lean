/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptionalStoppingUniformIntegrable

/-!
# Tests for optional stopping of uniformly integrable martingales

Restatements of the public signatures in
`MathlibExt.Probability.OptionalStoppingUniformIntegrable`, and the
constant martingale as a concrete uniformly integrable martingale for
which the stopped value and the limit expectation are both the constant.

The constant martingale also exercises the theorem at infinity.
Definition-level tests use a process that starts at zero and then stays at
one, a mixed zero/infinity stopping function, and the ramp `n / (n + 1)`.
The ramp's finite values are all below its limit one. These time-changing
fixtures test the stopped-value definition independently of the martingale theorem.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace MathlibExtTest.Probability.OptionalStoppingUniformIntegrable

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- Stopping a uniformly integrable martingale yields a uniformly
integrable stopped process. -/
example (hmart : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    UniformIntegrable (stoppedProcess f τ) 1 μ :=
  hmart.uniformIntegrable_stoppedProcess_of_uniformIntegrable hui τ hτ

/-- Optional stopping for uniformly integrable martingales, restated
with the exact public signature. -/
example (hmart : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    (∫ ω, f 0 ω ∂μ = ∫ ω, stoppedValueAtTop f τ ω ∂μ) ∧
    (∫ ω, stoppedValueAtTop f τ ω ∂μ = ∫ ω, ℱ.limitProcess f μ ω ∂μ) :=
  hmart.integral_stoppedValueAtTop_eq_of_uniformIntegrable hui τ hτ

/-- A constant process is a martingale, uniformly integrable in `L¹`. -/
private theorem uniformIntegrable_const_process (c : ℝ) :
    UniformIntegrable (fun (_ : ℕ) (_ : Ω) => c) 1 μ :=
  uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const c)

/-- For the constant martingale, the stopped value at the constant
stopping time `5` is the constant itself, pointwise. -/
example (c : ℝ) (ω : Ω) :
    stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ((5 : ℕ) : WithTop ℕ)) ω = c := by
  simp [stoppedValueAtTop]

/-- For the constant martingale, stopping at the constant stopping
time `5` preserves the expectation `c`. -/
example (c : ℝ) :
    ∫ ω, stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ((5 : ℕ) : WithTop ℕ)) ω ∂μ = c := by
  have h := (martingale_const ℱ μ c).integral_stoppedValueAtTop_eq_of_uniformIntegrable
    (uniformIntegrable_const_process (μ := μ) c) (fun _ => ((5 : ℕ) : WithTop ℕ))
    (isStoppingTime_const ℱ 5)
  have h0 : ∫ ω, (fun (_ : ℕ) (_ : Ω) => c) 0 ω ∂μ = c := by
    simp [integral_const]
  exact h.1 ▸ h0

/-- For the constant martingale, the limit process has expectation `c`. -/
example (c : ℝ) :
    ∫ ω, ℱ.limitProcess (fun (_ : ℕ) (_ : Ω) => c) μ ω ∂μ = c := by
  have h := (martingale_const ℱ μ c).integral_stoppedValueAtTop_eq_of_uniformIntegrable
    (uniformIntegrable_const_process (μ := μ) c) (fun _ => ((5 : ℕ) : WithTop ℕ))
    (isStoppingTime_const ℱ 5)
  have h0 : ∫ ω, (fun (_ : ℕ) (_ : Ω) => c) 0 ω ∂μ = c := by
    simp [integral_const]
  exact h.2 ▸ h.1 ▸ h0

/-- The constant martingale also has its constant value at infinity, pointwise. -/
example (c : ℝ) (ω : Ω) :
    stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ⊤) ω = c := by
  simp only [stoppedValueAtTop]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).limUnder_eq

/-- The optional-stopping theorem applies to the constant martingale at infinity. -/
example (c : ℝ) :
    ∫ ω, stoppedValueAtTop (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ⊤) ω ∂μ = c := by
  have hτ : IsStoppingTime ℱ (fun _ : Ω => (⊤ : WithTop ℕ)) := by
    intro n
    simp
  have h := (martingale_const ℱ μ c).integral_stoppedValueAtTop_eq_of_uniformIntegrable
    (uniformIntegrable_const_process (μ := μ) c) (fun _ => ⊤) hτ
  have h0 : ∫ ω, (fun (_ : ℕ) (_ : Ω) => c) 0 ω ∂μ = c := by
    simp [integral_const]
  exact h.1 ▸ h0

/-- The process that starts at zero and stays at one after time zero tends to one. -/
private theorem tendsto_zero_then_one :
    Tendsto (fun n : ℕ => if n = 0 then (0 : ℝ) else 1) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp [show n ≠ 0 by omega]

/-- At infinity, this time-changing process has value one, rather than its initial zero. -/
example (ω : Ω) :
    stoppedValueAtTop (fun n (_ : Ω) => if n = 0 then (0 : ℝ) else 1)
      (fun _ => ⊤) ω = 1 := by
  simp only [stoppedValueAtTop]
  exact tendsto_zero_then_one.limUnder_eq

/-- The same infinity branch has expectation one on a probability space. -/
example :
    ∫ ω, stoppedValueAtTop (fun n (_ : Ω) => if n = 0 then (0 : ℝ) else 1)
      (fun _ => ⊤) ω ∂μ = 1 := by
  simp [stoppedValueAtTop, tendsto_zero_then_one.limUnder_eq, integral_const]

/-- A stopping function taking both zero and infinity selects both branches. -/
example (b : Bool) :
    stoppedValueAtTop (fun n (_ : Bool) => if n = 0 then (0 : ℝ) else 1)
      (fun b => if b then ⊤ else (0 : WithTop ℕ)) b = (if b then 1 else 0) := by
  cases b <;> simp [stoppedValueAtTop, tendsto_zero_then_one.limUnder_eq]

/-- The ramp tends to one, while every finite-time value is strictly below one. -/
example (ω : Ω) :
    stoppedValueAtTop (fun n (_ : Ω) => (n : ℝ) / ((n : ℝ) + 1))
      (fun _ => ⊤) ω = 1 := by
  simp only [stoppedValueAtTop]
  exact (tendsto_natCast_div_add_atTop (1 : ℝ)).limUnder_eq

/-- Stopping the ramp at infinity has expectation one on a probability space. -/
example :
    ∫ ω, stoppedValueAtTop (fun n (_ : Ω) => (n : ℝ) / ((n : ℝ) + 1))
      (fun _ => ⊤) ω ∂μ = 1 := by
  have hlim := (tendsto_natCast_div_add_atTop (1 : ℝ)).limUnder_eq
  simp [stoppedValueAtTop, hlim, integral_const]

#print axioms Martingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable
#print axioms Martingale.integral_stoppedValueAtTop_eq_of_uniformIntegrable

end MathlibExtTest.Probability.OptionalStoppingUniformIntegrable
