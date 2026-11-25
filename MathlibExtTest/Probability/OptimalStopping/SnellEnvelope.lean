/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptimalStopping.SnellEnvelope

/-!
# Tests for the finite-horizon Snell envelope

Deterministic rewards on an arbitrary probability space: the envelope at time zero of a
one-step problem is the larger of the two rewards, and the optimality theorem applies to a
constant stopping time.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace MathlibExtTest.Probability.OptimalStopping.SnellEnvelope

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝒢 : Filtration ℕ m0}

/-- With horizon `0` the envelope is the reward itself. -/
example (G : ℕ → Ω → ℝ) : snellEnvelope 𝒢 μ G 0 0 = G 0 :=
  snellEnvelope_of_le le_rfl

/-- One-step problem with deterministic rewards `c 0` and `c 1`: the envelope at time zero is
`max (c 0) (c 1)` (the value of stopping now or at the horizon, whichever is larger). -/
theorem snellEnvelope_zero_const (c : ℕ → ℝ) :
    snellEnvelope 𝒢 μ (fun n _ => c n) 1 0 = fun _ => max (c 0) (c 1) := by
  rw [snellEnvelope_of_lt Nat.zero_lt_one, snellEnvelope_of_le le_rfl]
  funext ω
  rw [condExp_const (𝒢.le 0)]

/-- The one-step deterministic problem is non-degenerate: with rewards `G n = n`, the envelope
at time zero is `1`, which strictly exceeds the immediate reward `0`. -/
example : snellEnvelope 𝒢 μ (fun n _ => ((n : ℝ))) 1 0 = fun _ => 1 := by
  rw [snellEnvelope_zero_const]
  funext ω
  norm_num

/-- With rewards `G n = n` and horizon `1`, the first meeting time is `1`, not `0`: stopping at
once is not optimal (a non-vacuity probe of (1.1.8) and (1.1.12)). -/
example (ω : Ω) : snellStoppingTime 𝒢 μ (fun n _ => ((n : ℝ))) 1 ω = 1 := by
  have hle := snellStoppingTime_le (𝒢 := 𝒢) (μ := μ) (G := fun n _ => ((n : ℝ))) (N := 1) ω
  have hne : snellStoppingTime 𝒢 μ (fun n _ => ((n : ℝ))) 1 ω ≠ 0 := by
    intro h0
    have h := snellEnvelope_snellStoppingTime (𝒢 := 𝒢) (μ := μ) (G := fun n _ => ((n : ℝ)))
      (N := 1) ω
    rw [h0, snellEnvelope_zero_const] at h
    norm_num at h
  omega

/-- The smallest-supermartingale property against the constant supermartingale `1`, which
dominates the rewards `0, 1`. -/
example : snellEnvelope 𝒢 μ (fun n _ => ((n : ℝ))) 1 0 ≤ᵐ[μ] fun _ => 1 :=
  snellEnvelope_ae_le (fun _ => integrable_const _) (Y := fun _ _ => 1)
    (fun _ => integrable_const _)
    (fun k _ => by rw [condExp_const (𝒢.le k)])
    (fun k hk => Eventually.of_forall fun _ => by
      interval_cases k <;> norm_num)
    (Nat.zero_le 1)

/-- The envelope stopped at the first meeting time is a martingale for the deterministic
rewards. -/
example (c : ℕ → ℝ) :
    Martingale (stoppedProcess (snellEnvelope 𝒢 μ (fun n _ => c n) 1)
      (fun ω => (snellStoppingTime 𝒢 μ (fun n _ => c n) 1 ω : WithTop ℕ))) 𝒢 μ :=
  martingale_stoppedProcess_snellEnvelope (fun _ => stronglyMeasurable_const)
    (fun _ => integrable_const _)

/-- The deterministic reward is strongly adapted and integrable, so the optimality theorem
applies; here with the constant stopping time `0`. -/
example (c : ℕ → ℝ) :
    μ[stoppedValue (fun n (_ : Ω) => c n) (fun _ => ((0 : ℕ) : WithTop ℕ))] ≤
      μ[stoppedValue (fun n (_ : Ω) => c n)
        (fun ω => (snellStoppingTime 𝒢 μ (fun n _ => c n) 1 ω : WithTop ℕ))] :=
  snellStoppingTime_optimal (fun _ => stronglyMeasurable_const) (fun _ => integrable_const _)
    (isStoppingTime_const 𝒢 0) (fun _ => by exact_mod_cast Nat.zero_le 1)

/-- The conditional form at time `n = 1 ≤ N = 2` applies to the constant stopping time `2`. -/
example (c : ℕ → ℝ) :
    μ[stoppedValue (fun n (_ : Ω) => c n) (fun _ => ((2 : ℕ) : WithTop ℕ)) | 𝒢 1] ≤ᵐ[μ]
      snellEnvelope 𝒢 μ (fun n _ => c n) 2 1 :=
  condExp_stoppedValue_le_snellEnvelope (fun _ => stronglyMeasurable_const)
    (fun _ => integrable_const _) (isStoppingTime_const 𝒢 2)
    (fun _ => by exact_mod_cast (by norm_num : 1 ≤ 2)) (fun _ => le_rfl)

end MathlibExtTest.Probability.OptimalStopping.SnellEnvelope
