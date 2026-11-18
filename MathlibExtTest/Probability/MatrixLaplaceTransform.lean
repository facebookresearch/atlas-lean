/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MatrixLaplaceTransform

@[expose] public section

open MeasureTheory Matrix MathlibExt.Probability.MatrixLaplaceTransform

namespace MathlibExtTest.Probability.MatrixLaplaceTransform

/-- Non-vacuity of the upper tail bound: a deterministic random matrix `Y ≡ A` on a
probability space. The bound reads `1_{t ≤ λmax(A)} ≤ e^{-θt} tr e^{θA}`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (θ t : ℝ) (hθ : 0 < θ) :
    μ.real {_ω : Ω | t ≤ hA.lambdaMax} ≤
      Real.exp (-θ * t) * ∫ ω, traceMgf (fun _ : Ω => A) θ ω ∂μ :=
  measureReal_le_lambdaMax_le (μ := μ) (Y := fun _ : Ω => A) (fun _ => hA) hθ
    (integrable_const _) t

/-- Non-vacuity of the lower tail bound with a negative parameter. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Matrix (Fin 2) (Fin 2) ℂ) (hY : ∀ ω, (Y ω).IsHermitian)
    (hint : Integrable (traceMgf Y (-1)) μ) (t : ℝ) :
    μ.real {ω | (hY ω).lambdaMin ≤ t} ≤ Real.exp t * ∫ ω, traceMgf Y (-1) ω ∂μ := by
  simpa using measureReal_lambdaMin_le_le hY (by norm_num : (-1 : ℝ) < 0) hint t

/-- The expectation bound for a deterministic random matrix recovers the deterministic
inequality `λmax(A) ≤ θ⁻¹ log tr e^{θA}`. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (θ : ℝ) (hθ : 0 < θ) :
    hA.lambdaMax ≤ θ⁻¹ * Real.log (RCLike.re (NormedSpace.exp (θ • A)).trace) := by
  have := integral_lambdaMax_le (μ := Measure.dirac ()) (Y := fun _ : Unit => A)
    (fun _ => hA) hθ (integrable_const _) (integrable_const _)
  simpa [traceMgf] using this

end MathlibExtTest.Probability.MatrixLaplaceTransform
