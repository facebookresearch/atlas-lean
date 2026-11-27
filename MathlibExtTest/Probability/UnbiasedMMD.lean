/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.UnbiasedMMD

@[expose] public section

/-!
# Tests for the unbiased estimate of the squared MMD
-/

set_option autoImplicit false

open MeasureTheory
open MathlibExt.Probability.KernelMeanEmbedding MathlibExt.Probability.UnbiasedMMD

namespace MathlibExtTest.Probability.UnbiasedMMD

/-- A concrete RKHS: the constant kernel `k ≡ 1` on the one-point space. -/
abbrev H₁ := RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : Unit => (1 : ℝ)))

/-- Non-vacuity: on the one-point space every probability measure has an integrable feature map,
so the expectation of the unbiased statistic for samples of size two is the squared MMD. -/
example (μ ν : Measure Unit) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ z, mmdUnbiasedSq H₁ le_rfl le_rfl z.1 z.2 ∂((Measure.pi fun _ : Fin 2 => μ).prod
      (Measure.pi fun _ : Fin 2 => ν)) = mmd H₁ μ ν ^ 2 :=
  integral_mmdUnbiasedSq le_rfl le_rfl (Integrable.of_finite) (Integrable.of_finite)

/-- The unbiased statistic for one-point samples of size two from the same point vanishes. -/
example {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] (a : X) :
    mmdUnbiasedSq H le_rfl le_rfl (fun _ : Fin 2 => a) (fun _ : Fin 2 => a) = 0 := by
  simp only [mmdUnbiasedSq]
  simp
  ring

/-! The unbiased statistic needs samples of size at least two: for a sample of size one, which
has no pair `i ≠ j`, the size proof cannot be given. -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ :=
  mmdUnbiasedSq H₁ (by norm_num) le_rfl (fun _ : Fin 1 => ()) (fun _ : Fin 2 => ())

end MathlibExtTest.Probability.UnbiasedMMD
