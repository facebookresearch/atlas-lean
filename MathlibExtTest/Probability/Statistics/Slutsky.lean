/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for the product, ratio and scalar-multiple forms of Slutsky's theorem

API-shape tests on `Ω = ℝ` with the standard Gaussian law: `X n := id` converges in distribution
to `Z := id` (a constant sequence), and the deterministic `Y n := c + 1 / (n + 1)` converges in
probability to `c`. Each theorem is applied and its conclusion checked against the expected limit
variable, including the ratio at `c = 2`, the product at the boundary `c = 0`, and a scalar
multiple of a `Fin 2 → ℝ`-valued sequence.

The second limit is always a constant. The theorems make no claim for a random limit of `Y n`:
the marginal laws of `X n` and `Y n` do not determine the joint law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathlibExtTest.Probability.Statistics.Slutsky

/-- The deterministic sequence `c + 1 / (n + 1)` on `ℝ`. -/
noncomputable def Yc (c : ℝ) (n : ℕ) (_ : ℝ) : ℝ := c + 1 / ((n : ℝ) + 1)

/-- `Yc c n` is constant in `ω`, hence measurable. -/
theorem Yc_aemeasurable (c : ℝ) (n : ℕ) : AEMeasurable (Yc c n) (gaussianReal 0 1) :=
  aemeasurable_const

/-- `c + 1 / (n + 1)` converges to `c` in probability under the standard Gaussian. -/
theorem Yc_tendstoInMeasure (c : ℝ) :
    TendstoInMeasure (gaussianReal 0 1) (Yc c) atTop (fun _ ↦ c) := by
  refine tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const) (ae_of_all _ ?_)
  intro _
  simpa [Yc] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add c

/-- The constant sequence `id` converges in distribution to `id` under the standard Gaussian. -/
theorem id_tendstoInDistribution :
    TendstoInDistribution (fun (_ : ℕ) ↦ (id : ℝ → ℝ)) atTop id
      (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  tendstoInDistribution_const aemeasurable_id

/-- `(c + 1 / (n + 1))⁻¹ → c⁻¹` in probability at `c = 2`. -/
example : TendstoInMeasure (gaussianReal 0 1) (fun n ω ↦ (Yc 2 n ω)⁻¹) atTop (fun _ ↦ 2⁻¹) :=
  (Yc_tendstoInMeasure 2).inv_const two_ne_zero

/-- Product form at `c = 2`: `X n * Y n →ᵈ 2 * Z`. -/
example : TendstoInDistribution (fun n ω ↦ id ω * Yc 2 n ω) atTop (fun ω ↦ 2 * id ω)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  id_tendstoInDistribution.mul_of_tendstoInMeasure_const (Yc_tendstoInMeasure 2)
    (Yc_aemeasurable 2)

/-- Product form at the boundary `c = 0`: `X n * Y n →ᵈ 0 * Z`. -/
example : TendstoInDistribution (fun n ω ↦ id ω * Yc 0 n ω) atTop (fun ω ↦ 0 * id ω)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  id_tendstoInDistribution.mul_of_tendstoInMeasure_const (Yc_tendstoInMeasure 0)
    (Yc_aemeasurable 0)

/-- Ratio form at `c = 2`: `X n / Y n →ᵈ Z / 2`. -/
example : TendstoInDistribution (fun n ω ↦ id ω / Yc 2 n ω) atTop (fun ω ↦ id ω / 2)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  id_tendstoInDistribution.div_of_tendstoInMeasure_const two_ne_zero (Yc_tendstoInMeasure 2)
    (Yc_aemeasurable 2)

/-- Sum form (Mathlib's `add_of_tendstoInMeasure_const`) at `c = 2`: `X n + Y n →ᵈ Z + 2`. -/
example : TendstoInDistribution (fun n ↦ id + Yc 2 n) atTop (fun ω ↦ id ω + 2)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  id_tendstoInDistribution.add_of_tendstoInMeasure_const (Yc_tendstoInMeasure 2)
    (Yc_aemeasurable 2)

/-- The diagonal embedding `ℝ → (Fin 2 → ℝ)`. -/
def diag (ω : ℝ) : Fin 2 → ℝ := fun _ ↦ ω

/-- The diagonal embedding is measurable. -/
theorem diag_measurable : Measurable diag := measurable_pi_iff.2 fun _ ↦ measurable_id

/-- Scalar-multiple form for `Fin 2 → ℝ`-valued `X n` at `c = 2`: `Y n • X n →ᵈ 2 • Z`. -/
example : TendstoInDistribution (fun n ω ↦ Yc 2 n ω • diag ω) atTop (fun ω ↦ (2 : ℝ) • diag ω)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  (tendstoInDistribution_const (l := atTop) diag_measurable.aemeasurable
    ).smul_of_tendstoInMeasure_const (Yc_tendstoInMeasure 2) (Yc_aemeasurable 2)

/-- Replacing the limit by a variable with the same law on another space: `id` under the
standard Gaussian becomes the first coordinate under the product of two standard Gaussians. -/
example : TendstoInDistribution (fun (_ : ℕ) ↦ (id : ℝ → ℝ)) atTop (Prod.fst : ℝ × ℝ → ℝ)
    (fun _ ↦ gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  id_tendstoInDistribution.congr_hasLaw HasLaw.id
    ⟨measurable_fst.aemeasurable, by simp [Measure.map_fst_prod]⟩

end MathlibExtTest.Probability.Statistics.Slutsky
