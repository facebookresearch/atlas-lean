/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.LatticeConstants

/-!
# Tests for renewal lattice constants

Lattice non-vacuity witness: the geometric-type tail `F t = e^{-⌈t⌉}` on the
lattice `ℤ` (span `h = 1`, Cramér root `θ = 1`) has lattice constant `C = 1`;
the scaled tail oscillates with `limsup = 1`, `liminf = e^{-1}` and no limit.
Lattice-support bridge: a point mass at `2` sees `[1/2, ∞)` and `[1, ∞)` alike.
Tilting witness: the defective law `G = ½ δ₁` has Cramér root `θ = log 2`; its
tilt is a probability measure with mean `1`, and the Cramér–Lundberg numerator
is `(1 - ½) / log 2`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace MathlibExtTest.Probability.Renewal.LatticeConstants

open MathlibExt.Probability.Renewal.LatticeConstants

/-! ### Lattice witness `F t = e^{-⌈t⌉}`, `h = 1`, `θ = 1` -/

private lemma step : ∀ t : ℝ, exp (-(⌈t⌉ : ℝ)) = exp (-(⌈(1 : ℝ) * ⌈t / 1⌉⌉ : ℝ)) := by
  intro t
  simp

private lemma lat : Tendsto (fun k : ℕ => exp (1 * (k * 1)) * exp (-(⌈(k : ℝ) * 1⌉ : ℝ)))
    atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr fun k => ?_
  simp only [mul_one, one_mul]
  rw [Int.ceil_natCast, ← exp_add]
  push_cast
  simp

-- Offset `s = 1/2`: the scaled tail tends to `e^{-1/2}` there.
example : Tendsto (fun k : ℕ => exp (1 * (k * 1 - 1 / 2)) * exp (-(⌈(k : ℝ) * 1 - 1 / 2⌉ : ℝ)))
    atTop (𝓝 (exp (-(1 * (1 / 2))) * 1)) :=
  tendsto_scaled_tail_offset (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos step lat
    (by norm_num) (by norm_num)

-- Upper envelope: `limsup = C = 1`.
example : limsup (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop = 1 :=
  limsup_scaled_tail_eq (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos zero_le_one
    (fun _ => (exp_pos _).le) step lat

-- Lower envelope: `liminf = e^{-θ h} C = e^{-1}`.
example : liminf (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop = exp (-(1 * 1)) * 1 :=
  liminf_scaled_tail_eq (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos zero_le_one
    (fun _ => (exp_pos _).le) step lat

-- Dichotomy: no limit over the reals, for any candidate constant.
example (L : ℝ) : ¬ Tendsto (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop (𝓝 L) :=
  not_tendsto_scaled_tail (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos one_pos one_ne_zero step lat L

/-! ### Lattice-support bridge -/

example : Measure.dirac (2 : ℝ) (Ici ((1 : ℝ) / 2)) =
    Measure.dirac (2 : ℝ) (Ici ((1 : ℝ) * ⌈((1 : ℝ) / 2) / 1⌉)) :=
  measure_Ici_eq_measure_Ici_ceil one_pos (by rw [ae_dirac_eq]; exact ⟨2, by norm_num⟩) _

/-! ### Tilting witness `G = ½ δ₁`, `θ = log 2` -/

private lemma root : ∫ y, exp (log 2 * y) ∂((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) = 1 := by
  rw [integral_smul_measure, integral_dirac, mul_one, exp_log two_pos]
  norm_num

-- The tilted law is a probability measure.
example : IsProbabilityMeasure (((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)).tilted
    (fun y => log 2 * y)) :=
  isProbabilityMeasure_tilted_of_integral_eq_one root

-- The tilted law has mean `1`.
example : ∫ y, y ∂(((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)).tilted (fun y => log 2 * y)) = 1 := by
  rw [integral_id_tilt root, integral_smul_measure, integral_dirac, one_mul, mul_one,
    exp_log two_pos]
  norm_num

-- Tilting a renewal equation (here with the trivial solution `Z = z = 0`).
example (t : ℝ) : exp (log 2 * t) * (0 : ℝ) = exp (log 2 * t) * 0 +
    ∫ y, exp (log 2 * (t - y)) * (0 : ℝ)
      ∂(((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)).tilted (fun y => log 2 * y)) :=
  tilted_renewal_eq (Z := fun _ => 0) (z := fun _ => 0) root (fun _ => by simp) t

-- Cramér–Lundberg numerator: `∫_{(0,∞)} 2^s G(s, ∞) ds = (1 - ½) / log 2`.
example : ∫ s in Ioi 0, exp (log 2 * s) * ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)).real (Ioi s) =
    (1 - 1 / 2) / log 2 := by
  have : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    Measure.smul_finite _ (by norm_num)
  rw [integral_exp_mul_measureReal_Ioi (log_pos one_lt_two)
    (Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact zero_le_one) _)
    (integrable_dirac enorm_lt_top |>.smul_measure (by norm_num)), root]
  simp [measureReal_def]

end MathlibExtTest.Probability.Renewal.LatticeConstants
