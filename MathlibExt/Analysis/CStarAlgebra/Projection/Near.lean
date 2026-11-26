/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Star.Projection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correcting self-adjoint approximate projections

For a complete complex nonunital C-star algebra, the real spectral cutoff
at one half turns a self-adjoint element with defect less than one quarter
into an actual star projection. Its distance from the original element is
at most twice the original idempotence defect. The construction uses the
nonunital functional calculus, so no coefficient unit is supplied.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped CStarAlgebra

namespace CStarAlgebra

/-- **Spectral cutoff at one half.** This real-valued function is zero for `x ≤ 1/2` and one for `x >
1/2`. In particular, it fixes zero. -/
def projectionCut (x : ℝ) : ℝ := if x ≤ 1 / 2 then 0 else 1

@[simp]
theorem projectionCut_zero : projectionCut 0 = 0 := by
  norm_num [projectionCut]

@[simp]
theorem projectionCut_mul_self (x : ℝ) :
    projectionCut x * projectionCut x = projectionCut x := by
  unfold projectionCut
  split_ifs <;> norm_num

/-- **Scalar spectral-cutoff error.** For every real number `x`, the cutoff `χ(x) = 0` for `x ≤ 1/2` and
`χ(x) = 1` for `x > 1/2` satisfies `|χ(x)-x| ≤ 2 |x²-x|`. -/
theorem norm_projectionCut_sub_le (x : ℝ) :
    ‖projectionCut x - x‖ ≤ 2 * ‖x * x - x‖ := by
  by_cases hhalf : x ≤ 1 / 2
  · rw [projectionCut, if_pos hhalf]
    by_cases hx : 0 ≤ x
    · have hdef : x * x - x ≤ 0 := by nlinarith
      simp only [zero_sub, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg hx, abs_of_nonpos hdef]
      nlinarith
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have hdef : 0 ≤ x * x - x := by nlinarith [sq_nonneg x]
      simp only [zero_sub, norm_neg, Real.norm_eq_abs,
        abs_of_nonpos hx', abs_of_nonneg hdef]
      nlinarith [sq_nonneg x]
  · rw [projectionCut, if_neg hhalf]
    have hx : 1 / 2 < x := lt_of_not_ge hhalf
    by_cases hone : x ≤ 1
    · have hsub : 0 ≤ 1 - x := sub_nonneg.mpr hone
      have hdef : x * x - x ≤ 0 := by nlinarith
      simp only [Real.norm_eq_abs, abs_of_nonneg hsub, abs_of_nonpos hdef]
      nlinarith
    · have hone' : 1 ≤ x := le_of_not_ge hone
      have hsub : 1 - x ≤ 0 := sub_nonpos.mpr hone'
      have hdef : 0 ≤ x * x - x := by nlinarith
      simp only [Real.norm_eq_abs, abs_of_nonpos hsub, abs_of_nonneg hdef]
      nlinarith

theorem projectionCut_continuousAt {x : ℝ} (hx : x ≠ 1 / 2) :
    ContinuousAt projectionCut x := by
  by_cases hhalf : x ≤ 1 / 2
  · have hlt : x < 1 / 2 := by
      rcases lt_or_eq_of_le hhalf with hlt | heq
      · exact hlt
      · exact False.elim (hx heq)
    have heq : projectionCut =ᶠ[𝓝 x] (fun _ : ℝ => 0) :=
      (eventually_lt_nhds hlt).mono fun y hy => by simp only [projectionCut, if_pos hy.le]
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr heq.symm
  · have hlt : 1 / 2 < x := lt_of_not_ge hhalf
    have heq : projectionCut =ᶠ[𝓝 x] (fun _ : ℝ => 1) :=
      (eventually_gt_nhds hlt).mono fun y hy => by
        simp only [projectionCut, if_neg (not_le.mpr hy)]
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x).congr heq.symm

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

private theorem cfc_defect (a : A) (ha : IsSelfAdjoint a) :
    cfcₙ (fun x : ℝ => x * x - x) a = a * a - a := by
  rw [cfcₙ_sub (fun x : ℝ => x * x) (fun x : ℝ => x) a,
    cfcₙ_mul (fun x : ℝ => x) (fun x : ℝ => x) a,
    cfcₙ_id' ℝ a ha]

private theorem half_not_mem_quasispectrum (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := by
  intro hhalf
  have hnorm := norm_apply_le_norm_cfcₙ (fun x : ℝ => x * x - x) a hhalf
    ((continuous_id.mul continuous_id).sub continuous_id).continuousOn (by norm_num) ha
  rw [cfc_defect a ha] at hnorm
  norm_num at hnorm
  linarith

private theorem projectionCut_continuousOn_quasispectrum (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn projectionCut (quasispectrum ℝ a) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply projectionCut_continuousAt
  intro h
  exact half_not_mem_quasispectrum a ha hdef (h ▸ hx)

/-- **Nonunital spectral-cutoff value.** For a nonunital complex C*-algebra `A` and `a ∈ A`, this is the
value at `a` of nonunital continuous functional calculus for the real cutoff that is zero at and
below `1/2` and one above `1/2`. When `a` is self-adjoint and `‖a²-a‖ < 1/4`, the cutoff is
continuous on its quasispectrum and gives a projection. -/
def correctedProjectionValue (a : A) : A := cfcₙ projectionCut a

theorem correctedProjectionValue_isStarProjection (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) : IsStarProjection (correctedProjectionValue a) := by
  have hcont := projectionCut_continuousOn_quasispectrum a ha hdef
  refine ⟨?_, ?_⟩
  · change cfcₙ projectionCut a * cfcₙ projectionCut a = cfcₙ projectionCut a
    rw [← cfcₙ_mul projectionCut projectionCut a hcont projectionCut_zero hcont projectionCut_zero]
    congr 1
    funext x
    exact projectionCut_mul_self x
  · exact cfcₙ_predicate (R := ℝ) projectionCut a

theorem norm_correctedProjectionValue_sub_le (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) :
    ‖correctedProjectionValue a - a‖ ≤ 2 * ‖a * a - a‖ := by
  have hcont := projectionCut_continuousOn_quasispectrum a ha hdef
  change ‖cfcₙ projectionCut a - a‖ ≤ _
  have hsub : cfcₙ (fun x : ℝ => projectionCut x - x) a = cfcₙ projectionCut a - a := by
    rw [cfcₙ_sub projectionCut (fun x : ℝ => x) a hcont projectionCut_zero
      continuousOn_id (by rfl), cfcₙ_id' ℝ a ha]
  rw [← hsub]
  apply norm_cfcₙ_le
  intro x hx
  calc
    ‖projectionCut x - x‖ ≤ 2 * ‖x * x - x‖ := norm_projectionCut_sub_le x
    _ ≤ 2 * ‖cfcₙ (fun x : ℝ => x * x - x) a‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_apply_le_norm_cfcₙ (fun x : ℝ => x * x - x) a hx
          ((continuous_id.mul continuous_id).sub continuous_id).continuousOn (by norm_num) ha)
        (by norm_num)
    _ = 2 * ‖a * a - a‖ := by rw [cfc_defect a ha]

/-- **Correcting a nearly idempotent self-adjoint element.** In a nonunital complex C*-algebra `A`, a
self-adjoint `a` with `‖a²-a‖ < 1/4` gives a self-adjoint idempotent by applying the zero-preserving
spectral cutoff at `1/2` through nonunital continuous functional calculus. -/
def correctedProjection (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) : StarProjection A :=
  ⟨correctedProjectionValue a, correctedProjectionValue_isStarProjection a ha hdef⟩

@[simp]
theorem correctedProjection_coe (a : A) (ha : IsSelfAdjoint a)
    (hdef : ‖a * a - a‖ < 1 / 4) :
    (correctedProjection a ha hdef : A) = correctedProjectionValue a := rfl

end CStarAlgebra
