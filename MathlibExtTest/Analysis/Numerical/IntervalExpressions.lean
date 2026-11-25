/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.IntervalExpressions
public meta import MathlibExt.Analysis.Numerical.IntervalExpressions

/-!
# Tests for interval expressions

Concrete evaluations over `RatInterval`: a two-variable example, division with
a zero-free denominator (including negative-denominator acceptance), division
by an interval containing zero (not well defined, with zero at either
endpoint), the nested neg-div acceptance and rejection, the dependency witness recomputed,
the asymmetric division value, the magnitude value, and width checks. Also
prints the axioms used by the fundamental theorem, each test, and the
production lemmas.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.Certified

namespace RatInterval

/-- Two-variable evaluation `(x + 1) * (y - 2)` over `x ∈ [0, 1]`, `y ∈ [3, 4]`
has exact interval endpoints `⟨1, 4⟩`. -/
theorem twoVar_evalI :
    (Expr.mul (Expr.add (Expr.var true) (Expr.const 1))
      (Expr.sub (Expr.var false) (Expr.const 2))).evalI
      (fun | true => (⟨0, 1⟩ : RatInterval) | false => ⟨3, 4⟩) = ⟨1, 4⟩ := by
  simp only [Expr.evalI, RatInterval.ofRat, RatInterval.add, RatInterval.sub, RatInterval.mul]
  congr 1 <;> norm_num

/-- The pointwise value of `(x + 1) * (y - 2)` at `x = 1 / 2`, `y = 7 / 2` is
enclosed in the interval evaluation. -/
theorem twoVar_enclosed :
    ((Expr.mul (Expr.add (Expr.var true) (Expr.const 1))
      (Expr.sub (Expr.var false) (Expr.const 2))).evalI
      (fun | true => (⟨0, 1⟩ : RatInterval) | false => ⟨3, 4⟩)).Encloses
      ((Expr.mul (Expr.add (Expr.var true) (Expr.const 1))
        (Expr.sub (Expr.var false) (Expr.const 2))).eval
        (fun | true => (1 / 2 : ℝ) | false => 7 / 2)) := by
  apply Expr.encloses_eval
  · intro a
    cases a <;> simp only [encloses_iff] <;> norm_num
  · rfl

/-- Division `x / y` over `x, y ∈ [1, 2]` has exact endpoints `⟨1 / 2, 2⟩`. -/
theorem divZeroFree_evalI :
    (Expr.div (Expr.var true) (Expr.var false)).evalI
      (fun _ => (⟨1, 2⟩ : RatInterval)) = ⟨1 / 2, 2⟩ := by
  simp only [Expr.evalI, RatInterval.div, RatInterval.inv, RatInterval.mul]
  congr 1 <;> norm_num

/-- Division over the zero-free denominator interval `[1, 2]` is well defined. -/
theorem divZeroFree_wellDefined :
    (Expr.div (Expr.var true) (Expr.var false)).WellDefined
      (fun _ => (⟨1, 2⟩ : RatInterval)) = true := by
  simp only [Expr.WellDefined, Expr.evalI, Bool.and_eq_true]
  norm_num

/-- Division by the interval `[-1, 1]`, which contains zero, is not well
defined. -/
theorem divByZeroInterval_notWellDefined :
    (Expr.div (Expr.const 1) (Expr.var true)).WellDefined
      (fun _ => (⟨-1, 1⟩ : RatInterval)) = false := by
  simp only [Expr.WellDefined, Expr.evalI]
  norm_num

/-- Dependency recomputed: `x - x` over `[0, 1]` has interval value `⟨-1, 1⟩`
of width `2`, while the pointwise value at `1 / 2` is `0`. -/
theorem dependency_recompute :
    (Expr.sub (Expr.var true) (Expr.var true)).evalI
          (fun _ => (⟨0, 1⟩ : RatInterval)) = ⟨-1, 1⟩ ∧
      ((Expr.sub (Expr.var true) (Expr.var true)).evalI
        (fun _ => (⟨0, 1⟩ : RatInterval))).width = 2 ∧
      (Expr.sub (Expr.var true) (Expr.var true)).eval (fun _ => (1 / 2 : ℝ)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Expr.evalI, RatInterval.sub]
    congr 1 <;> norm_num
  · simp only [Expr.evalI, RatInterval.sub, RatInterval.width]
    norm_num
  · simp only [Expr.eval, sub_self]

/-- Width of the concrete sum `[1, 2] + [3, 5]` is `3`. -/
theorem width_sum_concrete :
    ((⟨1, 2⟩ : RatInterval).add ⟨3, 5⟩).width = 3 := by
  simp only [RatInterval.add, RatInterval.width]; norm_num

/-- Concrete instance of `width_mul_le` over `[1, 2]` and `[3, 5]`, with both
sides evaluated (`7 ≤ 9`). -/
theorem width_mul_le_concrete :
    ((⟨1, 2⟩ : RatInterval).mul ⟨3, 5⟩).width ≤
          (⟨1, 2⟩ : RatInterval).mag * (⟨3, 5⟩ : RatInterval).width +
            (⟨3, 5⟩ : RatInterval).mag * (⟨1, 2⟩ : RatInterval).width ∧
      ((⟨1, 2⟩ : RatInterval).mul ⟨3, 5⟩).width = 7 ∧
      (⟨1, 2⟩ : RatInterval).mag * (⟨3, 5⟩ : RatInterval).width +
          (⟨3, 5⟩ : RatInterval).mag * (⟨1, 2⟩ : RatInterval).width = 9 := by
  refine ⟨width_mul_le (I := (⟨1, 2⟩ : RatInterval)) (J := (⟨3, 5⟩ : RatInterval))
    (by norm_num) (by norm_num), ?_, ?_⟩
  · simp only [RatInterval.width, RatInterval.mul]
    norm_num
  · simp only [RatInterval.mag, RatInterval.width]
    norm_num

/-- Division by `[-2, -1]` is well-defined (denominator excludes zero). -/
theorem divNeg_wellDefined :
    (Expr.div (Expr.const 1) (Expr.var true)).WellDefined
      (fun _ => (⟨-2, -1⟩ : RatInterval)) = true := by
  decide

/-- Division by `[0, 1]` is not well-defined (contains zero). -/
theorem divZeroLower_notWellDefined :
    (Expr.div (Expr.const 1) (Expr.var true)).WellDefined
      (fun _ => (⟨0, 1⟩ : RatInterval)) = false := by
  decide

/-- Division by `[-1, 0]` is not well-defined (contains zero). -/
theorem divZeroUpper_notWellDefined :
    (Expr.div (Expr.const 1) (Expr.var true)).WellDefined
      (fun _ => (⟨-1, 0⟩ : RatInterval)) = false := by
  decide

/-- Negation of division by `[-1, 1]` is not well-defined (contains zero). -/
theorem negDivByZeroInterval_notWellDefined :
    (Expr.neg (Expr.div (Expr.const 1) (Expr.var true))).WellDefined
      (fun _ => (⟨-1, 1⟩ : RatInterval)) = false := by
  decide

/-- Asymmetric division `[1, 2] / [4, 8]` evaluates to `[1/8, 1/2]`. -/
theorem divAsym_evalI :
    (Expr.div (Expr.var true) (Expr.var false)).evalI
      (fun b => if b then (⟨1, 2⟩ : RatInterval) else ⟨4, 8⟩) = ⟨1 / 8, 1 / 2⟩ := by
  simp only [Expr.evalI, RatInterval.div, RatInterval.mul, RatInterval.inv]
  norm_num

/-- Magnitude of `[-3, 2]` is `3`. -/
theorem mag_concrete :
    (⟨-3, 2⟩ : RatInterval).mag = 3 := by
  decide

/-- Negation of division by `[1, 2]` is well-defined (zero-free denominator). -/
theorem negDivZeroFree_wellDefined :
    (Expr.neg (Expr.div (Expr.const 1) (Expr.var true))).WellDefined
      (fun _ => (⟨1, 2⟩ : RatInterval)) = true := by decide

#print axioms Expr.encloses_eval
#print axioms twoVar_evalI
#print axioms twoVar_enclosed
#print axioms divZeroFree_evalI
#print axioms divZeroFree_wellDefined
#print axioms divByZeroInterval_notWellDefined
#print axioms dependency_recompute
#print axioms width_sum_concrete
#print axioms width_mul_le_concrete
#print axioms Expr.eval_mem_Icc
#print axioms Expr.sub_self_dependency
#print axioms width_sub
#print axioms width_neg
#print axioms width_add
#print axioms width_mul_le
#print axioms divNeg_wellDefined
#print axioms divZeroLower_notWellDefined
#print axioms divZeroUpper_notWellDefined
#print axioms negDivByZeroInterval_notWellDefined
#print axioms divAsym_evalI
#print axioms mag_concrete
#print axioms negDivZeroFree_wellDefined

end RatInterval

end MathlibExt.Analysis.Numerical.Certified

end
