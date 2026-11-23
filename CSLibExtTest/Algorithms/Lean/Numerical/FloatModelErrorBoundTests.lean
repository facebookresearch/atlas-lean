/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.FloatModel

open Cslib.Algorithms.Lean.FloatingPoint

/-!
# Float model error-bound consumer tests

Value-level statements only: `toRat?` erases signed-zero identity, so
these results claim rational-value bounds and no bit equality.

`add_relative_error` and `mul_relative_error` route through
`abs_fl_sub_le`, not `abs_fl_sub_le_of_isFloatIn`.

`fl 53` has unbounded exponent; the normal-range premise constrains
the exact rational result, not the rounded value.

No runtime, C, CPU, or hardware conformance is claimed.

Zero, subnormal, and overflowing results, and NaN or infinite
operands, lie outside the premises.
-/

namespace Float.Model.ErrorBoundTests

theorem add_relative_error (a b : Float.Model) (x y : Rat)
    (hx : a.toRat? = some x) (hy : b.toRat? = some y)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ |x + y|)
    (hhi : |x + y| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    ∃ r : Rat, (Float.Model.add a b).toRat? = some r ∧
      |r - (x + y)| ≤ (2 : Rat) ^ (-(53 : Int)) * |x + y| := by
  refine ⟨fl 53 (x + y),
    Float.Model.toRat?_add a b x y hx hy hlo hhi, ?_⟩
  exact abs_fl_sub_le (p := 53) (x := x + y)

#print axioms add_relative_error

theorem mul_relative_error (a b : Float.Model) (x y : Rat)
    (hx : a.toRat? = some x) (hy : b.toRat? = some y)
    (hlo : (2 : Rat) ^ (-1022 : Int) ≤ |x * y|)
    (hhi : |x * y| ≤ (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int)) :
    ∃ r : Rat, (Float.Model.mul a b).toRat? = some r ∧
      |r - (x * y)| ≤ (2 : Rat) ^ (-(53 : Int)) * |x * y| := by
  refine ⟨fl 53 (x * y),
    Float.Model.toRat?_mul a b x y hx hy hlo hhi, ?_⟩
  exact abs_fl_sub_le (p := 53) (x := x * y)

#print axioms mul_relative_error

theorem mul_underflow_excluded :
    (Float.Model.ofBits 0x0000000000000001).toRat? =
      some ((2 : Rat) ^ (-1074 : Int)) ∧
    (Float.Model.ofBits 0x3fe0000000000000).toRat? =
      some ((2 : Rat) ^ (-1 : Int)) ∧
    |((2 : Rat) ^ (-1075 : Int))| ≤
      (2 ^ 53 - 1) * (2 : Rat) ^ (971 : Int) ∧
    ¬ ((2 : Rat) ^ (-1022 : Int) ≤ |((2 : Rat) ^ (-1075 : Int))|) ∧
    (Float.Model.mul (Float.Model.ofBits 0x0000000000000001)
      (Float.Model.ofBits 0x3fe0000000000000)).toRat? = some 0 ∧
    (¬ ∃ r : Rat, (Float.Model.mul (Float.Model.ofBits 0x0000000000000001)
        (Float.Model.ofBits 0x3fe0000000000000)).toRat? = some r ∧
      |r - (2 : Rat) ^ (-1075 : Int)| ≤
        (2 : Rat) ^ (-(53 : Int)) * |(2 : Rat) ^ (-1075 : Int)|) ∧
    (Float.Model.mul (Float.Model.ofBits 0x0000000000000001)
      (Float.Model.ofBits 0x3fe0000000000000)).toRat? ≠
      some (fl 53 ((2 : Rat) ^ (-1075 : Int))) := by
  have h5 : (Float.Model.mul (Float.Model.ofBits 0x0000000000000001)
      (Float.Model.ofBits 0x3fe0000000000000)).toRat? = some 0 := by
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact h5
  · intro h
    obtain ⟨r, hr, hle⟩ := h
    rw [h5] at hr
    simp at hr
    subst hr
    have hfalse : ¬ (|(0 : Rat) - (2 : Rat) ^ (-1075 : Int)| ≤
      (2 : Rat) ^ (-(53 : Int)) * |(2 : Rat) ^ (-1075 : Int)|) := by
      decide +kernel
    exact hfalse hle
  · have hfl : fl 53 ((2 : Rat) ^ (-1075 : Int)) =
        (2 : Rat) ^ (-1075 : Int) := by
      apply fl_eq_self
      · decide
      · refine ⟨1, -1075, by decide, by simp⟩
    rw [h5, hfl]
    decide +kernel

#print axioms mul_underflow_excluded

theorem add_tie_relative_error :
    ∃ r : Rat, (Float.Model.add (Float.Model.ofBits 0x3ff0000000000001)
      (Float.Model.ofBits 0x3ca0000000000000)).toRat? = some r ∧
      |r - ((4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int) +
        (2 : Rat) ^ (-53 : Int))| ≤
        (2 : Rat) ^ (-(53 : Int)) *
          |(4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int) +
            (2 : Rat) ^ (-53 : Int)| :=
  add_relative_error (Float.Model.ofBits 0x3ff0000000000001)
    (Float.Model.ofBits 0x3ca0000000000000)
    ((4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int))
    ((2 : Rat) ^ (-53 : Int))
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

#print axioms add_tie_relative_error

theorem mul_tie_relative_error :
    ∃ r : Rat, (Float.Model.mul (Float.Model.ofBits 0x3ff8000000000000)
      (Float.Model.ofBits 0x3ff0000000000001)).toRat? = some r ∧
      |r - ((3/2 : Rat) *
        ((4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int)))| ≤
        (2 : Rat) ^ (-(53 : Int)) *
          |(3/2 : Rat) *
            ((4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int))| :=
  mul_relative_error (Float.Model.ofBits 0x3ff8000000000000)
    (Float.Model.ofBits 0x3ff0000000000001) (3/2 : Rat)
    ((4503599627370497 : Rat) * (2 : Rat) ^ (-52 : Int))
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

#print axioms mul_tie_relative_error

end Float.Model.ErrorBoundTests
