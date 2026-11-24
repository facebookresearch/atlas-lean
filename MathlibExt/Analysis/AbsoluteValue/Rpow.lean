/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Real powers of absolute values

For `0 < c ≤ 1`, the function `x ↦ (v x) ^ c` is again an absolute value.
The triangle inequality follows from monotonicity and subadditivity of `Real.rpow`.
-/

@[expose] public section

namespace AbsoluteValue

variable {R : Type*} [Semiring R]

/-- **Powers of an absolute value.** Let $R$ be a semiring, $v$ a real-valued absolute value
on $R$ and $c$ a real number with $0 < c \le 1$. The $c$-th power of $v$ is the real-valued
absolute value $x \mapsto v(x)^c$ on $R$. -/
noncomputable def rpow (v : AbsoluteValue R ℝ) (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) :
    AbsoluteValue R ℝ where
  toFun x := (v x) ^ c
  map_mul' x y := by
    rw [AbsoluteValue.map_mul v x y,
      Real.mul_rpow (AbsoluteValue.nonneg v x) (AbsoluteValue.nonneg v y)]
  nonneg' x := Real.rpow_nonneg (AbsoluteValue.nonneg v x) c
  eq_zero' x := by
    rw [Real.rpow_eq_zero (AbsoluteValue.nonneg v x) hc₀.ne', AbsoluteValue.eq_zero v]
  add_le' x y := by
    calc
      v (x + y) ^ c ≤ (v x + v y) ^ c :=
        Real.rpow_le_rpow (AbsoluteValue.nonneg v (x + y)) (AbsoluteValue.add_le v x y) hc₀.le
      _ ≤ v x ^ c + v y ^ c :=
        Real.rpow_add_le_add_rpow (AbsoluteValue.nonneg v x) (AbsoluteValue.nonneg v y)
          hc₀.le hc₁

/-- **Values of a power of an absolute value.** Let $R$ be a semiring, $v$ a real-valued
absolute value on $R$ and $c$ a real number with $0 < c \le 1$. The $c$-th power of $v$ takes
the value $v(x)^c$ at every $x \in R$. -/
@[simp]
theorem rpow_apply (v : AbsoluteValue R ℝ) (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (x : R) :
    v.rpow c hc₀ hc₁ x = v x ^ c :=
  rfl

end AbsoluteValue
