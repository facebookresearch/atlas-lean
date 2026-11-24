/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fisher's sex-ratio principle

The Shaw-Mohler invasion fitness of a mutant parent with son fraction `x` in a population with
son fraction `y` is, up to the positive factor `1/4`,
`W x y = x / y + (1 - x) / (1 - y)`.

At the resident ratio `1/2`, every mutant has the same fitness. The selection gradient
`1/y - 1/(1-y)` is positive below `1/2`, negative above it, and zero only at `1/2`; `1/2` is
the unique uninvadable resident ratio. With unequal costs of sons and daughters, equal
investment still gives the stable investment fraction, while the resulting son fraction is
biased toward the cheaper sex.

## References

* M. Burd, "Why the Shaw–Mohler equation works and when it doesn't", *Proceedings of the
  Royal Society B* (2024).
* M. Mesterton-Gibbons, *Biocalculus*, Lecture 17, "Sex allocation and the product rule".
-/

@[expose] public section

open Set

namespace MathlibExt.Biology.PopulationGenetics.Classical.SexRatio

/-- Shaw–Mohler invasion fitness (up to the factor `1/4`) of a mutant with son fraction `x` in a
population with son fraction `y`. -/
noncomputable def W (x y : ℝ) : ℝ := x / y + (1 - x) / (1 - y)

/-- Neutrality at `1/2`: every mutant has the same fitness when the population ratio is `1/2`. -/
theorem W_half_right (x : ℝ) : W x (1 / 2) = 2 := by
  unfold W; ring

/-- Fitness advantage of a mutant over the resident. -/
theorem W_sub_W_self {x y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    W x y - W y y = (x - y) * (1 - 2 * y) / (y * (1 - y)) := by
  have h1 : (1 - y) ≠ 0 := by linarith
  unfold W
  field_simp
  ring

/-- Selection gradient: `∂W/∂x (x, y) = 1/y - 1/(1-y)`, independent of `x`. -/
theorem hasDerivAt_W_left (x y : ℝ) : HasDerivAt (fun x => W x y) (1 / y - 1 / (1 - y)) x := by
  have h : HasDerivAt (fun x => x / y + (1 - x) / (1 - y)) (1 / y + (0 - 1) / (1 - y)) x :=
    ((hasDerivAt_id' x).div_const y).add
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).div_const (1 - y))
  change HasDerivAt (fun x => x / y + (1 - x) / (1 - y)) _ x
  convert h using 1
  ring

/-- Convergence stability: the gradient is positive below `1/2` and negative above. -/
theorem gradient_pos {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 2) : 0 < 1 / y - 1 / (1 - y) := by
  rw [sub_pos]
  exact one_div_lt_one_div_of_lt hy0 (by linarith)

theorem gradient_neg {y : ℝ} (hy : 1 / 2 < y) (hy1 : y < 1) : 1 / y - 1 / (1 - y) < 0 := by
  rw [sub_neg]
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

theorem gradient_eq_zero_iff (y : ℝ) : 1 / y - 1 / (1 - y) = 0 ↔ y = 1 / 2 := by
  rw [sub_eq_zero, one_div, one_div, inv_eq_iff_eq_inv, inv_inv]
  constructor <;> intro h <;> linarith

/-- Evolutionary stability of `1/2` (playing the field): if a fraction `ε ∈ (0, 1]` of the
population switches to any other son fraction `x ∈ (0, 1)`, the resulting population ratio
`z = (1 - ε)/2 + ε x` gives the `1/2` strategy strictly higher fitness than the mutant. -/
theorem W_lt_W_half {x ε : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hx : x ≠ 1 / 2) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    W x ((1 - ε) * (1 / 2) + ε * x) < W (1 / 2) ((1 - ε) * (1 / 2) + ε * x) := by
  set z := (1 - ε) * (1 / 2) + ε * x with hz
  have hz0 : 0 < z := by nlinarith
  have hz1 : z < 1 := by nlinarith
  have hd : W (1 / 2) z - W x z = 2 * ε * (x - 1 / 2) ^ 2 / (z * (1 - z)) := by
    have h1 : (1 - z) ≠ 0 := by linarith
    unfold W
    field_simp
    rw [hz]
    ring
  have hpos : 0 < 2 * ε * (x - 1 / 2) ^ 2 / (z * (1 - z)) := by
    have : 0 < (x - 1 / 2) ^ 2 := by
      have : x - 1 / 2 ≠ 0 := sub_ne_zero.2 hx
      positivity
    have h1z : 0 < 1 - z := by linarith
    positivity
  linarith

/-- Uniqueness: every other resident ratio `y ∈ (0, 1)` can be invaded. -/
theorem exists_W_self_lt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hy : y ≠ 1 / 2) :
    ∃ x ∈ Ioo (0 : ℝ) 1, W y y < W x y := by
  refine ⟨(y + 1 / 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  have h := W_sub_W_self (x := (y + 1 / 2) / 2) hy0 hy1
  have hne : 1 - 2 * y ≠ 0 := fun h0 => hy (by linarith)
  have hpos : 0 < ((y + 1 / 2) / 2 - y) * (1 - 2 * y) / (y * (1 - y)) := by
    have : ((y + 1 / 2) / 2 - y) * (1 - 2 * y) = (1 - 2 * y) ^ 2 / 4 := by ring
    rw [this]
    have h1y : 0 < 1 - y := by linarith
    positivity
  linarith

/-- `1/2` is the unique uninvadable resident son fraction in `(0, 1)`. -/
theorem forall_W_le_iff {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    (∀ x ∈ Ioo (0 : ℝ) 1, W x y ≤ W y y) ↔ y = 1 / 2 := by
  constructor
  · intro h
    by_contra hy
    obtain ⟨x, hx, hlt⟩ := exists_W_self_lt hy0 hy1 hy
    exact (h x hx).not_gt hlt
  · rintro rfl x _
    rw [W_half_right, W_half_right]

/-! ### Unequal costs of sons and daughters -/

/-- Fitness of a parent investing a fraction `r'` of its resources in sons, sons costing `cs`
and daughters `cd`, in a population investing `r`: sons and daughters counted relative to the
population. -/
noncomputable def Wcost (cs cd r' r : ℝ) : ℝ :=
  (r' / cs) / (r / cs) + ((1 - r') / cd) / ((1 - r) / cd)

/-- The son fraction among offspring produced by investing a fraction `r` in sons. -/
noncomputable def sonFraction (cs cd r : ℝ) : ℝ := (r / cs) / (r / cs + (1 - r) / cd)

/-- With costs, the Shaw–Mohler fitness in investment fractions is `W`, so the stable
investment is `1/2` by `forall_W_le_iff`. -/
theorem Wcost_eq (cs cd r' r : ℝ) (hcs : cs ≠ 0) (hcd : cd ≠ 0) : Wcost cs cd r' r = W r' r := by
  unfold Wcost W
  rw [div_div_div_cancel_right₀ hcs, div_div_div_cancel_right₀ hcd]

/-- Equal investment `r = 1/2` gives the son fraction `cd / (cs + cd)`: the ratio is biased
towards the cheaper sex. -/
theorem sonFraction_half {cs cd : ℝ} (hcs : 0 < cs) (hcd : 0 < cd) :
    sonFraction cs cd (1 / 2) = cd / (cs + cd) := by
  unfold sonFraction
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.Classical.SexRatio
