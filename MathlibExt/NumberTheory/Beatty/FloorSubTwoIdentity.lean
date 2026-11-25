/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh

/-! # Polanco's floor identity for `⌊(β - 2) n⌋`

For an irrational `1 < α < 2` and `α⁻¹ + β⁻¹ = 1`, the main result
`beatty_floor_inv_sub_eq_floor_sub_two` is Polanco's identity
`⌊α⁻¹ ⌊nβ⌋⌋ - ⌊α⁻¹ (⌊nα⌋ + 1)⌋ = ⌊(β - 2) n⌋` for positive integers `n`. The two floors on the
left are `⌊nβ⌋ - n` and `n`, which only needs `1 < α`.
-/

namespace MetaMathlibExt

namespace beatty_floor_inv_sub_eq_floor_sub_two

/-- For `1 < α`, the number `α⁻¹ (⌊nα⌋ + 1)` lies in `(n, n + α⁻¹]`, so its floor is `n`. -/
private theorem floor_inv_mul_beattySeq_add_one {α : ℝ} (hα1 : 1 < α) (n : ℤ) :
    ⌊α⁻¹ * ((beattySeq α n + 1 : ℤ) : ℝ)⌋ = n := by
  have hα : 0 < α := one_pos.trans hα1
  have hle := Int.floor_le ((n : ℝ) * α)
  rw [Int.floor_eq_iff, inv_mul_eq_div, le_div_iff₀ hα, div_lt_iff₀ hα]
  push_cast
  refine ⟨(Int.lt_floor_add_one _).le, ?_⟩
  simp only [beattySeq]
  linarith

/-- For conjugate exponents `α` and `β`, the number `α⁻¹ ⌊nβ⌋ = ⌊nβ⌋ - β⁻¹ ⌊nβ⌋` has floor
`⌊nβ⌋ - n`, because `β⁻¹ ⌊nβ⌋` lies in `(n - 1, n]`. -/
private theorem floor_inv_mul_beattySeq {α β : ℝ} (hc : α.HolderConjugate β) (n : ℤ) :
    ⌊α⁻¹ * (beattySeq β n : ℝ)⌋ = beattySeq β n - n := by
  have hβ : 0 < β := hc.symm.pos
  have hβ1 : 1 < β := hc.symm.lt
  have hinv : α⁻¹ = 1 - β⁻¹ := eq_sub_of_add_eq hc.inv_add_inv_eq_one
  have hle : β⁻¹ * (beattySeq β n : ℝ) ≤ n := by
    rw [inv_mul_eq_div, div_le_iff₀ hβ]
    exact Int.floor_le _
  have hlt : (n : ℝ) - 1 < β⁻¹ * (beattySeq β n : ℝ) := by
    rw [inv_mul_eq_div, lt_div_iff₀ hβ]
    have := Int.lt_floor_add_one ((n : ℝ) * β)
    simp only [beattySeq]
    linarith
  rw [Int.floor_eq_iff, hinv]
  push_cast
  constructor <;> linarith

end beatty_floor_inv_sub_eq_floor_sub_two

-- The identity holds for every `α > 1` and every integer `n`: the irrationality of `α`, the bound
-- `α < 2` and the positivity of `n` are kept only to match the source statement.
set_option linter.unusedVariables false in
/-- **Polanco's floor identity for $\lfloor (\beta - 2) n \rfloor$.** Let $\alpha$ be an
irrational real number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and write $a_n = \lfloor n\alpha \rfloor$ and
$b_n = \lfloor n\beta \rfloor$. Then for every positive integer $n$,
$$
\lfloor \alpha^{-1} b_n \rfloor - \lfloor \alpha^{-1} (a_n + 1) \rfloor
= \lfloor (\beta - 2) n \rfloor.
$$

Since $\alpha > 1$, Beatty's theorem says that the conditions "$\alpha$ is irrational and
$\alpha^{-1} + \beta^{-1} = 1$" mean exactly that $(a_n)_{n \ge 1}$ and $(b_n)_{n \ge 1}$ are
complementary Beatty sequences.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (8) (`integers-2025-A104-thm-5`). -/
public theorem beatty_floor_inv_sub_eq_floor_sub_two {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊α⁻¹ * (beattySeq β n : ℝ)⌋ - ⌊α⁻¹ * ((beattySeq α n + 1 : ℤ) : ℝ)⌋ =
      beattySeq (β - 2) n := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  rw [beatty_floor_inv_sub_eq_floor_sub_two.floor_inv_mul_beattySeq hc,
    beatty_floor_inv_sub_eq_floor_sub_two.floor_inv_mul_beattySeq_add_one hα1]
  -- `⌊n (β - 2)⌋ = ⌊nβ - 2n⌋ = ⌊nβ⌋ - 2n`.
  simp only [beattySeq, mul_sub]
  rw [show (n : ℝ) * 2 = ((n * 2 : ℤ) : ℝ) by push_cast; ring, Int.floor_sub_intCast]
  ring

end MetaMathlibExt
