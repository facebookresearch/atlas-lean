/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh

/-! # Polanco's floor identity for `⌊(2 - α) n⌋`

We prove equation (7) of Polanco's Theorem 5 directly from the floor bounds and the relation
`α⁻¹ + β⁻¹ = 1`, rather than using the paper's count of intervening Beatty terms.
-/

namespace MetaMathlibExt

/-- **Polanco's floor identity for $\lfloor (2 - \alpha) n \rfloor$.** Let $\alpha$ be an
irrational real number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and write $a_m = \lfloor m\alpha \rfloor$ and
$b_m = \lfloor m\beta \rfloor$ for integers $m$ (so $b_0 = 0$). Then for every positive
integer $n$,
$$
\lfloor \beta^{-1} (b_{n-1} + 1) \rfloor - \lfloor \beta^{-1} a_n \rfloor
= \lfloor (2 - \alpha) n \rfloor.
$$

Since $\alpha > 1$, Beatty's theorem says that the conditions "$\alpha$ is irrational and
$\alpha^{-1} + \beta^{-1} = 1$" mean exactly that $(a_n)_{n \ge 1}$ and $(b_n)_{n \ge 1}$ are
complementary Beatty sequences.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (7) (`integers-2025-A104-thm-5`). -/
public theorem beatty_floor_inv_sub_eq_floor_two_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊β⁻¹ * ((beattySeq β (n - 1) + 1 : ℤ) : ℝ)⌋ - ⌊β⁻¹ * (beattySeq α n : ℝ)⌋ =
      beattySeq (2 - α) n := by
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  have hβinv : β⁻¹ = 1 - α⁻¹ := eq_sub_of_add_eq hc.symm.inv_add_inv_eq_one
  have hβ2 : 2 < β := by
    have hαinv : (2 : ℝ)⁻¹ < α⁻¹ := (inv_lt_inv₀ (by norm_num) hc.pos).2 hα2
    apply (inv_lt_inv₀ hc.symm.pos (by norm_num)).1
    rw [hβinv]
    norm_num at hαinv ⊢
    linarith
  have hfirst (m : ℤ) : ⌊β⁻¹ * ((beattySeq β m + 1 : ℤ) : ℝ)⌋ = m := by
    rw [Int.floor_eq_iff, inv_mul_eq_div, le_div_iff₀ hc.symm.pos, div_lt_iff₀ hc.symm.pos]
    simp only [Int.cast_add, Int.cast_one, beattySeq]
    exact ⟨(Int.lt_floor_add_one _).le, by linarith [Int.floor_le ((m : ℝ) * β)]⟩
  let a := beattySeq α n
  let δ : ℝ := (n : ℝ) * α - a
  have hδ0 : 0 < δ := by
    apply sub_pos.mpr
    exact (Int.floor_le _).lt_of_ne fun h ↦ (hirr.intCast_mul hn.ne').ne_int a h.symm
  have hδ1 : δ < 1 := by
    have h := Int.lt_floor_add_one ((n : ℝ) * α)
    change (n : ℝ) * α < (a : ℝ) + 1 at h
    exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using h)
  -- The second floor is `a - n` because the remaining term `δ / α` lies in `[0, 1)`.
  have hform : β⁻¹ * (a : ℝ) = (a : ℝ) - n + δ / α := by
    rw [hβinv]
    dsimp only [δ]
    rw [sub_div, mul_div_cancel_right₀ _ hc.pos.ne', div_eq_mul_inv]
    ring
  have hsecond : ⌊β⁻¹ * (a : ℝ)⌋ = a - n := by
    rw [hform, Int.floor_eq_iff, Int.cast_sub]
    have hlo := div_nonneg hδ0.le hc.nonneg
    have hhi := (div_lt_one hc.pos).2 (hδ1.trans hα1)
    constructor <;> linarith
  have hright : beattySeq (2 - α) n = 2 * n - 1 - a := by
    rw [beattySeq, Int.floor_eq_iff]
    push_cast
    dsimp only [δ] at hδ0 hδ1
    constructor <;> linarith
  change _ - ⌊β⁻¹ * (a : ℝ)⌋ = _
  rw [hfirst, hsecond, hright]
  ring

end MetaMathlibExt
