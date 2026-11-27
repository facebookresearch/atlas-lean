/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Beatty.SelfBetween

/-! # Increments of the α-Beatty counts between complementary endpoints

The count increment between consecutive pairs of complementary endpoints is the β-Beatty
increment minus two.
-/

namespace MetaMathlibExt

open Set

/-- **Increments of the $\alpha$-Beatty counts between $\lfloor n\alpha\rfloor$ and
$\lfloor n\beta\rfloor$.** Let $\beta$ be an irrational number with $\beta > 2$, let $\alpha$ be a
real number with $\alpha^{-1} + \beta^{-1} = 1$, let $A$ be the set of the numbers
$\lfloor k\alpha\rfloor$ for positive integers $k$, and for an integer $m$ let $c(m)$ be the number
of elements of $A$ in the open interval $(\lfloor m\alpha\rfloor, \lfloor m\beta\rfloor)$. Then for
every positive integer $n$, the difference $c(n + 1) - c(n)$ is $\lfloor\beta\rfloor - 2$ or
$\lfloor\beta\rfloor - 1$, and it equals $\lfloor\beta\rfloor - 2$ if and only if
$\lfloor (n + 1)\beta\rfloor - \lfloor n\beta\rfloor = \lfloor\beta\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 5 (`integers-2025-A104-lem-5`). -/
public theorem beatty_card_self_between_succ_sub {α β : ℝ} (hirr : Irrational β)
    (hβ : 2 < β) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let c : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq α k | k > 0}).ncard : ℤ)
    (c (n + 1) - c n = ⌊β⌋ - 2 ∨ c (n + 1) - c n = ⌊β⌋ - 1) ∧
      (c (n + 1) - c n = ⌊β⌋ - 2 ↔ beattySeq β (n + 1) - beattySeq β n = ⌊β⌋) := by
  have hc : β.HolderConjugate α :=
    Real.holderConjugate_iff.mpr ⟨by linarith, by simpa only [add_comm] using hαβ⟩
  have hα2 : α < 2 := by
    rw [hc.conjugate_eq, div_lt_iff₀ hc.sub_one_pos]
    linarith
  have hαirr : Irrational α := by
    apply Irrational.of_inv
    rw [show α⁻¹ = 1 - β⁻¹ by linarith only [hαβ]]
    simpa only [Int.cast_one] using hirr.inv.intCast_sub 1
  have count (m : ℤ) (hm : 0 < m) :
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq α k | k > 0}).ncard : ℤ) =
        beattySeq β m - m * 2 := by
    rw [beatty_card_self_between_eq_floor hαirr hc.symm.lt hα2 hαβ hm]
    simp only [beattySeq, mul_sub]
    rw [← Int.cast_two, ← Int.cast_mul, Int.floor_sub_intCast]
  dsimp only
  rw [count _ (by omega : 0 < n + 1), count _ hn]
  have hstep : ⌊β⌋ ≤ beattySeq β (n + 1) - beattySeq β n ∧
      beattySeq β (n + 1) - beattySeq β n ≤ ⌊β⌋ + 1 := by
    simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
    have hlo := Int.le_floor_add ((n : ℝ) * β) β
    have hhi := Int.le_floor_add_floor ((n : ℝ) * β) β
    omega
  omega

end MetaMathlibExt
