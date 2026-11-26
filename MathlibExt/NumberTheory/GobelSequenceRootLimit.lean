/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelSequenceRoots
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The limit of the normalized Göbel roots

Dividing the Göbel terms by `n + 2` gives a lower comparison whose normalized roots
are nondecreasing from index 4 and start strictly above one.
-/

namespace MetaMathlibExt

open Filter Topology

private theorem gobelSequence_succ_real (k l n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    (gobelSequence k l (n + 1) : ℝ) =
      ((n : ℝ) * (gobelSequence k l n : ℝ) + (gobelSequence k l n : ℝ) ^ k) / (n + 1) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (gobelSequence_succ k l n hn)
  push_cast at h
  rw [mul_add, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k),
    mul_comm (gobelSequence k l n : ℝ) (n : ℝ)] at h
  exact (eq_div_iff (by positivity)).mpr ((mul_comm _ _).trans h)

private theorem ten_le_gobelSequence_four (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    (10 : ℝ) ≤ gobelSequence k l 4 := by
  let g (n : ℕ) : ℝ := gobelSequence k l n
  have step (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 1 ≤ a) (h : a ≤ g n) :
      ((n : ℝ) * a + a ^ 2) / (n + 1) ≤ g (n + 1) := by
    change _ ≤ (gobelSequence k l (n + 1) : ℝ)
    rw [gobelSequence_succ_real k l n hk hn]
    exact div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n))
        ((pow_le_pow_left₀ (zero_le_one.trans ha) h 2).trans
          (pow_le_pow_right₀ (ha.trans h) hk))) (by positivity)
  have h₁ : (2 : ℝ) ≤ g 1 := by
    dsimp [g]
    rw [gobelSequence_one, Rat.cast_natCast]
    exact_mod_cast hl
  have h₂ := step 1 le_rfl 2 (by norm_num) h₁
  norm_num at h₂
  have h₃ := step 2 (by decide) 3 (by norm_num) h₂
  norm_num at h₃
  have h₄ := step 3 (by decide) 5 (by norm_num) h₃
  norm_num at h₄
  exact h₄

/-- **The normalized Göbel roots converge to a limit greater than 1.** Let $k, l \ge 2$ be natural
numbers and let $g_{k,l}$ be the $(k, l)$-Göbel sequence. There is a real number $C > 1$ such
that the real numbers $g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$.

The paper defines $C_{k,l}$ as this limit.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Proposition 10 (`jis-2024-24.8.1-prop-10`). -/
public theorem gobelSequence_root_tendsto_gt_one (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    ∃ C : ℝ, 1 < C ∧
      Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 C) := by
  let g (n : ℕ) : ℝ := gobelSequence k l n
  let u (n : ℕ) : ℝ := g n / ((n : ℝ) + 2)
  let e (n : ℕ) : ℝ := 1 / (k : ℝ) ^ n
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hu₄ : 1 < u 4 := by
    change 1 < g 4 / ((4 : ℝ) + 2)
    rw [lt_div_iff₀ (by positivity)]
    linarith [show (10 : ℝ) ≤ g 4 from ten_le_gobelSequence_four k l hk hl]
  -- The denominator in the power term of the scaled recurrence is at most `(n + 2)^k`.
  have hstep (n : ℕ) (hn : 4 ≤ n) (hg : 0 ≤ g n) : u n ^ k ≤ u (n + 1) := by
    have hscale : ((n : ℝ) + 1) * (n + 3) ≤ ((n : ℝ) + 2) ^ k := calc
      _ ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hk
    change (g n / ((n : ℝ) + 2)) ^ k ≤
      (gobelSequence k l (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) + 2)
    push_cast
    rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring, div_pow,
      gobelSequence_succ_real k l n hk (by omega), div_div]
    exact (div_le_div_of_nonneg_left (pow_nonneg hg _) (by positivity) hscale).trans
      (div_le_div_of_nonneg_right
        (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) hg)) (by positivity))
  have hg_of_hu (n : ℕ) (h : 1 ≤ u n) : 0 ≤ g n :=
    (by positivity : 0 ≤ 1 * ((n : ℝ) + 2)).trans ((le_div_iff₀ (by positivity)).mp h)
  have hu (n : ℕ) (hn : 4 ≤ n) : 1 ≤ u n ∧ u 4 ^ e 4 ≤ u n ^ e n := by
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hu₄.le, le_rfl⟩
    | succ n hn ih =>
      have hu₀ := zero_le_one.trans ih.1
      have hs := hstep n hn (hg_of_hu n ih.1)
      refine ⟨(one_le_pow₀ ih.1).trans hs, ih.2.trans ?_⟩
      calc
        _ = (u n ^ k) ^ e (n + 1) := by
          rw [← Real.rpow_natCast_mul hu₀]
          congr 1
          dsimp [e]
          rw [pow_succ]
          field_simp
        _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hu₀ _) hs (he _).le
  let f (n : ℕ) : ℝ := g (n + 4) ^ e (n + 4)
  have hf : Antitone f := antitone_nat_of_succ_le fun n => by
    simpa only [f, g, e, Nat.add_right_comm] using
      (gobelSequence_root_strictAnti k l (n + 4) hk hl (by omega)).1.le
  have hbound (n : ℕ) : u 4 ^ e 4 ≤ f n := by
    obtain ⟨hu₁, h⟩ := hu (n + 4) (by omega)
    have hu₀ := zero_le_one.trans hu₁
    exact h.trans (Real.rpow_le_rpow hu₀
      (div_le_self (hg_of_hu (n + 4) hu₁)
        (by linarith [Nat.cast_nonneg (α := ℝ) (n + 4)])) (he _).le)
  have hbdd : BddBelow (Set.range f) := ⟨u 4 ^ e 4, Set.forall_mem_range.mpr hbound⟩
  refine ⟨⨅ n, f n, (Real.one_lt_rpow hu₄ (he 4)).trans_le (le_ciInf hbound), ?_⟩
  exact (tendsto_add_atTop_iff_nat 4).mp (tendsto_atTop_ciInf hf hbdd)

end MetaMathlibExt
