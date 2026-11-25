/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WythoffTerminalPositions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.LinearCombination

/-!
# Golden-ratio formulas for the Wythoff mex sequences

We show that the two mex sequences for Wythoff's game with terminal positions admit
golden-ratio floor formulas with a common bounded integer correction.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace wythoffMex_floor_goldenRatio

local notation "a" => wythoffMexA
local notation "b" => wythoffMexB

private theorem mex_spec (ℓ n : ℕ) :
    ℓ < a ℓ n ∧ (∀ i < n, a ℓ n ≠ a ℓ i ∧ a ℓ n ≠ b ℓ i) ∧
      ∀ m, ℓ < m → (∀ i < n, m ≠ a ℓ i ∧ m ≠ b ℓ i) → a ℓ n ≤ m := by
  let s : Set ℕ := {m | ℓ < m ∧ ∀ i : Fin n, m ≠ a ℓ i ∧ m ≠ b ℓ i}
  have heq : a ℓ n = sInf s := by
    conv_lhs => rw [wythoffMexA]
    rfl
  have hnonempty : s.Nonempty := by
    let M := (Finset.range n).sup (b ℓ)
    refine ⟨ℓ + M + 1, by omega, fun i => ?_⟩
    have hbound : b ℓ i ≤ M := Finset.le_sup (Finset.mem_range.mpr i.isLt)
    have hcomp : b ℓ i = a ℓ i + i + ℓ + 1 := rfl
    constructor <;> omega
  have ha : a ℓ n ∈ s := heq ▸ Nat.sInf_mem hnonempty
  exact ⟨ha.1, fun i hi => ha.2 ⟨i, hi⟩,
    fun m hm havoid => heq.symm ▸ Nat.sInf_le (show m ∈ s from
      ⟨hm, fun i => havoid i i.isLt⟩)⟩

private theorem mex_strictMono (ℓ : ℕ) : StrictMono (a ℓ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨hlevel, hfresh, -⟩ := mex_spec ℓ (n + 1)
  have hle := (mex_spec ℓ n).2.2 _ hlevel (fun i hi => hfresh i (by omega))
  exact lt_of_le_of_ne hle (hfresh n (Nat.lt_succ_self n)).1.symm

private theorem companion_spacing (ℓ : ℕ) {i j : ℕ} (hij : i < j) :
    b ℓ i + 2 ≤ b ℓ j := by
  have h := mex_strictMono ℓ hij
  dsimp only [wythoffMexB]
  omega

-- The first companion term above a(n) can rule out only the immediate successor.
private theorem mex_succ (ℓ n k : ℕ) (hk : k ≤ n)
    (hlo : ∀ i < k, b ℓ i < a ℓ n) (hhi : a ℓ n < b ℓ k) :
    a ℓ (n + 1) = if b ℓ k = a ℓ n + 1 then a ℓ n + 2 else a ℓ n + 1 := by
  have hmono := mex_strictMono ℓ
  have hnext : a ℓ n < a ℓ (n + 1) := hmono (Nat.lt_succ_self n)
  have hmin (m : ℕ) (hm : a ℓ n < m) (hfresh : ∀ i < n + 1, m ≠ b ℓ i) :
      a ℓ (n + 1) ≤ m :=
    (mex_spec ℓ (n + 1)).2.2 m ((mex_spec ℓ n).1.trans hm) fun i hi =>
      ⟨ne_of_gt ((hmono.monotone (Nat.le_of_lt_succ hi)).trans_lt hm), hfresh i hi⟩
  split_ifs with heq
  · have hne := ((mex_spec ℓ (n + 1)).2.1 k (by omega)).2
    apply le_antisymm _ (by omega)
    apply hmin _ (by omega)
    intro i _
    rcases lt_trichotomy i k with hik | rfl | hki
    · have := hlo i hik
      omega
    · omega
    · have := companion_spacing ℓ hki
      omega
  · apply le_antisymm _ (by omega)
    apply hmin _ (by omega)
    intro i _
    rcases lt_trichotomy i k with hik | rfl | hki
    · have := hlo i hik
      omega
    · exact Ne.symm heq
    · have := companion_spacing ℓ hki
      omega

-- The index k counts the companion terms below a(n). It can increase by only one
-- at a mex step, and an increase requires k < n because b(n) is too far ahead.
private theorem mex_count (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∃ k : ℕ, k ≤ n ∧ (0 < n → k < n) ∧ a ℓ n = ℓ + 1 + n + k ∧
      a ℓ n < b ℓ k ∧ ∀ i < k, b ℓ i < a ℓ n := by
  induction n with
  | zero =>
    rw [wythoffMexA_zero]
    exact ⟨0, le_rfl, by omega, by omega, by rw [wythoffMexB_zero]; omega, by omega⟩
  | succ n ih =>
    obtain ⟨k, hk, -, hcount, hhi, hlo⟩ := ih
    have hnext := mex_succ ℓ n k hk hlo hhi
    split_ifs at hnext with heq
    · have hkn : k < n := by
        by_contra! hnk
        obtain rfl : k = n := by omega
        rw [wythoffMexB] at heq
        omega
      have hspacing : b ℓ k + 2 ≤ b ℓ (k + 1) :=
        companion_spacing ℓ (Nat.lt_succ_self k)
      refine ⟨k + 1, by omega, by omega, by omega, by omega, fun i hi => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hik | rfl
      · have := hlo i hik
        omega
      · omega
    · refine ⟨k, by omega, by omega, by omega, by omega, fun i hi => ?_⟩
      have := hlo i hi
      omega

-- Subtract the initial offset and the linear term. The count recurrence relates
-- the error at n to the error at the strictly smaller index k.
private theorem discrepancy (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) :
    |(a ℓ n : ℝ) - ((ℓ : ℝ) + 1) - (n : ℝ) * φ| ≤ φ * (ℓ : ℝ) := by
  let d (i : ℕ) : ℝ := (a ℓ i : ℝ) - ((ℓ : ℝ) + 1) - (i : ℝ) * φ
  change |d n| ≤ φ * (ℓ : ℝ)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      simp [d, wythoffMexA_zero, mul_nonneg Real.goldenRatio_pos.le ℓ.cast_nonneg]
    obtain ⟨k, _, hk, hcount, hhi, hlo⟩ := mex_count ℓ hℓ n
    have hlower : n + 1 ≤ a ℓ k := by
      rw [wythoffMexB] at hhi
      omega
    have hupper : a ℓ k ≤ n + ℓ + 1 := by
      cases k with
      | zero =>
        rw [wythoffMexA_zero]
        omega
      | succ j =>
        have hj := hlo j (Nat.lt_succ_self j)
        rw [wythoffMexB] at hj
        obtain ⟨p, hp, -, -, hhigh, hlow⟩ := mex_count ℓ hℓ j
        have hgap := mex_succ ℓ j p hp hlow hhigh
        split_ifs at hgap <;> omega
    have hresidual : |(a ℓ k : ℝ) - ((ℓ : ℝ) + 1) - (n : ℝ)| ≤ (ℓ : ℝ) := by
      rw [abs_le]
      have hlower' : (n : ℝ) + 1 ≤ (a ℓ k : ℝ) := by exact_mod_cast hlower
      have hupper' : (a ℓ k : ℝ) ≤ (n : ℝ) + ℓ + 1 := by
        exact_mod_cast hupper
      exact ⟨by linarith, by linarith [show (0 : ℝ) ≤ ℓ from ℓ.cast_nonneg]⟩
    have ha : (a ℓ n : ℝ) = (ℓ : ℝ) + 1 + n + k := by exact_mod_cast hcount
    have hrec : φ * d n + d k = (a ℓ k : ℝ) - ((ℓ : ℝ) + 1) - (n : ℝ) := by
      dsimp only [d]
      rw [ha]
      linear_combination -(n : ℝ) * Real.goldenRatio_sq
    have hdk := ih k (hk (Nat.pos_of_ne_zero hn))
    apply (mul_le_mul_iff_right₀ Real.goldenRatio_pos).mp
    calc
      φ * |d n| = |φ * d n| := by rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
      _ = |((a ℓ k : ℝ) - ((ℓ : ℝ) + 1) - (n : ℝ)) - d k| := by
        rw [← hrec, add_sub_cancel_right]
      _ ≤ |(a ℓ k : ℝ) - ((ℓ : ℝ) + 1) - (n : ℝ)| + |d k| := abs_sub _ _
      _ ≤ (ℓ : ℝ) + φ * (ℓ : ℝ) := add_le_add hresidual hdk
      _ = φ * (φ * (ℓ : ℝ)) := by linear_combination -(ℓ : ℝ) * Real.goldenRatio_sq

end wythoffMex_floor_goldenRatio

/-- **Golden-ratio formula for the mex sequences.** Let $\ell \ge 1$, let $\varphi$ be the golden
ratio, let $K^\ell$ be Wythoff's game in which the positions $(x, y)$ with $x + y \le \ell$ are
terminal, and let $(a_n)$ be the mex sequence of $K^\ell$ and $(b_n)$ its companion sequence.
Then there are integers $\lambda_n$ for $n \ge 0$ and an integer $C$ with $|\lambda_n| \le C$
for all $n$ such that, for every natural number $n$,
$a_n = \lfloor (n + \ell)\varphi \rfloor + \lambda_n$ and
$b_n = \lfloor (n + \ell)\varphi^2 \rfloor + \lambda_n + 1$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Corollary 19 (`jis-2026-26.1.6-cor-19`). -/
public theorem wythoffMex_floor_goldenRatio (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ lam : ℕ → ℤ, (∃ C : ℤ, ∀ n, |lam n| ≤ C) ∧ ∀ n,
      (wythoffMexA ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio⌋ + lam n ∧
      (wythoffMexB ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + lam n + 1 := by
  let lam (n : ℕ) : ℤ := (wythoffMexA ℓ n : ℤ) - ⌊((n + ℓ : ℕ) : ℝ) * φ⌋
  refine ⟨lam, ⟨3 * (ℓ : ℤ) + 2, fun n => ?_⟩, fun n => ?_⟩
  · have hd := abs_le.mp (wythoffMex_floor_goldenRatio.discrepancy ℓ hℓ n)
    let x : ℝ := ((n + ℓ : ℕ) : ℝ) * φ
    have hlo := Int.floor_le x
    have hhi := Int.lt_floor_add_one x
    dsimp only [x] at hlo hhi
    push_cast at hlo hhi
    have hmul : φ * (ℓ : ℝ) ≤ 2 * (ℓ : ℝ) :=
      mul_le_mul_of_nonneg_right Real.goldenRatio_lt_two.le ℓ.cast_nonneg
    have hl : |((lam n : ℤ) : ℝ)| ≤ 3 * (ℓ : ℝ) + 2 := by
      simp only [lam, Int.cast_sub, Int.cast_natCast, abs_le]
      push_cast
      constructor <;> linarith [hd.1, hd.2]
    exact_mod_cast hl
  · have hfloor :
        ⌊((n + ℓ : ℕ) : ℝ) * φ ^ 2⌋ = ⌊((n + ℓ : ℕ) : ℝ) * φ⌋ + (n + ℓ : ℕ) := by
      rw [Real.goldenRatio_sq, mul_add, mul_one, ← Int.cast_natCast, Int.floor_add_intCast]
    constructor
    · dsimp only [lam]
      omega
    · rw [hfloor, wythoffMexB]
      dsimp only [lam]
      push_cast
      omega

end MetaMathlibExt
