/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.InfiniteWord.Gutkovskiy
public import MathlibExt.Combinatorics.InfiniteWord.KimberlingBlock
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Closed form for Gutkovskiy's sequence

We prove Shallit's two floor formulas by tracking the effect of adjoining a digit to a
Kimberling representation and bounding the error in the resulting linear approximation.
-/

namespace MetaMathlibExt

namespace GutkovskiyFloor

private theorem le_succ (k : ℕ) : gutkovskiy k ≤ gutkovskiy (k + 1) := by
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add k
  have h' := gutkovskiy_eq_two_mul_sum_mod_two_add (k + 1)
  rw [Finset.sum_range_succ] at h'
  omega

-- Starting from the even value at t = 2k + g(k), the next two recurrence
-- calls both read g(k).
private theorem at_digit_of_even (k : ℕ)
    (h : gutkovskiy (2 * k + gutkovskiy k) = 2 * k) (d : ℕ) (hd : d ≤ 2) :
    gutkovskiy (2 * k + gutkovskiy k + d) = 2 * k + d := by
  let t := 2 * k + gutkovskiy k
  change gutkovskiy t = 2 * k at h
  have h₁ : gutkovskiy (t + 1) = 2 * k + 1 := by
    rw [gutkovskiy_succ, h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    dsimp [t]
    omega
  have h₂ : gutkovskiy (t + 2) = 2 * k + 2 := by
    rw [gutkovskiy_succ (t + 1), h₁, show (2 * k + 1) / 2 = k by omega]
    dsimp [t]
    omega
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
  · exact h
  · exact h₁
  · exact h₂

private theorem at_digit (k d : ℕ) (hd : d ≤ 2) :
    gutkovskiy (2 * k + gutkovskiy k + d) = 2 * k + d := by
  apply at_digit_of_even k _ d hd
  induction k with
  | zero => rfl
  | succ k ih =>
    let t := 2 * k + gutkovskiy k
    have h₂ : gutkovskiy (t + 2) = 2 * k + 2 := at_digit_of_even k ih 2 le_rfl
    have h₃ : gutkovskiy (t + 3) = t + 3 - gutkovskiy (k + 1) := by
      rw [gutkovskiy_succ (t + 2), h₂, show (2 * k + 2) / 2 = k + 1 by omega]
    -- Monotonicity at t+2 forces g(k+1) to be at most g(k)+1.
    have hm : gutkovskiy (t + 2) ≤ gutkovskiy (t + 3) := le_succ (t + 2)
    rw [h₂, h₃] at hm
    have hi := le_succ k
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [show 2 * (k + 1) + gutkovskiy (k + 1) = t + 2 by dsimp [t]; omega, h₂]
      omega
    · have hinc : gutkovskiy (k + 1) = gutkovskiy k + 1 := by dsimp [t] at hm; omega
      rw [show 2 * (k + 1) + gutkovskiy (k + 1) = t + 3 by dsimp [t]; omega, h₃, hinc]
      dsimp [t]
      omega

-- The value at offset j assigns the weight |K_{i+j}| to digit i.
private def value (a : List ℕ) (j : ℕ) : ℕ :=
  (a.mapIdx fun i d ↦ d * (kimberlingBlock (i + j)).length).sum

private theorem value_cons (d : ℕ) (a : List ℕ) (j : ℕ) :
    value (d :: a) j = d * (kimberlingBlock j).length + value a (j + 1) := by
  simp [value, List.mapIdx_cons, Nat.succ_add, Nat.add_assoc]

private theorem value_recurrence (a : List ℕ) (j : ℕ) :
    value a (j + 2) = 2 * value a (j + 1) + 2 * value a j := by
  induction a generalizing j with
  | nil => rfl
  | cons d a ih =>
    have h := congrArg List.length (kimberlingBlock_eq_append (n := j + 2) (by omega))
    simp only [Nat.add_sub_cancel, Nat.add_one_sub_one, List.length_append] at h
    simp only [value_cons]
    rw [h, ih (j + 1)]
    ring

private theorem value_cons_zero (d : ℕ) (a : List ℕ) :
    value (d :: a) 0 = d + value a 1 := by
  rw [value_cons, show (kimberlingBlock 0).length = 1 from rfl, Nat.mul_one]

-- Shifting all the digits one place sends k to 2k + g(k).
private theorem shift (a : List ℕ) (ha : ∀ d ∈ a, d ≤ 2) :
    value a 1 = 2 * value a 0 + gutkovskiy (value a 0) := by
  induction a with
  | nil => rfl
  | cons d a ih =>
    obtain ⟨hd, htail⟩ := List.forall_mem_cons.mp ha
    have hs := ih htail
    have hg : gutkovskiy (d + value a 1) = 2 * value a 0 + d := by
      rw [Nat.add_comm, hs]
      exact at_digit _ _ hd
    rw [value_cons d a 1, show (kimberlingBlock 1).length = 3 from rfl, value_cons_zero,
      value_recurrence a 0, Nat.zero_add, hg]
    ring

-- Multiplying the shifted value by α almost recovers the unshifted value.
-- Each new digit multiplies the previous error by 1 - √3 and adds a digit-dependent offset.
private noncomputable def error (a : List ℕ) : ℝ :=
  (√3 - 1) / 2 * value a 1 - value a 0

private theorem error_cons (d : ℕ) (a : List ℕ) :
    error (d :: a) = (3 * ((√3 - 1) / 2) - 1) * d - (√3 - 1) * error a := by
  unfold error
  rw [value_cons d a 1, show (kimberlingBlock 1).length = 3 from rfl,
    value_recurrence a 0, value_cons_zero]
  push_cast
  linear_combination (value a 1 : ℝ) / 2 * Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem error_bounds (a : List ℕ) (ha : ∀ d ∈ a, d ≤ 2) :
    2 - 4 * √3 / 3 < error a ∧ error a < 1 - √3 / 3 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hlo : 5 / 3 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  have hhi : √3 < 2 := by nlinarith
  induction a with
  | nil =>
    simp [error, value]
    constructor <;> linarith
  | cons d a ih =>
    obtain ⟨hd, htail⟩ := List.forall_mem_cons.mp ha
    obtain ⟨hl, hu⟩ := ih htail
    rw [error_cons]
    have hr : 0 < √3 - 1 := by linarith
    have hc : 0 ≤ 3 * ((√3 - 1) / 2) - 1 := by linarith
    have hd' : (d : ℝ) ≤ 2 := by exact_mod_cast hd
    constructor
    · nlinarith only [hsq, mul_lt_mul_of_pos_left hu hr, mul_nonneg hc (Nat.cast_nonneg d)]
    · nlinarith only [hsq, mul_lt_mul_of_pos_left hl hr, mul_le_mul_of_nonneg_left hd' hc]

end GutkovskiyFloor

open GutkovskiyFloor

/-- **Closed form for Gutkovskiy's sequence.** Let $g_0, g_1, \dots$ be Gutkovskiy's sequence,
let $|K_i|$ be the length of the Kimberling block $K_i$, and let $\alpha = (\sqrt{3} - 1)/2$ and
$\beta = \sqrt{3}/3$. Let $n$ be a natural number and let $a_0, a_1, \dots, a_{m-1}$ be digits in
$\{0, 1, 2\}$ such that no two consecutive digits $a_i, a_{i+1}$ are both $2$ and
$n = \sum_{i < m} a_i |K_i|$. If $m \ge 1$ and $a_0 = 1$, then
$g_n = 2\lfloor \alpha n \rfloor + 1$; if $m \ge 1$ and $a_0 \in \{0, 2\}$, then
$g_n = 2\lfloor \alpha n + \beta \rfloor$.

Written most significant digit first, $a_{m-1} \cdots a_1 a_0$ is a $K$-representation of $n$
ending in the digit $a_0$; leading zeros are allowed.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 2 (`integers-2024-A51-thm-2`). -/
public theorem gutkovskiy_eq_two_mul_floor {n : ℕ} {a : List ℕ} (ha : ∀ d ∈ a, d ≤ 2)
    (h22 : ¬ [2, 2] <:+: a)
    (hn : (a.mapIdx fun i d ↦ d * (kimberlingBlock i).length).sum = n) :
    (a.head? = some 1 → (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ)⌋ + 1) ∧
      (a.head? = some 0 ∨ a.head? = some 2 →
        (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ) + √3 / 3⌋) := by
  cases a with
  | nil => simp
  | cons d a =>
    obtain ⟨hd, htail⟩ := List.forall_mem_cons.mp ha
    have hn' : value (d :: a) 0 = n := by simpa [value] using hn
    rw [value_cons_zero] at hn'
    have hg : gutkovskiy n = 2 * value a 0 + d := by
      rw [← hn', Nat.add_comm, shift a htail]
      exact at_digit _ _ hd
    have he : (√3 - 1) / 2 * n =
        value a 0 + error a + (√3 - 1) / 2 * d := by
      rw [← hn', Nat.cast_add]
      unfold error
      ring
    obtain ⟨hl, hu⟩ := error_bounds a htail
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs : √3 < 9 / 5 := by nlinarith
    simp only [List.head?_cons, Option.some.injEq, hg, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, he]
    constructor
    · rintro rfl
      have hf : ⌊(value a 0 : ℝ) + error a + (√3 - 1) / 2 * 1⌋ = (value a 0 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        push_cast
        constructor <;> linarith
      simpa using congrArg (fun x : ℤ ↦ 2 * x + 1) hf.symm
    · intro hdigit
      have hf : ⌊(value a 0 : ℝ) + error a + (√3 - 1) / 2 * d + √3 / 3⌋ =
          (value a 0 : ℤ) + (d : ℤ) / 2 := by
        apply Int.floor_eq_iff.mpr
        rcases hdigit with rfl | rfl <;> norm_num <;> constructor <;> linarith
      rw [hf]
      rcases hdigit with rfl | rfl <;> omega

end MetaMathlibExt
