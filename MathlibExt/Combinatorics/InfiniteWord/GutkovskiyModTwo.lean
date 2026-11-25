/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.Gutkovskiy
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord
import Mathlib.Tactic.IntervalCases

/-! # Gutkovskiy's sequence modulo 2 as a morphic word

This module proves that the infinite word $(g_n \bmod 2)_{n \ge 0}$ is the
limit of the iterates of the morphism $0 \mapsto 01$, $1 \mapsto 0010$ at
the letter $0$.
-/

namespace MetaMathlibExt

@[expose] public section

namespace IsOmegaLimitGutkovskiyModTwo

/-- Monotonicity of Gutkovskiy's sequence, from its parity-sum formula. -/
private theorem le_succ (k : ℕ) : gutkovskiy k ≤ gutkovskiy (k + 1) := by
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add k
  have h' := gutkovskiy_eq_two_mul_sum_mod_two_add (k + 1)
  rw [Finset.sum_range_succ] at h'
  omega

/-- Successive terms of Gutkovskiy's sequence differ by at most one. -/
private theorem step (n : ℕ) :
    gutkovskiy n ≤ gutkovskiy (n + 1) ∧ gutkovskiy (n + 1) ≤ gutkovskiy n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [gutkovskiy_initial.1, gutkovskiy_initial.2.1]
    | succ n =>
      have hprev := ih n (by omega)
      let i := gutkovskiy n / 2
      let j := gutkovskiy (n + 1) / 2
      have hij : i ≤ j ∧ j ≤ i + 1 := by dsimp [i, j]; omega
      have hi : i ≤ n := (Nat.div_le_self _ _).trans (gutkovskiy_le n)
      have hj : j ≤ n + 1 := (Nat.div_le_self _ _).trans (gutkovskiy_le (n + 1))
      have hgi := (gutkovskiy_le i).trans hi
      have hgj := (gutkovskiy_le j).trans hj
      have h₁ : gutkovskiy (n + 1) = n + 1 - gutkovskiy i := gutkovskiy_succ n
      have h₂ : gutkovskiy (n + 2) = n + 2 - gutkovskiy j := gutkovskiy_succ (n + 1)
      by_cases heq : i = j
      · rw [← heq] at h₂
        change gutkovskiy (n + 1) ≤ gutkovskiy (n + 2) ∧
          gutkovskiy (n + 2) ≤ gutkovskiy (n + 1) + 1
        omega
      · have hnext : j = i + 1 := by omega
        have hgap := ih i (by omega)
        rw [hnext] at h₂
        change gutkovskiy (n + 1) ≤ gutkovskiy (n + 2) ∧
          gutkovskiy (n + 2) ≤ gutkovskiy (n + 1) + 1
        omega

/-- Starting from the even value at `2 * k + gutkovskiy k`, the next two
recurrence calls both read `gutkovskiy k`. -/
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

/-- The values of Gutkovskiy's sequence at the three positions starting
at `2 * k + gutkovskiy k`. -/
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

/-- The sum of the parities before `m` is the half of `gutkovskiy m`. -/
private theorem sum_mod_two_eq (m : ℕ) :
    ∑ i ∈ Finset.range m, gutkovskiy i % 2 = gutkovskiy m / 2 := by
  have h := gutkovskiy_eq_two_mul_sum_mod_two_add m
  have hp : gutkovskiy m % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

/-- Each block of the morphism, read in Gutkovskiy's parities. -/
private theorem block (i j : ℕ) (hj : j < 2 + 2 * (gutkovskiy i % 2)) :
    (if gutkovskiy i % 2 = 0 then [0, 1] else [0, 0, 1, 0]).getD j 0 =
      gutkovskiy (2 * i + 2 * (gutkovskiy i / 2) + j) % 2 := by
  have hp : gutkovskiy i % 2 = 0 ∨ gutkovskiy i % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases hp with hp | hp
  · simp only [hp, ite_true]
    have hj' : j < 2 := by omega
    interval_cases j
    · have h := at_digit i 0 (by decide)
      rw [show 2 * i + 2 * (gutkovskiy i / 2) + 0 = 2 * i + gutkovskiy i + 0 by omega, h]
      change (0 : ℕ) = (2 * i + 0) % 2
      omega
    · have h := at_digit i 1 (by decide)
      rw [show 2 * i + 2 * (gutkovskiy i / 2) + 1 = 2 * i + gutkovskiy i + 1 by omega, h]
      change (1 : ℕ) = (2 * i + 1) % 2
      omega
  · rw [ite_eq_right (by omega : ¬ gutkovskiy i % 2 = 0)]
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd hp (by decide)
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hj' : j < 4 := by omega
    have hdiff : gutkovskiy (k + 1) = gutkovskiy k + 1 := by
      have h₀ := gutkovskiy_eq_two_mul_sum_mod_two_add k
      have h₁ := gutkovskiy_eq_two_mul_sum_mod_two_add (k + 1)
      rw [Finset.sum_range_succ] at h₁
      have hstep := step k
      have hpk : gutkovskiy k % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    interval_cases j
    · have h := at_digit k 2 le_rfl
      have hEq : 2 * (k + 1) + 2 * (gutkovskiy (k + 1) / 2) + 0 =
          2 * k + gutkovskiy k + 2 := by omega
      rw [hEq, h]
      change (0 : ℕ) = (2 * k + 2) % 2
      omega
    · have h := at_digit (k + 1) 0 (by decide)
      have hEq : 2 * (k + 1) + 2 * (gutkovskiy (k + 1) / 2) + 1 =
          2 * (k + 1) + gutkovskiy (k + 1) + 0 := by omega
      rw [hEq, h]
      change (0 : ℕ) = (2 * (k + 1) + 0) % 2
      omega
    · have h := at_digit (k + 1) 1 (by decide)
      have hEq : 2 * (k + 1) + 2 * (gutkovskiy (k + 1) / 2) + 2 =
          2 * (k + 1) + gutkovskiy (k + 1) + 1 := by omega
      rw [hEq, h]
      change (1 : ℕ) = (2 * (k + 1) + 1) % 2
      omega
    · have h := at_digit (k + 1) 2 le_rfl
      have hEq : 2 * (k + 1) + 2 * (gutkovskiy (k + 1) / 2) + 3 =
          2 * (k + 1) + gutkovskiy (k + 1) + 2 := by omega
      rw [hEq, h]
      change (0 : ℕ) = (2 * (k + 1) + 2) % 2
      omega

/-- The total length of the first `m` blocks. -/
private theorem sum_length_eq (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 + 2 * (gutkovskiy i % 2)) =
      2 * m + 2 * (gutkovskiy m / 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h₁ := sum_mod_two_eq m
    have h₂ := sum_mod_two_eq (m + 1)
    rw [Finset.sum_range_succ] at h₂
    omega

/-- Extending a prefix of parities by one morphism step. -/
private theorem flatMap_map_range (m : ℕ) :
    ((List.range m).map (fun i => gutkovskiy i % 2)).flatMap
        (fun b : ℕ => if b = 0 then [0, 1] else [0, 0, 1, 0]) =
      (List.range (∑ i ∈ Finset.range m, (2 + 2 * (gutkovskiy i % 2)))).map
        (fun i => gutkovskiy i % 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfu : (if gutkovskiy m % 2 = 0 then [0, 1] else [0, 0, 1, 0]) =
        (List.range (2 + 2 * (gutkovskiy m % 2))).map
          (fun j => gutkovskiy (∑ i ∈ Finset.range m, (2 + 2 * (gutkovskiy i % 2)) + j) % 2) := by
      have hlen : (2 + 2 * (gutkovskiy m % 2)) =
          (if gutkovskiy m % 2 = 0 then [0, 1] else [0, 0, 1, 0]).length := by
        rcases Nat.mod_two_eq_zero_or_one (gutkovskiy m) with h | h <;> simp [h]
      refine List.ext_getElem (by rw [← hlen]; simp) fun j h₁ h₂ => ?_
      rw [← hlen] at h₁
      have hb := block m j h₁
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getElem_eq_getD, sum_length_eq]
      exact hb
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      Finset.sum_range_succ, List.range_add, List.map_append]
    simp only [List.map_singleton, List.flatMap_singleton, List.map_map,
      Function.comp_def]
    rw [hfu]

/-- Every iterate is a prefix of the parity word, of length at least `2 ^ n`. -/
private theorem iterate_eq (n : ℕ) :
    ∃ m : ℕ, morphIterate (fun b : ℕ => if b = 0 then [0, 1] else [0, 0, 1, 0]) n [0] =
      (List.range m).map (fun i => gutkovskiy i % 2) ∧ 2 ^ n ≤ m := by
  induction n with
  | zero => exact ⟨1, by rfl, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, hbound⟩ := ih
    refine ⟨∑ i ∈ Finset.range m, (2 + 2 * (gutkovskiy i % 2)), ?_, ?_⟩
    · rw [morphIterate, hm, morphExtend]
      exact flatMap_map_range m
    · have hge : 2 * m ≤ ∑ i ∈ Finset.range m, (2 + 2 * (gutkovskiy i % 2)) := by
        rw [sum_length_eq]
        omega
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
        _ ≤ 2 * m := by omega
        _ ≤ _ := hge

end IsOmegaLimitGutkovskiyModTwo

/-- **Gutkovskiy's sequence modulo 2 is generated by a morphism.** Let $g_0, g_1, g_2, \ldots$ be
Gutkovskiy's sequence, and let $u$ be the map on the alphabet $\mathbb{N}$ with $u(0) = 01$ and
$u(b) = 0010$ for every letter $b \ne 0$. Then the infinite word $(g_n \bmod 2)_{n \ge 0}$ is the
limit of the iterates of $u$ at the letter $0$. On the letters $0$ and $1$ that occur, $u$ is the
morphism $0 \mapsto 01$, $1 \mapsto 0010$, and the word is OEIS A284772.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 4 (`integers-2024-A51-thm-4`). -/
public theorem isOmegaLimit_gutkovskiy_mod_two :
    IsOmegaLimit (fun b : ℕ ↦ if b = 0 then [0, 1] else [0, 0, 1, 0]) 0
      fun n ↦ gutkovskiy n % 2 := by
  constructor
  · intro M
    obtain ⟨m, hm, hbound⟩ := IsOmegaLimitGutkovskiyModTwo.iterate_eq M
    refine ⟨M, ?_⟩
    rw [hm]
    simp only [List.length_map, List.length_range]
    have hM : M ≤ 2 ^ M := (Nat.lt_pow_self (by decide : 1 < 2)).le
    exact hM.trans hbound
  · intro n i h
    obtain ⟨m, hm, -⟩ := IsOmegaLimitGutkovskiyModTwo.iterate_eq n
    have hi : i < m := by
      rw [hm] at h
      simpa only [List.length_map, List.length_range] using h
    have hsome : (morphIterate (fun b : ℕ ↦ if b = 0 then [0, 1] else [0, 0, 1, 0]) n [0])[i]? =
        some (gutkovskiy i % 2) := by
      rw [hm]
      simp [hi]
    exact Option.some.inj ((List.getElem?_eq_getElem h).symm.trans hsome)

end

end MetaMathlibExt
