/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AcceleratedZeckendorfGame
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lower bound on the length of an Accelerated Zeckendorf Game

Every complete Accelerated Zeckendorf Game on `n ≥ 1` has at least
`Nat.greatestFib n - 2` moves.

## References

* Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin,
  *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, pp. 3–14,
  Definition 1.2, Theorem 1.3, and Lemma 2.1.
-/

namespace MetaMathlibExt

private def accelZeckValue : (ℕ →₀ ℕ) →+ ℕ where
  toFun s := s.sum fun i m => m * Nat.fib (i + 1)
  map_zero' := by simp
  map_add' s t := Finsupp.sum_add_index' (fun _ => Nat.zero_mul _) (fun _ _ _ => Nat.add_mul ..)

private theorem accelZeckValue_single (i m : ℕ) :
    accelZeckValue (Finsupp.single i m) = m * Nat.fib (i + 1) :=
  Finsupp.sum_single_index (h := fun i m => m * Nat.fib (i + 1)) (Nat.zero_mul _)

private theorem accelZeckValue_remove (s : ℕ →₀ ℕ) (i m : ℕ) (h : m ≤ s i) :
    accelZeckValue (s - Finsupp.single i m) + m * Nat.fib (i + 1) =
      accelZeckValue s := by
  rw [← accelZeckValue_single, ← map_add, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h)]

private theorem accelZeckValue_move (s t : ℕ →₀ ℕ) (h : AccelZeckMove s t) :
    accelZeckValue t = accelZeckValue s := by
  rcases h with ⟨m, _, ⟨i, hi, h₁, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, rfl⟩⟩
  · have h₂' : m ≤ (s - Finsupp.single (i - 1) m) i := by
      simpa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (by omega : i ≠ i - 1)] using h₂
    have hremove₁ := accelZeckValue_remove s (i - 1) m h₁
    have hremove₂ := accelZeckValue_remove _ i m h₂'
    have hf : Nat.fib (i + 1 + 1) = Nat.fib (i - 1 + 1) + Nat.fib (i + 1) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i), Nat.add_assoc] using
        @Nat.fib_add_two i
    rw [map_add, accelZeckValue_single, hf, Nat.mul_add]
    omega
  · have hremove := accelZeckValue_remove s 1 (2 * m) h₁
    rw [map_add, accelZeckValue_single]
    simp only [Nat.fib_add_two, Nat.fib_zero, Nat.fib_one, Nat.mul_one,
      Nat.zero_add] at hremove ⊢
    omega
  · have hremove := accelZeckValue_remove s 2 (2 * m) h₂
    simp only [map_add, accelZeckValue_single, Nat.fib_add_two, Nat.fib_zero,
      Nat.fib_one, Nat.mul_one, Nat.zero_add,
      Nat.mul_add] at hremove ⊢
    omega
  · have hremove := accelZeckValue_remove s i (2 * m) hᵢ
    have hf : Nat.fib (i - 2 + 1) + Nat.fib (i + 1 + 1) = 2 * Nat.fib (i + 1) := by
      have h₁ : Nat.fib (i + 1) = Nat.fib (i - 1) + Nat.fib i := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i),
          show i - 1 + 2 = i + 1 by omega] using @Nat.fib_add_two (i - 1)
      have h₂ := @Nat.fib_add_two i
      rw [show i - 2 + 1 = i - 1 by omega, show i + 1 + 1 = i + 2 by omega]
      omega
    simp only [map_add, accelZeckValue_single]
    rw [Nat.add_assoc, ← Nat.mul_add, hf, ← Nat.mul_assoc, Nat.mul_comm m 2]
    exact hremove

private theorem accelZeckMove_bound (s t : ℕ →₀ ℕ) (b : ℕ)
    (hs : ∀ i, i = 0 ∨ b < i → s i = 0) (h : AccelZeckMove s t) :
    ∀ i, i = 0 ∨ b + 1 < i → t i = 0 := by
  rcases h with ⟨m, hm, ⟨i, hi, _, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, rfl⟩⟩
  · have hb : i ≤ b := by
      by_contra hn
      have hz := hs i (Or.inr (by omega))
      omega
    intro k hk
    have hz := hs k (by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (by omega))
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  · have hb : 1 ≤ b := by
      by_contra hn
      have hz := hs 1 (Or.inr (by omega))
      omega
    intro k hk
    have hz := hs k (by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (by omega))
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  · have hb : 2 ≤ b := by
      by_contra hn
      have hz := hs 2 (Or.inr (by omega))
      omega
    intro k hk
    have hz := hs k (by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (by omega))
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  · have hb : i ≤ b := by
      by_contra hn
      have hz := hs i (Or.inr (by omega))
      omega
    intro k hk
    have hz := hs k (by
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (by omega))
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega

private theorem accelZeckGame_invariant (n L : ℕ) (g : ℕ → ℕ →₀ ℕ)
    (hg : IsAccelZeckGame n L g) (j : ℕ) (hj : j ≤ L) :
    accelZeckValue (g j) = n ∧ (∀ i, i = 0 ∨ j + 1 < i → g j i = 0) := by
  induction j with
  | zero =>
    rw [hg.1]
    constructor
    · simp [accelZeckValue_single]
    · intro i hi
      simp only [Finsupp.single_apply]
      split_ifs <;> omega
  | succ j ih =>
    have hprev := ih (by omega)
    have hmove := hg.2.1 j (by omega)
    constructor
    · exact (accelZeckValue_move _ _ hmove).trans hprev.1
    · exact accelZeckMove_bound _ _ (j + 1) hprev.2 hmove

/-- In a complete accelerated game on `n`, the Fibonacci value is `n` and the count at index
zero is zero at every step `j` up to and including the last step `L`. -/
public theorem IsAccelZeckGame.value_eq_and_zero {n L : ℕ} {g : ℕ → ℕ →₀ ℕ}
    (hg : IsAccelZeckGame n L g) {j : ℕ} (hj : j ≤ L) :
    (∑ i ∈ (g j).support, g j i * Nat.fib (i + 1)) = n ∧ g j 0 = 0 := by
  obtain ⟨hvalue, hbound⟩ := accelZeckGame_invariant n L g hg j hj
  exact ⟨hvalue, hbound 0 (Or.inl rfl)⟩

/-- In a state with no legal accelerated move, every positive index has at most one token. -/
public theorem accelZeck_count_le_one_of_terminal (s : ℕ →₀ ℕ)
    (ht : ∀ t, ¬ AccelZeckMove s t) (i : ℕ) (hi : 1 ≤ i) : s i ≤ 1 := by
  by_contra h
  have htwo : 2 * 1 ≤ s i := by omega
  rcases eq_or_ne i 1 with rfl | h₁
  · exact ht _ ⟨1, by decide, Or.inr (Or.inl ⟨htwo, rfl⟩)⟩
  rcases eq_or_ne i 2 with rfl | h₂
  · exact ht _ ⟨1, by decide, Or.inr (Or.inr (Or.inl ⟨htwo, rfl⟩))⟩
  exact ht _ ⟨1, by decide, Or.inr (Or.inr (Or.inr ⟨i, by omega, htwo, rfl⟩))⟩

/-- In a state with no legal accelerated move and no tokens at index zero, a nonzero count
at an index `i + 1` forces the count at index `i` to be zero. -/
public theorem accelZeck_count_eq_zero_of_succ_ne_zero_of_terminal (s : ℕ →₀ ℕ)
    (ht : ∀ t, ¬ AccelZeckMove s t) (hzero : s 0 = 0) (i : ℕ)
    (hi : s (i + 1) ≠ 0) : s i = 0 := by
  by_cases h : i = 0
  · simpa [h] using hzero
  by_contra hn
  exact ht _ ⟨1, by decide, Or.inl ⟨i + 1, by omega,
    by simpa using (show 1 ≤ s i by omega), by omega, rfl⟩⟩

private theorem accelZeckTerminal_sum (s : ℕ →₀ ℕ)
    (ht : ∀ t, ¬ AccelZeckMove s t) (hzero : s 0 = 0) (b : ℕ) :
    (∑ i ∈ Finset.range b, s i * Nat.fib (i + 1)) < Nat.fib (b + 1) := by
  induction b using Nat.twoStepInduction with
  | zero => simp
  | one => simp [hzero]
  | more b ih₀ ih₁ =>
    have hcount := accelZeck_count_le_one_of_terminal s ht (b + 1) (by omega)
    by_cases h : s (b + 1) = 0
    · rw [Finset.sum_range_succ, h, Nat.zero_mul, Nat.add_zero]
      exact ih₁.trans_le (Nat.fib_mono (by omega))
    · have hone : s (b + 1) = 1 := by omega
      have hprev := accelZeck_count_eq_zero_of_succ_ne_zero_of_terminal s ht hzero b h
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hprev, hone,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      have hf := @Nat.fib_add_two (b + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hf ⊢
      omega

@[expose] public section

/-- **Lower bound on the length of an Accelerated Zeckendorf Game.** Index the Fibonacci numbers
as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n \ge 1$ and let $F_k$ be the largest
Fibonacci number with $F_k \le n$, the largest term of the Zeckendorf decomposition of $n$. Then
every complete Accelerated Zeckendorf Game on $n$ (a sequence of moves from $n$ copies of $F_1$
to a state from which no move is possible) has at least $k - 1$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.1. -/
public theorem accelZeckGame_lower_bound (n : ℕ) (hn : 1 ≤ n) (L : ℕ)
    (g : ℕ → ℕ →₀ ℕ) (hg : IsAccelZeckGame n L g) :
    Nat.greatestFib n - 2 ≤ L := by
  have hpos : n ≠ 0 := Nat.ne_of_gt hn
  have hinv := accelZeckGame_invariant n L g hg L le_rfl
  have hzero := hinv.2 0 (Or.inl rfl)
  have hsum := accelZeckTerminal_sum (g L) hg.2.2 hzero (L + 2)
  have hvalue : accelZeckValue (g L) =
      ∑ i ∈ Finset.range (L + 2), g L i * Nat.fib (i + 1) := by
    change (g L).sum (fun i m => m * Nat.fib (i + 1)) = _
    apply Finsupp.sum_of_support_subset
    · intro i hi
      apply Finset.mem_range.mpr
      by_contra h
      have hz := hinv.2 i (Or.inr (by omega))
      exact (Finsupp.mem_support_iff.mp hi) hz
    · intro i _
      exact Nat.zero_mul _
  rw [← hvalue, hinv.1] at hsum
  have hbound := (Nat.greatestFib_lt).mpr hsum
  omega

end

end MetaMathlibExt
