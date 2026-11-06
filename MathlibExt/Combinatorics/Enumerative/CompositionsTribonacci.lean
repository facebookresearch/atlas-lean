/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compositions with parts one, two, and three

This file proves that compositions whose parts lie in `{1, 2, 3}` are counted by the
Tribonacci recurrence.
-/

@[expose] public section

namespace MetaMathlibExt

private def compositionsTrib_fixed (k n : ℕ) : ℕ :=
  Fintype.card {a : Fin k → Fin 3 // (∑ i : Fin k, ((a i).val + 1)) = n}

private def compositionsTrib_count (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), compositionsTrib_fixed k n

private def compositionsTrib_consEquiv (k n : ℕ) :
    {a : Fin (k + 1) → Fin 3 // (∑ i : Fin (k + 1), ((a i).val + 1)) = n} ≃
      Σ j : Fin 3, {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) + (j.val + 1) = n} where
  toFun a :=
    ⟨a.1 0, Fin.tail a.1, by
      have ha := a.2
      rw [Fin.sum_univ_succ] at ha
      simpa [Fin.tail, Nat.add_comm] using ha⟩
  invFun a :=
    ⟨Fin.cons a.1 a.2.1, by
      simpa [Fin.sum_univ_succ, Nat.add_comm] using a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    exact Fin.cons_self_tail a.1
  right_inv a := by
    rcases a with ⟨j, b, hb⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    exact Fin.tail_cons (α := fun _ : Fin (k + 1) ↦ Fin 3) j b

private theorem compositionsTrib_fixed_succ (k n : ℕ) :
    compositionsTrib_fixed (k + 1) (n + 3) =
      compositionsTrib_fixed k (n + 2) + compositionsTrib_fixed k (n + 1) +
        compositionsTrib_fixed k n := by
  unfold compositionsTrib_fixed
  rw [Fintype.card_congr (compositionsTrib_consEquiv k (n + 3))]
  rw [Fintype.card_sigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, add_zero]
  have h1 :
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) + 1 = n + 3} =
        Fintype.card {b : Fin k → Fin 3 //
          (∑ i : Fin k, ((b i).val + 1)) = n + 2} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  have h2 :
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) + 2 = n + 3} =
        Fintype.card {b : Fin k → Fin 3 //
          (∑ i : Fin k, ((b i).val + 1)) = n + 1} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  have h3 :
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) + 3 = n + 3} =
        Fintype.card {b : Fin k → Fin 3 //
          (∑ i : Fin k, ((b i).val + 1)) = n} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  rw [h1, h2, h3]
  omega

private theorem compositionsTrib_length_le_sum {k : ℕ} (a : Fin k → Fin 3) :
    k ≤ ∑ i : Fin k, ((a i).val + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (Fin.tail a)
      simp only [Fin.tail] at htail
      omega

private theorem compositionsTrib_fixed_eq_zero {k n : ℕ} (h : n < k) :
    compositionsTrib_fixed k n = 0 := by
  unfold compositionsTrib_fixed
  let hEmpty : IsEmpty {a : Fin k → Fin 3 //
      (∑ i : Fin k, ((a i).val + 1)) = n} :=
    ⟨fun a ↦ by
      have hle := compositionsTrib_length_le_sum a.1
      have ha := a.2
      omega⟩
  exact @Fintype.card_eq_zero _ inferInstance hEmpty

private theorem compositionsTrib_fixed_zero {n : ℕ} (h : 0 < n) :
    compositionsTrib_fixed 0 n = 0 := by
  simp [compositionsTrib_fixed, h.ne]

private theorem compositionsTrib_count_add_three (n : ℕ) :
    compositionsTrib_count (n + 3) =
      compositionsTrib_count (n + 2) + compositionsTrib_count (n + 1) +
        compositionsTrib_count n := by
  have hdrop1 :
      (∑ k ∈ Finset.range (n + 3), compositionsTrib_fixed k (n + 1)) =
        ∑ k ∈ Finset.range (n + 2), compositionsTrib_fixed k (n + 1) := by
    rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
  have hdrop2 :
      (∑ k ∈ Finset.range (n + 3), compositionsTrib_fixed k n) =
        ∑ k ∈ Finset.range (n + 1), compositionsTrib_fixed k n := by
    rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
  unfold compositionsTrib_count
  conv_lhs => rw [Finset.sum_range_succ']
  rw [compositionsTrib_fixed_zero (n := n + 3) (by omega), add_zero]
  simp_rw [compositionsTrib_fixed_succ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hdrop1, hdrop2]

private theorem compositionsTrib_count_one : compositionsTrib_count 1 = 1 := by
  decide

private theorem compositionsTrib_count_two : compositionsTrib_count 2 = 2 := by
  decide

private theorem compositionsTrib_count_three : compositionsTrib_count 3 = 4 := by
  decide

private theorem compositionsTrib_count_eq
    (T : ℕ → ℕ)
    (hT1 : T 1 = 1)
    (hT2 : T 2 = 1)
    (hT3 : T 3 = 2)
    (hTrec : ∀ m : ℕ, 3 < m →
      T m = T (m - 1) + T (m - 2) + T (m - 3)) :
    ∀ n : ℕ, 0 < n → compositionsTrib_count n = T (n + 1) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  by_cases hsmall : n < 4
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [compositionsTrib_count_one, hT2]
    · rw [compositionsTrib_count_two, hT3]
    · have hT4 : T 4 = 4 := by
        rw [hTrec 4 (by omega), hT3, hT2, hT1]
      rw [compositionsTrib_count_three, hT4]
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn4
    have hm3 := ih (m + 3) (by omega) (by omega)
    have hm2 := ih (m + 2) (by omega) (by omega)
    have hm1 := ih (m + 1) (by omega) (by omega)
    rw [show 4 + m = (m + 1) + 3 by omega, compositionsTrib_count_add_three]
    rw [hm3, hm2, hm1]
    have hrec := hTrec (m + 5) (by omega)
    have hsub1 : m + 5 - 1 = m + 4 := by omega
    have hsub2 : m + 5 - 2 = m + 3 := by omega
    have hsub3 : m + 5 - 3 = m + 2 := by omega
    rw [hsub1, hsub2, hsub3] at hrec
    have hindex : (m + 1 + 3) + 1 = m + 5 := by omega
    rw [hindex, hrec]

/--
**Compositions with parts $1$, $2$, $3$ are counted by Tribonacci numbers.** Let $T$ be a
sequence of natural numbers with $T_1 = T_2 = 1$, $T_3 = 2$ and
$T_m = T_{m-1} + T_{m-2} + T_{m-3}$ for every $m > 3$. Then for every positive integer $n$, the
number of compositions of $n$ (ordered sequences of positive integers with sum $n$) whose parts
are all $1$, $2$ or $3$ is $T_{n+1}$.

The result is due to V. E. Hoggatt, Jr., and M. Bicknell,
"Palindromic compositions," Fibonacci Quarterly 13 (1975), 350–356,
cited as [V] at source lines 429–430.

Proves `Wanted` entry `compositions_parts_one_two_three_eq_tribonacci`.

Proof: Split each nonempty composition by its first part, sum the resulting recurrence over its
length, and use strong induction, following Stanley, Section 1.2, and OEIS A000073.

Source: Yu-hong Guo, "Some Identities For Palindromic Compositions,"
Journal of Integer Sequences 21 (2018), Article 18.6.6, Theorem
citing [V], lines 118–125,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Guo/guo19.tex
-/
public theorem compositions_parts_one_two_three_eq_tribonacci
    (n : ℕ) (hn : 0 < n)
    (T : ℕ → ℕ)
    (hT1 : T 1 = 1)
    (hT2 : T 2 = 1)
    (hT3 : T 3 = 2)
    (hTrec : ∀ m : ℕ, 3 < m →
      T m = T (m - 1) + T (m - 2) + T (m - 3)) :
    (∑ k ∈ Finset.range (n + 1),
      Fintype.card {a : Fin k → Fin 3 //
        (∑ i : Fin k, ((a i).val + 1)) = n}) =
      T (n + 1) := by
  change compositionsTrib_count n = T (n + 1)
  exact compositionsTrib_count_eq T hT1 hT2 hT3 hTrec n hn

/--
**Compositions with parts $1$, $2$, $3$ and the Tribonacci sequence.** For every positive integer
$n$, the number of compositions of $n$ (ordered sequences of positive integers with sum $n$)
whose parts are all $1$, $2$ or $3$ equals $t_{n+2}$, where $t$ is the Tribonacci sequence
given by $t_0 = t_1 = 0$, $t_2 = 1$ and $t_{k+3} = t_{k+2} + t_{k+1} + t_k$ (OEIS A000073).

Proof: Specialize `compositions_parts_one_two_three_eq_tribonacci` to
`T k = tribonacci (k + 1)`, whose initial values and recurrence hold by definition.
-/
public theorem compositions_parts_one_two_three_eq_canonical_tribonacci
    (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1),
      Fintype.card {a : Fin k → Fin 3 //
        (∑ i : Fin k, ((a i).val + 1)) = n}) =
      tribonacci (n + 2) := by
  exact compositions_parts_one_two_three_eq_tribonacci n hn
    (fun k ↦ tribonacci (k + 1)) (by rfl) (by rfl) (by rfl) (by
      intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ m by omega)
      rw [show 4 + k + 1 = (k + 2) + 3 by omega]
      rw [show 4 + k - 1 + 1 = k + 4 by omega]
      rw [show 4 + k - 2 + 1 = k + 3 by omega]
      rw [show 4 + k - 3 + 1 = k + 2 by omega]
      rfl)

end MetaMathlibExt
