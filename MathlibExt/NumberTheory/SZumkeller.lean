/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# s-Zumkeller numbers

An s-Zumkeller number admits an equal-squares partition of its proper divisors.
For a positive even number, removing its half from the part containing it gives
a subset-sum criterion for such a partition.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **s-Zumkeller numbers.** A natural number $n$ is s-Zumkeller if its proper divisors can be
split into two disjoint nonempty sets whose elements have equal sums of squares. Each of the two
sums is then $(\sigma_2(n) - n^2)/2$, where $\sigma_2(n)$ is the sum of the squares of the
positive divisors of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 1. -/
def IsSZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ n.properDivisors, A.Nonempty ∧ (n.properDivisors \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ n.properDivisors \ A, d ^ 2

/-- **Unitary s-Zumkeller numbers.** A natural number $n$ is a unitary s-Zumkeller number when
its proper unitary divisors (the unitary divisors of $n$ other than $n$) split into two nonempty
disjoint sets $A$ and $B$ with equal sums of squares, $\sum_{d \in A} d^2 = \sum_{d \in B} d^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 2. -/
def IsUnitarySZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ (Nat.unitaryDivisors n).erase n, A.Nonempty ∧
    ((Nat.unitaryDivisors n).erase n \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2

/-- **$60$ is s-Zumkeller.** The number $60$ is s-Zumkeller: the squares of its proper divisors
$1, 2, 5, 30$ sum to $1^2 + 2^2 + 5^2 + 30^2 = 930$, which is half of the sum of the squares of
all proper divisors of $60$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 1. -/
theorem isSZumkeller_sixty : IsSZumkeller 60 :=
  ⟨{1, 2, 5, 30}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not s-Zumkeller.** The number $6$ is not an s-Zumkeller number: the squares of
its proper divisors sum to $1^2 + 2^2 + 3^2 = 14$, and they admit no split into two parts with
equal sums.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isSZumkeller_six : ¬ IsSZumkeller 6 := by
  unfold IsSZumkeller
  decide

/-- **The number 60 is unitary s-Zumkeller.** The number $60$ is a unitary s-Zumkeller number: its
proper unitary divisors are $1, 3, 4, 5, 12, 15, 20$, and $20^2 + 3^2 + 1^2 = 410$ is half the sum
of their squares.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 2. -/
theorem isUnitarySZumkeller_sixty : IsUnitarySZumkeller 60 :=
  ⟨{1, 3, 20}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not unitary s-Zumkeller.** The number $6$ is not a unitary s-Zumkeller
number.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isUnitarySZumkeller_six : ¬ IsUnitarySZumkeller 6 := by
  unfold IsUnitarySZumkeller
  decide

/-- **Criterion for even s-Zumkeller numbers.** Let $n$ be an even positive integer and let
$\sigma_2(n)$ be the sum of the squares of the positive divisors of $n$. Then $n$ is s-Zumkeller
if and only if there is a (possibly empty) set $S$ of proper divisors of $n$, not containing
$n/2$, such that $4 \sum_{d \in S} d^2 = 2\sigma_2(n) - 3n^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 2. -/
theorem isSZumkeller_iff_of_even (n : ℕ) (hn : 0 < n) (he : Even n) :
    IsSZumkeller n ↔
      ∃ S ⊆ n.properDivisors.erase (n / 2),
        4 * (∑ d ∈ S, d ^ 2 : ℤ) = 2 * ArithmeticFunction.sigma 2 n - 3 * n ^ 2 := by
  let k := n / 2
  have hk : k ∈ n.properDivisors := Nat.mem_properDivisors.mpr
    ⟨Nat.div_dvd_of_dvd he.two_dvd, Nat.div_lt_self hn (by decide)⟩
  have hsq : k ^ 2 * 4 = n ^ 2 := by
    calc
      k ^ 2 * 4 = (k * 2) ^ 2 := by norm_num [mul_pow]
      _ = n ^ 2 := by rw [show k * 2 = n from Nat.div_mul_cancel he.two_dvd]
  have hσ : ArithmeticFunction.sigma 2 n = n ^ 2 + ∑ d ∈ n.properDivisors, d ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, ← Nat.insert_self_properDivisors hn.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors]
  constructor
  · rintro ⟨A, hA, _, _, hbal⟩
    -- Choose the part containing k, exchanging the two parts if necessary.
    obtain ⟨B, hB, hkB, hsum⟩ : ∃ B ⊆ n.properDivisors, k ∈ B ∧
        ∑ d ∈ B, d ^ 2 = ∑ d ∈ n.properDivisors \ B, d ^ 2 := by
      by_cases h : k ∈ A
      · exact ⟨A, hA, h, hbal⟩
      · exact ⟨_, Finset.sdiff_subset, Finset.mem_sdiff.mpr ⟨hk, h⟩, by
          rwa [Finset.sdiff_sdiff_eq_self hA, eq_comm]⟩
    refine ⟨B.erase k, Finset.erase_subset_erase k hB, ?_⟩
    rw [eq_sub_iff_add_eq]
    have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hB
    have herase := B.sum_erase_add (fun d => d ^ 2) hkB
    exact_mod_cast (show 4 * (∑ d ∈ B.erase k, d ^ 2) + 3 * n ^ 2 =
      2 * ArithmeticFunction.sigma 2 n by omega)
  · rintro ⟨S, hS, hsum⟩
    have hkS : k ∉ S := Finset.notMem_mono hS (Finset.notMem_erase k _)
    have hA := Finset.insert_subset hk (hS.trans (Finset.erase_subset k n.properDivisors))
    rw [eq_sub_iff_add_eq] at hsum
    have hsum' : 4 * (∑ d ∈ S, d ^ 2) + 3 * n ^ 2 = 2 * ArithmeticFunction.sigma 2 n := by
      exact_mod_cast hsum
    have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
    have hbal : ∑ d ∈ insert k S, d ^ 2 = ∑ d ∈ n.properDivisors \ insert k S, d ^ 2 := by
      rw [Finset.sum_insert hkS] at hsplit ⊢
      omega
    refine ⟨insert k S, hA, Finset.insert_nonempty _ _, ?_, hbal⟩
    apply Finset.nonempty_of_sum_ne_zero (f := fun d : ℕ => d ^ 2)
    rw [← hbal, Finset.sum_insert hkS]
    have := Nat.pos_of_mem_properDivisors hk
    positivity

end

end MetaMathlibExt
