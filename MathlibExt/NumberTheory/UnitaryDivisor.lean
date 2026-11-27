/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/

@[expose] public section

namespace Nat

/-- **Unitary divisors.** For a natural number $n$, the unitary divisors of $n$ are the divisors
$d$ of $n$ that are coprime to the complementary divisor $n/d$, that is, with $\gcd(d, n/d) = 1$.
For $n = 0$ there are no unitary divisors. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => d.Coprime (n / d)

@[simp]
theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

@[simp]
theorem unitaryDivisors_zero : unitaryDivisors 0 = ∅ := by
  simp [unitaryDivisors]

theorem dvd_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) : d ∣ n :=
  (mem_unitaryDivisors.mp h).1

theorem coprime_div_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) :
    d.Coprime (n / d) :=
  (mem_unitaryDivisors.mp h).2.2

/-- **Sum of unitary divisors.** For a natural number $n$, $\sigma^*(n)$ denotes the sum of the
unitary divisors of $n$. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

theorem sigmaStar_eq_sum (n : ℕ) :
    sigmaStar n = ∑ d ∈ unitaryDivisors n, d :=
  rfl

@[simp]
theorem sigmaStar_zero : sigmaStar 0 = 0 := by
  simp [sigmaStar]

end Nat

namespace Set

/-- **Elements primitive under divisibility.** Let $S$ be a set of natural numbers. A natural
number $n$ is primitive in $S$ under divisibility when $n \in S$ and no proper divisor of $n$,
that is, no divisor $d$ of $n$ with $d < n$, belongs to $S$. -/
def IsPrimitiveByDivisibility (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

@[simp]
theorem isPrimitiveByDivisibility_iff {S : Set ℕ} {n : ℕ} :
    S.IsPrimitiveByDivisibility n ↔
      n ∈ S ∧ ∀ {d : ℕ}, d ∣ n → d < n → d ∉ S := by
  constructor
  · rintro ⟨hn, hdisjoint⟩
    refine ⟨hn, fun {d} hdvd hdlt hdS => ?_⟩
    exact Set.disjoint_left.mp hdisjoint (Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩) hdS
  · rintro ⟨hn, hminimal⟩
    refine ⟨hn, Set.disjoint_left.mpr ?_⟩
    intro d hdproper hdS
    exact hminimal (Nat.mem_properDivisors.mp hdproper).1
      (Nat.mem_properDivisors.mp hdproper).2 hdS

theorem IsPrimitiveByDivisibility.mem {S : Set ℕ} {n : ℕ}
    (h : S.IsPrimitiveByDivisibility n) : n ∈ S :=
  h.1

theorem IsPrimitiveByDivisibility.not_mem_of_dvd_lt {S : Set ℕ} {n d : ℕ}
    (h : S.IsPrimitiveByDivisibility n) (hdvd : d ∣ n) (hdn : d < n) : d ∉ S := by
  intro hd
  exact isPrimitiveByDivisibility_iff.mp h |>.2 hdvd hdn hd

end Set
