/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# Counting and summing unitary divisors

Each subset of the distinct prime factors selects the full prime powers of a unitary divisor.
-/

namespace MetaMathlibExt

open Finset

private def selectedFactorization (n : ℕ) (s : Finset ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter (· ∈ s)

private def unitaryDivisorOfSubset (n : ℕ) (s : Finset ℕ) : ℕ :=
  (selectedFactorization n s).prod (· ^ ·)

private theorem support_selectedFactorization {n : ℕ} {s : Finset ℕ} (hs : s ⊆ n.primeFactors) :
    (selectedFactorization n s).support = s := by
  rw [selectedFactorization, Finsupp.support_filter, Nat.support_factorization]
  ext p
  rw [mem_filter]
  exact ⟨And.right, fun hp => ⟨hs hp, hp⟩⟩

private theorem unitaryDivisorOfSubset_spec {n : ℕ} {s : Finset ℕ} (hn : n ≠ 0)
    (hs : s ∈ n.primeFactors.powerset) :
    unitaryDivisorOfSubset n s ∈ Nat.unitaryDivisors n ∧
      (unitaryDivisorOfSubset n s).primeFactors = s := by
  have hle : selectedFactorization n s ≤ n.factorization := by
    rw [Finsupp.le_def]
    intro p
    by_cases hp : p ∈ s <;> simp [selectedFactorization, hp]
  have hfac : (unitaryDivisorOfSubset n s).factorization = selectedFactorization n s :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization hle
  have hprimes : (unitaryDivisorOfSubset n s).primeFactors = s := by
    rw [← Nat.support_factorization, hfac, support_selectedFactorization (mem_powerset.mp hs)]
  refine ⟨?_, hprimes⟩
  -- A selected prime occurs to its full exponent and cannot divide the quotient.
  have hdvd : unitaryDivisorOfSubset n s ∣ n := Nat.prod_pow_dvd_of_le_factorization hle
  have hd0 : unitaryDivisorOfSubset n s ≠ 0 := ne_zero_of_dvd_ne_zero hn hdvd
  have hq0 : n / unitaryDivisorOfSubset n s ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hd0)).ne'
  refine Nat.mem_unitaryDivisors.mpr ⟨hdvd, hn, (Nat.disjoint_primeFactors hd0 hq0).mp ?_⟩
  rw [disjoint_left]
  intro p hp hq
  rw [hprimes] at hp
  have hz : (n / unitaryDivisorOfSubset n s).factorization p = 0 := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, hfac]
    simp [selectedFactorization, hp]
  exact (Finsupp.notMem_support_iff.mpr hz) hq

private theorem primeFactors_mem_powerset_of_mem_unitaryDivisors {n d : ℕ}
    (hd : d ∈ Nat.unitaryDivisors n) : d.primeFactors ∈ n.primeFactors.powerset := by
  obtain ⟨hdvd, hn, _⟩ := Nat.mem_unitaryDivisors.mp hd
  exact mem_powerset.mpr (Nat.primeFactors_mono hdvd hn)

private theorem unitaryDivisorOfSubset_primeFactors {n d : ℕ}
    (hd : d ∈ Nat.unitaryDivisors n) : unitaryDivisorOfSubset n d.primeFactors = d := by
  -- The prime factors of a unitary divisor recover its entire factorization.
  obtain ⟨hdvd, hn, hcop⟩ := Nat.mem_unitaryDivisors.mp hd
  change (selectedFactorization n d.primeFactors).prod (· ^ ·) = d
  suffices selectedFactorization n d.primeFactors = d.factorization by
    rw [this, Nat.prod_factorization_pow_eq_self (ne_zero_of_dvd_ne_zero hn hdvd)]
  ext p
  by_cases hp : p ∈ d.primeFactors
  · rw [selectedFactorization, Finsupp.filter_apply_pos _ _ hp, ← Nat.div_mul_cancel hdvd,
      Nat.factorization_eq_of_coprime_right hcop.symm
        (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
  · rw [selectedFactorization, Finsupp.filter_apply_neg _ _ hp,
      Finsupp.notMem_support_iff.mp hp]

/-- **Number of unitary divisors.** A positive integer $n$ with $m$ distinct prime factors has
exactly $2^m$ unitary divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 2 (quoting Bege). -/
public theorem card_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    (Nat.unitaryDivisors n).card = 2 ^ n.primeFactors.card := by
  rw [← card_powerset]
  symm
  exact card_bij' (fun s _ => unitaryDivisorOfSubset n s) (fun d _ => d.primeFactors)
    (fun _ hs => (unitaryDivisorOfSubset_spec hn hs).1)
    (fun _ hd => primeFactors_mem_powerset_of_mem_unitaryDivisors hd)
    (fun _ hs => (unitaryDivisorOfSubset_spec hn hs).2)
    (fun _ hd => unitaryDivisorOfSubset_primeFactors hd)

/-- **Sum of squares of unitary divisors.** For every positive integer $n$, the sum of the
squares of the unitary divisors of $n$ equals $\prod_{p} \left(1 + p^{2k_p}\right)$, where $p$
ranges over the distinct prime factors of $n$ and $k_p$ is the exponent of $p$ in $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 3(i) (quoting Subbarao and
Warren). -/
public theorem sum_sq_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 =
      ∏ p ∈ n.primeFactors, (1 + p ^ (2 * n.factorization p)) := by
  rw [prod_one_add]
  symm
  refine sum_bij' (fun s _ => unitaryDivisorOfSubset n s) (fun d _ => d.primeFactors)
    (fun _ hs => (unitaryDivisorOfSubset_spec hn hs).1)
    (fun _ hd => primeFactors_mem_powerset_of_mem_unitaryDivisors hd)
    (fun _ hs => (unitaryDivisorOfSubset_spec hn hs).2)
    (fun _ hd => unitaryDivisorOfSubset_primeFactors hd) ?_
  intro s hs
  rw [unitaryDivisorOfSubset, Finsupp.prod, ← prod_pow,
    support_selectedFactorization (mem_powerset.mp hs)]
  refine prod_congr rfl fun p hp => ?_
  rw [selectedFactorization, Finsupp.filter_apply_pos _ _ hp, ← pow_mul, Nat.mul_comm]

end MetaMathlibExt
