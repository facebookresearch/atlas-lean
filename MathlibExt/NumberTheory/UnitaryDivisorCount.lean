/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# Counting unitary divisors

Each subset of the distinct prime factors selects the full prime powers of a unitary divisor.
-/

namespace MetaMathlibExt

open Finset

/-- **Number of unitary divisors.** A positive integer $n$ with $m$ distinct prime factors has
exactly $2^m$ unitary divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 2 (quoting Bege). -/
public theorem card_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    (Nat.unitaryDivisors n).card = 2 ^ n.primeFactors.card := by
  let exponents (s : Finset ℕ) := n.factorization.filter (· ∈ s)
  let fromSubset (s : Finset ℕ) := (exponents s).prod (· ^ ·)
  have hle (s : Finset ℕ) : exponents s ≤ n.factorization := by
    rw [Finsupp.le_def]
    intro p
    by_cases hp : p ∈ s <;> simp [exponents, hp]
  have hfac (s : Finset ℕ) : (fromSubset s).factorization = exponents s :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization (hle s)
  have hprimes (s : Finset ℕ) : (fromSubset s).primeFactors = n.primeFactors.filter (· ∈ s) := by
    rw [← Nat.support_factorization, hfac]
    simp [exponents]
  rw [← card_powerset]
  symm
  refine card_bij' (fun s _ => fromSubset s) (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · -- Any selected prime occurs to its full exponent, so it cannot divide the quotient.
    intro s _
    have hdvd : fromSubset s ∣ n := Nat.prod_pow_dvd_of_le_factorization (hle s)
    have hd0 : fromSubset s ≠ 0 := ne_zero_of_dvd_ne_zero hn hdvd
    have hq0 : n / fromSubset s ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hd0)).ne'
    refine Nat.mem_unitaryDivisors.mpr ⟨hdvd, hn, (Nat.disjoint_primeFactors hd0 hq0).mp ?_⟩
    rw [disjoint_left]
    intro p hp hq
    rw [hprimes, mem_filter] at hp
    have hz : (n / fromSubset s).factorization p = 0 := by
      rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, hfac]
      simp [exponents, hp.2]
    exact (Finsupp.notMem_support_iff.mpr hz) hq
  · intro d hd
    exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_unitaryDivisors hd) hn)
  · intro s hs
    rw [hprimes]
    ext p
    rw [mem_filter]
    exact ⟨And.right, fun hp => ⟨mem_powerset.mp hs hp, hp⟩⟩
  · -- Conversely, the prime factors of a unitary divisor recover its entire factorization.
    intro d hd
    obtain ⟨hdvd, _, hcop⟩ := Nat.mem_unitaryDivisors.mp hd
    change (exponents d.primeFactors).prod (· ^ ·) = d
    suffices exponents d.primeFactors = d.factorization by
      rw [this, Nat.prod_factorization_pow_eq_self (ne_zero_of_dvd_ne_zero hn hdvd)]
    ext p
    dsimp only [exponents]
    by_cases hp : p ∈ d.primeFactors
    · rw [Finsupp.filter_apply_pos _ _ hp, ← Nat.div_mul_cancel hdvd,
        Nat.factorization_eq_of_coprime_right hcop.symm
          (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)]
    · rw [Finsupp.filter_apply_neg _ _ hp, Finsupp.notMem_support_iff.mp hp]

end MetaMathlibExt
