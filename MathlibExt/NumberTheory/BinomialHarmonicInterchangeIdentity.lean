/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/--
**Binomial interchange identity with harmonic weights.** Let $K$ be a field of
characteristic zero. For every natural number $n$ and every sequence $a : \mathbb{N} \to K$,
$$\sum_{k=1}^{n} \frac{1}{k} \sum_{j=1}^{k} \binom{k}{j} a_j =
\sum_{k=1}^{n} \binom{n}{k} \frac{a_k}{k}.$$

The source notes a generalization in Boyadzhiev, attributed to 't Woord. The statement
generalizes the source's real or complex sequences to any field of characteristic zero.

Proves `Wanted` entry `binomial_harmonic_interchange_identity`.

Source: Necdet Batır and Anthony Sofo, "A Unified Treatment of Certain
Classes of Combinatorial Identities," Journal of Integer Sequences 24 (2021),
Article 21.3.2, Lemma A (label LemmaA), lines 150–156,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Batir/batir7.tex
-/
theorem binomial_harmonic_interchange_identity {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (a : ℕ → K) :
  Finset.sum (Finset.Icc 1 n)
    (fun k => (1 / (k : K)) *
      Finset.sum (Finset.Icc 1 k) (fun j => (Nat.choose k j : K) * a j)) =
  Finset.sum (Finset.Icc 1 n) (fun k => (Nat.choose n k : K) * a k / (k : K)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : (1 : ℕ) ≤ n + 1 := by omega
    have hN : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have absorb : ∀ k ∈ Finset.Icc 1 n,
        (1 / ((n + 1 : ℕ) : K)) * ((Nat.choose (n + 1) k : K) * a k) =
          (Nat.choose n (k - 1) : K) * a k / (k : K) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkk : (k - 1) + 1 = k := by omega
      have hnat := Nat.add_one_mul_choose_eq n (k - 1)
      rw [hkk] at hnat
      have hkK : (k : K) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hcast : ((n + 1 : ℕ) : K) * (Nat.choose n (k - 1) : K) =
          (Nat.choose (n + 1) k : K) * (k : K) := by
        exact_mod_cast hnat
      have e1 : (1 / ((n + 1 : ℕ) : K)) * ((Nat.choose (n + 1) k : K) * a k)
          = ((Nat.choose (n + 1) k : K) * a k) / ((n + 1 : ℕ) : K) := by ring
      rw [e1, div_eq_div_iff hN hkK]
      linear_combination -(a k) * hcast
    have pascal : ∀ k ∈ Finset.Icc 1 n,
        (Nat.choose (n + 1) k : K) * a k / (k : K) =
          (Nat.choose n k : K) * a k / (k : K) +
            (Nat.choose n (k - 1) : K) * a k / (k : K) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hnat : Nat.choose (n + 1) k =
          Nat.choose n (k - 1) + Nat.choose n k := by
        have hps := Nat.choose_succ_succ n (k - 1)
        rwa [show (k - 1).succ = k from by omega,
          show n.succ = n + 1 from rfl] at hps
      have hcast : (Nat.choose (n + 1) k : K) =
          (Nat.choose n (k - 1) : K) + (Nat.choose n k : K) := by
        exact_mod_cast hnat
      rw [hcast]
      ring
    have hA : (1 / ((n + 1 : ℕ) : K)) *
          Finset.sum (Finset.Icc 1 (n + 1))
            (fun j => (Nat.choose (n + 1) j : K) * a j) =
          Finset.sum (Finset.Icc 1 n)
            (fun k => (Nat.choose n (k - 1) : K) * a k / (k : K)) +
          (Nat.choose (n + 1) (n + 1) : K) * a (n + 1) / ((n + 1 : ℕ) : K) := by
      rw [Finset.sum_Icc_succ_top hle, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl (fun k hk => absorb k hk)
      · ring
    have hB : Finset.sum (Finset.Icc 1 n)
            (fun k => (Nat.choose (n + 1) k : K) * a k / (k : K)) =
          Finset.sum (Finset.Icc 1 n)
            (fun k => (Nat.choose n k : K) * a k / (k : K)) +
          Finset.sum (Finset.Icc 1 n)
            (fun k => (Nat.choose n (k - 1) : K) * a k / (k : K)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk => pascal k hk)
    conv_lhs => rw [Finset.sum_Icc_succ_top hle]
    conv_rhs => rw [Finset.sum_Icc_succ_top hle]
    rw [ih]
    linear_combination hA - hB

end MetaMathlibExt
