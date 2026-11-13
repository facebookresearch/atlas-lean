/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- **Alternating binomial sums of partial sums.** For every sequence $a_0, a_1, a_2, \dots$ of
complex numbers and every natural number $n$,
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \sum_{j=1}^{k} a_j =
\sum_{k=0}^{n-1} (-1)^{k+1} \binom{n-1}{k} a_{k+1},$$
where an empty sum is $0$, so both sides vanish when $n = 0$.

Source: Necdet Batır and Anthony Sofo, "A Unified Treatment of Certain
Classes of Combinatorial Identities," Journal of Integer Sequences 24
(2021), Article 21.3.2, Theorem A.
Proves `Wanted` entry `alternating_binomial_partial_sum`. -/
theorem alternating_binomial_partial_sum
    (a : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * (∑ j ∈ Finset.Icc 1 k, a j)) =
    ∑ k ∈ Finset.range n,
      (-1 : ℂ) ^ (k + 1) * (Nat.choose (n - 1) k : ℂ) * a (k + 1) := by
  have inner : ∀ j, 1 ≤ j → j ≤ n →
      (∑ k ∈ Finset.Icc j n, (-1 : ℂ) ^ k * (Nat.choose n k : ℂ)) =
        (-1 : ℂ) ^ j * (Nat.choose (n - 1) (j - 1) : ℂ) := by
    intro j hj1 hjn
    have npos : 1 ≤ n := le_trans hj1 hjn
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm] at hjn ⊢
    have eN : m + 1 - 1 = m := by omega
    rw [eN]
    set F : ℕ → ℂ := fun t => (-1 : ℂ) ^ (t + 1) * (Nat.choose m (t - 1) : ℂ) with hF
    have perterm : ∀ k ∈ Finset.Icc j (m + 1),
        (-1 : ℂ) ^ k * (Nat.choose (m + 1) k : ℂ) = F (k + 1) - F k := by
      intro k hk
      have hk1 : 1 ≤ k := le_trans hj1 (Finset.mem_Icc.mp hk).1
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hk1
      rw [ht]
      simp only [hF]
      have e0 : (1 : ℕ) + t = t + 1 := by omega
      rw [e0]
      have e1 : (t + 1) - 1 = t := by omega
      have e2 : ((t + 1) + 1) - 1 = t + 1 := by omega
      rw [Nat.choose_succ_succ', e1, e2]
      have key : ∀ u, (-1 : ℂ) ^ (u + 1) = (-1 : ℂ) ^ u * -1 := by
        intro u
        rw [pow_succ]
      simp only [key, Nat.add_comm, Nat.cast_add]
      ring
    have tele := Finset.sum_Icc_sub hjn F
    calc (∑ k ∈ Finset.Icc j (m + 1), (-1 : ℂ) ^ k * (Nat.choose (m + 1) k : ℂ))
        = (∑ k ∈ Finset.Icc j (m + 1), (F (k + 1) - F k)) :=
          Finset.sum_congr rfl perterm
      _ = F ((m + 1) + 1) - F j := tele
      _ = (-1 : ℂ) ^ j * (Nat.choose m (j - 1) : ℂ) := by
        have hC0 : (Nat.choose m (m + 1) : ℂ) = 0 := by
          exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.lt_succ_self _)
        have eM : ((m + 1) + 1) - 1 = m + 1 := by omega
        have pw : (-1 : ℂ) ^ (j + 1) = -(-1 : ℂ) ^ j := by
          rw [pow_succ]
          ring
        simp only [hF]
        rw [eM, hC0, mul_zero, zero_sub, pw]
        ring
  simp only [Finset.mul_sum]
  set F : ℕ → ℕ → ℂ :=
    fun k j => (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * a j with hF
  have e1 : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 k, F k j)
      = ∑ p ∈ (Finset.range (n + 1)).sigma (fun k => Finset.Icc 1 k), F p.1 p.2 := by
    rw [Finset.sum_sigma]
  have sbij : (∑ p ∈ (Finset.range (n + 1)).sigma (fun k => Finset.Icc 1 k), F p.1 p.2)
      = ∑ p ∈ (Finset.Icc 1 n).sigma (fun j => Finset.Icc j n), F p.2 p.1 := by
    refine Finset.sum_bij (fun p _ => (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨a, b⟩ := p
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hp ⊢
      omega
    · intro p hp q hq h
      obtain ⟨a, b⟩ := p
      obtain ⟨c, d⟩ := q
      have h1 : b = d := congrArg Sigma.fst h
      have h2 : a = c := congrArg Sigma.snd h
      subst h1
      subst h2
      rfl
    · intro q hq
      obtain ⟨c, d⟩ := q
      refine ⟨⟨d, c⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hq ⊢
      omega
    · intro p _
      rfl
  have e3 : (∑ p ∈ (Finset.Icc 1 n).sigma (fun j => Finset.Icc j n), F p.2 p.1)
      = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, F k j := by
    rw [Finset.sum_sigma]
  have swap : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 k, F k j)
      = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, F k j := by
    rw [e1, sbij, e3]
  have factored : ∀ j ∈ Finset.Icc 1 n,
      (∑ k ∈ Finset.Icc j n, F k j)
        = a j * ((-1 : ℂ) ^ j * (Nat.choose (n - 1) (j - 1) : ℂ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    simp only [hF]
    rw [← Finset.sum_mul, inner j hj1 hjn]
    ring
  have hIco : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [swap, Finset.sum_congr rfl factored, hIco, Finset.sum_Ico_eq_sum_range]
  have eN' : n + 1 - 1 = n := by omega
  rw [eN']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have g1 : 1 + i = i + 1 := by omega
  have g2 : (i + 1) - 1 = i := by omega
  simp only [g1, g2]
  ring

end MetaMathlibExt
