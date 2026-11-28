/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoP
public import MathlibExt.NumberTheory.LeonardoPTilings
import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Recurrence for the hyper Leonardo `p`-numbers

The hyper Leonardo `p`-numbers satisfy the Pascal-type recurrence in the
order and the index, and at order zero they are the Leonardo `p`-numbers.
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.LeonardoPWanted

-- Scaling the Fibonacci `p`-numbers by `p + 1` gives the Leonardo
-- `p`-numbers with additive constant `p`, up to the constant itself.
private theorem hyperLeonardoP_rec_scaled (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    ((p : ℤ) + 1) * (fibonacciP p (m + 1) : ℤ) = leonardoPK p p m + p := by
  have step (i : ℕ) :
      (fibonacciP p (p + i + 1) : ℤ) =
        (fibonacciP p (p + i) : ℤ) + fibonacciP p i := by
    have h := fibonacciP_rec p (p + i + 1) (by omega)
    rw [show p + i + 1 - 1 = p + i by omega,
      show p + i + 1 - p - 1 = i by omega] at h
    rw [h]
    push_cast
    ring
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ p
    · have h : fibonacciP p (m + 1) = 1 := by
        rcases hm.lt_or_eq with hlt | heq
        · exact fibonacciP_eq_one p _ (by omega) hlt
        · have heq' : m + 1 = p + 1 := by omega
          rw [heq', fibonacciP_rec p (p + 1) (by omega),
            show p + 1 - 1 = p by omega, show p + 1 - p - 1 = 0 by omega,
            fibonacciP_eq_one p p hp le_rfl, fibonacciP_zero]
      simp [h, leonardoPK_of_le p p m hm, add_comm]
    · obtain ⟨i, rfl⟩ : ∃ i, m = p + i + 1 := ⟨m - p - 1, by omega⟩
      rw [leonardoPK_recurrence, show p + i + 1 + 1 = p + (i + 1) + 1 by omega,
        step, ← Nat.add_assoc, mul_add, ih (p + i) (by omega), ih i (by omega)]
      omega

-- At order zero the binomial sum defining the hyper Leonardo `p`-numbers
-- is the binomial sum for the Fibonacci `p`-numbers.
private theorem hyperLeonardoP_rec_zero (p n : ℕ) (hp : 1 ≤ p) :
    hyperLeonardoP p n 0 = leonardoPK p p n := by
  have hsum : ((fibonacciP p (n + 1) : ℤ)) =
      ∑ i ∈ Finset.range (n / (p + 1) + 1), ((n - p * i).choose i : ℤ) := by
    rw [fibonacciP_succ_eq_sum_choose p n hp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.mul_comm i p]
  have h := hyperLeonardoP_rec_scaled p hp n
  rw [hyperLeonardoP]
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← hsum]
  omega

-- Pascal's rule applied to each summand, plus the extra summand that
-- appears when `n` is divisible by `p + 1` and is zero in the first sum.
private theorem hyperLeonardoP_rec_step (p n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    hyperLeonardoP p n k =
      hyperLeonardoP p (n - 1) k + hyperLeonardoP p n (k - 1) := by
  have pascal_term (i : ℕ) (hi : i ≤ n / (p + 1)) :
      ((n + k - p * i).choose (i + k) : ℤ) =
        ((n - 1 + k - p * i).choose (i + k) : ℤ) +
          ((n + k - 1 - p * i).choose (i + k - 1) : ℤ) := by
    have hpi : p * i ≤ n := by
      have h1 : (n / (p + 1)) * (p + 1) ≤ n := Nat.div_mul_le_self n (p + 1)
      have h2 : p * i ≤ p * (n / (p + 1)) := Nat.mul_le_mul_left p hi
      have h3 : p * (n / (p + 1)) ≤ (n / (p + 1)) * (p + 1) := by
        have h5 : p ≤ p + 1 := Nat.le_add_right p 1
        calc p * (n / (p + 1)) = (n / (p + 1)) * p := Nat.mul_comm _ _
          _ ≤ (n / (p + 1)) * (p + 1) := Nat.mul_le_mul_left _ h5
      have h4 : (n / (p + 1)) * (p + 1) =
          p * (n / (p + 1)) + n / (p + 1) := by ring
      omega
    have e1 : n + k - p * i = (n + k - 1 - p * i) + 1 := by omega
    have e2 : i + k = (i + k - 1) + 1 := by omega
    have e3 : n - 1 + k - p * i = n + k - 1 - p * i := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ']
    push_cast
    ring
  have extend : (∑ i ∈ Finset.range ((n - 1) / (p + 1) + 1),
        ((n - 1 + k - p * i).choose (i + k) : ℤ)) =
      ∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n - 1 + k - p * i).choose (i + k) : ℤ) := by
    apply Finset.sum_subset
    · apply Finset.range_mono
      have hle : (n - 1) / (p + 1) ≤ n / (p + 1) := Nat.div_le_div_right (by omega)
      omega
    · intro i hi1 hi2
      simp only [Finset.mem_range, not_lt] at hi1 hi2
      have hdiv : (n - 1) / (p + 1) < i := by omega
      have hmul := (Nat.div_lt_iff_lt_mul (by omega : 0 < p + 1)).mp hdiv
      have hmul' : n - 1 < i * (p + 1) := hmul
      have hmul2 : (p + 1) * i = p * i + i := by ring
      have hmul3 : i * (p + 1) = (p + 1) * i := Nat.mul_comm _ _
      have hlt : n - 1 + k - p * i < i + k := by omega
      simp [Nat.choose_eq_zero_of_lt hlt]
  have pascal_choose :
      ((n + k).choose k : ℤ) =
        ((n - 1 + k).choose k : ℤ) + ((n + k - 1).choose (k - 1) : ℤ) := by
    have hnat := Nat.choose_succ_succ' (n + k - 1) (k - 1)
    rw [show n + k - 1 + 1 = n + k by omega, show k - 1 + 1 = k by omega] at hnat
    rw [show n - 1 + k = n + k - 1 by omega]
    have hcast : ((n + k).choose k : ℤ) =
        ((n + k - 1).choose (k - 1) : ℤ) + ((n + k - 1).choose k : ℤ) := by
      exact_mod_cast hnat
    rw [hcast, add_comm]
  have sum_eq : (∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n + k - p * i).choose (i + k) : ℤ)) =
      (∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n - 1 + k - p * i).choose (i + k) : ℤ)) +
      (∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n + k - 1 - p * i).choose (i + k - 1) : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact pascal_term i (by simp only [Finset.mem_range] at hi; omega)
  have h1 : hyperLeonardoP p (n - 1) k =
      (p + 1) * (∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n - 1 + k - p * i).choose (i + k) : ℤ)) -
      p * ((n - 1 + k).choose k : ℤ) := by
    rw [hyperLeonardoP, extend]
  have h2 : hyperLeonardoP p n (k - 1) =
      (p + 1) * (∑ i ∈ Finset.range (n / (p + 1) + 1),
        ((n + k - 1 - p * i).choose (i + k - 1) : ℤ)) -
      p * ((n + k - 1).choose (k - 1) : ℤ) := by
    have sum2 : (∑ i ∈ Finset.range (n / (p + 1) + 1),
          ((n + (k - 1) - p * i).choose (i + (k - 1)) : ℤ)) =
        ∑ i ∈ Finset.range (n / (p + 1) + 1),
          ((n + k - 1 - p * i).choose (i + k - 1) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show n + (k - 1) - p * i = n + k - 1 - p * i by omega,
        show i + (k - 1) = i + k - 1 by omega]
    rw [hyperLeonardoP, sum2, show n + (k - 1) = n + k - 1 by omega]
  rw [hyperLeonardoP, h1, h2, sum_eq, pascal_choose]
  ring

/-- **Recurrence for the hyper Leonardo $p$-numbers.** Let $p \ge 1$ be a natural number. For all
natural numbers $n \ge 1$ and $k \ge 1$, the hyper Leonardo $p$-numbers satisfy
$\mathcal{L}^{(k)}_{p,n} = \mathcal{L}^{(k)}_{p,n-1} + \mathcal{L}^{(k-1)}_{p,n}$, and for every
natural number $n$, $\mathcal{L}^{(0)}_{p,n} = \mathcal{L}_{p,n}$, where $\mathcal{L}_{p,n}$ is the
Leonardo $p$-number: $\mathcal{L}_{p,n} = 1$ for $n \le p$ and
$\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 10. -/
theorem hyperLeonardoP_rec (p : ℕ) (hp : 1 ≤ p) :
    (∀ n k, 1 ≤ n → 1 ≤ k →
      hyperLeonardoP p n k = hyperLeonardoP p (n - 1) k + hyperLeonardoP p n (k - 1)) ∧
    ∀ n, hyperLeonardoP p n 0 = leonardoPK p p n := by
  refine ⟨fun n k hn hk => hyperLeonardoP_rec_step p n k hk hn, fun n => ?_⟩
  exact hyperLeonardoP_rec_zero p n hp

private theorem hyperLeonardoP_add_aux (p m n k : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) (hmk : m ≤ k) :
    hyperLeonardoP p (n + m) k =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℤ) * hyperLeonardoP p (n + i) (k - i) := by
  induction m generalizing n k with
  | zero => simp
  | succ r ih =>
      have hrec := (hyperLeonardoP_rec p hp).1 (n + (r + 1)) k (by omega) (by omega)
      rw [show n + (r + 1) - 1 = n + r by omega] at hrec
      calc
        hyperLeonardoP p (n + (r + 1)) k =
            hyperLeonardoP p (n + r) k + hyperLeonardoP p ((n + 1) + r) (k - 1) := by
          rw [hrec, show n + (r + 1) = (n + 1) + r by omega]
        _ = _ := by
          rw [ih n k hn (by omega), ih (n + 1) (k - 1) (by omega) (by omega),
            Finset.sum_choose_succ_mul (fun i _ => hyperLeonardoP p (n + i) (k - i)) r]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (n + 1) + i = n + (i + 1) by omega,
            show k - 1 - i = k - (i + 1) by omega]

set_option linter.unusedVariables false in
/-- **Binomial addition formula for hyper Leonardo $p$-numbers.** For natural numbers $p \ge 1$,
$n \ge 1$, $m \ge 1$ and $k \ge m$, the hyper Leonardo $p$-numbers satisfy
$$\mathcal{L}^{(k)}_{p,n+m} = \sum_{i=0}^{m} \binom{m}{i} \mathcal{L}^{(k-i)}_{p,n+i}.$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 9. -/
public theorem hyperLeonardoP_add (p n m k : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    hyperLeonardoP p (n + m) k =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℤ) * hyperLeonardoP p (n + i) (k - i) :=
  hyperLeonardoP_add_aux p m n k hp hn hmk

end

end MetaMathlibExt
