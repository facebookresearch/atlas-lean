/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace MetaMathlibExt

private theorem fib_eq_range_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), (n - k).choose k := by
  have h1 := Nat.fib_succ_eq_sum_choose n
  have h2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (M := ℕ) (fun p : ℕ × ℕ => p.1.choose p.2) n
  rw [h1, h2]
  have h3 : (∑ k ∈ Finset.range (n + 1), k.choose (n - k))
      = ∑ k ∈ Finset.range (n + 1), (n - k).choose k := by
    have hrefl := Finset.sum_range_reflect (fun k => k.choose (n - k)) (n + 1)
    rw [← hrefl]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have e1 : n + 1 - 1 - j = n - j := by omega
    rw [e1]
    have e2 : n - (n - j) = j := by omega
    rw [e2]
  simpa using h3

private theorem fib_eq_trunc_range_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n / 2 + 1), (n - k).choose k := by
  rw [fib_eq_range_choose n]
  symm
  have hsub : Finset.range (n / 2 + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  apply Finset.sum_subset hsub
  intro x hx hxout
  rw [Finset.mem_range] at hx hxout
  have hx2 : n / 2 + 1 ≤ x := Nat.le_of_not_lt hxout
  show (n - x).choose x = 0
  apply Nat.choose_eq_zero_of_lt
  omega

private theorem inner_pascal (n k : ℕ) (h : 2 * k ≤ n) :
    (∑ q ∈ Finset.range (n + 2 - 2 * k + 1), (n + 2 - k).choose q)
      = 2 * (∑ q ∈ Finset.range (n + 1 - 2 * k + 1), (n + 1 - k).choose q)
        + (if k = 0 then (0:ℕ) else (n + 1 - k).choose (k - 1)) := by
  have eA : n + 2 - 2 * k + 1 = (n - 2 * k + 2) + 1 := by omega
  have eB : n + 1 - 2 * k + 1 = (n - 2 * k + 2) := by omega
  have eN : n + 2 - k = (n + 1 - k) + 1 := by omega
  rw [eA, eB, eN, Finset.sum_range_succ', Nat.choose_zero_right]
  have hP : (∑ j ∈ Finset.range (n - 2 * k + 2), ((n + 1 - k) + 1).choose (j + 1))
      = (∑ j ∈ Finset.range (n - 2 * k + 2), (n + 1 - k).choose j)
        + (∑ j ∈ Finset.range (n - 2 * k + 2), (n + 1 - k).choose (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.choose_succ_succ _ _
  rw [hP]
  have hS : (∑ j ∈ Finset.range (n - 2 * k + 2), (n + 1 - k).choose (j + 1)) + 1
      = (∑ q ∈ Finset.range (n - 2 * k + 2), (n + 1 - k).choose q)
        + (n + 1 - k).choose (n - 2 * k + 2) := by
    have h1 := Finset.sum_range_succ' (fun t => (n + 1 - k).choose t) (n - 2 * k + 2)
    have h2 := Finset.sum_range_succ (fun t => (n + 1 - k).choose t) (n - 2 * k + 2)
    have h12 := h1.symm.trans h2
    rwa [Nat.choose_zero_right] at h12
  have hB1 : 1 ≤ ∑ q ∈ Finset.range (n - 2 * k + 2), (n + 1 - k).choose q := by
    have hmem : 0 ∈ Finset.range (n - 2 * k + 2) := by
      simp only [Finset.mem_range]; omega
    have hle := Finset.single_le_sum
      (fun i _ => Nat.zero_le ((n + 1 - k).choose i)) hmem
    rwa [Nat.choose_zero_right] at hle
  have hcorr : (n + 1 - k).choose (n - 2 * k + 2)
      = (if k = 0 then (0:ℕ) else (n + 1 - k).choose (k - 1)) := by
    split
    · next hk0 =>
      subst hk0
      simp only [Nat.sub_zero, Nat.mul_zero]
      apply Nat.choose_eq_zero_of_lt
      omega
    · next hk0 =>
      have hle : n - 2 * k + 2 ≤ n + 1 - k := by omega
      have hsym := Nat.choose_symm hle
      have heq : n + 1 - k - (n - 2 * k + 2) = k - 1 := by omega
      rw [heq] at hsym
      exact hsym.symm
  omega

private theorem inner_boundary_odd (n k : ℕ) (h : 2 * k = n + 1) :
    (∑ q ∈ Finset.range (n + 2 - 2 * k + 1), (n + 2 - k).choose q)
      = 2 * (∑ q ∈ Finset.range (n + 1 - 2 * k + 1), (n + 1 - k).choose q)
        + (if k = 0 then (0:ℕ) else (n + 1 - k).choose (k - 1)) := by
  have hk : k ≠ 0 := by omega
  have eA : n + 2 - 2 * k + 1 = 1 + 1 := by omega
  have eB : n + 1 - 2 * k + 1 = 0 + 1 := by omega
  have eN : n + 2 - k = k + 1 := by omega
  have eN' : n + 1 - k = k := by omega
  rw [eA, eB, eN, eN']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have ekm : m + 1 - 1 = m := by omega
  rw [ekm, Nat.choose_succ_self_right]
  split
  · next h0 => omega
  · next _ => omega

private theorem inner_boundary_even (n k : ℕ) (h : 2 * k = n + 2) :
    (∑ q ∈ Finset.range (n + 2 - 2 * k + 1), (n + 2 - k).choose q) = 1
    ∧ (if k = 0 then (0:ℕ) else (n + 1 - k).choose (k - 1)) = 1 := by
  have hk : k ≠ 0 := by omega
  have eA : n + 2 - 2 * k + 1 = 0 + 1 := by omega
  have eN : n + 2 - k = k := by omega
  have eN' : n + 1 - k = k - 1 := by omega
  constructor
  · rw [eA, eN]
    simp
  · rw [eN']
    split
    · next h0 => omega
    · next _ => exact Nat.choose_self _

private theorem S_add_two (n : ℕ) :
    (∑ k ∈ Finset.range ((n + 2) / 2 + 1),
      ∑ q ∈ Finset.range (n + 2 - 2 * k + 1), (n + 2 - k).choose q)
    = 2 * (∑ k ∈ Finset.range ((n + 1) / 2 + 1),
        ∑ q ∈ Finset.range (n + 1 - 2 * k + 1), (n + 1 - k).choose q)
      + Nat.fib (n + 1) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have eR : (m + m + 2) / 2 + 1 = (m + 1) + 1 := by omega
    have eR' : (m + m + 1) / 2 + 1 = m + 1 := by omega
    have eF : (m + m) / 2 + 1 = m + 1 := by omega
    rw [eR, eR', Finset.sum_range_succ]
    have hper : ∀ k ∈ Finset.range (m + 1),
        (∑ q ∈ Finset.range (m + m + 2 - 2 * k + 1), (m + m + 2 - k).choose q)
        = 2 * (∑ q ∈ Finset.range (m + m + 1 - 2 * k + 1), (m + m + 1 - k).choose q)
          + (if k = 0 then (0:ℕ) else (m + m + 1 - k).choose (k - 1)) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      exact inner_pascal (m + m) k (by omega)
    have hsum : (∑ k ∈ Finset.range (m + 1),
          (∑ q ∈ Finset.range (m + m + 2 - 2 * k + 1), (m + m + 2 - k).choose q))
        = (∑ k ∈ Finset.range (m + 1),
          (2 * (∑ q ∈ Finset.range (m + m + 1 - 2 * k + 1), (m + m + 1 - k).choose q)
            + (if k = 0 then (0:ℕ) else (m + m + 1 - k).choose (k - 1)))) :=
      Finset.sum_congr rfl hper
    rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have htop := inner_boundary_even (m + m) (m + 1) (by omega)
    rw [htop.1]
    have hfib := fib_eq_trunc_range_choose (m + m)
    rw [eF, Finset.sum_range_succ] at hfib
    have eTop : ((m + m) - m).choose m = 1 := by
      rw [Nat.add_sub_cancel]
      exact Nat.choose_self m
    rw [eTop] at hfib
    have hci : (∑ k ∈ Finset.range (m + 1),
          (if k = 0 then (0:ℕ) else (m + m + 1 - k).choose (k - 1)))
        = ∑ j ∈ Finset.range m, ((m + m) - j).choose j := by
      have hstep : ∀ j ∈ Finset.range m,
          (if j + 1 = 0 then (0:ℕ) else (m + m + 1 - (j + 1)).choose (j + 1 - 1))
          = ((m + m) - j).choose j := by
        intro j _
        have e1 : m + m + 1 - (j + 1) = (m + m) - j := by omega
        have e2 : j + 1 - 1 = j := by omega
        split
        · next h => omega
        · next _ => rw [e1, e2]
      have hcc : (∑ j ∈ Finset.range m,
            (if j + 1 = 0 then (0:ℕ) else (m + m + 1 - (j + 1)).choose (j + 1 - 1)))
          = ∑ j ∈ Finset.range m, ((m + m) - j).choose j :=
        Finset.sum_congr rfl hstep
      have hpeel : (∑ k ∈ Finset.range (m + 1),
            (if k = 0 then (0:ℕ) else (m + m + 1 - k).choose (k - 1)))
          = (∑ j ∈ Finset.range m,
              (if j + 1 = 0 then (0:ℕ) else (m + m + 1 - (j + 1)).choose (j + 1 - 1)))
            + (if (0:ℕ) = 0 then (0:ℕ) else (m + m + 1 - 0).choose (0 - 1)) :=
        Finset.sum_range_succ' _ _
      rw [hpeel, hcc]
      simp
    rw [hci, add_assoc, ← hfib]
  · have eR : (2 * m + 1 + 2) / 2 + 1 = m + 2 := by omega
    have eR' : (2 * m + 1 + 1) / 2 + 1 = m + 2 := by omega
    have eF : (2 * m + 1) / 2 + 1 = m + 1 := by omega
    rw [eR, eR']
    have hper : ∀ k ∈ Finset.range (m + 2),
        (∑ q ∈ Finset.range (2 * m + 1 + 2 - 2 * k + 1), (2 * m + 1 + 2 - k).choose q)
        = 2 * (∑ q ∈ Finset.range (2 * m + 1 + 1 - 2 * k + 1), (2 * m + 1 + 1 - k).choose q)
          + (if k = 0 then (0:ℕ) else (2 * m + 1 + 1 - k).choose (k - 1)) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      by_cases h2k : 2 * k ≤ 2 * m + 1
      · exact inner_pascal (2 * m + 1) k h2k
      · have h2ke : 2 * k = (2 * m + 1) + 1 := by omega
        exact inner_boundary_odd (2 * m + 1) k h2ke
    have hsum : (∑ k ∈ Finset.range (m + 2),
          (∑ q ∈ Finset.range (2 * m + 1 + 2 - 2 * k + 1), (2 * m + 1 + 2 - k).choose q))
        = (∑ k ∈ Finset.range (m + 2),
          (2 * (∑ q ∈ Finset.range (2 * m + 1 + 1 - 2 * k + 1), (2 * m + 1 + 1 - k).choose q)
            + (if k = 0 then (0:ℕ) else (2 * m + 1 + 1 - k).choose (k - 1)))) :=
      Finset.sum_congr rfl hper
    rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hfib := fib_eq_trunc_range_choose (2 * m + 1)
    rw [eF] at hfib
    have hci : (∑ k ∈ Finset.range (m + 2),
          (if k = 0 then (0:ℕ) else (2 * m + 1 + 1 - k).choose (k - 1)))
        = ∑ j ∈ Finset.range (m + 1), ((2 * m + 1) - j).choose j := by
      have hstep : ∀ j ∈ Finset.range (m + 1),
          (if j + 1 = 0 then (0:ℕ) else (2 * m + 1 + 1 - (j + 1)).choose (j + 1 - 1))
          = ((2 * m + 1) - j).choose j := by
        intro j _
        have e1 : 2 * m + 1 + 1 - (j + 1) = (2 * m + 1) - j := by omega
        have e2 : j + 1 - 1 = j := by omega
        split
        · next h => omega
        · next _ => rw [e1, e2]
      have hcc : (∑ j ∈ Finset.range (m + 1),
            (if j + 1 = 0 then (0:ℕ) else (2 * m + 1 + 1 - (j + 1)).choose (j + 1 - 1)))
          = ∑ j ∈ Finset.range (m + 1), ((2 * m + 1) - j).choose j :=
        Finset.sum_congr rfl hstep
      have hpeel : (∑ k ∈ Finset.range (m + 2),
            (if k = 0 then (0:ℕ) else (2 * m + 1 + 1 - k).choose (k - 1)))
          = (∑ j ∈ Finset.range (m + 1),
              (if j + 1 = 0 then (0:ℕ) else (2 * m + 1 + 1 - (j + 1)).choose (j + 1 - 1)))
            + (if (0:ℕ) = 0 then (0:ℕ) else (2 * m + 1 + 1 - 0).choose (0 - 1)) :=
        Finset.sum_range_succ' _ _
      rw [hpeel, hcc]
      simp
    rw [hci, hfib]

/--
**A binomial double sum equal to a power of two minus a Fibonacci number.** For every natural
number $n$,

$$\sum_{k=0}^{\lfloor n/2 \rfloor} \sum_{q=0}^{n-2k} \binom{n-k}{q} = 2^{n+1} - F_{n+2},$$

where $F_m$ is the $m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$.

Proves `Wanted` entry `binomial_double_sum_eq_pow_sub_fib`.

Source: Denis Neiter and Amsha Proag, "Links Between Sums Over Paths in
Bernoulli's Triangles and the Fibonacci Numbers," Journal of Integer
Sequences 19 (2016), Article 16.8.3, Theorem (label theoremS2),
lines 247–252,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Proag/proag3.tex
-/
theorem binomial_double_sum_eq_pow_sub_fib (n : ℕ) :
    (∑ k ∈ Finset.range (n / 2 + 1),
      ∑ q ∈ Finset.range (n - 2 * k + 1), Nat.choose (n - k) q) =
      2 ^ (n + 1) - Nat.fib (n + 2) := by
  have hall : ∀ m, (∑ k ∈ Finset.range (m / 2 + 1),
        ∑ q ∈ Finset.range (m - 2 * k + 1), Nat.choose (m - k) q)
      + Nat.fib (m + 2) = 2 ^ (m + 1) := by
    have base0 : (∑ k ∈ Finset.range (0 / 2 + 1),
          ∑ q ∈ Finset.range (0 - 2 * k + 1), Nat.choose (0 - k) q)
        + Nat.fib (0 + 2) = 2 ^ (0 + 1) := by
      simp [Nat.fib_two]
    have base1 : (∑ k ∈ Finset.range (1 / 2 + 1),
          ∑ q ∈ Finset.range (1 - 2 * k + 1), Nat.choose (1 - k) q)
        + Nat.fib (1 + 2) = 2 ^ (1 + 1) := by
      simp [Finset.sum_range_succ, Nat.fib_add_two, Nat.fib_one]
    have step : ∀ m, (∑ k ∈ Finset.range (m / 2 + 1),
          ∑ q ∈ Finset.range (m - 2 * k + 1), Nat.choose (m - k) q)
        + Nat.fib (m + 2) = 2 ^ (m + 1) →
        (∑ k ∈ Finset.range ((m + 1) / 2 + 1),
          ∑ q ∈ Finset.range (m + 1 - 2 * k + 1), Nat.choose (m + 1 - k) q)
        + Nat.fib ((m + 1) + 2) = 2 ^ ((m + 1) + 1) →
        (∑ k ∈ Finset.range ((m + 2) / 2 + 1),
          ∑ q ∈ Finset.range (m + 2 - 2 * k + 1), Nat.choose (m + 2 - k) q)
        + Nat.fib ((m + 2) + 2) = 2 ^ ((m + 2) + 1) := by
      intro m ih0 ih1
      have hS := S_add_two m
      have hf1 : Nat.fib (m + 1) + Nat.fib (m + 2) = Nat.fib ((m + 1) + 2) := by
        have h := Nat.fib_add_two (n := m + 1)
        have e2 : (m + 1) + 1 = m + 2 := by omega
        rw [e2] at h
        exact h.symm
      have hf2 : Nat.fib ((m + 2) + 2) = Nat.fib (m + 2) + Nat.fib ((m + 1) + 2) := by
        have h := Nat.fib_add_two (n := m + 2)
        have e2 : (m + 2) + 1 = (m + 1) + 2 := by omega
        rw [e2] at h
        exact h
      have hp : (2:ℕ) ^ ((m + 2) + 1) = 2 * 2 ^ ((m + 1) + 1) := by
        have e : (m + 2) + 1 = ((m + 1) + 1) + 1 := by omega
        rw [e, pow_succ, mul_comm]
      omega
    intro m
    refine Nat.twoStepInduction (motive := fun m =>
      (∑ k ∈ Finset.range (m / 2 + 1),
        ∑ q ∈ Finset.range (m - 2 * k + 1), Nat.choose (m - k) q)
      + Nat.fib (m + 2) = 2 ^ (m + 1)) base0 base1 step m
  have hQ := hall n
  omega
