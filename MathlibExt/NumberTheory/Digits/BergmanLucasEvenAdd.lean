/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations
import MathlibExt.NumberTheory.Digits.BasePhiConjugate
import MathlibExt.NumberTheory.Digits.BasePhiLucasPowers
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Bergman expansion of $L_{2n} + k$

The Bergman expansion of $L_{2n} + k$ is obtained from the Bergman expansion of $k$ by
adjoining the positions $2n$ and $-2n$ whenever $k \le L_{2n-1}$; the proof bounds the
lowest position of a Bergman expansion through its conjugate golden ratio sum and uses
uniqueness of Bergman expansions.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace bergman_lucas_even_add

open BasePhiConjugate
open BasePhiRepresentations (value_pow_le_of_mem)

private theorem upper_bound {S : Finset ℤ} {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) (hSk : basePhiValue S = k) :
    ∀ i ∈ S, i ≤ 2 * (n : ℤ) - 2 := by
  intro i hi
  by_contra hlt
  have hlt : 2 * (n : ℤ) - 2 < i := not_le.mp hlt
  have hexp : ((2 * n - 1 : ℕ) : ℤ) ≤ i := by
    have hcast : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by
      rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hn]
      push_cast
      ring
    rw [hcast]
    omega
  have hle : φ ^ ((2 * n - 1 : ℕ) : ℤ) ≤ φ ^ i :=
    zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le hexp
  have h1 : φ ^ i ≤ (k : ℝ) := by
    rw [← hSk]
    exact value_pow_le_of_mem hi
  have h2 : (k : ℝ) ≤ (lucasNumber (2 * n - 1) : ℝ) := by exact_mod_cast hk
  have h3 := BasePhiLucasPowers.lucas_odd_lt (n - 1)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at h3
  linarith

private theorem min_ge {S : Finset ℤ} {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) (hS : IsBergmanExpansion S)
    (hSk : basePhiValue S = k) (hne : S.Nonempty) :
    -(2 * (n : ℤ)) + 2 ≤ S.min' hne := by
  set m := S.min' hne
  have hm : m ∈ S := Finset.min'_mem S hne
  have hmin : ∀ i ∈ S, m ≤ i := fun i hi => Finset.min'_le S i hi
  have hC := conj_factor_gt hS hm hmin
  have hCpos : (0 : ℝ) < ∑ i ∈ S, ψ ^ (i - m) := by
    have hψpos : (0 : ℝ) < -ψ := by linarith [Real.goldenConj_neg]
    linarith
  have hfactor : ∑ i ∈ S, ψ ^ i = ψ ^ m * ∑ i ∈ S, ψ ^ (i - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← zpow_add₀ Real.goldenConj_ne_zero]
    congr 1
    omega
  have hconj := conj_sum_eq hSk
  have hkge : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hnotOdd : ¬ Odd m := by
    intro hodd
    have hneg : ψ ^ m < 0 := by
      obtain ⟨t, ht⟩ := hodd
      rw [ht, zpow_add₀ Real.goldenConj_ne_zero, zpow_mul, zpow_one]
      have hsq : (0 : ℝ) < ψ ^ (2 : ℤ) := by
        rw [zpow_ofNat, pow_two]
        exact mul_pos_of_neg_of_neg Real.goldenConj_neg Real.goldenConj_neg
      have hpow : (0 : ℝ) < (ψ ^ (2 : ℤ)) ^ t := zpow_pos hsq _
      exact mul_neg_of_pos_of_neg hpow Real.goldenConj_neg
    have hlt : ψ ^ m * ∑ i ∈ S, ψ ^ (i - m) < 0 :=
      mul_neg_of_neg_of_pos hneg hCpos
    rw [← hfactor, hconj] at hlt
    linarith
  have heven : Even m := by
    rcases Int.even_or_odd m with h | h
    · exact h
    · exact absurd h hnotOdd
  by_contra hlt
  have hlt : m < -(2 * (n : ℤ)) + 2 := not_le.mp hlt
  have hmle : m ≤ -(2 * (n : ℤ)) := by
    obtain ⟨t, ht⟩ := heven
    omega
  have hC' : φ⁻¹ < ∑ i ∈ S, ψ ^ (i - m) := by
    rw [Real.inv_goldenRatio]
    exact hC
  have hprod : φ⁻¹ * φ ^ (-m) < (k : ℝ) := by
    have hpos : (0 : ℝ) < φ ^ (-m) := zpow_pos Real.goldenRatio_pos _
    have h1 : φ⁻¹ * φ ^ (-m) < (∑ i ∈ S, ψ ^ (i - m)) * φ ^ (-m) :=
      mul_lt_mul_of_pos_right hC' hpos
    have h2 : (∑ i ∈ S, ψ ^ (i - m)) * φ ^ (-m) = (k : ℝ) := by
      rw [mul_comm, ← even_pow_eq heven, ← hfactor, hconj]
    linarith
  have hpow : φ ^ ((2 : ℤ) * (n : ℤ) - 1) ≤ φ⁻¹ * φ ^ (-m) := by
    have hexp : (2 : ℤ) * (n : ℤ) - 1 ≤ -m + -1 := by omega
    have h3 : φ ^ ((2 : ℤ) * (n : ℤ) - 1) ≤ φ ^ (-m + -1) :=
      zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le hexp
    have h4 : φ ^ (-m + -1) = φ⁻¹ * φ ^ (-m) := by
      rw [zpow_add₀ Real.goldenRatio_ne_zero, zpow_neg_one, mul_comm]
    linarith
  have h2 : (k : ℝ) ≤ (lucasNumber (2 * n - 1) : ℝ) := by exact_mod_cast hk
  have h3 := BasePhiLucasPowers.lucas_odd_lt (n - 1)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at h3
  have hexp2 : ((2 * n - 1 : ℕ) : ℤ) = (2 : ℤ) * (n : ℤ) - 1 := by
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hn]
    push_cast
    ring
  rw [hexp2] at h3
  linarith

private theorem lower_bound {S : Finset ℤ} {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) (hS : IsBergmanExpansion S)
    (hSk : basePhiValue S = k) :
    ∀ i ∈ S, -(2 * (n : ℤ)) + 2 ≤ i := by
  intro i hi
  by_cases hne : S.Nonempty
  · have hmin := min_ge hn hk hS hSk hne
    have hle := Finset.min'_le S i hi
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hi
    simp at hi

end bergman_lucas_even_add

/-- **Bergman expansion of $L_{2n} + k$.** Let $n \ge 1$ and let $k$ be a natural number with
$k \le L_{2n-1}$, where $L_m$ is the $m$-th Lucas number. Let $S$ and $T$ be finite sets of
integers, each with no two consecutive elements (Bergman expansions), whose base phi values are
$k$ and $L_{2n} + k$ respectively. Then $2n \notin S$, $-2n \notin S$, and
$T = S \cup \{2n, -2n\}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 I,
quoting F. M. Dekking, *How to add two numbers in base phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem bergman_lucas_even_add (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) {S T : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSk : basePhiValue S = k)
    (hT : IsBergmanExpansion T) (hTN : basePhiValue T = (lucasNumber (2 * n) + k : ℕ)) :
    (2 * n : ℤ) ∉ S ∧ -(2 * n : ℤ) ∉ S ∧ T = insert (2 * n : ℤ) (insert (-(2 * n : ℤ)) S) := by
  have hnZ : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hub := bergman_lucas_even_add.upper_bound hn hk hSk
  have hlb := bergman_lucas_even_add.lower_bound hn hk hS hSk
  have hnotA : (2 : ℤ) * (n : ℤ) ∉ S := by
    intro h
    have := hub _ h
    omega
  have hnotB : -(2 * (n : ℤ)) ∉ S := by
    intro h
    have := hlb _ h
    omega
  refine ⟨hnotA, hnotB, ?_⟩
  have hval : basePhiValue (insert (2 * (n : ℤ)) (insert (-(2 * (n : ℤ))) S)) =
      basePhiValue T := by
    have hnotA' : (2 : ℤ) * (n : ℤ) ∉ insert (-(2 * (n : ℤ))) S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨by omega, hnotA⟩
    rw [basePhiValue_eq_sum, Finset.sum_insert hnotA', Finset.sum_insert hnotB,
      ← basePhiValue_eq_sum S, hSk, ← add_assoc, BasePhiLucasPowers.pair_value, hTN]
    norm_cast
  have hberg : IsBergmanExpansion
      (insert (2 * (n : ℤ)) (insert (-(2 * (n : ℤ))) S)) := by
    intro i hi
    have hi' : i = 2 * (n : ℤ) ∨ i = -(2 * (n : ℤ)) ∨ i ∈ S := by
      simpa [Finset.mem_insert] using hi
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, ?_, ?_⟩
    · rcases hi' with rfl | rfl | hiS
      · omega
      · omega
      · intro heq
        have := hub i hiS
        omega
    · rcases hi' with rfl | rfl | hiS
      · omega
      · omega
      · intro heq
        have := hlb i hiS
        omega
    · rcases hi' with rfl | rfl | hiS
      · intro hmem
        have := hub _ hmem
        omega
      · intro hmem
        have := hlb _ hmem
        omega
      · exact hS i hiS
  have heq := BasePhiRepresentations.bergman_eq_of_value_eq hberg hT hval
  exact heq.symm


end MetaMathlibExt
