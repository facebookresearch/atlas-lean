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
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import MathlibExt.NumberTheory.Digits.BasePhiConjugate
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

private theorem pow_add_prev (i : ℤ) : φ ^ i + φ ^ (i - 1) = φ ^ (i + 1) := by
  rw [show i = (i - 1) + 1 by omega, show i - 1 + 1 - 1 = i - 1 by omega,
    show i - 1 + 1 + 1 = (i - 1) + 2 by omega, zpow_add₀ Real.goldenRatio_ne_zero,
    zpow_add₀ Real.goldenRatio_ne_zero (i - 1) 2, zpow_one, zpow_ofNat, Real.goldenRatio_sq]
  ring

private theorem value_insert {S : Finset ℤ} {i : ℤ} (hi : i ∉ S) :
    basePhiValue (insert i S) = φ ^ i + basePhiValue S :=
  Finset.sum_insert hi

private theorem value_lt_of_spacing (S : Finset ℤ) (g : ℤ) (hg : g = 1 ∨ g = 2)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → i + g ≤ j) (k : ℤ) (hk : ∀ i ∈ S, i < k) :
    basePhiValue S < φ ^ (k + 2 - g) := by
  induction S using Finset.strongInductionOn generalizing k
  rename_i S ih
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := Finset.max'_mem _ _
    have hrest := ih (S.erase m) (Finset.erase_ssubset hm)
      (fun i hi j hj hij => hgap i (Finset.mem_of_mem_erase hi) j
        (Finset.mem_of_mem_erase hj) hij) (m + 1 - g) (by
      intro i hi
      have hiS := Finset.mem_of_mem_erase hi
      have him : i < m :=
        lt_of_le_of_ne (Finset.le_max' S i hiS) (Finset.ne_of_mem_erase hi)
      have := hgap i hiS m hm him
      omega)
    have heq : basePhiValue S = φ ^ m + basePhiValue (S.erase m) := by
      rw [← value_insert (Finset.notMem_erase m S), Finset.insert_erase hm]
    have hm' := hk m hm
    rw [heq]
    rcases hg with rfl | rfl
    · have h₁ : m + 1 - 1 + 2 - 1 = m + 1 := by omega
      rw [h₁] at hrest
      calc
        _ < φ ^ (m + 1) + φ ^ m := by linarith
        _ = φ ^ (m + 2) := by
          simpa only [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
            using pow_add_prev (m + 1)
        _ ≤ _ := zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
    · have h₂ : m + 1 - 2 + 2 - 2 = m - 1 := by omega
      rw [h₂] at hrest
      calc
        _ < φ ^ m + φ ^ (m - 1) := by linarith
        _ = φ ^ (m + 1) := pow_add_prev m
        _ ≤ _ := zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, basePhiValue_empty]
    exact zpow_pos Real.goldenRatio_pos _

private theorem bergman_value_lt {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {k : ℤ} (hk : ∀ i ∈ S, i < k) : basePhiValue S < φ ^ k := by
  simpa using value_lt_of_spacing S 2 (Or.inr rfl) (by
    intro i hi j hj hij
    have hn := hS i hi
    by_contra! h
    obtain rfl : j = i + 1 := by omega
    exact hn hj) k hk

private theorem value_pow_le_of_mem {S : Finset ℤ} {i : ℤ} (hi : i ∈ S) :
    φ ^ i ≤ basePhiValue S :=
  Finset.single_le_sum (fun j _ => (zpow_pos Real.goldenRatio_pos j).le) hi

private theorem bergman_eq_of_value_eq {S T : Finset ℤ}
    (hS : IsBergmanExpansion S) (hT : IsBergmanExpansion T)
    (hval : basePhiValue S = basePhiValue T) : S = T := by
  classical
  by_contra hne
  let D := (S \ T) ∪ (T \ S)
  have hD : D.Nonempty := by
    by_contra h
    apply hne
    ext i
    have hni : i ∉ D := fun hi => h ⟨i, hi⟩
    simp only [D, Finset.mem_union, Finset.mem_sdiff] at hni
    tauto
  let k := D.max' hD
  have hk : k ∈ D := Finset.max'_mem _ _
  have hdiff : basePhiValue (S \ T) = basePhiValue (T \ S) := by
    have hs := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) (f := fun i : ℤ => φ ^ i)
      Finset.inter_subset_left
    have ht := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := T) (f := fun i : ℤ => φ ^ i)
      Finset.inter_subset_right
    rw [Finset.sdiff_inter_self_left] at hs
    rw [Finset.sdiff_inter_self_right] at ht
    unfold basePhiValue at *
    linarith
  have impossible {A B : Finset ℤ} (hAB : A ∪ B = D)
      (hA : k ∈ A) (hB : k ∉ B) (hBerg : IsBergmanExpansion B)
      (hval : basePhiValue A = basePhiValue B) : False := by
    have hlt := bergman_value_lt hBerg (k := k) (by
      intro i hi
      have hle := Finset.le_max' D i (hAB ▸ Finset.mem_union_right A hi)
      exact lt_of_le_of_ne hle fun h => hB (h ▸ hi))
    exact hlt.not_ge (hval ▸ value_pow_le_of_mem hA)
  rcases Finset.mem_union.mp hk with h | h
  · exact impossible rfl h (fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_sdiff.mp h).1)
      (fun i hi hj => hT i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1) hdiff
  · exact impossible (Finset.union_comm ..) h
      (fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_sdiff.mp h).1)
      (fun i hi hj => hS i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1) hdiff.symm

private theorem lucas_lt_pow {n : ℕ} (hn : 1 ≤ n) :
    (lucasNumber (2 * n - 1) : ℝ) < φ ^ ((2 * n - 1 : ℕ) : ℤ) := by
  rw [← cb_lucas_binet, ← zpow_natCast φ, ← zpow_natCast ψ]
  have hψneg : ψ ^ ((2 * n - 1 : ℕ) : ℤ) < 0 := by
    have hexp : ((2 * n - 1 : ℕ) : ℤ) = 2 * ((n : ℤ) - 1) + 1 := by
      rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hn]
      push_cast
      ring
    rw [hexp, zpow_add₀ Real.goldenConj_ne_zero, zpow_mul, zpow_one]
    have hsq : (0:ℝ) < ψ ^ (2 : ℤ) := by
      rw [zpow_ofNat, pow_two]
      exact mul_pos_of_neg_of_neg Real.goldenConj_neg Real.goldenConj_neg
    have hpow : (0:ℝ) < (ψ ^ (2 : ℤ)) ^ ((n : ℤ) - 1) := zpow_pos hsq _
    have := mul_neg_of_pos_of_neg hpow Real.goldenConj_neg
    exact this
  linarith

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
  have h3 := lucas_lt_pow hn
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
  have h3 := lucas_lt_pow hn
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

private theorem pair_value (n : ℕ) :
    φ ^ (2 * (n : ℤ)) + φ ^ (-(2 * (n : ℤ))) = (lucasNumber (2 * n) : ℝ) := by
  have hcast : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have hev : Even (2 * (n : ℤ)) := by
    use (n : ℤ)
    ring
  rw [← cb_lucas_binet, ← zpow_natCast φ, ← zpow_natCast ψ, hcast]
  congr 1
  exact (even_pow_eq hev).symm

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
    rw [bergman_lucas_even_add.value_insert hnotA',
      bergman_lucas_even_add.value_insert hnotB, hSk, ← add_assoc,
      bergman_lucas_even_add.pair_value, hTN]
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
  have heq := bergman_lucas_even_add.bergman_eq_of_value_eq hberg hT hval
  exact heq.symm


end MetaMathlibExt
