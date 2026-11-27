/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import MathlibExt.NumberTheory.Digits.BasePhiConjugate
public import MathlibExt.NumberTheory.Digits.BergmanLucasEvenAdd
public import MathlibExt.NumberTheory.Digits.BergmanWordFib
public import MathlibExt.NumberTheory.Digits.FibMemLucasIntervals
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Lowest Bergman digit from the Lucas interval

The lowest position of the Bergman expansion of a natural number `N` is determined by the Lucas
interval containing `N`: on the even interval `[L_{2n}, L_{2n+1}]` it is `-2n`, and on the odd
interval `[L_{2n+1} + 1, L_{2n+2} - 1]` it is `-2n - 2`. The proof factors the conjugate golden
ratio sum through the lowest position and bounds the value between consecutive odd powers of the
golden ratio.

Statements from Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci
Quarterly 62 (2024), no. 2, 112-124.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace bergman_lowest_position_lucasInterval

open BasePhiConjugate

private theorem conj_factor_lt {S : Finset ℤ} {R : ℤ} (hmin : ∀ i ∈ S, R ≤ i) :
    ∑ i ∈ S, ψ ^ (i - R) < φ := by
  classical
  set r : ℝ := -ψ with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith [Real.goldenConj_neg]
  have hr1 : r < 1 := by rw [hrdef]; linarith [Real.neg_one_lt_goldenConj]
  have hψr : ψ = -r := by rw [hrdef]; ring
  have hr2 : (1 : ℝ) - r ^ 2 = r := by
    have h : r = φ - 1 := by
      rw [hrdef]
      linarith [Real.goldenRatio_add_goldenConj]
    rw [h]
    linear_combination -Real.goldenRatio_sq
  have hterm : ∀ j : ℤ, Even j → ψ ^ j = r ^ j := by
    intro j hj
    rw [hψr]
    exact hj.neg_zpow r
  have htermOdd : ∀ j : ℤ, Odd j → ψ ^ j = -r ^ j := by
    intro j hj
    rw [hψr]
    exact hj.neg_zpow r
  let E := S.filter fun i => Even (i - R)
  let O := S.filter fun i => ¬ Even (i - R)
  have hsplit : ∑ i ∈ S, ψ ^ (i - R) =
      (∑ i ∈ E, ψ ^ (i - R)) + ∑ i ∈ O, ψ ^ (i - R) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => Even (i - R)) _]
  have hE : (∑ i ∈ E, ψ ^ (i - R)) = ∑ i ∈ E, r ^ (i - R) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm _ (Finset.mem_filter.mp hi).2
  have hO : ∑ i ∈ O, ψ ^ (i - R) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hodd : Odd (i - R) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2
    rw [htermOdd (i - R) hodd]
    have hnn : (0 : ℝ) ≤ r ^ (i - R) := (zpow_pos hr0 _).le
    linarith
  -- Reindex the even offsets by `t = (i - R).toNat / 2`.
  let f : ℤ → ℕ := fun i => (i - R).toNat / 2
  let A : Finset ℕ := E.image f
  have hjnat : ∀ i ∈ E, (i - R).toNat = 2 * f i := by
    intro i hi
    have hev : Even (i - R) := (Finset.mem_filter.mp hi).2
    have hcast : ((i - R).toNat : ℤ) = i - R :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    have hevNat : Even (i - R).toNat := by
      have h := hev
      rw [← hcast] at h
      exact (Int.even_natCast _).mp h
    obtain ⟨k, hk⟩ := hevNat
    have hf : f i = (i - R).toNat / 2 := rfl
    omega
  have hinj : Set.InjOn f E := by
    intro i hi j hj hij
    have h1 := hjnat i hi
    have h2 := hjnat j hj
    have hcast1 : ((i - R).toNat : ℤ) = i - R :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    have hcast2 : ((j - R).toNat : ℤ) = j - R :=
      Int.toNat_of_nonneg (by have := hmin j (Finset.mem_filter.mp hj).1; omega)
    omega
  have hAeq : (∑ t ∈ A, (r ^ 2) ^ t) = ∑ i ∈ E, r ^ (i - R) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    have h1 := hjnat i hi
    have hcast : ((i - R).toNat : ℤ) = i - R :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    have h2 : i - R = 2 * (f i : ℤ) := by
      have h1c : ((i - R).toNat : ℤ) = 2 * (f i : ℤ) := by exact_mod_cast h1
      omega
    have h3 : (2 : ℤ) * (f i : ℤ) = ((2 * f i : ℕ) : ℤ) := by push_cast; ring
    rw [h2, h3, zpow_natCast, pow_mul]
  -- Every index lies below `M`, so the sum is below the `M`-th partial geometric sum.
  set M : ℕ := A.sum id + 1 with hMdef
  have hsub : A ⊆ Finset.range M := by
    intro t ht
    have hle : t ≤ A.sum id := Finset.single_le_sum (fun t _ => Nat.zero_le t) ht
    rw [Finset.mem_range]
    omega
  have hAle : (∑ t ∈ A, (r ^ 2) ^ t) ≤ ∑ t ∈ Finset.range M, (r ^ 2) ^ t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro t _ _
    positivity
  have hSlt : (∑ t ∈ Finset.range M, (r ^ 2) ^ t) < φ := by
    have hrinv : r⁻¹ = φ := by
      rw [hrdef, ← Real.inv_goldenRatio, inv_inv]
    have hgeom := geom_sum_mul_neg (r ^ 2) M
    have hX1 : r ^ 2 < 1 := pow_lt_one₀ hr0.le hr1 two_ne_zero
    have hMpos : M ≠ 0 := by omega
    have hXM : (r ^ 2) ^ M < 1 := pow_lt_one₀ (sq_nonneg r) hX1 hMpos
    have hXMpos : (0 : ℝ) < (r ^ 2) ^ M := pow_pos (pow_pos hr0 2) M
    have hpos : (0 : ℝ) < 1 - r ^ 2 := by linarith
    have h1 : (∑ t ∈ Finset.range M, (r ^ 2) ^ t) * (1 - r ^ 2) < 1 := by
      rw [hgeom]
      linarith
    have h2 : (∑ t ∈ Finset.range M, (r ^ 2) ^ t) < (1 - r ^ 2)⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hpos]
      exact h1
    rw [hr2] at h2
    rw [hrinv] at h2
    exact h2
  rw [hsplit, hE]
  calc (∑ i ∈ E, r ^ (i - R)) + ∑ i ∈ O, ψ ^ (i - R)
      ≤ (∑ i ∈ E, r ^ (i - R)) + 0 := add_le_add_right hO _
    _ = ∑ i ∈ E, r ^ (i - R) := add_zero _
    _ = ∑ t ∈ A, (r ^ 2) ^ t := hAeq.symm
    _ ≤ ∑ t ∈ Finset.range M, (r ^ 2) ^ t := hAle
    _ < φ := hSlt

private theorem even_min_of_bergman {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {R : ℤ} (hmem : R ∈ S) (hmin : ∀ i ∈ S, R ≤ i) {N : ℕ}
    (hSN : basePhiValue S = N) : Even R := by
  have hfactor : ∑ i ∈ S, ψ ^ i = ψ ^ R * ∑ i ∈ S, ψ ^ (i - R) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← zpow_add₀ Real.goldenConj_ne_zero]
    congr 1
    omega
  have hC := conj_factor_gt hS hmem hmin
  have hCpos : (0 : ℝ) < ∑ i ∈ S, ψ ^ (i - R) := by
    have hψpos : (0 : ℝ) < -ψ := by linarith [Real.goldenConj_neg]
    linarith
  have hconj := conj_sum_eq hSN
  have hnotOdd : ¬ Odd R := by
    intro hodd
    have hneg : ψ ^ R < 0 := by
      obtain ⟨t, ht⟩ := hodd
      rw [ht, zpow_add₀ Real.goldenConj_ne_zero, zpow_mul, zpow_one]
      have hsq : (0 : ℝ) < ψ ^ (2 : ℤ) := by
        rw [zpow_ofNat, pow_two]
        exact mul_pos_of_neg_of_neg Real.goldenConj_neg Real.goldenConj_neg
      have hpow : (0 : ℝ) < (ψ ^ (2 : ℤ)) ^ t := zpow_pos hsq _
      exact mul_neg_of_pos_of_neg hpow Real.goldenConj_neg
    have hlt : ψ ^ R * ∑ i ∈ S, ψ ^ (i - R) < 0 :=
      mul_neg_of_neg_of_pos hneg hCpos
    rw [← hfactor, hconj] at hlt
    have hkge : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  rcases Int.even_or_odd R with h | h
  · exact h
  · exact absurd h hnotOdd

private theorem psi_even_pow_pos (k : ℕ) : (0 : ℝ) < ψ ^ (2 * k) := by
  have hψ2 : (0 : ℝ) < ψ ^ 2 := by
    rw [pow_two]
    exact mul_pos_of_neg_of_neg Real.goldenConj_neg Real.goldenConj_neg
  calc (0 : ℝ) < (ψ ^ 2) ^ k := pow_pos hψ2 k
    _ = ψ ^ (2 * k) := by rw [← pow_mul]

private theorem lucas_even_gt (k : ℕ) :
    φ ^ ((2 * k : ℕ) : ℤ) < (lucasNumber (2 * k) : ℝ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hψ := psi_even_pow_pos k
  linarith

private theorem lucas_odd_lt (k : ℕ) :
    (lucasNumber (2 * k + 1) : ℝ) < φ ^ ((2 * k + 1 : ℕ) : ℤ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hψr : ψ = -(-ψ) := by ring
  have hpos : (0 : ℝ) < -ψ := by linarith [Real.goldenConj_neg]
  have h2 : ψ ^ (2 * k + 1) = -((-ψ) ^ (2 * k + 1)) := by
    conv_lhs => rw [hψr]
    exact hodd.neg_pow (-ψ)
  have h1 : (0 : ℝ) < (-ψ) ^ (2 * k + 1) := pow_pos hpos _
  linarith

private theorem lucas_odd_add_one_gt (k : ℕ) :
    φ ^ ((2 * k + 1 : ℕ) : ℤ) < (lucasNumber (2 * k + 1) : ℝ) + 1 := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hψr : ψ = -(-ψ) := by ring
  have hr0 : (0 : ℝ) ≤ -ψ := le_of_lt (by linarith [Real.goldenConj_neg])
  have hr1 : -ψ < 1 := by linarith [Real.neg_one_lt_goldenConj]
  have h1 : (-ψ) ^ (2 * k + 1) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have h2 : ψ ^ (2 * k + 1) = -((-ψ) ^ (2 * k + 1)) := by
    conv_lhs => rw [hψr]
    exact hodd.neg_pow (-ψ)
  linarith

private theorem lucas_even_sub_one_lt (k : ℕ) :
    (lucasNumber (2 * k + 2) : ℝ) - 1 < φ ^ ((2 * k + 2 : ℕ) : ℤ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  have hψr : ψ = -(-ψ) := by ring
  have hr0 : (0 : ℝ) ≤ -ψ := le_of_lt (by linarith [Real.goldenConj_neg])
  have hr1 : -ψ < 1 := by linarith [Real.neg_one_lt_goldenConj]
  have h1 : (-ψ) ^ (2 * k + 2) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have h2 : ψ ^ (2 * k + 2) = (-ψ) ^ (2 * k + 2) := by
    conv_lhs => rw [hψr]
    exact hev.neg_pow (-ψ)
  linarith

private theorem phi_pow_bounds {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {N : ℕ} (hSN : basePhiValue S = N) {R : ℤ} (hmem : R ∈ S)
    (hmin : ∀ i ∈ S, R ≤ i) :
    Even (-R) ∧ φ ^ (-R - 1) < (N : ℝ) ∧ (N : ℝ) < φ ^ (-R + 1) := by
  have hevR := even_min_of_bergman hS hmem hmin hSN
  have hevu : Even (-R) := even_neg.mpr hevR
  have hfactor : ∑ i ∈ S, ψ ^ i = ψ ^ R * ∑ i ∈ S, ψ ^ (i - R) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← zpow_add₀ Real.goldenConj_ne_zero]
    congr 1
    omega
  have hconj := conj_sum_eq hSN
  have hClow := conj_factor_gt hS hmem hmin
  have hChigh := conj_factor_lt hmin
  have hψR : ψ ^ R = φ ^ (-R) := even_pow_eq hevR
  have hN : (N : ℝ) = φ ^ (-R) * ∑ i ∈ S, ψ ^ (i - R) := by
    rw [← hconj, hfactor, hψR]
  have hφu : (0 : ℝ) < φ ^ (-R) := zpow_pos Real.goldenRatio_pos _
  have hinv : φ⁻¹ = -ψ := Real.inv_goldenRatio
  refine ⟨hevu, ?_, ?_⟩
  · have hlt : φ ^ (-R) * φ⁻¹ < φ ^ (-R) * ∑ i ∈ S, ψ ^ (i - R) :=
      mul_lt_mul_of_pos_left (by linarith) hφu
    have hpow : φ ^ (-R - 1) = φ ^ (-R) * φ⁻¹ :=
      zpow_sub_one₀ Real.goldenRatio_ne_zero _
    rw [hN, hpow]
    exact hlt
  · have hlt : φ ^ (-R) * ∑ i ∈ S, ψ ^ (i - R) < φ ^ (-R) * φ :=
      mul_lt_mul_of_pos_left hChigh hφu
    have hpow : φ ^ (-R + 1) = φ ^ (-R) * φ :=
      zpow_add_one₀ Real.goldenRatio_ne_zero _
    rw [hN, hpow]
    exact hlt

end bergman_lowest_position_lucasInterval

/-- **Lowest Bergman digit of $N$ from its Lucas interval.** Let $N$ and $n$ be natural numbers,
let $S$ be a finite set of integers with no two consecutive elements (a Bergman expansion) whose
base phi value is $N$, and let $R$ be the least element of $S$. Write $L_m$ for the $m$-th Lucas
number. If $L_{2n} \le N \le L_{2n+1}$, then $-R = 2n$. If $L_{2n+1} + 1 \le N \le L_{2n+2} - 1$,
then $-R = 2n + 2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(b)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem bergman_lowest_position_lucasInterval (N n : ℕ) {S : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) {R : ℤ}
    (hR : IsLeast (S : Set ℤ) R) :
    (N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) → -R = 2 * n) ∧
      (N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1) →
        -R = 2 * n + 2) := by
  have hmem : R ∈ S := Finset.mem_coe.mp hR.1
  have hlb := mem_lowerBounds.mp hR.2
  have hmin : ∀ i ∈ S, R ≤ i := fun i hi => hlb _ (Finset.mem_coe.mpr hi)
  obtain ⟨hevu, hlo, hhi⟩ :=
    bergman_lowest_position_lucasInterval.phi_pow_bounds hS hSN hmem hmin
  have hφ := Real.one_lt_goldenRatio
  constructor
  · intro hN
    obtain ⟨hloN, hhiN⟩ := Set.mem_Icc.mp hN
    have hNlt : (N : ℝ) < φ ^ ((2 * n + 1 : ℕ) : ℤ) := by
      have h1 : (N : ℝ) ≤ (lucasNumber (2 * n + 1) : ℝ) := by exact_mod_cast hhiN
      have h2 := bergman_lowest_position_lucasInterval.lucas_odd_lt n
      linarith
    have hexp1 : -R - 1 < ((2 * n + 1 : ℕ) : ℤ) :=
      (zpow_lt_zpow_iff_right₀ hφ).mp (lt_trans hlo hNlt)
    have hNgt : φ ^ ((2 * n : ℕ) : ℤ) < (N : ℝ) := by
      have h1 : (lucasNumber (2 * n) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hloN
      have h2 := bergman_lowest_position_lucasInterval.lucas_even_gt n
      linarith
    have hexp2 : ((2 * n : ℕ) : ℤ) < -R + 1 :=
      (zpow_lt_zpow_iff_right₀ hφ).mp (lt_trans hNgt hhi)
    push_cast at hexp1 hexp2
    obtain ⟨r, hr⟩ := hevu
    omega
  · intro hN
    obtain ⟨hloN, hhiN⟩ := Set.mem_Icc.mp hN
    have hNgt : φ ^ ((2 * n + 1 : ℕ) : ℤ) < (N : ℝ) := by
      have h1 : (lucasNumber (2 * n + 1) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hloN
      have h2 := bergman_lowest_position_lucasInterval.lucas_odd_add_one_gt n
      linarith
    have hexp1 : ((2 * n + 1 : ℕ) : ℤ) < -R + 1 :=
      (zpow_lt_zpow_iff_right₀ hφ).mp (lt_trans hNgt hhi)
    have hBge : 2 ≤ lucasNumber (2 * n + 2) := by omega
    have hN1 : N + 1 ≤ lucasNumber (2 * n + 2) := by omega
    have hNlt : (N : ℝ) < φ ^ ((2 * n + 2 : ℕ) : ℤ) := by
      have h1 : (N : ℝ) + 1 ≤ (lucasNumber (2 * n + 2) : ℝ) := by exact_mod_cast hN1
      have h2 := bergman_lowest_position_lucasInterval.lucas_even_sub_one_lt n
      linarith
    have hexp2 : -R - 1 < ((2 * n + 2 : ℕ) : ℤ) :=
      (zpow_lt_zpow_iff_right₀ hφ).mp (lt_trans hlo hNlt)
    push_cast at hexp1 hexp2
    obtain ⟨r, hr⟩ := hevu
    omega

end MetaMathlibExt
