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

/-!
# Conjugate golden ratio sums of base phi expansions

Facts about the conjugate $\psi = 1 - \varphi$ of the golden ratio $\varphi$ shared by the proofs
about the lowest position of a Bergman expansion:

* `pow_repr`: $\varphi^i = a + b\varphi$ and $\psi^i = a + b\psi$ for the same integers $a, b$.
* `conj_sum_eq`: a finite set $S$ of integers with $\sum_{i \in S} \varphi^i = k \in \mathbb{N}$
  also has $\sum_{i \in S} \psi^i = k$.
* `conj_factor_gt`: for a Bergman expansion $S$ with least element $m$,
  $\sum_{i \in S} \psi^{i - m} > -\psi$.
* `even_pow_eq`: $\psi^j = \varphi^{-j}$ for even $j$.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace BasePhiConjugate

/-- **Integer powers of the golden ratio.** For every integer $i$ there are integers $a$ and $b$
with $\varphi^i = a + b\varphi$ and $\psi^i = a + b\psi$, where $\psi$ is the conjugate of the
golden ratio $\varphi$. -/
public theorem pow_repr (i : ℤ) :
    ∃ a b : ℤ, φ ^ i = a + b * φ ∧ ψ ^ i = a + b * ψ := by
  induction i using Int.induction_on with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨a, b, hφ, hψ⟩ := ih
    refine ⟨b, a + b, ?_, ?_⟩
    · rw [show (↑n + 1 : ℤ) = (n : ℤ) + (1 : ℤ) by norm_cast,
        zpow_add₀ Real.goldenRatio_ne_zero, zpow_one, hφ]
      push_cast
      linear_combination (b : ℝ) * Real.goldenRatio_sq
    · rw [show (↑n + 1 : ℤ) = (n : ℤ) + (1 : ℤ) by norm_cast,
        zpow_add₀ Real.goldenConj_ne_zero, zpow_one, hψ]
      push_cast
      linear_combination (b : ℝ) * Real.goldenConj_sq
  | pred n ih =>
    obtain ⟨a, b, hφ, hψ⟩ := ih
    refine ⟨b - a, a, ?_, ?_⟩
    · have h1 : φ⁻¹ = φ - 1 := by
        rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
      rw [show (-↑n - 1 : ℤ) = (-↑n : ℤ) + (-1 : ℤ) by ring,
        zpow_add₀ Real.goldenRatio_ne_zero, zpow_neg_one, hφ, h1]
      push_cast
      linear_combination (b : ℝ) * Real.goldenRatio_sq
    · have h1 : ψ⁻¹ = ψ - 1 := by
        rw [Real.inv_goldenConj, ← Real.one_sub_goldenRatio]; ring
      rw [show (-↑n - 1 : ℤ) = (-↑n : ℤ) + (-1 : ℤ) by ring,
        zpow_add₀ Real.goldenConj_ne_zero, zpow_neg_one, hψ, h1]
      push_cast
      linear_combination (b : ℝ) * Real.goldenConj_sq

/-- **Conjugate sum of a base phi expansion.** If a finite set $S$ of integers has base phi value
$\sum_{i \in S} \varphi^i = k$ for a natural number $k$, then also $\sum_{i \in S} \psi^i = k$,
where $\psi$ is the conjugate of the golden ratio $\varphi$. -/
public theorem conj_sum_eq {S : Finset ℤ} {k : ℕ} (h : basePhiValue S = k) :
    ∑ i ∈ S, ψ ^ i = k := by
  classical
  choose a b hab using fun i => pow_repr i
  have hsumφ : ∑ i ∈ S, φ ^ i = (∑ i ∈ S, (a i : ℝ)) + (∑ i ∈ S, (b i : ℝ)) * φ := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hab i).1]
  have hsumψ : ∑ i ∈ S, ψ ^ i = (∑ i ∈ S, (a i : ℝ)) + (∑ i ∈ S, (b i : ℝ)) * ψ := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hab i).2]
  have hB : (∑ i ∈ S, (b i : ℝ)) = 0 := by
    by_contra hne
    have hφeq : (∑ i ∈ S, (b i : ℝ)) * φ = (k : ℝ) - ∑ i ∈ S, (a i : ℝ) := by
      have h2 := h
      rw [basePhiValue, hsumφ] at h2
      linarith
    have hcastB : (∑ i ∈ S, (b i : ℝ)) = ((∑ i ∈ S, b i : ℤ) : ℝ) := by push_cast; rfl
    have hcastA : ∑ i ∈ S, (a i : ℝ) = ((∑ i ∈ S, a i : ℤ) : ℝ) := by push_cast; rfl
    have hBint : (∑ i ∈ S, b i : ℤ) ≠ 0 := by
      intro hb0
      apply hne
      rw [hcastB, hb0, Int.cast_zero]
    have hrat : φ = ((((k : ℤ) - ∑ i ∈ S, a i : ℤ) / (∑ i ∈ S, b i : ℤ) : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
      rw [eq_div_iff (by exact_mod_cast hBint)]
      push_cast
      linear_combination hφeq
    exact Real.goldenRatio_irrational ⟨_, hrat.symm⟩
  rw [hsumψ, hB, zero_mul, add_zero]
  have h2 := h
  rw [basePhiValue, hsumφ, hB, zero_mul, add_zero] at h2
  exact h2

/-- **Normalized conjugate sum of a Bergman expansion.** Let $S$ be a Bergman expansion (a finite
set of integers with no two consecutive elements) with least element $m$. Then
$\sum_{i \in S} \psi^{i - m} > -\psi$, where $\psi$ is the conjugate of the golden ratio. -/
public theorem conj_factor_gt {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {m : ℤ} (hm : m ∈ S) (hmin : ∀ i ∈ S, m ≤ i) :
    -ψ < ∑ i ∈ S, ψ ^ (i - m) := by
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
  let E := S.filter fun i => Even (i - m)
  let O := S.filter fun i => ¬ Even (i - m)
  have hsplit : ∑ i ∈ S, ψ ^ (i - m) =
      (∑ i ∈ E, ψ ^ (i - m)) + ∑ i ∈ O, ψ ^ (i - m) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => Even (i - m)) _]
  have hE : (∑ i ∈ E, ψ ^ (i - m)) = ∑ i ∈ E, r ^ (i - m) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm _ (Finset.mem_filter.mp hi).2
  have hO : (∑ i ∈ O, ψ ^ (i - m)) = -∑ i ∈ O, r ^ (i - m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hodd : Odd (i - m) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2
    exact htermOdd _ hodd
  have hEge : (1 : ℝ) ≤ ∑ i ∈ E, r ^ (i - m) := by
    have hmE : m ∈ E := Finset.mem_filter.mpr ⟨hm, by simp⟩
    have h1 : r ^ (m - m) ≤ ∑ i ∈ E, r ^ (i - m) :=
      Finset.single_le_sum (s := E) (f := fun i => r ^ (i - m))
        (fun i _ => (zpow_pos hr0 _).le) hmE
    simpa using h1
  have hoddGe : ∀ i ∈ O, 3 ≤ i - m ∧ Odd (i - m) := by
    intro i hi
    have hiS := (Finset.mem_filter.mp hi).1
    have hodd : Odd (i - m) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2
    have hne1 : i - m ≠ 1 := by
      intro h1
      have : m + 1 ∈ S := by
        have : i = m + 1 := by omega
        rwa [this] at hiS
      exact hS m hm this
    have hodd' := hodd
    obtain ⟨k, hk⟩ := hodd
    have hge0 : 0 ≤ i - m := by have := hmin i hiS; omega
    exact ⟨by omega, hodd'⟩
  -- Reindex the odd offsets by `t = ((i - m).toNat - 3) / 2`.
  let f : ℤ → ℕ := fun i => ((i - m).toNat - 3) / 2
  let A : Finset ℕ := O.image f
  have hjnat : ∀ i ∈ O, (i - m).toNat = 2 * f i + 3 := by
    intro i hi
    obtain ⟨hge, hodd⟩ := hoddGe i hi
    have hcast : ((i - m).toNat : ℤ) = i - m :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    have hoddNat : Odd (i - m).toNat := by
      have h := hodd
      rw [← hcast] at h
      exact (Int.odd_natCast _).mp h
    obtain ⟨k, hk⟩ := hoddNat
    have hgeNat : 3 ≤ (i - m).toNat := by omega
    have hf : f i = ((i - m).toNat - 3) / 2 := rfl
    omega
  have hinj : Set.InjOn f O := by
    intro i hi j hj hij
    have h1 := hjnat i hi
    have h2 := hjnat j hj
    have hcast1 : ((i - m).toNat : ℤ) = i - m :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    have hcast2 : ((j - m).toNat : ℤ) = j - m :=
      Int.toNat_of_nonneg (by have := hmin j (Finset.mem_filter.mp hj).1; omega)
    simp only [f] at hij
    omega
  have hAeq : (∑ t ∈ A, r ^ (2 * t + 3)) = ∑ i ∈ O, r ^ (i - m) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    have h1 := hjnat i hi
    have hcast : ((i - m).toNat : ℤ) = i - m :=
      Int.toNat_of_nonneg (by have := hmin i (Finset.mem_filter.mp hi).1; omega)
    rw [← zpow_natCast, ← h1, ← hcast]
    norm_cast
  -- The odd sum is strictly below the geometric series `r ^ 2`.
  have hGsum : Summable (fun t : ℕ => r ^ (2 * t + 3)) := by
    have hbase : Summable (fun t : ℕ => (r ^ 2) ^ t) :=
      summable_geometric_of_lt_one (by positivity) (by nlinarith [hr0, hr1])
    have hEq : (fun t : ℕ => r ^ (2 * t + 3)) = fun t : ℕ => r ^ 3 * (r ^ 2) ^ t := by
      funext t
      rw [pow_add, pow_mul]
      ring
    rw [hEq]
    exact hbase.mul_left _
  have hGval : (∑' t : ℕ, r ^ (2 * t + 3)) = r ^ 2 := by
    have hEq : (∑' t : ℕ, r ^ (2 * t + 3)) = ∑' t : ℕ, r ^ 3 * (r ^ 2) ^ t := by
      apply tsum_congr
      intro t
      rw [pow_add, pow_mul]
      ring
    rw [hEq, tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
      (by nlinarith [hr0, hr1])]
    rw [hr2]
    field_simp
  have ht0 : ∃ t0 : ℕ, t0 ∉ A := by
    refine ⟨A.sum id + 1, ?_⟩
    intro hmem
    have hle := Finset.single_le_sum (fun t _ => Nat.zero_le t) hmem
    simp only [id] at hle
    omega
  obtain ⟨t0, ht0⟩ := ht0
  have hOlt : (∑ i ∈ O, r ^ (i - m)) < r ^ 2 := by
    rw [← hAeq, ← hGval]
    have hF : (∑' t : ℕ, (if t ∈ A then r ^ (2 * t + 3) else 0)) =
        ∑ t ∈ A, r ^ (2 * t + 3) := by
      rw [tsum_eq_sum (s := A) (fun b hb => by simp [hb])]
      apply Finset.sum_congr rfl
      intro b hb
      simp [hb]
    rw [← hF]
    apply Summable.tsum_lt_tsum_of_nonneg (i := t0)
    · intro b
      split_ifs with hb
      · positivity
      · exact le_refl 0
    · intro b
      split_ifs with hb
      · exact le_refl _
      · positivity
    · have h0 : (if t0 ∈ A then r ^ (2 * t0 + 3) else (0 : ℝ)) = 0 := by simp [ht0]
      rw [h0]
      positivity
    · exact hGsum
  rw [hsplit, hE, hO]
  have : (1 : ℝ) - r ^ 2 = r := hr2
  linarith [hEge, hOlt]

/-- **Even powers of the conjugate golden ratio.** For every even integer $j$,
$\psi^j = \varphi^{-j}$, where $\varphi$ is the golden ratio and $\psi$ its conjugate. -/
public theorem even_pow_eq {j : ℤ} (hj : Even j) : ψ ^ j = φ ^ (-j) := by
  have hψ : ψ = -φ⁻¹ := by
    rw [Real.inv_goldenRatio]
    ring
  rw [hψ, hj.neg_zpow (φ⁻¹), inv_zpow, ← zpow_neg]

end BasePhiConjugate

end MetaMathlibExt
