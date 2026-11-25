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

private theorem lucasNumber_eq_pow_add_pow (m : ℕ) :
    (lucasNumber m : ℝ) = φ ^ (m : ℤ) + ψ ^ (m : ℤ) := by
  induction m using Nat.twoStepInduction with
  | zero => change ((2 : ℕ) : ℝ) = φ ^ (0 : ℤ) + ψ ^ (0 : ℤ); norm_num
  | one => rw [show lucasNumber 1 = 1 from rfl]; simp [Real.goldenRatio_add_goldenConj]
  | more m ih1 ih2 =>
    have hL : lucasNumber (m + 2) = lucasNumber (m + 1) + lucasNumber m := rfl
    rw [hL, Nat.cast_add, ih1, ih2]
    push_cast
    have hφz : φ ^ ((m : ℤ) + 2) = φ ^ ((m : ℤ) + 1) + φ ^ (m : ℤ) := by
      rw [zpow_add₀ Real.goldenRatio_ne_zero, zpow_add₀ Real.goldenRatio_ne_zero,
        zpow_ofNat, zpow_one, Real.goldenRatio_sq]
      ring
    have hψz : ψ ^ ((m : ℤ) + 2) = ψ ^ ((m : ℤ) + 1) + ψ ^ (m : ℤ) := by
      rw [zpow_add₀ Real.goldenConj_ne_zero, zpow_add₀ Real.goldenConj_ne_zero,
        zpow_ofNat, zpow_one, Real.goldenConj_sq]
      ring
    rw [hφz, hψz]
    ring

private theorem pow_repr (i : ℤ) :
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

private theorem conj_sum_eq {S : Finset ℤ} {k : ℕ} (h : basePhiValue S = k) :
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
  rw [lucasNumber_eq_pow_add_pow]
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

private theorem conj_factor_gt {S : Finset ℤ} (hS : IsBergmanExpansion S)
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

private theorem even_pow_eq {j : ℤ} (hj : Even j) : ψ ^ j = φ ^ (-j) := by
  have hψ : ψ = -φ⁻¹ := by
    rw [Real.inv_goldenRatio]
    ring
  rw [hψ, hj.neg_zpow (φ⁻¹), inv_zpow, ← zpow_neg]

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
  rw [lucasNumber_eq_pow_add_pow, hcast]
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
