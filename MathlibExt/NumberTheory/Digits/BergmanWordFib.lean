/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations

/-!
# Bergman expansions of the Fibonacci numbers

The Bergman expansion of $F_{2n}$ is the word $(1000)^{n-1}1$ and the Bergman
expansion of $F_{2n+1}$ is the word $(1000)^{n-1}1001$, up to translation of the
set of positions. The proof exhibits the two words, computes their base phi
values by the Fibonacci recurrence, and uses uniqueness of Bergman expansions.
-/

open scoped goldenRatio

namespace MetaMathlibExt

namespace bergmanWord_fib

private theorem pow_add_prev (i : ℤ) : φ ^ i + φ ^ (i - 1) = φ ^ (i + 1) := by
  rw [show i = (i - 1) + 1 by omega, show i - 1 + 1 - 1 = i - 1 by omega,
    show i - 1 + 1 + 1 = (i - 1) + 2 by omega, zpow_add₀ Real.goldenRatio_ne_zero,
    zpow_add₀ Real.goldenRatio_ne_zero (i - 1) 2, zpow_one, zpow_ofNat, Real.goldenRatio_sq]
  ring

private theorem value_insert {S : Finset ℤ} {i : ℤ} (hi : i ∉ S) :
    basePhiValue (insert i S) = φ ^ i + basePhiValue S :=
  Finset.sum_insert hi

private theorem value_lt_of_spacing (S : Finset ℤ)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → i + 2 ≤ j) (k : ℤ) (hk : ∀ i ∈ S, i < k) :
    basePhiValue S < φ ^ k := by
  induction S using Finset.strongInductionOn generalizing k
  rename_i S ih
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := Finset.max'_mem _ _
    have hrest := ih (S.erase m) (Finset.erase_ssubset hm)
      (fun i hi j hj hij => hgap i (Finset.mem_of_mem_erase hi) j
        (Finset.mem_of_mem_erase hj) hij) (m - 1) (by
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
    calc
      _ < φ ^ m + φ ^ (m - 1) := by linarith
      _ = φ ^ (m + 1) := pow_add_prev m
      _ ≤ _ := zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, basePhiValue_empty]
    exact zpow_pos Real.goldenRatio_pos _

private theorem bergman_value_lt {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {k : ℤ} (hk : ∀ i ∈ S, i < k) : basePhiValue S < φ ^ k := by
  apply value_lt_of_spacing S _ k hk
  intro i hi j hj hij
  have hn := hS i hi
  by_contra! h
  obtain rfl : j = i + 1 := by omega
  exact hn hj

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

private theorem fib_step (m : ℕ) :
    (Nat.fib (m + 2) : ℝ) = φ ^ m + φ ^ (-2 : ℤ) * (Nat.fib m : ℝ) := by
  have h : φ ^ (-2 : ℤ) = ψ + 1 := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow, Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]
  rw [h, Nat.fib_add_two, Nat.cast_add]
  have hfib := Real.fib_succ_sub_goldenConj_mul_fib m
  linear_combination hfib

private theorem even_fib_step (n : ℕ) :
    (Nat.fib (2 * n + 2) : ℝ) =
      φ ^ (2 * (n : ℤ)) + φ ^ (-2 : ℤ) * (Nat.fib (2 * n) : ℝ) := by
  exact fib_step (2 * n)

private theorem odd_fib_step (n : ℕ) :
    (Nat.fib (2 * n + 1 + 2) : ℝ) =
      φ ^ (2 * (n : ℤ) + 1) + φ ^ (-2 : ℤ) * (Nat.fib (2 * n + 1) : ℝ) := by
  exact fib_step (2 * n + 1)

private theorem even_value_sum (n : ℕ) :
    basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) =
      ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
  unfold basePhiValue
  rw [Finset.sum_image]
  intro a _ b _ h
  dsimp only at h
  have h' : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast h'

private theorem even_value (n : ℕ) :
    basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) =
      Nat.fib (2 * n) := by
  induction n with
  | zero => simp [basePhiValue]
  | succ n ih =>
    rw [even_value_sum, Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hlast : (4 : ℤ) * ((n : ℤ)) + (2 - 2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) := by
      rw [hcast]; ring
    rw [hlast]
    have hfactor : ∑ j ∈ Finset.range n,
        φ ^ (4 * (j : ℤ) + (2 - 2 * ((n + 1 : ℕ) : ℤ))) =
        φ ^ (-2 : ℤ) * ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show 4 * (j : ℤ) + (2 - 2 * ((n + 1 : ℕ) : ℤ)) =
        (-2 : ℤ) + (4 * (j : ℤ) + (2 - 2 * (n : ℤ))) by rw [hcast]; ring,
        zpow_add₀ Real.goldenRatio_ne_zero]
    rw [hfactor, ← even_value_sum, ih]
    have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [h2]
    rw [even_fib_step]
    ring

private theorem odd_value_sum (n : ℕ) :
    basePhiValue (insert (-(2 * (n : ℤ)))
        ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) =
      φ ^ (-(2 * (n : ℤ))) +
        ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ)))) := by
  have hnot : -(2 * (n : ℤ)) ∉
      (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))) := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    omega
  rw [value_insert hnot]
  unfold basePhiValue
  rw [Finset.sum_image]
  intro a _ b _ h
  dsimp only at h
  have h' : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast h'

private theorem odd_value (n : ℕ) :
    basePhiValue (insert (-(2 * (n : ℤ)))
        ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) =
      Nat.fib (2 * n + 1) := by
  induction n with
  | zero => simp [basePhiValue]
  | succ n ih =>
    rw [odd_value_sum, Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hlast : (4 : ℤ) * (n : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ))) = 2 * (n : ℤ) + 1 := by
      rw [hcast]; ring
    rw [hlast]
    have hfactor : φ ^ (-(2 * ((n + 1 : ℕ) : ℤ))) +
        ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ)))) =
        φ ^ (-2 : ℤ) * (φ ^ (-(2 * (n : ℤ))) +
          ∑ j ∈ Finset.range n, φ ^ (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
      have hpow : φ ^ (-(2 * ((n + 1 : ℕ) : ℤ))) =
          φ ^ (-2 : ℤ) * φ ^ (-(2 * (n : ℤ))) := by
        rw [← zpow_add₀ Real.goldenRatio_ne_zero]
        congr 1
        rw [hcast]; ring
      rw [hpow, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show 4 * (j : ℤ) + 3 + (-(2 * ((n + 1 : ℕ) : ℤ))) =
        (-2 : ℤ) + (4 * (j : ℤ) + 3 + (-(2 * (n : ℤ)))) by rw [hcast]; ring,
        zpow_add₀ Real.goldenRatio_ne_zero]
    rw [← add_assoc, hfactor, ← odd_value_sum, ih]
    have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    rw [h2]
    rw [odd_fib_step]
    ring

private theorem bergman_even (n : ℕ) :
    IsBergmanExpansion
      ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
  intro i hi h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  omega

private theorem bergman_odd (n : ℕ) :
    IsBergmanExpansion (insert (-(2 * (n : ℤ)))
      ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
  intro i hi h
  rcases Finset.mem_insert.mp hi with rfl | hi
  · rcases Finset.mem_insert.mp h with h | h
    · omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      omega
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
      omega

end bergmanWord_fib

set_option linter.unusedVariables false in
/-- **Bergman expansions of the Fibonacci numbers.** Let $n \ge 1$ and write $F_m$ for the $m$-th
Fibonacci number, with $F_1 = F_2 = 1$. Let $S$ be a finite set of integers with no two
consecutive elements (a Bergman expansion). If the base phi value of $S$ is $F_{2n}$, then
$S = \{t + 4j : 0 \le j < n\}$ for some integer $t$. If the base phi value of $S$ is
$F_{2n+1}$, then $S = \{t\} \cup \{t + 3 + 4j : 0 \le j < n\}$ for some integer $t$.

Read from the highest to the lowest position, these are the digit words $(1000)^{n-1}1$ and
$(1000)^{n-1}1001$; the position of the radix point is not determined.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 3.1
(`fq-2024-dekking11102023-prop-3.1`). -/
public theorem bergmanWord_fib (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n) →
      ∃ t : ℤ, S = (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + t) ∧
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n + 1) →
      ∃ t : ℤ, S = insert t ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + t)) := by
  constructor
  · intro S hS hval
    refine ⟨2 - 2 * (n : ℤ), ?_⟩
    have hval' : basePhiValue S =
        basePhiValue ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + (2 - 2 * (n : ℤ))) := by
      rw [hval, bergmanWord_fib.even_value]
    exact bergmanWord_fib.bergman_eq_of_value_eq hS (bergmanWord_fib.bergman_even n) hval'
  · intro S hS hval
    refine ⟨-(2 * (n : ℤ)), ?_⟩
    have hval' : basePhiValue S =
        basePhiValue (insert (-(2 * (n : ℤ)))
          ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + (-(2 * (n : ℤ))))) := by
      rw [hval, bergmanWord_fib.odd_value]
    exact bergmanWord_fib.bergman_eq_of_value_eq hS (bergmanWord_fib.bergman_odd n) hval'

end MetaMathlibExt
