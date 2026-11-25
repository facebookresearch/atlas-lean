/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.Enumerative.Composition
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Pell and Pell–Lucas numbers as composition sums with $\sqrt 2$ weights

We prove that the two composition sums with $\sqrt 2$ weights in
`MetaMathlibExt.pell_pellLucas_composition_sums_sqrt_two` equal the stated
combinations of Pell and Pell–Lucas numbers, by showing that both sums and
both targets satisfy the same two-term recurrence.
-/

namespace MetaMathlibExt

open scoped BigOperators

namespace pell_pellLucas_composition_sums_sqrt_two

open Finset

private lemma sq_sqrt_two : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

private lemma div_two_sqrt_two : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
  rw [div_eq_iff sqrt_two_ne_zero, ← pow_two]
  exact sq_sqrt_two.symm


/-- The weight of a part in the first composition sum. -/
private noncomputable def weightOne (j : ℕ) : ℝ :=
  ((j : ℝ) - 1) * Real.sqrt 2 ^ (j - 2)

/-- The weight of a part in the second composition sum. -/
private noncomputable def weightTwo (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) / Real.sqrt 2 ^ j

/-- A weighted sum over the compositions of `n`. -/
private noncomputable def compSum (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map w).prod

/-- The empty composition contributes `1`. -/
private lemma compSum_zero (w : ℕ → ℝ) : compSum w 0 = 1 := by
  simp [compSum, (Composition.blocks_eq_nil _).mpr rfl, composition_card]

/-- A nonempty composition is determined by its first part and the rest. -/
private def prepend (n : ℕ) (p : Σ i : Fin (n + 1), Composition (n - i.val)) :
    Composition (n + 1) :=
  ((Composition.single (p.1.val + 1) (Nat.succ_pos _)).append p.2).cast (by
    have := p.1.isLt
    omega)

private lemma prepend_bijective (n : ℕ) : Function.Bijective (prepend n) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hblocks := congrArg Composition.blocks h
    change (i.val + 1) :: c.blocks = (j.val + 1) :: d.blocks at hblocks
    obtain ⟨hij, hcd⟩ := List.cons.inj hblocks
    have : i = j := Fin.ext (by omega)
    subst j
    rw [Composition.ext hcd]
  · rintro ⟨l, hpos, hsum⟩
    obtain _ | ⟨b, l⟩ := l
    · simp at hsum
    cases b with
    | zero => simp at hpos
    | succ i =>
      simp only [List.sum_cons] at hsum
      let c : Composition (n - i) :=
        ⟨l, fun h => hpos (List.mem_cons_of_mem _ h), by omega⟩
      exact ⟨⟨⟨i, by omega⟩, c⟩, rfl⟩

/-- Splitting a composition sum by its first part. -/
private lemma compSum_succ (w : ℕ → ℝ) (n : ℕ) :
    compSum w (n + 1) =
      ∑ i ∈ range (n + 1), w (i + 1) * compSum w (n - i) := by
  let e := Equiv.ofBijective (prepend n) (prepend_bijective n)
  unfold compSum
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (((i.val + 1) :: c.blocks).map w).prod = _
  rw [List.map_cons, List.prod_cons]

private lemma sum_range_add_two (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 2), f i = f 0 + f 1 + ∑ i ∈ range n, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h : (∑ i ∈ range n, f (i + 1 + 1)) = ∑ i ∈ range n, f (i + 2) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [h]
  change (∑ i ∈ range n, f (i + 2)) + f 1 + f 0 = f 0 + f 1 + ∑ i ∈ range n, f (i + 2)
  ring

/-- If the weights satisfy a two-term recurrence, so does the composition sum. -/
private lemma compSum_recurrence (w : ℕ → ℝ) (a b : ℝ)
    (hw : ∀ j, 1 ≤ j → w (j + 2) = a * w (j + 1) + b * w j) (k : ℕ) :
    compSum w (k + 3) =
      (w 1 + a) * compSum w (k + 2) + (w 2 - a * w 1 + b) * compSum w (k + 1) := by
  have hS3 := compSum_succ w (k + 2)
  have hS2 := compSum_succ w (k + 1)
  have hS1 := compSum_succ w k
  have hexp : compSum w (k + 3) =
      w 1 * compSum w (k + 2) + w 2 * compSum w (k + 1) +
        ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) := by
    have h := sum_range_add_two (fun i => w (i + 1) * compSum w (k + 2 - i)) (k + 1)
    have htail : (∑ i ∈ range (k + 1), w (i + 2 + 1) * compSum w (k + 2 - (i + 2))) =
        ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2; omega
    rw [hS3, h, htail, Nat.sub_zero, show k + 2 - 1 = k + 1 by omega]
  have hsplit2 : compSum w (k + 2) =
      (∑ i ∈ range (k + 1), w (i + 2) * compSum w (k - i)) +
        w 1 * compSum w (k + 1) := by
    rw [hS2, Finset.sum_range_succ']
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2; omega
  have hsumw : ∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i) =
      a * (∑ i ∈ range (k + 1), w (i + 2) * compSum w (k - i)) +
        b * compSum w (k + 1) := by
    have h1 : (∑ i ∈ range (k + 1), w (i + 3) * compSum w (k - i)) =
        ∑ i ∈ range (k + 1), (a * w (i + 2) + b * w (i + 1)) * compSum w (k - i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hw (i + 1) (by omega)]
    rw [h1]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hS1]
  linear_combination hexp + hsumw - a * hsplit2

/-- The first weight satisfies `w (j + 2) = 2√2 * w (j + 1) - 2 * w j`. -/
private lemma weightOne_recurrence (j : ℕ) (hj : 1 ≤ j) :
    weightOne (j + 2) = (2 * Real.sqrt 2) * weightOne (j + 1) + (-2) * weightOne j := by
  rcases Nat.eq_or_lt_of_le hj with h | hj2
  · rw [← h]
    norm_num [weightOne]
  · have e1 : j + 2 - 2 = j := by omega
    have e2 : j + 1 - 2 = j - 1 := by omega
    have hp1 : Real.sqrt 2 ^ j = Real.sqrt 2 ^ (j - 1) * Real.sqrt 2 := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      rw [pow_succ]
    have hp2 : Real.sqrt 2 ^ (j - 1) = Real.sqrt 2 ^ (j - 2) * Real.sqrt 2 := by
      conv_lhs => rw [show j - 1 = (j - 2) + 1 by omega]
      rw [pow_succ]
    rw [weightOne, weightOne, weightOne, e1, e2, hp1, hp2]
    have hc1 : ((j + 2 : ℕ) : ℝ) - 1 = (j : ℝ) + 1 := by push_cast; ring
    have hc2 : ((j + 1 : ℕ) : ℝ) - 1 = (j : ℝ) := by push_cast; ring
    rw [hc1, hc2]
    linear_combination ((1 - (j : ℝ)) * Real.sqrt 2 ^ (j - 2)) * sq_sqrt_two

/-- The second weight, rewritten with the ratio `√2 / 2 = 1 / √2`. -/
private lemma weightTwo_eq (j : ℕ) :
    weightTwo j = ((j : ℝ) + 1) * (Real.sqrt 2 / 2) ^ j := by
  have hts : Real.sqrt 2 / 2 * Real.sqrt 2 = 1 := by
    field_simp
    linarith [sq_sqrt_two]
  rw [weightTwo, div_eq_iff (pow_ne_zero j sqrt_two_ne_zero)]
  rw [mul_assoc, ← mul_pow, hts, one_pow, mul_one]

/-- The second weight satisfies `w (j + 2) = √2 * w (j + 1) - (1 / 2) * w j`. -/
private lemma weightTwo_recurrence (j : ℕ) (_hj : 1 ≤ j) :
    weightTwo (j + 2) =
      Real.sqrt 2 * weightTwo (j + 1) + (-1 / 2) * weightTwo j := by
  have hst : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    field_simp
    linarith [sq_sqrt_two]
  have ht2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, sq_sqrt_two]; norm_num
  have hA : weightTwo (j + 2) = ((j : ℝ) + 3) * (Real.sqrt 2 / 2) ^ j * (1 / 2) := by
    rw [weightTwo_eq]
    have hc : ((j + 2 : ℕ) : ℝ) + 1 = (j : ℝ) + 3 := by push_cast; ring
    rw [hc, pow_add, ht2]
    ring
  have hB : Real.sqrt 2 * weightTwo (j + 1) =
      ((j : ℝ) + 2) * (Real.sqrt 2 / 2) ^ j := by
    rw [weightTwo_eq]
    have hc : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    rw [hc, pow_succ]
    calc Real.sqrt 2 * (((j : ℝ) + 2) * ((Real.sqrt 2 / 2) ^ j * (Real.sqrt 2 / 2)))
        = ((j : ℝ) + 2) * (Real.sqrt 2 / 2) ^ j * (Real.sqrt 2 * (Real.sqrt 2 / 2)) := by
          ring
      _ = _ := by rw [hst, mul_one]
  rw [hA, hB, weightTwo_eq]
  ring

/-- The first composition sum satisfies the `√2` recurrence. -/
private lemma compSum_weightOne_recurrence (k : ℕ) :
    compSum weightOne (k + 3) =
      2 * Real.sqrt 2 * compSum weightOne (k + 2) - compSum weightOne (k + 1) := by
  have h := compSum_recurrence weightOne (2 * Real.sqrt 2) (-2) weightOne_recurrence k
  have hw1 : weightOne 1 = 0 := by rw [weightOne]; norm_num
  have hw2 : weightOne 2 = 1 := by rw [weightOne]; norm_num
  rw [hw1, hw2] at h
  linear_combination h

/-- The second composition sum satisfies the `√2` recurrence. -/
private lemma compSum_weightTwo_recurrence (k : ℕ) :
    compSum weightTwo (k + 3) =
      2 * Real.sqrt 2 * compSum weightTwo (k + 2) - compSum weightTwo (k + 1) := by
  have h := compSum_recurrence weightTwo (Real.sqrt 2) (-1 / 2) weightTwo_recurrence k
  have hw1 : weightTwo 1 = Real.sqrt 2 := by
    have h : weightTwo 1 = (2 : ℝ) / Real.sqrt 2 := by
      rw [weightTwo]
      norm_num
    rw [h, div_two_sqrt_two]
  have hw2 : weightTwo 2 = 3 / 2 := by
    rw [weightTwo_eq, div_pow, sq_sqrt_two]
    norm_num
  rw [hw1, hw2] at h
  have hcoef : (Real.sqrt 2 + Real.sqrt 2) * compSum weightTwo (k + 2) +
      (3 / 2 - Real.sqrt 2 * Real.sqrt 2 + -1 / 2) * compSum weightTwo (k + 1) =
      2 * Real.sqrt 2 * compSum weightTwo (k + 2) - compSum weightTwo (k + 1) := by
    linear_combination -compSum weightTwo (k + 1) * sq_sqrt_two
  rw [hcoef] at h
  exact h

private lemma compSum_weightOne_one : compSum weightOne 1 = 0 := by
  have h := compSum_succ weightOne 0
  simp only [Finset.sum_range_one, Nat.sub_zero, zero_add] at h
  rw [compSum_zero] at h
  have hw1 : weightOne 1 = 0 := by rw [weightOne]; norm_num
  rw [hw1] at h
  simpa using h

private lemma compSum_weightOne_two : compSum weightOne 2 = 1 := by
  have h := compSum_succ weightOne 1
  simp only [Finset.sum_range_succ, Nat.sub_zero] at h
  rw [compSum_weightOne_one, compSum_zero] at h
  have hw1 : weightOne 1 = 0 := by rw [weightOne]; norm_num
  have hw2 : weightOne 2 = 1 := by rw [weightOne]; norm_num
  rw [hw1, hw2] at h
  simpa using h

private lemma compSum_weightTwo_one : compSum weightTwo 1 = Real.sqrt 2 := by
  have h := compSum_succ weightTwo 0
  simp only [Finset.sum_range_one, Nat.sub_zero, zero_add] at h
  rw [compSum_zero] at h
  have hw1 : weightTwo 1 = Real.sqrt 2 := by
    have h1 : weightTwo 1 = (2 : ℝ) / Real.sqrt 2 := by
      rw [weightTwo]
      norm_num
    rw [h1, div_two_sqrt_two]
  rw [hw1] at h
  simpa using h

private lemma compSum_weightTwo_two : compSum weightTwo 2 = 7 / 2 := by
  have h := compSum_succ weightTwo 1
  simp only [Finset.sum_range_succ, Nat.sub_zero] at h
  rw [compSum_weightTwo_one, compSum_zero] at h
  have hw1 : weightTwo 1 = Real.sqrt 2 := by
    have h1 : weightTwo 1 = (2 : ℝ) / Real.sqrt 2 := by
      rw [weightTwo]
      norm_num
    rw [h1, div_two_sqrt_two]
  have hw2 : weightTwo 2 = 3 / 2 := by
    rw [weightTwo_eq, div_pow, sq_sqrt_two]
    norm_num
  rw [hw1, hw2, ← pow_two, sq_sqrt_two] at h
  norm_num at h
  exact h

/-- The Pell–Lucas numbers in terms of Pell numbers. -/
private lemma pellLucas_rel (k : ℕ) :
    pellLucas (k + 1) = pellNumber k + pellNumber (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih₀ ih₁ =>
    have ih₁' : pellLucas (k + 2) = pellNumber (k + 1) + pellNumber (k + 3) := ih₁
    have hQ : pellLucas (k + 3) = 2 * pellLucas (k + 2) + pellLucas (k + 1) := rfl
    have hP : pellNumber (k + 4) = 2 * pellNumber (k + 3) + pellNumber (k + 2) := rfl
    have hP2 : pellNumber (k + 3) = 2 * pellNumber (k + 2) + pellNumber (k + 1) := rfl
    have hP3 : pellNumber (k + 2) = 2 * pellNumber (k + 1) + pellNumber k := rfl
    change pellLucas (k + 3) = pellNumber (k + 2) + pellNumber (k + 4)
    omega

private lemma pellLucas_add (k : ℕ) (hk : 1 ≤ k) :
    pellLucas (k + 2) + pellLucas k = 8 * pellNumber (k + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have h1 : pellLucas (t + 3) = pellNumber (t + 2) + pellNumber (t + 4) := pellLucas_rel (t + 2)
  have h2 := pellLucas_rel t
  have hP1 : pellNumber (t + 4) = 2 * pellNumber (t + 3) + pellNumber (t + 2) := rfl
  have hP2 : pellNumber (t + 3) = 2 * pellNumber (t + 2) + pellNumber (t + 1) := rfl
  have hP3 : pellNumber (t + 2) = 2 * pellNumber (t + 1) + pellNumber t := rfl
  change pellLucas (t + 3) + pellLucas (t + 1) = 8 * pellNumber (t + 2)
  omega

/-- The first target sequence. -/
private noncomputable def targetOne (n : ℕ) : ℝ :=
  if Odd n then Real.sqrt 2 * (pellNumber (n - 1) : ℝ)
  else (pellLucas (n - 1) : ℝ) / 2

/-- The second target sequence. -/
private noncomputable def targetTwo (n : ℕ) : ℝ :=
  if Odd n then (pellNumber (n + 1) : ℝ) / Real.sqrt 2
  else (pellLucas (n + 1) : ℝ) / 4

private lemma targetOne_rec (n : ℕ) :
    targetOne (n + 3) = 2 * Real.sqrt 2 * targetOne (n + 2) - targetOne (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hodd1 : Odd (n + 1) := ⟨k, by omega⟩
    have hnot2 : ¬ Odd (n + 2) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by omega⟩
    have hodd3 : Odd (n + 3) := ⟨k + 1, by omega⟩
    simp only [targetOne, hodd3, hnot2, hodd1, ite_true, ite_false]
    have hQ : (pellLucas (n + 1) : ℝ) = (pellNumber n : ℝ) + (pellNumber (n + 2) : ℝ) := by
      exact_mod_cast pellLucas_rel n
    rw [show n + 3 - 1 = n + 2 by omega, show n + 2 - 1 = n + 1 by omega,
      show n + 1 - 1 = n by omega]
    linear_combination -Real.sqrt 2 * hQ
  · have hnot1 : ¬ Odd (n + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by omega⟩
    have hodd2 : Odd (n + 2) := ⟨k + 1, by omega⟩
    have hnot3 : ¬ Odd (n + 3) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 2, by omega⟩
    simp only [targetOne, hnot3, hodd2, hnot1, ite_true, ite_false]
    have hsumR : (pellLucas (n + 2) : ℝ) + (pellLucas n : ℝ) =
        8 * (pellNumber (n + 1) : ℝ) := by
      exact_mod_cast pellLucas_add n (by omega)
    rw [show n + 3 - 1 = n + 2 by omega, show n + 2 - 1 = n + 1 by omega,
      show n + 1 - 1 = n by omega]
    linear_combination (1 / 2 : ℝ) * hsumR + (-2 * (pellNumber (n + 1) : ℝ)) * sq_sqrt_two

private lemma targetTwo_rec (n : ℕ) :
    targetTwo (n + 3) = 2 * Real.sqrt 2 * targetTwo (n + 2) - targetTwo (n + 1) := by
  have hsinv : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    linarith [sq_sqrt_two]
  have hsinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [inv_eq_one_div]; exact hsinv
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hodd1 : Odd (n + 1) := ⟨k, by omega⟩
    have hnot2 : ¬ Odd (n + 2) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by omega⟩
    have hodd3 : Odd (n + 3) := ⟨k + 1, by omega⟩
    simp only [targetTwo, hodd3, hnot2, hodd1, ite_true, ite_false]
    have hQ : (pellLucas (n + 3) : ℝ) = (pellNumber (n + 2) : ℝ) + (pellNumber (n + 4) : ℝ) := by
      have h := pellLucas_rel (n + 2)
      rw [show n + 2 + 1 = n + 3 from by omega, show n + 2 + 2 = n + 4 from by omega] at h
      exact_mod_cast h
    simp only [div_eq_mul_inv, hsinv']
    rw [show n + 2 + 1 = n + 3 by omega, show n + 3 + 1 = n + 4 by omega]
    linear_combination -(Real.sqrt 2 / 2) * hQ
  · have hnot1 : ¬ Odd (n + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by omega⟩
    have hodd2 : Odd (n + 2) := ⟨k + 1, by omega⟩
    have hnot3 : ¬ Odd (n + 3) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 2, by omega⟩
    simp only [targetTwo, hnot3, hodd2, hnot1, ite_true, ite_false]
    have hsumR : (pellLucas (n + 4) : ℝ) + (pellLucas (n + 2) : ℝ) =
        8 * (pellNumber (n + 3) : ℝ) := by
      exact_mod_cast pellLucas_add (n + 2) (by omega)
    simp only [div_eq_mul_inv, hsinv']
    linear_combination (1 / 4 : ℝ) * hsumR +
      (-(pellNumber (n + 3) : ℝ)) * sq_sqrt_two

/-- The first composition sum equals the first target at two consecutive indices. -/
private lemma compSum_weightOne_eq (k : ℕ) :
    compSum weightOne (k + 1) = targetOne (k + 1) ∧
      compSum weightOne (k + 2) = targetOne (k + 2) := by
  induction k with
  | zero =>
    constructor
    · rw [compSum_weightOne_one]
      simp [targetOne, pellNumber]
    · rw [compSum_weightOne_two]
      simp [targetOne, pellLucas]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    change compSum weightOne (k + 3) = targetOne (k + 3)
    rw [compSum_weightOne_recurrence k, targetOne_rec k, ih.1, ih.2]

/-- The second composition sum equals the second target at two consecutive indices. -/
private lemma compSum_weightTwo_eq (k : ℕ) :
    compSum weightTwo (k + 1) = targetTwo (k + 1) ∧
      compSum weightTwo (k + 2) = targetTwo (k + 2) := by
  induction k with
  | zero =>
    constructor
    · rw [compSum_weightTwo_one]
      simp [targetTwo, pellNumber]
    · rw [compSum_weightTwo_two]
      simp [targetTwo, pellLucas]
      norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    change compSum weightTwo (k + 3) = targetTwo (k + 3)
    rw [compSum_weightTwo_recurrence k, targetTwo_rec k, ih.1, ih.2]

/-- A composition sum over lists of parts, as a product over part indices. -/
private lemma compSum_eq (w : ℕ → ℝ) (n : ℕ) :
    compSum w n = ∑ c : Composition n, ∏ i : Fin c.length, w (c.blocksFun i) := by
  unfold compSum
  apply Finset.sum_congr rfl
  intro c _
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]

end pell_pellLucas_composition_sums_sqrt_two

open pell_pellLucas_composition_sums_sqrt_two in
/-- **Pell and Pell–Lucas numbers as composition sums with $\sqrt 2$ weights.** Let $P_n$ be the
Pell numbers and $Q_n$ the Pell–Lucas numbers ($Q_0 = Q_1 = 2$, $Q_{k+2} = 2Q_{k+1} + Q_k$). For
every $n \ge 1$, with $c$ running over the compositions of $n$ (ordered tuples of positive
integers with sum $n$) and the products running over the parts $j$ of $c$, the real number
$$\sum_c \prod_{j \in c} (j - 1) (\sqrt 2)^{j-2}$$
equals $\sqrt 2\, P_{n-1}$ for odd $n$ and $Q_{n-1}/2$ for even $n$ (identity (10)), and
$$\sum_c \prod_{j \in c} \frac{j + 1}{(\sqrt 2)^j}$$
equals $P_{n+1}/\sqrt 2$ for odd $n$ and $Q_{n+1}/4$ for even $n$ (identity (11)).

In the source both are multinomial sums; the weight of the first vanishes on parts $1$, so its
sum runs over the compositions of $n$ without parts $1$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 2 (`integers-2025-A97-cor-2`). -/
public theorem pell_pellLucas_composition_sums_sqrt_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2) =
      (if Odd n then Real.sqrt 2 * (pellNumber (n - 1) : ℝ)
        else (pellLucas (n - 1) : ℝ) / 2) ∧
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i =
      (if Odd n then (pellNumber (n + 1) : ℝ) / Real.sqrt 2
        else (pellLucas (n + 1) : ℝ) / 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  constructor
  · rw [show (∑ c : Composition (k + 1), ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2)) =
        compSum weightOne (k + 1) from (compSum_eq weightOne (k + 1)).symm]
    exact (compSum_weightOne_eq k).1
  · rw [show (∑ c : Composition (k + 1), ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i) =
        compSum weightTwo (k + 1) from (compSum_eq weightTwo (k + 1)).symm]
    exact (compSum_weightTwo_eq k).1

end MetaMathlibExt
