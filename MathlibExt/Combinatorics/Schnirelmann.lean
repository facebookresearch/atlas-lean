/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Schnirelmann
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

@[expose] public section

/-! # Schnirelmann density: sumset inequality and bases

This module proves a lower bound for the density of a sumset and shows that a set containing zero
with positive Schnirelmann density is an additive basis of finite order. The basis result follows
Lemma 1 of Tim Jameson's ["Linnik's proof of the Waring-Hilbert theorem from Hua's book (with a
correction)"](https://www.maths.lancs.ac.uk/jameson/warlin.pdf).
-/

namespace MathlibExt.Combinatorics.Schnirelmann

open Finset
open scoped Pointwise

/-- The number of positive members of `A` that are at most `n`. -/
private def schnirelmannCount (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  #{a ∈ Ioc 0 n | a ∈ A}

private lemma schnirelmannCount_mono {A B : Set ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] (h : A ⊆ B) (n : ℕ) :
    schnirelmannCount A n ≤ schnirelmannCount B n := by
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_Ioc] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

private lemma schnirelmannCount_eq_succ_of_max {A : Set ℕ} [DecidablePred (· ∈ A)]
    {a n : ℕ} (ha : 0 < a) (han : a ≤ n) (haA : a ∈ A)
    (hmax : ∀ x ∈ A, x ≤ n → x ≤ a) :
    schnirelmannCount A n = schnirelmannCount A (a - 1) + 1 := by
  have heq : {x ∈ Ioc 0 n | x ∈ A} = insert a {x ∈ Ioc 0 (a - 1) | x ∈ A} := by
    ext x
    simp only [mem_filter, mem_Ioc, mem_insert]
    constructor
    · rintro ⟨⟨hx0, hxn⟩, hxA⟩
      have hxa := hmax x hxA hxn
      rcases hxa.eq_or_lt with rfl | hxa
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hx0, by omega⟩, hxA⟩
    · rintro (rfl | ⟨⟨hx0, hxa⟩, hxA⟩)
      · exact ⟨⟨ha, han⟩, haA⟩
      · exact ⟨⟨hx0, hxa.trans (Nat.pred_le _ |>.trans han)⟩, hxA⟩
  dsimp [schnirelmannCount]
  rw [heq, card_insert_of_notMem]
  simp

private lemma schnirelmannCount_sumset_growth {A B : Set ℕ} [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] {a n : ℕ} (ha : 0 < a) (han : a ≤ n)
    (haA : a ∈ A) (hB : 0 ∈ B) :
    schnirelmannCount (A + B) (a - 1) + schnirelmannCount B (n - a) + 1 ≤
      schnirelmannCount (A + B) n := by
  let low := {x ∈ Ioc 0 (a - 1) | x ∈ A + B}
  let bs := {b ∈ Ioc 0 (n - a) | b ∈ B}
  let high := insert a (bs.image fun b ↦ a + b)
  have ha_not_image : a ∉ bs.image (fun b ↦ a + b) := by
    simp only [mem_image, not_exists]
    intro b hb
    simp only [bs, mem_filter, mem_Ioc] at hb
    omega
  have hhighcard : #high = schnirelmannCount B (n - a) + 1 := by
    rw [show high = insert a (bs.image fun b ↦ a + b) from rfl,
      card_insert_of_notMem ha_not_image, card_image_of_injective]
    · rfl
    · exact fun _ _ h ↦ Nat.add_left_cancel h
  have hdisj : Disjoint low high := by
    rw [disjoint_left]
    intro x hxlow hxhigh
    have hxle : x ≤ a - 1 := by
      simp only [low, mem_filter, mem_Ioc] at hxlow
      exact hxlow.1.2
    have hax : a ≤ x := by
      simp only [high, mem_insert, mem_image] at hxhigh
      rcases hxhigh with rfl | ⟨b, _, rfl⟩
      · exact le_rfl
      · exact Nat.le_add_right _ _
    omega
  have hunion : low ∪ high ⊆ {x ∈ Ioc 0 n | x ∈ A + B} := by
    intro x hx
    simp only [mem_filter, mem_Ioc]
    rcases mem_union.mp hx with hxlow | hxhigh
    · simp only [low, mem_filter, mem_Ioc] at hxlow
      exact ⟨⟨hxlow.1.1, hxlow.1.2.trans (Nat.pred_le _ |>.trans han)⟩, hxlow.2⟩
    · simp only [high, mem_insert, mem_image] at hxhigh
      rcases hxhigh with hxa | ⟨b, hb, hxb⟩
      · subst x
        exact ⟨⟨ha, han⟩, Set.mem_add.2 ⟨a, haA, 0, hB, by simp⟩⟩
      · subst x
        simp only [bs, mem_filter, mem_Ioc] at hb
        refine ⟨⟨Nat.add_pos_left ha b, ?_⟩, Set.mem_add.2 ⟨a, haA, b, hb.2, rfl⟩⟩
        omega
  have hcard := card_le_card hunion
  rw [card_union_of_disjoint hdisj, hhighcard] at hcard
  exact hcard

private lemma schnirelmannCount_add_lower {A B : Set ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A + B)]
    (hA : 0 ∈ A) (hB : 0 ∈ B) (n : ℕ) :
    (schnirelmannCount A n : ℝ) +
        schnirelmannDensity B * ((n : ℝ) - schnirelmannCount A n) ≤
      schnirelmannCount (A + B) n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let sA := {x ∈ Icc 0 n | x ∈ A}
      have hsA : sA.Nonempty := ⟨0, by simp [sA, hA]⟩
      let a := sA.max' hsA
      have ha_mem : a ∈ sA := sA.max'_mem hsA
      have ha_mem' :=
        mem_filter.mp (show a ∈ {x ∈ Icc 0 n | x ∈ A} by simpa [sA] using ha_mem)
      have han : a ≤ n := (Finset.mem_Icc.mp ha_mem'.1).2
      have haA : a ∈ A := ha_mem'.2
      have hmax : ∀ x ∈ A, x ≤ n → x ≤ a := by
        intro x hxA hxn
        apply sA.le_max' x
        simp [sA, hxA, hxn]
      by_cases ha0 : a = 0
      · have hcountA : schnirelmannCount A n = 0 := by
          dsimp [schnirelmannCount]
          rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
          rintro ⟨x, hx⟩
          simp only [mem_filter, mem_Ioc] at hx
          have hxa := hmax x hx.2 hx.1.2
          omega
        have hmono := schnirelmannCount_mono (A := B) (B := A + B)
          (fun b hb ↦ Set.mem_add.2 ⟨0, hA, b, hb, by simp⟩) n
        have hmono' : (schnirelmannCount B n : ℝ) ≤ schnirelmannCount (A + B) n := by
          exact_mod_cast hmono
        have hdensity := @schnirelmannDensity_mul_le_card_filter B _ n
        rw [hcountA]
        norm_num
        exact hdensity.trans hmono'
      · have ha : 0 < a := Nat.pos_of_ne_zero ha0
        have hpred : a - 1 < n := by omega
        have hind := ih (a - 1) hpred
        have hcountA := schnirelmannCount_eq_succ_of_max ha han haA hmax
        have hgrowth := schnirelmannCount_sumset_growth ha han haA hB
        have hgrowth' :
            (schnirelmannCount (A + B) (a - 1) : ℝ) +
                schnirelmannCount B (n - a) + 1 ≤
              schnirelmannCount (A + B) n := by
          exact_mod_cast hgrowth
        have hdensity := @schnirelmannDensity_mul_le_card_filter B _ (n - a)
        change schnirelmannDensity B * ((n - a : ℕ) : ℝ) ≤
          (schnirelmannCount B (n - a) : ℝ) at hdensity
        rw [hcountA]
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ a)] at hind
        simp only [Nat.cast_one] at hind
        rw [Nat.cast_sub han] at hdensity
        calc
          (schnirelmannCount A (a - 1) : ℝ) + 1 + schnirelmannDensity B *
                ((n : ℝ) - ((schnirelmannCount A (a - 1) : ℝ) + 1)) =
              ((schnirelmannCount A (a - 1) : ℝ) + schnirelmannDensity B *
                ((a : ℝ) - 1 - schnirelmannCount A (a - 1))) +
                schnirelmannDensity B * ((n : ℝ) - a) + 1 := by ring
          _ ≤ (schnirelmannCount (A + B) (a - 1) : ℝ) +
              schnirelmannCount B (n - a) + 1 :=
            add_le_add (add_le_add hind hdensity) le_rfl
          _ ≤ schnirelmannCount (A + B) n := hgrowth'

/-- **Schnirelmann's inequality.** For a set $A$ of natural numbers, let
$\sigma(A) = \inf_{n \ge 1} |A \cap \{1, \dots, n\}| / n$ be its Schnirelmann density. If $A$
and $B$ are sets of natural numbers that both contain $0$, then their sumset
$A + B = \{a + b : a \in A,\ b \in B\}$ satisfies
$\sigma(A) + \sigma(B) - \sigma(A)\sigma(B) \le \sigma(A + B)$. -/
theorem _root_.schnirelmannDensity_add_lower_bound {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A + B)]
    (hA : 0 ∈ A) (hB : 0 ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B -
        schnirelmannDensity A * schnirelmannDensity B ≤
      schnirelmannDensity (A + B) := by
  classical
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hsum := schnirelmannCount_add_lower hA hB n
  have hAcount := @schnirelmannDensity_mul_le_card_filter A _ n
  have hB_le : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
  dsimp [schnirelmannCount] at hsum hAcount ⊢
  nlinarith

private def schnirelmannSumset (A : Set ℕ) (h : ℕ) : Set ℕ :=
  {n | ∃ x : Fin h → ℕ, (∀ i, x i ∈ A) ∧ n = ∑ i, x i}

private lemma schnirelmannSumset_zero_mem {A : Set ℕ} (hA : 0 ∈ A) (h : ℕ) :
    0 ∈ schnirelmannSumset A h := by
  refine ⟨fun _ ↦ 0, fun _ ↦ hA, ?_⟩
  simp

private lemma schnirelmannSumset_add (A : Set ℕ) (h j : ℕ) :
    schnirelmannSumset A h + schnirelmannSumset A j = schnirelmannSumset A (h + j) := by
  ext n
  constructor
  · rintro ⟨u, ⟨x, hxA, rfl⟩, v, ⟨y, hyA, rfl⟩, rfl⟩
    refine ⟨Fin.append x y, ?_, ?_⟩
    · intro i
      refine Fin.addCases (motive := fun i ↦ Fin.append x y i ∈ A) ?_ ?_ i
      · intro j
        simpa using hxA j
      · intro j
        simpa using hyA j
    · simp [Fin.sum_univ_add]
  · rintro ⟨z, hzA, rfl⟩
    refine Set.mem_add.2 ⟨∑ i : Fin h, z (Fin.castAdd j i), ?_,
      ∑ i : Fin j, z (Fin.natAdd h i), ?_, (Fin.sum_univ_add z).symm⟩
    · exact ⟨fun i ↦ z (Fin.castAdd j i), fun i ↦ hzA _, rfl⟩
    · exact ⟨fun i ↦ z (Fin.natAdd h i), fun i ↦ hzA _, rfl⟩

private lemma schnirelmannSumset_zero (A : Set ℕ) : schnirelmannSumset A 0 = {0} := by
  ext n
  simp [schnirelmannSumset]

private lemma schnirelmannSumset_one (A : Set ℕ) : schnirelmannSumset A 1 = A := by
  ext n
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx 0
  · intro hn
    refine ⟨fun _ ↦ n, fun _ ↦ hn, ?_⟩
    simp

private lemma schnirelmannSumset_density_compl_le {A : Set ℕ} [DecidablePred (· ∈ A)]
    (hA : 0 ∈ A) (h : ℕ) :
    1 - @schnirelmannDensity (schnirelmannSumset A h)
      (fun x ↦ Classical.propDecidable (x ∈ schnirelmannSumset A h)) ≤
      (1 - schnirelmannDensity A) ^ h := by
  induction h with
  | zero =>
      let _ : DecidablePred (· ∈ schnirelmannSumset A 0) :=
        fun x ↦ Classical.propDecidable (x ∈ schnirelmannSumset A 0)
      have hfinite : (schnirelmannSumset A 0).Finite := by
        rw [schnirelmannSumset_zero]
        exact Set.finite_singleton 0
      have hz : schnirelmannDensity (schnirelmannSumset A 0) = 0 :=
        schnirelmannDensity_finite hfinite
      rw [hz]
      norm_num
  | succ h ih =>
      let _ : DecidablePred (· ∈ schnirelmannSumset A h) :=
        fun x ↦ Classical.propDecidable (x ∈ schnirelmannSumset A h)
      let _ : DecidablePred (· ∈ schnirelmannSumset A h + A) :=
        fun x ↦ Classical.propDecidable (x ∈ schnirelmannSumset A h + A)
      have hsuc : schnirelmannSumset A (h + 1) = schnirelmannSumset A h + A := by
        calc
          schnirelmannSumset A (h + 1) =
              schnirelmannSumset A h + schnirelmannSumset A 1 :=
            (schnirelmannSumset_add A h 1).symm
          _ = schnirelmannSumset A h + A :=
            congrArg (schnirelmannSumset A h + ·) (schnirelmannSumset_one A)
      rw [hsuc]
      have hadd := schnirelmannDensity_add_lower_bound
        (schnirelmannSumset_zero_mem hA h) hA
      have hnonneg : 0 ≤ 1 - schnirelmannDensity A := by
        linarith [@schnirelmannDensity_le_one A _]
      calc
        1 - schnirelmannDensity (schnirelmannSumset A h + A) ≤
            (1 - schnirelmannDensity (schnirelmannSumset A h)) *
              (1 - schnirelmannDensity A) := by nlinarith
        _ ≤ (1 - schnirelmannDensity A) ^ h * (1 - schnirelmannDensity A) :=
          mul_le_mul_of_nonneg_right ih hnonneg
        _ = (1 - schnirelmannDensity A) ^ (h + 1) := (pow_succ _ _).symm

/-- **Schnirelmann's basis theorem.** Let $A$ be a set of natural numbers with $0 \in A$ whose
Schnirelmann density $\sigma(A) = \inf_{n \ge 1} |A \cap \{1, \dots, n\}| / n$ is positive.
Then $A$ is an additive basis of finite order: there is a natural number $h$ such that every
natural number $n$ can be written as $n = a_1 + \dots + a_h$ with $a_1, \dots, a_h \in A$,
repetitions allowed.

Source: Lemma 1 of Tim Jameson's notes on Linnik's proof of the Waring-Hilbert theorem. -/
theorem _root_.exists_additive_basis_of_pos_schnirelmannDensity {A : Set ℕ}
    [DecidablePred (· ∈ A)] (hA : 0 ∈ A) (hσ : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, ∀ n : ℕ, ∃ x : Fin h → ℕ,
      (∀ i, x i ∈ A) ∧ n = ∑ i, x i := by
  have hd_nonneg : 0 ≤ 1 - schnirelmannDensity A := by
    linarith [@schnirelmannDensity_le_one A _]
  have hd_lt_one : 1 - schnirelmannDensity A < 1 := by linarith
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (K := ℝ) (x := (2 : ℝ)⁻¹)
    (by norm_num) hd_lt_one
  let S := schnirelmannSumset A h
  let _ : DecidablePred (· ∈ S) := fun x ↦ Classical.propDecidable (x ∈ S)
  let _ : DecidablePred (· ∈ S + S) := fun x ↦ Classical.propDecidable (x ∈ S + S)
  have hrec := schnirelmannSumset_density_compl_le hA h
  have hσS : (2 : ℝ)⁻¹ < schnirelmannDensity S := by
    dsimp [S]
    linarith
  have hS0 : 0 ∈ S := schnirelmannSumset_zero_mem hA h
  have hcover : S + S = Set.univ :=
    add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity hS0 hS0 (by
      linarith)
  refine ⟨h + h, fun n ↦ ?_⟩
  have hn : n ∈ S + S := by rw [hcover]; trivial
  have hn' : n ∈ schnirelmannSumset A (h + h) := by
    rw [← schnirelmannSumset_add A h h]
    exact hn
  simpa [schnirelmannSumset] using hn'

end MathlibExt.Combinatorics.Schnirelmann
