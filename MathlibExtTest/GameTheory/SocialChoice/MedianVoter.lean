/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SocialChoice.MedianVoter
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-! Examples for `MathlibExt.GameTheory.SocialChoice.MedianVoter`: with three voters the
median peak wins every pairwise majority vote, and with two voters whose peaks differ
neither peak is a Condorcet winner although both satisfy the median conditions, and
a single voter's peak wins. -/

namespace MathlibExtTest.GameTheory.SocialChoice.MedianVoter

section Examples

open MathlibExt.GameTheory.SocialChoice

theorem neg_abs_sub_lt_of_lt_of_le {p a b : ℝ} (hab : a < b) (hbp : b ≤ p) :
    -|a - p| < -|b - p| := by
  have ha : a - p ≤ 0 := by linarith
  have hb : b - p ≤ 0 := by linarith
  rw [abs_of_nonpos ha, abs_of_nonpos hb]
  linarith

theorem neg_abs_sub_lt_of_le_of_lt {p a b : ℝ} (hap : p ≤ a) (hab : a < b) :
    -|b - p| < -|a - p| := by
  have ha : 0 ≤ a - p := by linarith
  have hb : 0 ≤ b - p := by linarith
  rw [abs_of_nonneg ha, abs_of_nonneg hb]
  linarith

def P3 : SinglePeakedProfile (Fin 3) ℝ where
  utility := fun v a => -|a - ![1, 2, 4] v|
  peak := ![1, 2, 4]
  lt_of_lt_of_le_peak := fun _ _ _ hab hbp => neg_abs_sub_lt_of_lt_of_le hab hbp
  lt_of_peak_le_of_lt := fun _ _ _ hap hab => neg_abs_sub_lt_of_le_of_lt hap hab

theorem P3_condorcet : P3.IsCondorcetWinner 2 := by
  apply SinglePeakedProfile.isCondorcetWinner_of_median P3
  · have h3 : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    rw [h3]
    exact ⟨1, rfl⟩
  · have hsub : ({0, 1} : Finset (Fin 3)) ⊆
        Finset.univ.filter (fun v => P3.peak v ≤ 2) := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv with rfl | rfl
      · show (![1, 2, 4] 0 : ℝ) ≤ 2
        have h0 : (![1, 2, 4] 0 : ℝ) = 1 := by simp
        rw [h0]; norm_num
      · show (![1, 2, 4] 1 : ℝ) ≤ 2
        have h1 : (![1, 2, 4] 1 : ℝ) = 2 := by simp
        rw [h1]
    have h2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    have hle2 : 2 ≤ (Finset.univ.filter (fun v => P3.peak v ≤ 2)).card := by
      calc 2 = ({0, 1} : Finset (Fin 3)).card := h2.symm
      _ ≤ (Finset.univ.filter (fun v => P3.peak v ≤ 2)).card :=
        Finset.card_le_card hsub
    have h3 : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    rw [h3]
    omega
  · have hsub : ({1, 2} : Finset (Fin 3)) ⊆
        Finset.univ.filter (fun v => 2 ≤ P3.peak v) := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv with rfl | rfl
      · show (2 : ℝ) ≤ ![1, 2, 4] 1
        have h1 : (![1, 2, 4] 1 : ℝ) = 2 := by simp
        rw [h1]
      · show (2 : ℝ) ≤ ![1, 2, 4] 2
        have h2 : (![1, 2, 4] 2 : ℝ) = 4 := by simp
        rw [h2]; norm_num
    have h2 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    have hge2 : 2 ≤ (Finset.univ.filter (fun v => 2 ≤ P3.peak v)).card := by
      calc 2 = ({1, 2} : Finset (Fin 3)).card := h2.symm
      _ ≤ (Finset.univ.filter (fun v => 2 ≤ P3.peak v)).card :=
        Finset.card_le_card hsub
    have h3 : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    rw [h3]
    omega

def P2 : SinglePeakedProfile (Fin 2) ℝ where
  utility := fun v a => -|a - ![0, 1] v|
  peak := ![0, 1]
  lt_of_lt_of_le_peak := fun _ _ _ hab hbp => neg_abs_sub_lt_of_lt_of_le hab hbp
  lt_of_peak_le_of_lt := fun _ _ _ hap hab => neg_abs_sub_lt_of_le_of_lt hap hab

theorem P2_not_condorcet_0 : ¬ P2.IsCondorcetWinner 0 := by
  intro h
  have hb := h 1 (by norm_num)
  have hsub : Finset.univ.filter (fun v => P2.utility v 1 < P2.utility v 0) ⊆
      ({0} : Finset (Fin 2)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_singleton]
    fin_cases v
    · rfl
    · exfalso
      simp only [P2] at hv
      simp at hv
      norm_num at hv
  have hcard := Finset.card_le_card hsub
  have h1card : ({0} : Finset (Fin 2)).card = 1 := by decide
  have h2card : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2card] at hb
  omega

theorem P2_not_condorcet_1 : ¬ P2.IsCondorcetWinner 1 := by
  intro h
  have hb := h 0 (by norm_num)
  have hsub : Finset.univ.filter (fun v => P2.utility v 0 < P2.utility v 1) ⊆
      ({1} : Finset (Fin 2)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_singleton]
    fin_cases v
    · exfalso
      simp only [P2] at hv
      simp at hv
      norm_num at hv
    · rfl
  have hcard := Finset.card_le_card hsub
  have h1card : ({1} : Finset (Fin 2)).card = 1 := by decide
  have h2card : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2card] at hb
  omega

theorem P2_median_0_hle :
    Fintype.card (Fin 2) ≤ 2 * (Finset.univ.filter fun v => P2.peak v ≤ 0).card := by
  have hsub : ({0} : Finset (Fin 2)) ⊆
      Finset.univ.filter (fun v => P2.peak v ≤ 0) := by
    intro v hv
    simp only [Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with rfl
    show (![0, 1] 0 : ℝ) ≤ 0
    have h0 : (![0, 1] 0 : ℝ) = 0 := by simp
    rw [h0]
  have h1 : ({0} : Finset (Fin 2)).card = 1 := by decide
  have hle1 : 1 ≤ (Finset.univ.filter (fun v => P2.peak v ≤ 0)).card := by
    calc 1 = ({0} : Finset (Fin 2)).card := h1.symm
    _ ≤ (Finset.univ.filter (fun v => P2.peak v ≤ 0)).card :=
      Finset.card_le_card hsub
  have h2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2]
  omega

theorem P2_median_0_hge :
    Fintype.card (Fin 2) ≤ 2 * (Finset.univ.filter fun v => 0 ≤ P2.peak v).card := by
  have hsub : ({0, 1} : Finset (Fin 2)) ⊆
      Finset.univ.filter (fun v => 0 ≤ P2.peak v) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with rfl | rfl
    · show (0 : ℝ) ≤ ![0, 1] 0
      have h0 : (![0, 1] 0 : ℝ) = 0 := by simp
      rw [h0]
    · show (0 : ℝ) ≤ ![0, 1] 1
      have h1 : (![0, 1] 1 : ℝ) = 1 := by simp
      rw [h1]; norm_num
  have h2c : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  have hge2 : 2 ≤ (Finset.univ.filter (fun v => 0 ≤ P2.peak v)).card := by
    calc 2 = ({0, 1} : Finset (Fin 2)).card := h2c.symm
    _ ≤ (Finset.univ.filter (fun v => 0 ≤ P2.peak v)).card :=
      Finset.card_le_card hsub
  have h2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2]
  omega

theorem P2_median_1_hle :
    Fintype.card (Fin 2) ≤ 2 * (Finset.univ.filter fun v => P2.peak v ≤ 1).card := by
  have hsub : ({0, 1} : Finset (Fin 2)) ⊆
      Finset.univ.filter (fun v => P2.peak v ≤ 1) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with rfl | rfl
    · show (![0, 1] 0 : ℝ) ≤ 1
      have h0 : (![0, 1] 0 : ℝ) = 0 := by simp
      rw [h0]; norm_num
    · show (![0, 1] 1 : ℝ) ≤ 1
      have h1 : (![0, 1] 1 : ℝ) = 1 := by simp
      rw [h1]
  have h2c : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  have hle2 : 2 ≤ (Finset.univ.filter (fun v => P2.peak v ≤ 1)).card := by
    calc 2 = ({0, 1} : Finset (Fin 2)).card := h2c.symm
    _ ≤ (Finset.univ.filter (fun v => P2.peak v ≤ 1)).card :=
      Finset.card_le_card hsub
  have h2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2]
  omega

theorem P2_median_1_hge :
    Fintype.card (Fin 2) ≤ 2 * (Finset.univ.filter fun v => 1 ≤ P2.peak v).card := by
  have hsub : ({1} : Finset (Fin 2)) ⊆
      Finset.univ.filter (fun v => 1 ≤ P2.peak v) := by
    intro v hv
    simp only [Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with rfl
    show (1 : ℝ) ≤ ![0, 1] 1
    have h1 : (![0, 1] 1 : ℝ) = 1 := by simp
    rw [h1]
  have h1c : ({1} : Finset (Fin 2)).card = 1 := by decide
  have hge1 : 1 ≤ (Finset.univ.filter (fun v => 1 ≤ P2.peak v)).card := by
    calc 1 = ({1} : Finset (Fin 2)).card := h1c.symm
    _ ≤ (Finset.univ.filter (fun v => 1 ≤ P2.peak v)).card :=
      Finset.card_le_card hsub
  have h2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [h2]
  omega

def P1 : SinglePeakedProfile (Fin 1) ℝ where
  utility := fun _ a => -|a - 3|
  peak := fun _ => 3
  lt_of_lt_of_le_peak := fun _ _ _ hab hbp => neg_abs_sub_lt_of_lt_of_le hab hbp
  lt_of_peak_le_of_lt := fun _ _ _ hap hab => neg_abs_sub_lt_of_le_of_lt hap hab

theorem P1_condorcet : P1.IsCondorcetWinner 3 := by
  apply SinglePeakedProfile.isCondorcetWinner_of_median P1
  · have h1 : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    rw [h1]
    exact ⟨0, rfl⟩
  · have hsub : ({0} : Finset (Fin 1)) ⊆
        Finset.univ.filter (fun v => P1.peak v ≤ 3) := by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv with rfl
      exact le_rfl
    have h1c : ({0} : Finset (Fin 1)).card = 1 := by decide
    have hle1 : 1 ≤ (Finset.univ.filter (fun v => P1.peak v ≤ 3)).card := by
      calc 1 = ({0} : Finset (Fin 1)).card := h1c.symm
      _ ≤ (Finset.univ.filter (fun v => P1.peak v ≤ 3)).card :=
        Finset.card_le_card hsub
    have h1 : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    rw [h1]
    omega
  · have hsub : ({0} : Finset (Fin 1)) ⊆
        Finset.univ.filter (fun v => 3 ≤ P1.peak v) := by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv with rfl
      exact le_rfl
    have h1c : ({0} : Finset (Fin 1)).card = 1 := by decide
    have hge1 : 1 ≤ (Finset.univ.filter (fun v => 3 ≤ P1.peak v)).card := by
      calc 1 = ({0} : Finset (Fin 1)).card := h1c.symm
      _ ≤ (Finset.univ.filter (fun v => 3 ≤ P1.peak v)).card :=
        Finset.card_le_card hsub
    have h1 : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    rw [h1]
    omega

end Examples

#print axioms MathlibExt.GameTheory.SocialChoice.SinglePeakedProfile.isCondorcetWinner_of_median

end MathlibExtTest.GameTheory.SocialChoice.MedianVoter
