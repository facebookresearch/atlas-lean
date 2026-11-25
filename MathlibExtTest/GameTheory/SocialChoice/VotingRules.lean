/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import MathlibExt.GameTheory.SocialChoice.VotingRules
public import MathlibExt.GameTheory.Matching.StableMechanism
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace MathlibExtTest.GameTheory.SocialChoice.VotingRules
open Classical
open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open MathlibExt.GameTheory.Matching.StableMechanism
open scoped BigOperators
@[expose] public section
/-- Ballot `0 ≻ 1 ≻ 2` on `Fin 3`. -/
def b0 : MathlibExt.Order.StrictTotalOrder (Fin 3) :=
  rankOrder ![0, 1, 2] (by decide)
/-- Ballot `1 ≻ 2 ≻ 0` on `Fin 3`. -/
def b1 : MathlibExt.Order.StrictTotalOrder (Fin 3) :=
  rankOrder ![2, 0, 1] (by decide)
/-- Ballot `2 ≻ 0 ≻ 1` on `Fin 3`. -/
def b2 : MathlibExt.Order.StrictTotalOrder (Fin 3) :=
  rankOrder ![1, 2, 0] (by decide)
/-- Condorcet cycle profile on `Fin 3`. -/
def cycP : Profile (Fin 3) (Fin 3) :=
  fun i => ![b0, b1, b2] i
/-- Cycle net preference and Copeland scores. -/
theorem t1_cycle_net_copeland :
    netPreference cycP 0 1 = 1 ∧ copelandScore cycP 0 = 0 ∧
      (winners (copelandScore cycP)).card = 3 := by
  have hnet01 : netPreference cycP 0 1 = 1 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 0 1) = {0, 2} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ (0 = 0 ∨ 0 = 2)
        decide
      · show ![2, 0, 1] 0 < ![2, 0, 1] 1 ↔ (1 = 0 ∨ 1 = 2)
        decide
      · show ![1, 2, 0] 0 < ![1, 2, 0] 1 ↔ (2 = 0 ∨ 2 = 2)
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 1 0) = {1} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ (0 = 1)
        decide
      · show ![2, 0, 1] 1 < ![2, 0, 1] 0 ↔ (1 = 1)
        decide
      · show ![1, 2, 0] 1 < ![1, 2, 0] 0 ↔ (2 = 1)
        decide
    rw [hf1, hf2]
    decide
  have hnet02 : netPreference cycP 0 2 = -1 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 0 2) = {0} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ (0 = 0)
        decide
      · show ![2, 0, 1] 0 < ![2, 0, 1] 2 ↔ (1 = 0)
        decide
      · show ![1, 2, 0] 0 < ![1, 2, 0] 2 ↔ (2 = 0)
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 2 0) = {1, 2} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ (0 = 1 ∨ 0 = 2)
        decide
      · show ![2, 0, 1] 2 < ![2, 0, 1] 0 ↔ (1 = 1 ∨ 1 = 2)
        decide
      · show ![1, 2, 0] 2 < ![1, 2, 0] 0 ↔ (2 = 1 ∨ 2 = 2)
        decide
    rw [hf1, hf2]
    decide
  have hnet12 : netPreference cycP 1 2 = 1 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 1 2) = {0, 1} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 1 < ![0, 1, 2] 2 ↔ (0 = 0 ∨ 0 = 1)
        decide
      · show ![2, 0, 1] 1 < ![2, 0, 1] 2 ↔ (1 = 0 ∨ 1 = 1)
        decide
      · show ![1, 2, 0] 1 < ![1, 2, 0] 2 ↔ (2 = 0 ∨ 2 = 1)
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (cycP i).lt 2 1) = {2} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases i
      · show ![0, 1, 2] 2 < ![0, 1, 2] 1 ↔ (0 = 2)
        decide
      · show ![2, 0, 1] 2 < ![2, 0, 1] 1 ↔ (1 = 2)
        decide
      · show ![1, 2, 0] 2 < ![1, 2, 0] 1 ↔ (2 = 2)
        decide
    rw [hf1, hf2]
    decide
  have hnet10 : netPreference cycP 1 0 = -1 := by
    rw [netPreference_antisymm, hnet01]
  have hnet20 : netPreference cycP 2 0 = 1 := by
    rw [netPreference_antisymm, hnet02]
    simp
  have hnet21 : netPreference cycP 2 1 = -1 := by
    rw [netPreference_antisymm, hnet12]
  have hcop0 : copelandScore cycP 0 = 0 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP 0 b) = {1} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 0 0 ↔ (0 = 1)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers cycP 0 1 ↔ (1 = 1)
        simp [majorityPrefers_iff_netPreference_pos, hnet01]
      · show CondorcetCycle.MajorityPrefers cycP 0 2 ↔ (2 = 1)
        simp [majorityPrefers_iff_netPreference_pos, hnet02]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP b 0) = {2} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 0 0 ↔ (0 = 2)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers cycP 1 0 ↔ (1 = 2)
        simp [majorityPrefers_iff_netPreference_pos, hnet10]
      · show CondorcetCycle.MajorityPrefers cycP 2 0 ↔ (2 = 2)
        simp [majorityPrefers_iff_netPreference_pos, hnet20]
    rw [hwins, hloss]
    decide
  have hcop1 : copelandScore cycP 1 = 0 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP 1 b) = {2} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 1 0 ↔ (0 = 2)
        simp [majorityPrefers_iff_netPreference_pos, hnet10]
      · show CondorcetCycle.MajorityPrefers cycP 1 1 ↔ (1 = 2)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers cycP 1 2 ↔ (2 = 2)
        simp [majorityPrefers_iff_netPreference_pos, hnet12]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP b 1) = {0} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 0 1 ↔ (0 = 0)
        simp [majorityPrefers_iff_netPreference_pos, hnet01]
      · show CondorcetCycle.MajorityPrefers cycP 1 1 ↔ (1 = 0)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers cycP 2 1 ↔ (2 = 0)
        simp [majorityPrefers_iff_netPreference_pos, hnet21]
    rw [hwins, hloss]
    decide
  have hcop2 : copelandScore cycP 2 = 0 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP 2 b) = {0} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 2 0 ↔ (0 = 0)
        simp [majorityPrefers_iff_netPreference_pos, hnet20]
      · show CondorcetCycle.MajorityPrefers cycP 2 1 ↔ (1 = 0)
        simp [majorityPrefers_iff_netPreference_pos, hnet21]
      · show CondorcetCycle.MajorityPrefers cycP 2 2 ↔ (2 = 0)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        CondorcetCycle.MajorityPrefers cycP b 2) = {1} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers cycP 0 2 ↔ (0 = 1)
        simp [majorityPrefers_iff_netPreference_pos, hnet02]
      · show CondorcetCycle.MajorityPrefers cycP 1 2 ↔ (1 = 1)
        simp [majorityPrefers_iff_netPreference_pos, hnet12]
      · show CondorcetCycle.MajorityPrefers cycP 2 2 ↔ (2 = 1)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    rw [hwins, hloss]
    decide
  have hwinners : (winners (copelandScore cycP)).card = 3 := by
    have hall : ∀ a : Fin 3, copelandScore cycP a = 0 := by
      intro a
      fin_cases a
      · exact hcop0
      · exact hcop1
      · exact hcop2
    have h2 : winners (copelandScore cycP) = Finset.univ := by
      ext a
      simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _ b
        rw [hall b, hall a]
    rw [h2, Finset.card_univ, Fintype.card_fin]
  exact ⟨hnet01, hcop0, hwinners⟩
/-- Kendall tau distance between the first two cycle ballots. -/
theorem t2_kendallTau : kendallTau b0 b1 = 2 := by
  unfold kendallTau
  have h : ((Finset.univ ×ˢ Finset.univ).filter
        fun p : Fin 3 × Fin 3 => b0.lt p.1 p.2 ∧ b1.lt p.2 p.1) =
        {(0, 1), (0, 2)} := by
    apply Finset.ext
    intro p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    fin_cases a <;> fin_cases b
    · show ![0, 1, 2] 0 < ![0, 1, 2] 0 ∧ ![2, 0, 1] 0 < ![2, 0, 1] 0 ↔
          ((0, 0) = (0, 1) ∨ (0, 0) = (0, 2))
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ∧ ![2, 0, 1] 1 < ![2, 0, 1] 0 ↔
          ((0, 1) = (0, 1) ∨ (0, 1) = (0, 2))
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ∧ ![2, 0, 1] 2 < ![2, 0, 1] 0 ↔
          ((0, 2) = (0, 1) ∨ (0, 2) = (0, 2))
      decide
    · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ∧ ![2, 0, 1] 0 < ![2, 0, 1] 1 ↔
          ((1, 0) = (0, 1) ∨ (1, 0) = (0, 2))
      decide
    · show ![0, 1, 2] 1 < ![0, 1, 2] 1 ∧ ![2, 0, 1] 1 < ![2, 0, 1] 1 ↔
          ((1, 1) = (0, 1) ∨ (1, 1) = (0, 2))
      decide
    · show ![0, 1, 2] 1 < ![0, 1, 2] 2 ∧ ![2, 0, 1] 2 < ![2, 0, 1] 1 ↔
          ((1, 2) = (0, 1) ∨ (1, 2) = (0, 2))
      decide
    · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ∧ ![2, 0, 1] 0 < ![2, 0, 1] 2 ↔
          ((2, 0) = (0, 1) ∨ (2, 0) = (0, 2))
      decide
    · show ![0, 1, 2] 2 < ![0, 1, 2] 1 ∧ ![2, 0, 1] 1 < ![2, 0, 1] 2 ↔
          ((2, 1) = (0, 1) ∨ (2, 1) = (0, 2))
      decide
    · show ![0, 1, 2] 2 < ![0, 1, 2] 2 ∧ ![2, 0, 1] 2 < ![2, 0, 1] 2 ↔
          ((2, 2) = (0, 1) ∨ (2, 2) = (0, 2))
      decide
  rw [h]
  decide
/-- Kemeny score of the first ballot in the cycle profile. -/
theorem t3_kemenyScore : kemenyScore cycP b0 = 4 := by
  unfold kemenyScore
  rw [Fin.sum_univ_three]
  have hc0 : cycP 0 = b0 := rfl
  have hc1 : cycP 1 = b1 := rfl
  have hc2 : cycP 2 = b2 := rfl
  have hk00 : kendallTau (cycP 0) b0 = 0 := by
    rw [hc0]
    exact kendallTau_self b0
  have hk10 : kendallTau (cycP 1) b0 = 2 := by
    rw [hc1, kendallTau_comm]
    exact t2_kendallTau
  have hk20 : kendallTau (cycP 2) b0 = 2 := by
    rw [hc2]
    unfold kendallTau
    have h : ((Finset.univ ×ˢ Finset.univ).filter
          fun p : Fin 3 × Fin 3 => b2.lt p.1 p.2 ∧ b0.lt p.2 p.1) =
          {(2, 0), (2, 1)} := by
      apply Finset.ext
      intro p
      obtain ⟨a, b⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      fin_cases a <;> fin_cases b
      · show ![1, 2, 0] 0 < ![1, 2, 0] 0 ∧ ![0, 1, 2] 0 < ![0, 1, 2] 0 ↔
            ((0, 0) = (2, 0) ∨ (0, 0) = (2, 1))
        decide
      · show ![1, 2, 0] 0 < ![1, 2, 0] 1 ∧ ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔
            ((0, 1) = (2, 0) ∨ (0, 1) = (2, 1))
        decide
      · show ![1, 2, 0] 0 < ![1, 2, 0] 2 ∧ ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔
            ((0, 2) = (2, 0) ∨ (0, 2) = (2, 1))
        decide
      · show ![1, 2, 0] 1 < ![1, 2, 0] 0 ∧ ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔
            ((1, 0) = (2, 0) ∨ (1, 0) = (2, 1))
        decide
      · show ![1, 2, 0] 1 < ![1, 2, 0] 1 ∧ ![0, 1, 2] 1 < ![0, 1, 2] 1 ↔
            ((1, 1) = (2, 0) ∨ (1, 1) = (2, 1))
        decide
      · show ![1, 2, 0] 1 < ![1, 2, 0] 2 ∧ ![0, 1, 2] 2 < ![0, 1, 2] 1 ↔
            ((1, 2) = (2, 0) ∨ (1, 2) = (2, 1))
        decide
      · show ![1, 2, 0] 2 < ![1, 2, 0] 0 ∧ ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔
            ((2, 0) = (2, 0) ∨ (2, 0) = (2, 1))
        decide
      · show ![1, 2, 0] 2 < ![1, 2, 0] 1 ∧ ![0, 1, 2] 1 < ![0, 1, 2] 2 ↔
            ((2, 1) = (2, 0) ∨ (2, 1) = (2, 1))
        decide
      · show ![1, 2, 0] 2 < ![1, 2, 0] 2 ∧ ![0, 1, 2] 2 < ![0, 1, 2] 2 ↔
            ((2, 2) = (2, 0) ∨ (2, 2) = (2, 1))
        decide
    rw [h]
    decide
  rw [hk00, hk10, hk20]
/-- Unanimous profile on `Fin 3`: every voter ranks `0 ≻ 1 ≻ 2`. -/
def unanimousP : Profile (Fin 3) (Fin 3) :=
  fun _ => b0
/-- Copeland scores and second-order boundary values on the unanimous
profile: `0` is the unique lexicographic second-order Copeland winner. -/
theorem t10_second_order_boundary :
    copelandScore unanimousP 0 = 2 ∧ copelandScore unanimousP 1 = 0 ∧
      copelandScore unanimousP 2 = -2 ∧
      secondOrderCopelandScore unanimousP 0 = -2 ∧
      secondOrderCopelandScore unanimousP 2 = 0 ∧
      secondOrderCopelandWinners unanimousP = {0} := by
  have hnet01 : netPreference unanimousP 0 1 = 3 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 0 1) = Finset.univ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases i
      · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
        decide
      · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
        decide
      · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 1 0) = ∅ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty]
      fin_cases i
      · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
        decide
      · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
        decide
      · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
        decide
    rw [hf1, hf2, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
    decide
  have hnet02 : netPreference unanimousP 0 2 = 3 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 0 2) = Finset.univ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases i
      · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
        decide
      · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
        decide
      · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 2 0) = ∅ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty]
      fin_cases i
      · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
        decide
      · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
        decide
      · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
        decide
    rw [hf1, hf2, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
    decide
  have hnet12 : netPreference unanimousP 1 2 = 3 := by
    unfold netPreference
    have hf1 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 1 2) = Finset.univ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases i
      · show ![0, 1, 2] 1 < ![0, 1, 2] 2 ↔ True
        decide
      · show ![0, 1, 2] 1 < ![0, 1, 2] 2 ↔ True
        decide
      · show ![0, 1, 2] 1 < ![0, 1, 2] 2 ↔ True
        decide
    have hf2 : (Finset.univ.filter fun i : Fin 3 =>
        (unanimousP i).lt 2 1) = ∅ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty]
      fin_cases i
      · show ![0, 1, 2] 2 < ![0, 1, 2] 1 ↔ False
        decide
      · show ![0, 1, 2] 2 < ![0, 1, 2] 1 ↔ False
        decide
      · show ![0, 1, 2] 2 < ![0, 1, 2] 1 ↔ False
        decide
    rw [hf1, hf2, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
    decide
  have hnet10 : netPreference unanimousP 1 0 = -3 := by
    rw [netPreference_antisymm, hnet01]
  have hnet20 : netPreference unanimousP 2 0 = -3 := by
    rw [netPreference_antisymm, hnet02]
  have hnet21 : netPreference unanimousP 2 1 = -3 := by
    rw [netPreference_antisymm, hnet12]
  have hwins0 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP 0 b) = {1, 2} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 0 0 ↔ (0 = 1 ∨ 0 = 2)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers unanimousP 0 1 ↔ (1 = 1 ∨ 1 = 2)
      simp [majorityPrefers_iff_netPreference_pos, hnet01]
    · show CondorcetCycle.MajorityPrefers unanimousP 0 2 ↔ (2 = 1 ∨ 2 = 2)
      simp [majorityPrefers_iff_netPreference_pos, hnet02]
  have hloss0 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP b 0) = ∅ := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 0 0 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers unanimousP 1 0 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, hnet10]
    · show CondorcetCycle.MajorityPrefers unanimousP 2 0 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, hnet20]
  have hcop0 : copelandScore unanimousP 0 = 2 := by
    unfold copelandScore
    rw [hwins0, hloss0, Finset.card_empty]
    decide
  have hwins1 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP 1 b) = {2} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 1 0 ↔ (0 = 2)
      simp [majorityPrefers_iff_netPreference_pos, hnet10]
    · show CondorcetCycle.MajorityPrefers unanimousP 1 1 ↔ (1 = 2)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers unanimousP 1 2 ↔ (2 = 2)
      simp [majorityPrefers_iff_netPreference_pos, hnet12]
  have hloss1 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP b 1) = {0} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 0 1 ↔ (0 = 0)
      simp [majorityPrefers_iff_netPreference_pos, hnet01]
    · show CondorcetCycle.MajorityPrefers unanimousP 1 1 ↔ (1 = 0)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers unanimousP 2 1 ↔ (2 = 0)
      simp [majorityPrefers_iff_netPreference_pos, hnet21]
  have hcop1 : copelandScore unanimousP 1 = 0 := by
    unfold copelandScore
    rw [hwins1, hloss1]
    decide
  have hwins2 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP 2 b) = ∅ := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 2 0 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, hnet20]
    · show CondorcetCycle.MajorityPrefers unanimousP 2 1 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, hnet21]
    · show CondorcetCycle.MajorityPrefers unanimousP 2 2 ↔ False
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
  have hloss2 : (Finset.univ.filter fun b : Fin 3 =>
      CondorcetCycle.MajorityPrefers unanimousP b 2) = {0, 1} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers unanimousP 0 2 ↔ (0 = 0 ∨ 0 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet02]
    · show CondorcetCycle.MajorityPrefers unanimousP 1 2 ↔ (1 = 0 ∨ 1 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet12]
    · show CondorcetCycle.MajorityPrefers unanimousP 2 2 ↔ (2 = 0 ∨ 2 = 1)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
  have hcop2 : copelandScore unanimousP 2 = -2 := by
    unfold copelandScore
    rw [hwins2, hloss2, Finset.card_empty]
    decide
  have hso0 : secondOrderCopelandScore unanimousP 0 = -2 := by
    unfold secondOrderCopelandScore
    rw [hwins0, Finset.sum_insert (by decide), Finset.sum_singleton, hcop1, hcop2]
    decide
  have hso2 : secondOrderCopelandScore unanimousP 2 = 0 := by
    unfold secondOrderCopelandScore
    rw [hwins2, Finset.sum_empty]
  have hwinners : secondOrderCopelandWinners unanimousP = {0} := by
    apply Finset.ext
    intro b
    simp only [secondOrderCopelandWinners, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    fin_cases b
    · show IsSecondOrderCopelandWinner unanimousP 0 ↔ (0 = 0)
      constructor
      · intro _; rfl
      · intro _
        unfold IsSecondOrderCopelandWinner
        intro c
        fin_cases c
        · exact Or.inr ⟨rfl, le_refl _⟩
        · refine Or.inl ?_
          show copelandScore unanimousP 1 < copelandScore unanimousP 0
          rw [hcop1, hcop0]
          decide
        · refine Or.inl ?_
          show copelandScore unanimousP 2 < copelandScore unanimousP 0
          rw [hcop2, hcop0]
          decide
    · show IsSecondOrderCopelandWinner unanimousP 1 ↔ (1 = 0)
      constructor
      · intro h
        rcases h 0 with hlt | ⟨heq, _⟩
        · rw [hcop0, hcop1] at hlt
          exact absurd hlt (by decide)
        · rw [hcop0, hcop1] at heq
          exact absurd heq (by decide)
      · intro h
        exact absurd h (by decide)
    · show IsSecondOrderCopelandWinner unanimousP 2 ↔ (2 = 0)
      constructor
      · intro h
        rcases h 0 with hlt | ⟨heq, _⟩
        · rw [hcop0, hcop2] at hlt
          exact absurd hlt (by decide)
        · rw [hcop0, hcop2] at heq
          exact absurd heq (by decide)
      · intro h
        exact absurd h (by decide)
  exact ⟨hcop0, hcop1, hcop2, hso0, hso2, hwinners⟩
/-- Ballot `0 ≻ 3 ≻ 1 ≻ 2` on `Fin 4`. -/
def tbA : MathlibExt.Order.StrictTotalOrder (Fin 4) :=
  rankOrder ![0, 2, 3, 1] (by decide)
/-- Ballot `2 ≻ 3 ≻ 0 ≻ 1` on `Fin 4`. -/
def tbB : MathlibExt.Order.StrictTotalOrder (Fin 4) :=
  rankOrder ![2, 3, 0, 1] (by decide)
/-- Ballot `1 ≻ 2 ≻ 3 ≻ 0` on `Fin 4`. -/
def tbC : MathlibExt.Order.StrictTotalOrder (Fin 4) :=
  rankOrder ![3, 0, 1, 2] (by decide)
/-- Five-voter profile on `Fin 4` where `2` and `3` tie on Copeland score
and the second-order score separates them. -/
def tieP : Profile (Fin 4) (Fin 5) :=
  fun i => ![tbA, tbA, tbB, tbB, tbC] i
/-- Net preference of `0` over `1` in the tie profile. -/
private theorem tieP_net01 : netPreference tieP 0 1 = 3 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 0 1) = {0, 1, 2, 3} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 1 ↔
          (0 = 0 ∨ 0 = 1 ∨ 0 = 2 ∨ 0 = 3)
      decide
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 1 ↔
          (1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 1 ↔
          (2 = 0 ∨ 2 = 1 ∨ 2 = 2 ∨ 2 = 3)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 1 ↔
          (3 = 0 ∨ 3 = 1 ∨ 3 = 2 ∨ 3 = 3)
      decide
    · show ![3, 0, 1, 2] 0 < ![3, 0, 1, 2] 1 ↔
          (4 = 0 ∨ 4 = 1 ∨ 4 = 2 ∨ 4 = 3)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 1 0) = {4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 0 ↔ (0 = 4)
      decide
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 0 ↔ (1 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 0 ↔ (2 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 0 ↔ (3 = 4)
      decide
    · show ![3, 0, 1, 2] 1 < ![3, 0, 1, 2] 0 ↔ (4 = 4)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `0` over `2` in the tie profile. -/
private theorem tieP_net02 : netPreference tieP 0 2 = -1 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 0 2) = {0, 1} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 2 ↔ (0 = 0 ∨ 0 = 1)
      decide
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 2 ↔ (1 = 0 ∨ 1 = 1)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 2 ↔ (2 = 0 ∨ 2 = 1)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 2 ↔ (3 = 0 ∨ 3 = 1)
      decide
    · show ![3, 0, 1, 2] 0 < ![3, 0, 1, 2] 2 ↔ (4 = 0 ∨ 4 = 1)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 2 0) = {2, 3, 4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 0 ↔ (0 = 2 ∨ 0 = 3 ∨ 0 = 4)
      decide
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 0 ↔ (1 = 2 ∨ 1 = 3 ∨ 1 = 4)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 0 ↔ (2 = 2 ∨ 2 = 3 ∨ 2 = 4)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 0 ↔ (3 = 2 ∨ 3 = 3 ∨ 3 = 4)
      decide
    · show ![3, 0, 1, 2] 2 < ![3, 0, 1, 2] 0 ↔ (4 = 2 ∨ 4 = 3 ∨ 4 = 4)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `0` over `3` in the tie profile. -/
private theorem tieP_net03 : netPreference tieP 0 3 = -1 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 0 3) = {0, 1} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 3 ↔ (0 = 0 ∨ 0 = 1)
      decide
    · show ![0, 2, 3, 1] 0 < ![0, 2, 3, 1] 3 ↔ (1 = 0 ∨ 1 = 1)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 3 ↔ (2 = 0 ∨ 2 = 1)
      decide
    · show ![2, 3, 0, 1] 0 < ![2, 3, 0, 1] 3 ↔ (3 = 0 ∨ 3 = 1)
      decide
    · show ![3, 0, 1, 2] 0 < ![3, 0, 1, 2] 3 ↔ (4 = 0 ∨ 4 = 1)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 3 0) = {2, 3, 4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 0 ↔ (0 = 2 ∨ 0 = 3 ∨ 0 = 4)
      decide
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 0 ↔ (1 = 2 ∨ 1 = 3 ∨ 1 = 4)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 0 ↔ (2 = 2 ∨ 2 = 3 ∨ 2 = 4)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 0 ↔ (3 = 2 ∨ 3 = 3 ∨ 3 = 4)
      decide
    · show ![3, 0, 1, 2] 3 < ![3, 0, 1, 2] 0 ↔ (4 = 2 ∨ 4 = 3 ∨ 4 = 4)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `1` over `2` in the tie profile. -/
private theorem tieP_net12 : netPreference tieP 1 2 = 1 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 1 2) = {0, 1, 4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 2 ↔ (0 = 0 ∨ 0 = 1 ∨ 0 = 4)
      decide
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 2 ↔ (1 = 0 ∨ 1 = 1 ∨ 1 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 2 ↔ (2 = 0 ∨ 2 = 1 ∨ 2 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 2 ↔ (3 = 0 ∨ 3 = 1 ∨ 3 = 4)
      decide
    · show ![3, 0, 1, 2] 1 < ![3, 0, 1, 2] 2 ↔ (4 = 0 ∨ 4 = 1 ∨ 4 = 4)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 2 1) = {2, 3} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 1 ↔ (0 = 2 ∨ 0 = 3)
      decide
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 1 ↔ (1 = 2 ∨ 1 = 3)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 1 ↔ (2 = 2 ∨ 2 = 3)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 1 ↔ (3 = 2 ∨ 3 = 3)
      decide
    · show ![3, 0, 1, 2] 2 < ![3, 0, 1, 2] 1 ↔ (4 = 2 ∨ 4 = 3)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `1` over `3` in the tie profile. -/
private theorem tieP_net13 : netPreference tieP 1 3 = -3 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 1 3) = {4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 3 ↔ (0 = 4)
      decide
    · show ![0, 2, 3, 1] 1 < ![0, 2, 3, 1] 3 ↔ (1 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 3 ↔ (2 = 4)
      decide
    · show ![2, 3, 0, 1] 1 < ![2, 3, 0, 1] 3 ↔ (3 = 4)
      decide
    · show ![3, 0, 1, 2] 1 < ![3, 0, 1, 2] 3 ↔ (4 = 4)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 3 1) = {0, 1, 2, 3} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 1 ↔
          (0 = 0 ∨ 0 = 1 ∨ 0 = 2 ∨ 0 = 3)
      decide
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 1 ↔
          (1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 1 ↔
          (2 = 0 ∨ 2 = 1 ∨ 2 = 2 ∨ 2 = 3)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 1 ↔
          (3 = 0 ∨ 3 = 1 ∨ 3 = 2 ∨ 3 = 3)
      decide
    · show ![3, 0, 1, 2] 3 < ![3, 0, 1, 2] 1 ↔
          (4 = 0 ∨ 4 = 1 ∨ 4 = 2 ∨ 4 = 3)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `2` over `3` in the tie profile. -/
private theorem tieP_net23 : netPreference tieP 2 3 = 1 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 2 3) = {2, 3, 4} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 3 ↔ (0 = 2 ∨ 0 = 3 ∨ 0 = 4)
      decide
    · show ![0, 2, 3, 1] 2 < ![0, 2, 3, 1] 3 ↔ (1 = 2 ∨ 1 = 3 ∨ 1 = 4)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 3 ↔ (2 = 2 ∨ 2 = 3 ∨ 2 = 4)
      decide
    · show ![2, 3, 0, 1] 2 < ![2, 3, 0, 1] 3 ↔ (3 = 2 ∨ 3 = 3 ∨ 3 = 4)
      decide
    · show ![3, 0, 1, 2] 2 < ![3, 0, 1, 2] 3 ↔ (4 = 2 ∨ 4 = 3 ∨ 4 = 4)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 5 =>
      (tieP i).lt 3 2) = {0, 1} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 2 ↔ (0 = 0 ∨ 0 = 1)
      decide
    · show ![0, 2, 3, 1] 3 < ![0, 2, 3, 1] 2 ↔ (1 = 0 ∨ 1 = 1)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 2 ↔ (2 = 0 ∨ 2 = 1)
      decide
    · show ![2, 3, 0, 1] 3 < ![2, 3, 0, 1] 2 ↔ (3 = 0 ∨ 3 = 1)
      decide
    · show ![3, 0, 1, 2] 3 < ![3, 0, 1, 2] 2 ↔ (4 = 0 ∨ 4 = 1)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `0` over `2` in the cycle profile. -/
private theorem cycP_net02 : netPreference cycP 0 2 = -1 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 3 =>
      (cycP i).lt 0 2) = {0} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases i
    · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ (0 = 0)
      decide
    · show ![2, 0, 1] 0 < ![2, 0, 1] 2 ↔ (1 = 0)
      decide
    · show ![1, 2, 0] 0 < ![1, 2, 0] 2 ↔ (2 = 0)
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 3 =>
      (cycP i).lt 2 0) = {1, 2} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ (0 = 1 ∨ 0 = 2)
      decide
    · show ![2, 0, 1] 2 < ![2, 0, 1] 0 ↔ (1 = 1 ∨ 1 = 2)
      decide
    · show ![1, 2, 0] 2 < ![1, 2, 0] 0 ↔ (2 = 1 ∨ 2 = 2)
      decide
  rw [hf1, hf2]
  decide
/-- Net preference of `0` over `1` in the unanimous profile. -/
private theorem unanimousP_net01 : netPreference unanimousP 0 1 = 3 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 3 =>
      (unanimousP i).lt 0 1) = Finset.univ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i
    · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 1 ↔ True
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 3 =>
      (unanimousP i).lt 1 0) = ∅ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty]
    fin_cases i
    · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
      decide
    · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
      decide
    · show ![0, 1, 2] 1 < ![0, 1, 2] 0 ↔ False
      decide
  rw [hf1, hf2, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
  decide
/-- Net preference of `0` over `2` in the unanimous profile. -/
private theorem unanimousP_net02 : netPreference unanimousP 0 2 = 3 := by
  unfold netPreference
  have hf1 : (Finset.univ.filter fun i : Fin 3 =>
      (unanimousP i).lt 0 2) = Finset.univ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i
    · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
      decide
    · show ![0, 1, 2] 0 < ![0, 1, 2] 2 ↔ True
      decide
  have hf2 : (Finset.univ.filter fun i : Fin 3 =>
      (unanimousP i).lt 2 0) = ∅ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty]
    fin_cases i
    · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
      decide
    · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
      decide
    · show ![0, 1, 2] 2 < ![0, 1, 2] 0 ↔ False
      decide
  rw [hf1, hf2, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
  decide
/-- Second-order tie-break: `2` and `3` tie on Copeland score `1`, but
`2` has the higher second-order score and is the unique winner. -/
theorem t11_second_order_tiebreak :
    copelandScore tieP 2 = 1 ∧ copelandScore tieP 3 = 1 ∧
      secondOrderCopelandScore tieP 2 = 0 ∧
      secondOrderCopelandScore tieP 3 = -2 ∧
      secondOrderCopelandWinners tieP = {2} := by
  have hnet10 : netPreference tieP 1 0 = -3 := by
    rw [netPreference_antisymm, tieP_net01]
  have hnet20 : netPreference tieP 2 0 = 1 := by
    rw [netPreference_antisymm, tieP_net02]
    simp
  have hnet30 : netPreference tieP 3 0 = 1 := by
    rw [netPreference_antisymm, tieP_net03]
    simp
  have hnet21 : netPreference tieP 2 1 = -1 := by
    rw [netPreference_antisymm, tieP_net12]
  have hnet31 : netPreference tieP 3 1 = 3 := by
    rw [netPreference_antisymm, tieP_net13]
    simp
  have hnet32 : netPreference tieP 3 2 = -1 := by
    rw [netPreference_antisymm, tieP_net23]
  have hcop0 : copelandScore tieP 0 = -1 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 4 =>
        CondorcetCycle.MajorityPrefers tieP 0 b) = {1} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers tieP 0 0 ↔ (0 = 1)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers tieP 0 1 ↔ (1 = 1)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net01]
      · show CondorcetCycle.MajorityPrefers tieP 0 2 ↔ (2 = 1)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net02]
      · show CondorcetCycle.MajorityPrefers tieP 0 3 ↔ (3 = 1)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net03]
    have hloss : (Finset.univ.filter fun b : Fin 4 =>
        CondorcetCycle.MajorityPrefers tieP b 0) = {2, 3} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers tieP 0 0 ↔ (0 = 2 ∨ 0 = 3)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers tieP 1 0 ↔ (1 = 2 ∨ 1 = 3)
        simp [majorityPrefers_iff_netPreference_pos, hnet10]
      · show CondorcetCycle.MajorityPrefers tieP 2 0 ↔ (2 = 2 ∨ 2 = 3)
        simp [majorityPrefers_iff_netPreference_pos, hnet20]
      · show CondorcetCycle.MajorityPrefers tieP 3 0 ↔ (3 = 2 ∨ 3 = 3)
        simp [majorityPrefers_iff_netPreference_pos, hnet30]
    rw [hwins, hloss]
    decide
  have hcop1 : copelandScore tieP 1 = -1 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 4 =>
        CondorcetCycle.MajorityPrefers tieP 1 b) = {2} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers tieP 1 0 ↔ (0 = 2)
        simp [majorityPrefers_iff_netPreference_pos, hnet10]
      · show CondorcetCycle.MajorityPrefers tieP 1 1 ↔ (1 = 2)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers tieP 1 2 ↔ (2 = 2)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net12]
      · show CondorcetCycle.MajorityPrefers tieP 1 3 ↔ (3 = 2)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net13]
    have hloss : (Finset.univ.filter fun b : Fin 4 =>
        CondorcetCycle.MajorityPrefers tieP b 1) = {0, 3} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases b
      · show CondorcetCycle.MajorityPrefers tieP 0 1 ↔ (0 = 0 ∨ 0 = 3)
        simp [majorityPrefers_iff_netPreference_pos, tieP_net01]
      · show CondorcetCycle.MajorityPrefers tieP 1 1 ↔ (1 = 0 ∨ 1 = 3)
        simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
      · show CondorcetCycle.MajorityPrefers tieP 2 1 ↔ (2 = 0 ∨ 2 = 3)
        simp [majorityPrefers_iff_netPreference_pos, hnet21]
      · show CondorcetCycle.MajorityPrefers tieP 3 1 ↔ (3 = 0 ∨ 3 = 3)
        simp [majorityPrefers_iff_netPreference_pos, hnet31]
    rw [hwins, hloss]
    decide
  have hwins2 : (Finset.univ.filter fun b : Fin 4 =>
      CondorcetCycle.MajorityPrefers tieP 2 b) = {0, 3} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers tieP 2 0 ↔ (0 = 0 ∨ 0 = 3)
      simp [majorityPrefers_iff_netPreference_pos, hnet20]
    · show CondorcetCycle.MajorityPrefers tieP 2 1 ↔ (1 = 0 ∨ 1 = 3)
      simp [majorityPrefers_iff_netPreference_pos, hnet21]
    · show CondorcetCycle.MajorityPrefers tieP 2 2 ↔ (2 = 0 ∨ 2 = 3)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers tieP 2 3 ↔ (3 = 0 ∨ 3 = 3)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net23]
  have hloss2 : (Finset.univ.filter fun b : Fin 4 =>
      CondorcetCycle.MajorityPrefers tieP b 2) = {1} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers tieP 0 2 ↔ (0 = 1)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net02]
    · show CondorcetCycle.MajorityPrefers tieP 1 2 ↔ (1 = 1)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net12]
    · show CondorcetCycle.MajorityPrefers tieP 2 2 ↔ (2 = 1)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
    · show CondorcetCycle.MajorityPrefers tieP 3 2 ↔ (3 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet32]
  have hcop2 : copelandScore tieP 2 = 1 := by
    unfold copelandScore
    rw [hwins2, hloss2]
    decide
  have hwins3 : (Finset.univ.filter fun b : Fin 4 =>
      CondorcetCycle.MajorityPrefers tieP 3 b) = {0, 1} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers tieP 3 0 ↔ (0 = 0 ∨ 0 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet30]
    · show CondorcetCycle.MajorityPrefers tieP 3 1 ↔ (1 = 0 ∨ 1 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet31]
    · show CondorcetCycle.MajorityPrefers tieP 3 2 ↔ (2 = 0 ∨ 2 = 1)
      simp [majorityPrefers_iff_netPreference_pos, hnet32]
    · show CondorcetCycle.MajorityPrefers tieP 3 3 ↔ (3 = 0 ∨ 3 = 1)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
  have hloss3 : (Finset.univ.filter fun b : Fin 4 =>
      CondorcetCycle.MajorityPrefers tieP b 3) = {2} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases b
    · show CondorcetCycle.MajorityPrefers tieP 0 3 ↔ (0 = 2)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net03]
    · show CondorcetCycle.MajorityPrefers tieP 1 3 ↔ (1 = 2)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net13]
    · show CondorcetCycle.MajorityPrefers tieP 2 3 ↔ (2 = 2)
      simp [majorityPrefers_iff_netPreference_pos, tieP_net23]
    · show CondorcetCycle.MajorityPrefers tieP 3 3 ↔ (3 = 2)
      simp [majorityPrefers_iff_netPreference_pos, netPreference_self]
  have hcop3 : copelandScore tieP 3 = 1 := by
    unfold copelandScore
    rw [hwins3, hloss3]
    decide
  have hso2 : secondOrderCopelandScore tieP 2 = 0 := by
    unfold secondOrderCopelandScore
    rw [hwins2, Finset.sum_insert (by decide), Finset.sum_singleton, hcop0, hcop3]
    decide
  have hso3 : secondOrderCopelandScore tieP 3 = -2 := by
    unfold secondOrderCopelandScore
    rw [hwins3, Finset.sum_insert (by decide), Finset.sum_singleton, hcop0, hcop1]
    decide
  have hwinners : secondOrderCopelandWinners tieP = {2} := by
    apply Finset.ext
    intro b
    simp only [secondOrderCopelandWinners, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    fin_cases b
    · show IsSecondOrderCopelandWinner tieP 0 ↔ (0 = 2)
      constructor
      · intro h
        rcases h 2 with hlt | ⟨heq, _⟩
        · rw [hcop2, hcop0] at hlt
          exact absurd hlt (by decide)
        · rw [hcop2, hcop0] at heq
          exact absurd heq (by decide)
      · intro h
        exact absurd h (by decide)
    · show IsSecondOrderCopelandWinner tieP 1 ↔ (1 = 2)
      constructor
      · intro h
        rcases h 2 with hlt | ⟨heq, _⟩
        · rw [hcop2, hcop1] at hlt
          exact absurd hlt (by decide)
        · rw [hcop2, hcop1] at heq
          exact absurd heq (by decide)
      · intro h
        exact absurd h (by decide)
    · show IsSecondOrderCopelandWinner tieP 2 ↔ (2 = 2)
      constructor
      · intro _; rfl
      · intro _
        unfold IsSecondOrderCopelandWinner
        intro c
        fin_cases c
        · refine Or.inl ?_
          show copelandScore tieP 0 < copelandScore tieP 2
          rw [hcop0, hcop2]
          decide
        · refine Or.inl ?_
          show copelandScore tieP 1 < copelandScore tieP 2
          rw [hcop1, hcop2]
          decide
        · exact Or.inr ⟨rfl, le_refl _⟩
        · refine Or.inr ⟨?_, ?_⟩
          · show copelandScore tieP 3 = copelandScore tieP 2
            rw [hcop3, hcop2]
          · show secondOrderCopelandScore tieP 3 ≤
              secondOrderCopelandScore tieP 2
            rw [hso3, hso2]
            decide
    · show IsSecondOrderCopelandWinner tieP 3 ↔ (3 = 2)
      constructor
      · intro h
        rcases h 2 with hlt | ⟨_, hle⟩
        · rw [hcop2, hcop3] at hlt
          exact absurd hlt (by decide)
        · rw [hso2, hso3] at hle
          exact absurd hle (by decide)
      · intro h
        exact absurd h (by decide)
  exact ⟨hcop2, hcop3, hso2, hso3, hwinners⟩
private theorem t12_net10 : netPreference tieP 1 0 = -3 := by
  have h1 := netPreference_antisymm tieP 1 0
  have h2 := tieP_net01
  rw [h1, h2]

private theorem t12_net20 : netPreference tieP 2 0 = 1 := by
  have h1 := netPreference_antisymm tieP 2 0
  have h2 := tieP_net02
  rw [h1, h2]; decide

private theorem t12_net21 : netPreference tieP 2 1 = -1 := by
  have h1 := netPreference_antisymm tieP 2 1
  have h2 := tieP_net12
  rw [h1, h2]

private theorem t12_net30 : netPreference tieP 3 0 = 1 := by
  have h1 := netPreference_antisymm tieP 3 0
  have h2 := tieP_net03
  rw [h1, h2]; decide

private theorem t12_net31 : netPreference tieP 3 1 = 3 := by
  have h1 := netPreference_antisymm tieP 3 1
  have h2 := tieP_net13
  rw [h1, h2]; decide

private theorem t12_net32 : netPreference tieP 3 2 = -1 := by
  have h1 := netPreference_antisymm tieP 3 2
  have h2 := tieP_net23
  rw [h1, h2]

private theorem t12_img_tie0 :
    (Finset.univ.erase (0 : Fin 4)).image (netPreference tieP 0) = {-1, 3} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    fin_cases b
    · exact absurd rfl hb
    · show netPreference tieP 0 1 = -1 ∨ netPreference tieP 0 1 = 3
      rw [tieP_net01]; decide
    · show netPreference tieP 0 2 = -1 ∨ netPreference tieP 0 2 = 3
      rw [tieP_net02]; decide
    · show netPreference tieP 0 3 = -1 ∨ netPreference tieP 0 3 = 3
      rw [tieP_net03]; decide
  · rintro (rfl | rfl)
    · exact ⟨2, by decide, tieP_net02⟩
    · exact ⟨1, by decide, tieP_net01⟩

private theorem t12_img_tie1 :
    (Finset.univ.erase (1 : Fin 4)).image (netPreference tieP 1) = {-3, 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    fin_cases b
    · show netPreference tieP 1 0 = -3 ∨ netPreference tieP 1 0 = 1
      rw [t12_net10]; decide
    · exact absurd rfl hb
    · show netPreference tieP 1 2 = -3 ∨ netPreference tieP 1 2 = 1
      rw [tieP_net12]; decide
    · show netPreference tieP 1 3 = -3 ∨ netPreference tieP 1 3 = 1
      rw [tieP_net13]; decide
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, t12_net10⟩
    · exact ⟨2, by decide, tieP_net12⟩

private theorem t12_img_tie2 :
    (Finset.univ.erase (2 : Fin 4)).image (netPreference tieP 2) = {-1, 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    fin_cases b
    · show netPreference tieP 2 0 = -1 ∨ netPreference tieP 2 0 = 1
      rw [t12_net20]; decide
    · show netPreference tieP 2 1 = -1 ∨ netPreference tieP 2 1 = 1
      rw [t12_net21]; decide
    · exact absurd rfl hb
    · show netPreference tieP 2 3 = -1 ∨ netPreference tieP 2 3 = 1
      rw [tieP_net23]; decide
  · rintro (rfl | rfl)
    · exact ⟨1, by decide, t12_net21⟩
    · exact ⟨0, by decide, t12_net20⟩

private theorem t12_img_tie3 :
    (Finset.univ.erase (3 : Fin 4)).image (netPreference tieP 3) = {-1, 1, 3} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    fin_cases b
    · show netPreference tieP 3 0 = -1 ∨ netPreference tieP 3 0 = 1 ∨ netPreference tieP 3 0 = 3
      rw [t12_net30]; decide
    · show netPreference tieP 3 1 = -1 ∨ netPreference tieP 3 1 = 1 ∨ netPreference tieP 3 1 = 3
      rw [t12_net31]; decide
    · show netPreference tieP 3 2 = -1 ∨ netPreference tieP 3 2 = 1 ∨ netPreference tieP 3 2 = 3
      rw [t12_net32]; decide
    · exact absurd rfl hb
  · rintro (rfl | rfl | rfl)
    · exact ⟨2, by decide, t12_net32⟩
    · exact ⟨0, by decide, t12_net30⟩
    · exact ⟨1, by decide, t12_net31⟩

private theorem t12_img_cyc0 :
    (Finset.univ.erase (0 : Fin 3)).image (netPreference cycP 0) = {-1, 1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    fin_cases b
    · exact absurd rfl hb
    · show netPreference cycP 0 1 = -1 ∨ netPreference cycP 0 1 = 1
      rw [t1_cycle_net_copeland.1]; decide
    · show netPreference cycP 0 2 = -1 ∨ netPreference cycP 0 2 = 1
      rw [cycP_net02]; decide
  · rintro (rfl | rfl)
    · exact ⟨2, by decide, cycP_net02⟩
    · exact ⟨1, by decide, t1_cycle_net_copeland.1⟩

private theorem t12_maximin_of_image {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] [Nontrivial Alt] {P : Profile Alt Voter} {a : Alt}
    {s : Finset ℤ} {v : ℤ}
    (himg : (Finset.univ.erase a).image (netPreference P a) = s) (hmem : v ∈ s)
    (hle : ∀ y ∈ s, v ≤ y) : maximinScore P a = v := by
  simp only [maximinScore]
  apply le_antisymm
  · have hmem' : v ∈ (Finset.univ.erase a).image (netPreference P a) := by
      rw [himg]
      exact hmem
    exact Finset.min'_le _ _ hmem'
  · refine Finset.le_min' _ _ _ ?_
    intro y hy
    have hy' : y ∈ s := by
      rw [←himg]
      exact hy
    exact hle y hy'

private theorem t12_max_tie0 : maximinScore tieP 0 = -1 := by
  refine t12_maximin_of_image t12_img_tie0 ?_ ?_
  · decide
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> decide

private theorem t12_max_tie1 : maximinScore tieP 1 = -3 := by
  refine t12_maximin_of_image t12_img_tie1 ?_ ?_
  · decide
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> decide

private theorem t12_max_tie2 : maximinScore tieP 2 = -1 := by
  refine t12_maximin_of_image t12_img_tie2 ?_ ?_
  · decide
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> decide

private theorem t12_max_tie3 : maximinScore tieP 3 = -1 := by
  refine t12_maximin_of_image t12_img_tie3 ?_ ?_
  · decide
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> decide

private theorem t12_max_cyc0 : maximinScore cycP 0 = -1 := by
  refine t12_maximin_of_image t12_img_cyc0 ?_ ?_
  · decide
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> decide

private def b1swap : MathlibExt.Order.StrictTotalOrder (Fin 3) :=
  rankOrder ![1, 0, 2] (by decide)

private def swapP : Profile (Fin 3) (Fin 3) := fun i => ![b0, b1swap, b2] i

private theorem t12_swapP_net01 : netPreference swapP 0 1 = 1 := by
  have hf1 : Finset.univ.filter (fun i : Fin 3 => (swapP i).lt 0 1) = {0, 2} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (0 : ℕ) < 1 ↔ (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (1 : ℕ) < 0 ↔ (1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (1 : ℕ) < 2 ↔ (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      decide
  have hf2 : Finset.univ.filter (fun i : Fin 3 => (swapP i).lt 1 0) = {1} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (1 : ℕ) < 0 ↔ (0 : Fin 3) ∈ ({1} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (0 : ℕ) < 1 ↔ (1 : Fin 3) ∈ ({1} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (2 : ℕ) < 1 ↔ (2 : Fin 3) ∈ ({1} : Finset (Fin 3))
      decide
  simp only [netPreference, hf1, hf2]
  decide

private theorem t12_swapP_net02 : netPreference swapP 0 2 = 1 := by
  have hf1 : Finset.univ.filter (fun i : Fin 3 => (swapP i).lt 0 2) = {0, 1} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (0 : ℕ) < 2 ↔ (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (1 : ℕ) < 2 ↔ (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (1 : ℕ) < 0 ↔ (2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      decide
  have hf2 : Finset.univ.filter (fun i : Fin 3 => (swapP i).lt 2 0) = {2} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (2 : ℕ) < 0 ↔ (0 : Fin 3) ∈ ({2} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (2 : ℕ) < 1 ↔ (1 : Fin 3) ∈ ({2} : Finset (Fin 3))
      decide
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (0 : ℕ) < 1 ↔ (2 : Fin 3) ∈ ({2} : Finset (Fin 3))
      decide
  simp only [netPreference, hf1, hf2]
  decide

private theorem t12_kendall_b1swap : kendallTau b1 b1swap = 1 := by
  have hdis : ((Finset.univ ×ˢ Finset.univ).filter
      fun p : Fin 3 × Fin 3 => b1.lt p.1 p.2 ∧ b1swap.lt p.2 p.1) = {(2, 0)} := by
    ext p
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;>
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_singleton]
    · show ((2 : ℕ) < 2 ∧ (1 : ℕ) < 1) ↔ ((0 : Fin 3), 0) = (2, 0)
      decide
    · show ((2 : ℕ) < 0 ∧ (0 : ℕ) < 1) ↔ ((0 : Fin 3), 1) = (2, 0)
      decide
    · show ((2 : ℕ) < 1 ∧ (2 : ℕ) < 1) ↔ ((0 : Fin 3), 2) = (2, 0)
      decide
    · show ((0 : ℕ) < 2 ∧ (1 : ℕ) < 0) ↔ ((1 : Fin 3), 0) = (2, 0)
      decide
    · show ((0 : ℕ) < 0 ∧ (0 : ℕ) < 0) ↔ ((1 : Fin 3), 1) = (2, 0)
      decide
    · show ((0 : ℕ) < 1 ∧ (2 : ℕ) < 0) ↔ ((1 : Fin 3), 2) = (2, 0)
      decide
    · show ((1 : ℕ) < 2 ∧ (1 : ℕ) < 2) ↔ ((2 : Fin 3), 0) = (2, 0)
      decide
    · show ((1 : ℕ) < 0 ∧ (0 : ℕ) < 2) ↔ ((2 : Fin 3), 1) = (2, 0)
      decide
    · show ((1 : ℕ) < 1 ∧ (2 : ℕ) < 2) ↔ ((2 : Fin 3), 2) = (2, 0)
      decide
  simp only [kendallTau, hdis, Finset.card_singleton]

private theorem t12_cond_swapP : IsCondorcetWinner swapP 0 := by
  intro b hb
  fin_cases b
  · exact absurd rfl hb
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference swapP 0 1
    rw [t12_swapP_net01]; decide
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference swapP 0 2
    rw [t12_swapP_net02]; decide

private theorem t12_dist_swapP : profileDist cycP swapP = 1 := by
  simp only [profileDist, Fin.sum_univ_three]
  show kendallTau b0 b0 + kendallTau b1 b1swap + kendallTau b2 b2 = 1
  rw [kendallTau_self b0, kendallTau_self b2, t12_kendall_b1swap]

private theorem t12_kendallTau_agree {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (u v : MathlibExt.Order.StrictTotalOrder Alt) (h : kendallTau u v = 0)
    (x y : Alt) : u.lt x y ↔ v.lt x y := by
  have hempty : ((Finset.univ ×ˢ Finset.univ).filter
      fun p : Alt × Alt => u.lt p.1 p.2 ∧ v.lt p.2 p.1) = ∅ := by
    simp only [kendallTau] at h
    exact Finset.card_eq_zero.mp h
  constructor
  · intro huxy
    by_contra hnvy
    have hne : x ≠ y := by
      rintro rfl
      exact u.irrefl _ huxy
    have hvyx : v.lt y x := (v.total hne).resolve_left hnvy
    have hmem : (x, y) ∈ ((Finset.univ ×ˢ Finset.univ).filter
        fun p : Alt × Alt => u.lt p.1 p.2 ∧ v.lt p.2 p.1) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨huxy, hvyx⟩
    rw [hempty] at hmem
    simp at hmem
  · intro hvxy
    by_contra hnuxy
    have hne : x ≠ y := by
      rintro rfl
      exact v.irrefl _ hvxy
    have huyx : u.lt y x := (u.total hne).resolve_left hnuxy
    have hmem : (y, x) ∈ ((Finset.univ ×ˢ Finset.univ).filter
        fun p : Alt × Alt => u.lt p.1 p.2 ∧ v.lt p.2 p.1) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨huyx, hvxy⟩
    rw [hempty] at hmem
    simp at hmem

private theorem t12_bddBelow_range (P : Profile (Fin 3) (Fin 3)) :
    BddBelow (Set.range fun Q : {Q : Profile (Fin 3) (Fin 3) //
      IsCondorcetWinner Q (0 : Fin 3)} => profileDist P Q.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact Nat.zero_le _

private theorem t12_dodg_cyc : dodgsonScore cycP 0 = 1 := by
  simp only [dodgsonScore]
  apply le_antisymm
  · calc (⨅ Q : {Q : Profile (Fin 3) (Fin 3) // IsCondorcetWinner Q (0 : Fin 3)},
          profileDist cycP Q.1)
        ≤ profileDist cycP swapP :=
          ciInf_le (t12_bddBelow_range cycP) ⟨swapP, t12_cond_swapP⟩
      _ = 1 := t12_dist_swapP
  · have hne : Nonempty {Q : Profile (Fin 3) (Fin 3) //
        IsCondorcetWinner Q (0 : Fin 3)} := ⟨⟨swapP, t12_cond_swapP⟩⟩
    refine @le_ciInf _ _ _ hne _ _ (fun Q => ?_)
    show (1 : ℕ) ≤ profileDist cycP Q.1
    by_contra hcon
    have h0 : profileDist cycP Q.1 = 0 := Nat.lt_one_iff.mp (not_le.mp hcon)
    simp only [profileDist] at h0
    have hk : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        kendallTau (cycP i) (Q.1 i) = 0 :=
      Finset.sum_eq_zero_iff.mp h0
    have hnet : netPreference Q.1 0 2 = netPreference cycP 0 2 := by
      simp only [netPreference]
      have hf1 : Finset.univ.filter (fun i : Fin 3 => (Q.1 i).lt 0 2) =
          Finset.univ.filter (fun i : Fin 3 => (cycP i).lt 0 2) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (t12_kendallTau_agree _ _ (hk i (Finset.mem_univ i)) 0 2).symm
      have hf2 : Finset.univ.filter (fun i : Fin 3 => (Q.1 i).lt 2 0) =
          Finset.univ.filter (fun i : Fin 3 => (cycP i).lt 2 0) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (t12_kendallTau_agree _ _ (hk i (Finset.mem_univ i)) 2 0).symm
      rw [hf1, hf2]
    have hpos := Q.2 2 (by decide : (2 : Fin 3) ≠ (0 : Fin 3))
    rw [majorityPrefers_iff_netPreference_pos] at hpos
    rw [hnet, cycP_net02] at hpos
    exact absurd hpos (by decide)

private theorem t12_cond_unan : IsCondorcetWinner unanimousP 0 := by
  intro b hb
  fin_cases b
  · exact absurd rfl hb
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference unanimousP 0 1
    rw [unanimousP_net01]; decide
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference unanimousP 0 2
    rw [unanimousP_net02]; decide

private theorem t12_dist_unan : profileDist unanimousP unanimousP = 0 := by
  simp [profileDist, kendallTau_self]

private theorem t12_dodg_unan : dodgsonScore unanimousP 0 = 0 := by
  simp only [dodgsonScore]
  apply le_antisymm
  · calc (⨅ Q : {Q : Profile (Fin 3) (Fin 3) // IsCondorcetWinner Q (0 : Fin 3)},
          profileDist unanimousP Q.1)
        ≤ profileDist unanimousP unanimousP :=
          ciInf_le (t12_bddBelow_range unanimousP) ⟨unanimousP, t12_cond_unan⟩
      _ = 0 := t12_dist_unan
  · exact Nat.zero_le _

/-- Concrete maximin and Dodgson values: on the tie profile every
maximin score is negative (no Condorcet winner); on the cycle profile
`0` needs exactly one adjacent swap to become a Condorcet winner, and
on the unanimous profile its Dodgson score is `0`. -/
theorem t12_maximin_dodgson_checks :
    maximinScore tieP 0 = -1 ∧ maximinScore tieP 1 = -3 ∧
      maximinScore tieP 2 = -1 ∧ maximinScore tieP 3 = -1 ∧
      maximinScore cycP 0 = -1 ∧ dodgsonScore cycP 0 = 1 ∧
      dodgsonScore unanimousP 0 = 0 := by
  exact ⟨t12_max_tie0, t12_max_tie1, t12_max_tie2, t12_max_tie3, t12_max_cyc0,
    t12_dodg_cyc, t12_dodg_unan⟩
end
