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
        majorityPrefers cycP 0 b) = {1} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 0 0 ↔ (0 = 1)
        simp [majorityPrefers, netPreference_self]
      · show majorityPrefers cycP 0 1 ↔ (1 = 1)
        simp [majorityPrefers, hnet01]
      · show majorityPrefers cycP 0 2 ↔ (2 = 1)
        simp [majorityPrefers, hnet02]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        majorityPrefers cycP b 0) = {2} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 0 0 ↔ (0 = 2)
        simp [majorityPrefers, netPreference_self]
      · show majorityPrefers cycP 1 0 ↔ (1 = 2)
        simp [majorityPrefers, hnet10]
      · show majorityPrefers cycP 2 0 ↔ (2 = 2)
        simp [majorityPrefers, hnet20]
    rw [hwins, hloss]
    decide
  have hcop1 : copelandScore cycP 1 = 0 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 3 =>
        majorityPrefers cycP 1 b) = {2} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 1 0 ↔ (0 = 2)
        simp [majorityPrefers, hnet10]
      · show majorityPrefers cycP 1 1 ↔ (1 = 2)
        simp [majorityPrefers, netPreference_self]
      · show majorityPrefers cycP 1 2 ↔ (2 = 2)
        simp [majorityPrefers, hnet12]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        majorityPrefers cycP b 1) = {0} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 0 1 ↔ (0 = 0)
        simp [majorityPrefers, hnet01]
      · show majorityPrefers cycP 1 1 ↔ (1 = 0)
        simp [majorityPrefers, netPreference_self]
      · show majorityPrefers cycP 2 1 ↔ (2 = 0)
        simp [majorityPrefers, hnet21]
    rw [hwins, hloss]
    decide
  have hcop2 : copelandScore cycP 2 = 0 := by
    unfold copelandScore
    have hwins : (Finset.univ.filter fun b : Fin 3 =>
        majorityPrefers cycP 2 b) = {0} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 2 0 ↔ (0 = 0)
        simp [majorityPrefers, hnet20]
      · show majorityPrefers cycP 2 1 ↔ (1 = 0)
        simp [majorityPrefers, hnet21]
      · show majorityPrefers cycP 2 2 ↔ (2 = 0)
        simp [majorityPrefers, netPreference_self]
    have hloss : (Finset.univ.filter fun b : Fin 3 =>
        majorityPrefers cycP b 2) = {1} := by
      apply Finset.ext
      intro b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      fin_cases b
      · show majorityPrefers cycP 0 2 ↔ (0 = 1)
        simp [majorityPrefers, hnet02]
      · show majorityPrefers cycP 1 2 ↔ (1 = 1)
        simp [majorityPrefers, hnet12]
      · show majorityPrefers cycP 2 2 ↔ (2 = 1)
        simp [majorityPrefers, netPreference_self]
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
end
