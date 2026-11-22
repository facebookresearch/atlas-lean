/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.FairDivision.Indivisible

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace MathlibExt.GameTheory.FairDivision.Indivisible

@[expose] public section

/-!
# Maximum Nash welfare and Pareto optimality

The refined maximum Nash welfare rule used here first maximises the
number of agents with positive value and, subject to that, the product
of those agents' values. The main theorem is that every such allocation
is Pareto optimal for additive nonnegative valuations.

## References

* I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah and J. Wang,
  "The unreasonable fairness of maximum Nash welfare", *ACM Transactions
  on Economics and Computation* 7(3), 2019.
-/

/-- Agents whose bundle has positive value under `A`. -/
noncomputable def positiveAgents {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι) : Finset ι :=
  Finset.univ.filter (fun i => 0 < value v A i)

/-- Product of the bundle values over the positive agents under `A`. -/
noncomputable def positiveWelfare {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι) : ℝ :=
  ∏ i ∈ positiveAgents v A, value v A i

/-- Maximum Nash welfare in the refined sense: the number of positive agents
is maximal, and subject to that, the product of the positive agents' values
is maximal. -/
def IsMaxNashWelfare {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : Prop :=
  ∀ B : γ → ι, (positiveAgents v B).card ≤ (positiveAgents v A).card ∧
    ((positiveAgents v B).card = (positiveAgents v A).card →
      positiveWelfare v B ≤ positiveWelfare v A)

/-- Membership in `positiveAgents` unfolds to positivity of the bundle value. -/
theorem mem_positiveAgents {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι) (i : ι) :
    i ∈ positiveAgents v A ↔ 0 < value v A i := by
  simp [positiveAgents]

/-- The product over the positive agents is positive, as a product of
positive bundle values. -/
theorem positiveWelfare_pos {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι) :
    0 < positiveWelfare v A := by
  unfold positiveWelfare
  apply Finset.prod_pos
  intro i hi
  exact (mem_positiveAgents v A i).mp hi

/-- When every agent has positive bundle value, the positive-agent product
is the full Nash welfare product. -/
theorem positiveWelfare_eq_nashWelfare {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι)
    (h : ∀ i, 0 < value v A i) :
    positiveWelfare v A = nashWelfare v A := by
  have hS : positiveAgents v A = Finset.univ := by
    ext i
    simp [mem_positiveAgents, h i]
  simp only [positiveWelfare, nashWelfare, hS]

/-- Existence of a maximum Nash welfare allocation: first maximise the number
of agents with positive value, then their value product. -/
theorem exists_isMaxNashWelfare {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ) :
    ∃ A : γ → ι, IsMaxNashWelfare v A := by
  classical
  have hne : (Finset.univ : Finset (γ → ι)).Nonempty :=
    ⟨fun _ => Classical.choice inferInstance, Finset.mem_univ _⟩
  obtain ⟨A₀, -, hmax₀⟩ := Finset.exists_max_image Finset.univ
    (fun A => (positiveAgents v A).card) hne
  set S : Finset (γ → ι) := Finset.univ.filter
    (fun A => (positiveAgents v A).card = (positiveAgents v A₀).card) with hS
  have hA₀S : A₀ ∈ S := by simp [hS]
  have hSne : S.Nonempty := ⟨A₀, hA₀S⟩
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image S (positiveWelfare v) hSne
  have hcardA : (positiveAgents v A).card = (positiveAgents v A₀).card := by
    simpa [hS] using hAS
  refine ⟨A, ?_⟩
  intro B
  constructor
  · rw [hcardA]
    exact hmax₀ B (Finset.mem_univ B)
  · intro heq
    have hBS : B ∈ S := by simp [hS, heq, hcardA]
    exact hmax B hBS

/-- Every maximum Nash welfare allocation is Pareto optimal. -/
theorem isParetoOptimal_of_isMaxNashWelfare {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    {A : γ → ι} (hA : IsMaxNashWelfare v A) :
    IsParetoOptimal v A := by
  intro hcon
  obtain ⟨B, hle, j, hlt⟩ := hcon
  have hnonneg : ∀ (C : γ → ι) (i : ι), 0 ≤ value v C i := by
    intro C i
    unfold value bundleValue
    exact Finset.sum_nonneg fun g _ => hv i g
  have hsub : positiveAgents v A ⊆ positiveAgents v B := by
    intro i hi
    simp only [mem_positiveAgents] at hi ⊢
    exact lt_of_lt_of_le hi (hle i)
  have hcardle : (positiveAgents v A).card ≤ (positiveAgents v B).card :=
    Finset.card_le_card hsub
  have hcardeq : (positiveAgents v B).card = (positiveAgents v A).card :=
    le_antisymm (hA B).1 hcardle
  have hseteq : positiveAgents v A = positiveAgents v B :=
    Finset.eq_of_subset_of_card_le hsub (hA B).1
  have hjB : j ∈ positiveAgents v B := by
    rw [mem_positiveAgents]
    exact lt_of_le_of_lt (hnonneg A j) hlt
  have hjA : j ∈ positiveAgents v A := by
    rw [hseteq]
    exact hjB
  have hpos : ∀ i ∈ positiveAgents v A, 0 < value v A i := by
    intro i hi
    exact (mem_positiveAgents v A i).mp hi
  have hprod : positiveWelfare v A < positiveWelfare v B := by
    unfold positiveWelfare
    rw [← hseteq]
    exact Finset.prod_lt_prod₀ hpos (fun i _ => hle i) ⟨j, hjA, hlt⟩
  exact (not_le_of_gt hprod) ((hA B).2 hcardeq)

end

end MathlibExt.GameTheory.FairDivision.Indivisible
