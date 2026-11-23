/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ChowLiu

@[expose] public section

/-!
# Tests for Chow–Liu trees

* Non-vacuity of `DependenceForest`: the chain `X₀ → X₁ → X₂` and the empty forest.
* The empty forest has weight `0`, so its divergence is the multi-information
  `∑_i H(X_i) - H(X)`.
* Since mutual information is nonnegative, the chain approximates every joint law at least as well
  as the product of the marginals (`divergence_le_divergence_iff`).
* `P ≪ P_τ` and `∑ P_τ = 1` instantiated at a point mass.
-/

open MeasureTheory Real InformationTheory
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.ChowLiu

/-- The chain `X₀ → X₁ → X₂`. -/
def chain3 : DependenceForest (Fin 3) where
  parent i := if h : i.val = 0 then none else some ⟨i.val - 1, by omega⟩
  rank i := i.val
  rank_lt i j h := by
    split_ifs at h with h0
    cases h
    simp only
    omega

/-- The empty forest: the product of the marginals. -/
def empty (ι : Type*) : DependenceForest ι where
  parent _ := none
  rank _ := 0
  rank_lt _ _ h := by cases h

example : chain3.parent 2 = some 1 := rfl
example : chain3.parent 0 = none := rfl

theorem weight_empty {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p : PMF (∀ i, α i)) : (empty ι).weight p = 0 := by
  simp [DependenceForest.weight, empty]

/-- The product of the marginals is off by the multi-information. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (p : PMF (∀ i, α i)) :
    (empty ι).divergence p = ∑ i, shannonEntropy (p.map fun y ↦ y i) - shannonEntropy p := by
  rw [DependenceForest.divergence_eq, weight_empty, sub_zero]

theorem finiteMutualInformation_nonneg {α β : Type*} [Fintype α] [Fintype β] (p : PMF (α × β)) :
    0 ≤ finiteMutualInformation p :=
  ENNReal.toReal_nonneg

/-- The chain is at least as good as the product of the marginals, for every joint law. -/
example {α : Fin 3 → Type*} [∀ i, Fintype (α i)] (p : PMF (∀ i, α i)) :
    chain3.divergence p ≤ (empty (Fin 3)).divergence p := by
  rw [DependenceForest.divergence_le_divergence_iff, weight_empty]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  simp only [chain3]
  split_ifs
  · exact le_rfl
  · exact finiteMutualInformation_nonneg _

/-- The approximation charges every outcome the law charges (`P ≪ P_τ`), here at a point mass. -/
example (x : Fin 3 → Bool) : 0 < chain3.approx (PMF.pure x) x :=
  chain3.approx_pos _ (by simp)

/-- `P_τ` sums to one, so it is a probability law. -/
example (x : Fin 3 → Bool) : ∑ y, chain3.approx (PMF.pure x) y = 1 :=
  chain3.sum_approx _

end MathlibExtTest.InformationTheory.ChowLiu
