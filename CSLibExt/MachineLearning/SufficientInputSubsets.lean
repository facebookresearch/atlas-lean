/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Monotone.Basic

/-!
# Sufficient input subsets (SIS)

Carter, Mueller, Jain and Gifford explain a decision `f x ≥ τ` of a black-box model by a
*sufficient input subset*: a small set `S` of features whose values alone keep `f ≥ τ` when
all other features are masked. Here the features form a finite type `ι` and the model on the
masked input is a set function `g : Finset ι → ℝ` (`g S = f(x_S)`, the prediction when the
features outside `S` are replaced by the mask, e.g. their mean).

* `BackSelect` (backward selection) repeatedly masks the remaining feature whose masking keeps
  `g` largest. `chain g pick R` is the list of the nested remaining sets `R = R₀ ⊋ R₁ ⊋ ⋯ ⊋ ∅`;
  the choice function `pick` is any greedy tie-breaking rule (`IsGreedy`).
* `FindSIS` un-masks features in reverse order of masking and returns the first set with
  `g ≥ τ`. Since the reverse of `chain` lists exactly these sets, `findSIS` is
  `(chain g pick R).reverse.find? (τ ≤ g ·)`.
* `SIScollection` repeats on the features not yet in a returned SIS.

## Main results

* `findSIS_isSome`: if `τ ≤ g R`, a SIS is found; `findSIS_sufficient`: it is a subset of `R`
  with `τ ≤ g S` (criterion (1) of the paper).
* `findSIS_erase_lt` and `findSIS_card_le`: **Proposition 1** of the paper: no feature of the
  SIS can be additionally masked while keeping `g ≥ τ`, and the SIS has the smallest cardinality
  among the sufficient sets met during backward selection.
* `findSIS_minimal_of_monotone`: if `g` is monotone (masking more features never raises the
  prediction), no proper subset of the SIS is sufficient, so the SIS is inclusion-minimal. This
  corollary is derived here; the paper states only the approximate minimality of Proposition 1.
* `sisCollection_sufficient`, `sisCollection_pairwiseDisjoint`, and
  `sisCollection_remaining_lt`: the SIS-collection consists of disjoint sufficient subsets and,
  when `g ∅ < τ`, masking all of them leaves `g < τ` (**Proposition 2**).

## References

* B. Carter, J. Mueller, S. Jain and D. Gifford, "What made you do this? Understanding
  black-box decisions with sufficient input subsets", *Proceedings of the 22nd International
  Conference on Artificial Intelligence and Statistics (AISTATS)*, PMLR 89 (2019).
-/

@[expose] public section

namespace Cslib.MachineLearning.SufficientInputSubsets

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- `pick` is a greedy backward-selection rule for `g`: from a nonempty remaining set `R` it
masks a feature `i ∈ R` maximizing `g (R.erase i)`. -/
def IsGreedy (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R) : Prop :=
  ∀ (R : Finset ι) (h : R.Nonempty), ∀ i ∈ R, g (R.erase i) ≤ g (R.erase (pick R h))

/-- Greedy rules exist for every `g`. -/
theorem exists_isGreedy (g : Finset ι → ℝ) :
    ∃ pick : (R : Finset ι) → R.Nonempty → R, IsGreedy g pick := by
  choose f hf using fun (R : Finset ι) (h : R.Nonempty) =>
    R.exists_max_image (fun i => g (R.erase i)) h
  exact ⟨fun R h => ⟨f R h, (hf R h).1⟩, fun R h i hi => (hf R h).2 i hi⟩

/-- Backward selection: the list of remaining sets `R₀ = R, R₁, …, ∅`, where `R_{t+1}` is
`R_t` with the feature chosen by `pick` masked. -/
def chain (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R) (R : Finset ι) :
    List (Finset ι) :=
  if h : R.Nonempty then R :: chain g pick (R.erase (pick R h)) else [R]
termination_by R.card
decreasing_by exact card_erase_lt_of_mem (pick R h).2

/-- `FindSIS`: un-mask features in reverse order of masking (start from `∅`) and return the
first set on which the prediction reaches the threshold, or `none`. The paper's procedure does
not test `∅` itself; the two agree whenever `g ∅ < τ`, the case the paper considers. -/
noncomputable def findSIS (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R) (τ : ℝ)
    (R : Finset ι) : Option (Finset ι) :=
  (chain g pick R).reverse.find? fun S => decide (τ ≤ g S)

variable {g : Finset ι → ℝ} {pick : (R : Finset ι) → R.Nonempty → R} {τ : ℝ}

/-- Unfolding `chain` at a nonempty set. -/
theorem chain_of_nonempty (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R)
    {R : Finset ι} (h : R.Nonempty) :
    chain g pick R = R :: chain g pick (R.erase (pick R h)) := by
  rw [chain]; simp [h]

/-- Unfolding `chain` at the empty set (the chain stops). -/
theorem chain_of_not_nonempty (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R)
    {R : Finset ι} (h : ¬R.Nonempty) : chain g pick R = [R] := by
  rw [chain]; simp [h]

/-- Every set in the backward-selection chain is a subset of the starting set. -/
theorem subset_of_mem_chain {R S : Finset ι} (h : S ∈ chain g pick R) : S ⊆ R := by
  induction R using Finset.strongInduction generalizing S with
  | H R ih =>
    by_cases hR : R.Nonempty
    · rw [chain_of_nonempty g pick hR, List.mem_cons] at h
      rcases h with rfl | h
      · exact subset_rfl
      · exact (ih _ (erase_ssubset (pick R hR).2) h).trans (erase_subset _ _)
    · rw [chain_of_not_nonempty g pick hR, List.mem_singleton] at h
      exact h ▸ subset_rfl

/-- The starting set is the first set of the chain. -/
theorem mem_chain_self (R : Finset ι) : R ∈ chain g pick R := by
  by_cases hR : R.Nonempty
  · rw [chain_of_nonempty g pick hR]; exact List.mem_cons_self
  · rw [chain_of_not_nonempty g pick hR]; exact List.mem_singleton_self _

/-- Key invariant of the chain: if a set `S` of the chain has no sufficient set strictly after
it, then removing any one feature from `S` makes it insufficient. -/
private theorem erase_lt_of_mem_chain (hpick : IsGreedy g pick) {R S : Finset ι}
    (hS : S ∈ chain g pick R)
    (hafter : ∀ T ∈ chain g pick R, T ⊂ S → g T < τ) :
    ∀ s ∈ S, g (S.erase s) < τ := by
  induction R using Finset.strongInduction generalizing S with
  | H R ih =>
    by_cases hR : R.Nonempty
    · rw [chain_of_nonempty g pick hR, List.mem_cons] at hS
      have hsub : ∀ T ∈ chain g pick (R.erase (pick R hR)), T ∈ chain g pick R := by
        intro T hT; rw [chain_of_nonempty g pick hR]; exact List.mem_cons_of_mem _ hT
      rcases hS with rfl | hS
      · intro s hs
        have hnext : g (S.erase (pick S hR)) < τ :=
          hafter _ (hsub _ (mem_chain_self _)) (erase_ssubset (pick S hR).2)
        exact ((hpick : ∀ (R : Finset ι) (h : R.Nonempty), ∀ i ∈ R, g (R.erase i) ≤
          g (R.erase (pick R h))) S hR s hs).trans_lt hnext
      · exact ih _ (erase_ssubset (pick R hR).2) hS fun T hT hTS => hafter T (hsub T hT) hTS
    · rw [chain_of_not_nonempty g pick hR, List.mem_singleton] at hS
      subst hS
      intro s hs
      exact absurd ⟨s, hs⟩ hR

/-- The sets of the chain are strictly decreasing: a set later in the chain is a strict subset
of an earlier one. Stated as: in `chain g pick R`, every set other than the head is a strict
subset of `R`. -/
private theorem ssubset_of_mem_chain_tail {R T : Finset ι} (hR : R.Nonempty)
    (hT : T ∈ chain g pick (R.erase (pick R hR))) : T ⊂ R :=
  lt_of_le_of_lt (subset_of_mem_chain hT) (erase_ssubset (pick R hR).2)

/-- The chain is strictly decreasing for inclusion. -/
private theorem chain_pairwise (R : Finset ι) :
    (chain g pick R).Pairwise (fun A B => B ⊂ A) := by
  induction R using Finset.strongInduction with
  | H R ih =>
    by_cases hR : R.Nonempty
    · rw [chain_of_nonempty g pick hR, List.pairwise_cons]
      exact ⟨fun T hT => ssubset_of_mem_chain_tail hR hT,
        ih _ (erase_ssubset (pick R hR).2)⟩
    · rw [chain_of_not_nonempty g pick hR]; exact List.pairwise_singleton _ _

/-- The chain is ordered by strict inclusion: of two distinct members, one is a strict subset
of the other. -/
private theorem chain_total {R S T : Finset ι} (hS : S ∈ chain g pick R)
    (hT : T ∈ chain g pick R) : S = T ∨ S ⊂ T ∨ T ⊂ S := by
  induction R using Finset.strongInduction generalizing S T with
  | H R ih =>
    by_cases hR : R.Nonempty
    · rw [chain_of_nonempty g pick hR, List.mem_cons] at hS hT
      rcases hS with rfl | hS <;> rcases hT with rfl | hT
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (ssubset_of_mem_chain_tail hR hT))
      · exact Or.inr (Or.inl (ssubset_of_mem_chain_tail hR hS))
      · exact ih _ (erase_ssubset (pick R hR).2) hS hT
    · rw [chain_of_not_nonempty g pick hR, List.mem_singleton] at hS hT
      exact Or.inl (hS.trans hT.symm)

/-- The SIS returned by `findSIS`, if any, is a member of the chain with `τ ≤ g S`, and every
strictly smaller member of the chain is insufficient. -/
private theorem findSIS_spec {R S : Finset ι} (h : findSIS g pick τ R = some S) :
    S ∈ chain g pick R ∧ τ ≤ g S ∧ ∀ T ∈ chain g pick R, T ⊂ S → g T < τ := by
  have hp : (chain g pick R).Pairwise (fun A B => B ⊂ A) := chain_pairwise R
  rw [findSIS, List.find?_eq_some_iff_append] at h
  obtain ⟨hτ, as, bs, hl, has⟩ := h
  have hmem : S ∈ chain g pick R := by
    rw [← List.mem_reverse, hl]; simp
  refine ⟨hmem, by simpa using hτ, fun T hT hTS => ?_⟩
  have hpr : (as ++ S :: bs).Pairwise (fun A B => A ⊂ B) := by
    rw [← hl, List.pairwise_reverse]; exact hp
  have hTr : T ∈ as ++ S :: bs := by
    rw [← hl, List.mem_reverse]; exact hT
  rcases List.mem_append.1 hTr with hTa | hTb
  · simpa using has T hTa
  · rcases List.mem_cons.1 hTb with rfl | hTb
    · exact absurd hTS (lt_irrefl _)
    · rw [List.pairwise_append, List.pairwise_cons] at hpr
      exact absurd (hpr.2.1.1 T hTb) (asymm hTS)

/-- If the prediction on the starting set reaches the threshold, `findSIS` returns a set. -/
theorem findSIS_isSome {R : Finset ι} (hR : τ ≤ g R) : (findSIS g pick τ R).isSome := by
  rw [findSIS, List.find?_isSome]
  exact ⟨R, List.mem_reverse.2 (mem_chain_self R), by simpa using hR⟩

/-- Criterion (1): the returned SIS is a subset of the starting features and is sufficient. -/
theorem findSIS_sufficient {R S : Finset ι} (h : findSIS g pick τ R = some S) :
    S ⊆ R ∧ τ ≤ g S :=
  ⟨subset_of_mem_chain (findSIS_spec h).1, (findSIS_spec h).2.1⟩

/-- **Proposition 1 (first part)** of Carter et al.: no feature of the returned SIS can be
additionally masked while keeping the prediction at or above the threshold. -/
theorem findSIS_erase_lt (hpick : IsGreedy g pick) {R S : Finset ι}
    (h : findSIS g pick τ R = some S) : ∀ s ∈ S, g (S.erase s) < τ :=
  erase_lt_of_mem_chain hpick (findSIS_spec h).1 (findSIS_spec h).2.2

/-- **Proposition 1 (second part)** of Carter et al.: among the sets met during backward
selection, the returned SIS has the smallest cardinality among the sufficient ones. -/
theorem findSIS_card_le {R S T : Finset ι} (h : findSIS g pick τ R = some S)
    (hT : T ∈ chain g pick R) (hTτ : τ ≤ g T) : S.card ≤ T.card := by
  obtain ⟨hS, -, hmin⟩ := findSIS_spec h
  rcases chain_total hS hT with rfl | hST | hTS
  · exact le_rfl
  · exact (card_lt_card hST).le
  · exact absurd hTτ (not_le.2 (hmin T hT hTS))

/-- For a monotone set function (masking more features never raises the prediction), the
returned SIS is inclusion-minimal: no proper subset is sufficient. (Derived; the paper states
only Proposition 1.) -/
theorem findSIS_minimal_of_monotone (hpick : IsGreedy g pick) (hg : Monotone g)
    {R S : Finset ι} (h : findSIS g pick τ R = some S) {T : Finset ι} (hT : T ⊂ S) :
    g T < τ := by
  obtain ⟨s, hsS, hsT⟩ := exists_of_ssubset hT
  exact (hg (subset_erase.2 ⟨hT.subset, hsT⟩)).trans_lt (findSIS_erase_lt hpick h s hsS)

/-- `SIScollection`: while the remaining features `R` are sufficient (`τ ≤ g R`), find a SIS
among them, record it and mask it. Stops if `findSIS` returns an empty set (only possible
when `τ ≤ g ∅`). -/
noncomputable def sisCollection (g : Finset ι → ℝ) (pick : (R : Finset ι) → R.Nonempty → R)
    (τ : ℝ) (R : Finset ι) : List (Finset ι) :=
  if τ ≤ g R then
    match hS : findSIS g pick τ R with
    | some S =>
        if hne : S.Nonempty then
          have _ : (R \ S).card < R.card :=
            card_lt_card (sdiff_ssubset (findSIS_sufficient hS).1 hne)
          S :: sisCollection g pick τ (R \ S)
        else []
    | none => []
  else []
termination_by R.card
decreasing_by assumption

/-- Every set of the SIS-collection is a nonempty sufficient subset of the starting features. -/
theorem sisCollection_sufficient {R S : Finset ι} (h : S ∈ sisCollection g pick τ R) :
    S.Nonempty ∧ S ⊆ R ∧ τ ≤ g S := by
  induction R using Finset.strongInduction with
  | H R ih =>
    rw [sisCollection] at h
    split_ifs at h with hR
    · split at h
      next S' hS' =>
        split_ifs at h with hne
        · rcases List.mem_cons.1 h with rfl | h
          · exact ⟨hne, findSIS_sufficient hS'⟩
          · obtain ⟨h1, h2, h3⟩ := ih _ (sdiff_ssubset (findSIS_sufficient hS').1 hne) h
            exact ⟨h1, h2.trans sdiff_subset, h3⟩
        · simp at h
      next => simp at h
    · simp at h

/-- The sets of the SIS-collection are pairwise disjoint. -/
theorem sisCollection_pairwiseDisjoint (R : Finset ι) :
    (sisCollection g pick τ R).Pairwise Disjoint := by
  induction R using Finset.strongInduction with
  | H R ih =>
    rw [sisCollection]
    split_ifs with hR
    · split
      next S' hS' =>
        split_ifs with hne
        · rw [List.pairwise_cons]
          exact ⟨fun T hT => disjoint_sdiff.mono_right (sisCollection_sufficient hT).2.1,
            ih _ (sdiff_ssubset (findSIS_sufficient hS').1 hne)⟩
        · exact List.Pairwise.nil
      next => exact List.Pairwise.nil
    · exact List.Pairwise.nil

/-- **Proposition 2** of Carter et al.: if the fully masked input is below the threshold,
masking every set of the SIS-collection leaves the prediction below the threshold. -/
theorem sisCollection_remaining_lt (hempty : g ∅ < τ) (R : Finset ι) :
    g (R \ (sisCollection g pick τ R).foldr (fun A B => A ∪ B) ∅) < τ := by
  induction R using Finset.strongInduction with
  | H R ih =>
    rw [sisCollection]
    split_ifs with hR
    · split
      next S' hS' =>
        have hne : S'.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          exact absurd (findSIS_sufficient hS').2 (not_le.2 hempty)
        simp only [hne, ↓reduceDIte, List.foldr_cons]
        rw [show ∀ A B C : Finset ι, A \ (B ∪ C) = (A \ B) \ C from fun A B C => by
          ext; simp only [mem_sdiff, mem_union]; tauto]
        exact ih _ (sdiff_ssubset (findSIS_sufficient hS').1 hne)
      next hS' =>
        have := findSIS_isSome (g := g) (pick := pick) hR
        rw [hS'] at this
        exact absurd this (by simp)
    · simpa using not_le.1 hR

end Cslib.MachineLearning.SufficientInputSubsets
