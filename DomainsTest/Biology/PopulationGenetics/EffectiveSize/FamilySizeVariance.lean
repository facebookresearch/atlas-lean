/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.EffectiveSize.FamilySizeVariance

/-!
# Tests for the effective population size and the variance in family size

Small populations: equal contributions (`N_e = 2N - 1 > N`), contributions `(3, 1)` whose
variance `1 = 2 - 2/2` is the Wright–Fisher value (`N_e = N`), all gene copies from one parent
(`N_e = 1`), the single parent of `N = 1`, a contribution vector realised by a parent map, and
the Wright–Fisher expectations at `N = 1` and `N = 2`.
-/

open Domains.Biology.PopulationGenetics.EffectiveSize

namespace DomainsTest.Biology.PopulationGenetics.EffectiveSize.FamilySizeVariance

/-- Three parents with equal contributions: gene copies `2i` and `2i + 1` come from parent `i`. -/
def equalParent : Fin (2 * 3) → Fin 3 := fun c => ⟨c / 2, by omega⟩

/-- Two parents contributing `3` and `1` gametes. -/
def skewParent : Fin (2 * 2) → Fin 2 := fun c => if c.val = 3 then 1 else 0

/-- Two parents, all four gene copies from parent `0`. -/
def oneParent : Fin (2 * 2) → Fin 2 := fun _ => 0

-- Equal contributions give `V_n = 0` and `N_e = 2N - 1 = 5`, which exceeds `N = 3`.
example : contributionVariance equalParent = 0 ∧ familyEffectiveSize equalParent = 5 ∧
    (3 : ℝ) < familyEffectiveSize equalParent := by
  obtain ⟨-, h, -⟩ := effective_size_and_variance_in_family_size (N := 3) (by norm_num)
  obtain ⟨-, -, -, -, -, -, hiff, hzero, -⟩ := h equalParent
  have hV : contributionVariance equalParent = 0 := hiff.2 (by decide)
  obtain ⟨hNe, -, hgt⟩ := hzero hV
  refine ⟨hV, by rw [hNe]; norm_num, by exact_mod_cast hgt (by norm_num)⟩

-- Contributions `(3, 1)`: `V_n = 1 = 2 - 2/N`, `P = 1/2`, `N_e = N = 2`, and the two gene copies
-- are copies of the same parental gene with probability `1/4`.
example : contributionVariance skewParent = 1 ∧ sameParentProb skewParent = 1 / 2 ∧
    familyEffectiveSize skewParent = 2 ∧ sameParentalGeneProb skewParent = 1 / 4 := by
  obtain ⟨-, h, -⟩ := effective_size_and_variance_in_family_size (N := 2) (by norm_num)
  obtain ⟨-, -, hP, hgene, -, -, -, -, hWF⟩ := h skewParent
  have h0 : gameteContribution skewParent 0 = 3 := by decide
  have h1 : gameteContribution skewParent 1 = 1 := by decide
  have hV : contributionVariance skewParent = 1 := by
    simp only [contributionVariance, Fin.sum_univ_two, h0, h1]
    norm_num
  have hP' : sameParentProb skewParent = 1 / 2 := by
    rw [hP, hV]
    norm_num
  refine ⟨hV, hP', ?_, by rw [hgene, hP']; norm_num⟩
  rw [hWF (by rw [hV]; norm_num)]
  norm_num

-- All gene copies from one parent: `n = (4, 0)`, `V_n = 4`, `P = 1` and `N_e = 1`.
example : contributionVariance oneParent = 4 ∧ sameParentProb oneParent = 1 ∧
    familyEffectiveSize oneParent = 1 := by
  obtain ⟨-, h, -⟩ := effective_size_and_variance_in_family_size (N := 2) (by norm_num)
  obtain ⟨hsum, -, -, -, -, hNe, -⟩ := h oneParent
  have h0 : gameteContribution oneParent 0 = 4 := by decide
  have h1 : gameteContribution oneParent 1 = 0 := by decide
  have hV : contributionVariance oneParent = 4 := by
    simp only [contributionVariance, Fin.sum_univ_two, h0, h1]
    norm_num
  refine ⟨hV, ?_, by rw [hNe, hV]; norm_num⟩
  rw [hsum, Fin.sum_univ_two, h0, h1]
  norm_num

-- A single parent (`N = 1`) contributes both gene copies: `V_n = 0` and `N_e = 2N - 1 = N = 1`.
example (parent : Fin (2 * 1) → Fin 1) :
    contributionVariance parent = 0 ∧ familyEffectiveSize parent = 1 := by
  obtain ⟨-, h, -⟩ := effective_size_and_variance_in_family_size (N := 1) (by norm_num)
  obtain ⟨-, -, -, -, -, -, hiff, hzero, -⟩ := h parent
  have hV : contributionVariance parent = 0 :=
    hiff.2 fun i => by
      rw [gameteContribution, Subsingleton.elim i 0, Finset.filter_true_of_mem fun c _ =>
        Subsingleton.elim _ _]
      rfl
  refine ⟨hV, ?_⟩
  rw [(hzero hV).1]
  norm_num

-- The contribution vector `(3, 1)` sums to `2N = 4`, so some parent map realises it.
example : ∃ parent : Fin (2 * 2) → Fin 2, gameteContribution parent = ![3, 1] :=
  ((effective_size_and_variance_in_family_size (N := 2) (by norm_num)).1 ![3, 1]).1 (by decide)

-- A contribution vector summing to `5 ≠ 4` is realised by no parent map.
example : ¬ ∃ parent : Fin (2 * 2) → Fin 2, gameteContribution parent = ![4, 1] := by
  rw [← (effective_size_and_variance_in_family_size (N := 2) (by norm_num)).1 ![4, 1]]
  decide

-- Wright–Fisher expectations at `N = 2`: `E[V_n] = 1` and `E[P] = 1/2`.
example :
    ∫ parent, contributionVariance parent
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (2 * 2) → Fin 2))) = 1 ∧
      ∫ parent, sameParentProb parent
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (2 * 2) → Fin 2))) = 1 / 2 := by
  obtain ⟨-, -, hV, hP⟩ := effective_size_and_variance_in_family_size (N := 2) (by norm_num)
  refine ⟨by rw [hV]; norm_num, by rw [hP]; norm_num⟩

-- At `N = 1` the Wright–Fisher expectations are `E[V_n] = 0` and `E[P] = 1`.
example :
    ∫ parent, contributionVariance parent
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (2 * 1) → Fin 1))) = 0 ∧
      ∫ parent, sameParentProb parent
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (2 * 1) → Fin 1))) = 1 := by
  obtain ⟨-, -, hV, hP⟩ := effective_size_and_variance_in_family_size (N := 1) (by norm_num)
  refine ⟨by rw [hV]; norm_num, by rw [hP]; norm_num⟩

end DomainsTest.Biology.PopulationGenetics.EffectiveSize.FamilySizeVariance
