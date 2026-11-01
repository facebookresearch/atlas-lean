/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.SufficientInputSubsets
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

/-!
# Sufficient input subsets tests

The prediction `g S = |S|` (count the unmasked features) is monotone, and every feature is a
greedy choice, so `R.min'` is a greedy rule. With threshold `2` on three features, the SIS found
from the full set has exactly two features. The prediction `g S = 1` for every `S` is sufficient
already when everything is masked (`τ ≤ g ∅`): the empty set is then a SIS, the degenerate case
that the paper excludes and `sisCollection` stops on.
-/

namespace Cslib.MachineLearning.SufficientInputSubsets

open Finset

private noncomputable def card3 : Finset (Fin 3) → ℝ := fun S => (S.card : ℝ)

private def minPick : (R : Finset (Fin 3)) → R.Nonempty → R := fun R h => ⟨R.min' h, R.min'_mem h⟩

private theorem card3_mono : Monotone card3 := fun S T h => by
  simp only [card3]; exact_mod_cast card_le_card h

private theorem minPick_greedy : IsGreedy card3 minPick := by
  intro R h i hi
  simp only [card3, card_erase_of_mem hi, card_erase_of_mem (minPick R h).2, le_refl]

/-- On three features with threshold `2`, the SIS has exactly two features. -/
example : ∃ S, findSIS card3 minPick 2 univ = some S ∧ S.card = 2 := by
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1
    (findSIS_isSome (g := card3) (pick := minPick) (τ := 2) (R := univ) (by norm_num [card3]))
  refine ⟨S, hS, le_antisymm ?_ ?_⟩
  · by_contra hlt
    have hlt : 2 < S.card := not_le.1 hlt
    obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq (s := S) (n := 2) hlt.le
    have hss : T ⊂ S := Finset.ssubset_iff_subset_ne.2 ⟨hTS, fun h => by subst h; omega⟩
    have := findSIS_minimal_of_monotone minPick_greedy card3_mono hS hss
    simp [card3, hT] at this
  · have := (findSIS_sufficient hS).2
    simp only [card3] at this
    exact_mod_cast this

/-- Proposition 1 on the example: removing a feature of the SIS drops below the threshold. -/
example {S : Finset (Fin 3)} (hS : findSIS card3 minPick 2 univ = some S) :
    ∀ s ∈ S, card3 (S.erase s) < 2 :=
  findSIS_erase_lt minPick_greedy hS

/-- Greedy rules exist for every prediction function. -/
example (g : Finset (Fin 3) → ℝ) : ∃ pick, IsGreedy g pick := exists_isGreedy g

/-- Degenerate case `τ ≤ g ∅`: the returned SIS may be empty (here it is). -/
example : findSIS (fun _ : Finset (Fin 3) => (1 : ℝ)) minPick 1 univ = some ∅ := by
  have hsome := findSIS_isSome (g := fun _ : Finset (Fin 3) => (1 : ℝ)) (pick := minPick)
    (τ := 1) (R := univ) le_rfl
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 hsome
  rw [hS]
  congr 1
  by_contra hne
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have := findSIS_erase_lt (τ := 1) (fun R h i hi => le_rfl) hS s hs
  simp at this

/-- Proposition 2 on the example: when the empty input is below the threshold, masking the
whole SIS-collection leaves the prediction below the threshold. -/
example : card3 (univ \ (sisCollection card3 minPick 2 univ).foldr (fun A B => A ∪ B) ∅) < 2 :=
  sisCollection_remaining_lt (by simp [card3]) univ

end Cslib.MachineLearning.SufficientInputSubsets
