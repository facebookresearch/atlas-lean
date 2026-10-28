/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Centrality of the exact F21 word from the original C431/R source relations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7Consequences

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Nonadjacency of all seven literal F21 letters to the remaining e1 generator. -/
theorem y431F21_letters_nonadjacent :
    ∀ i ∈ ([0, 5, 1, 8, 6, 2, 7] : List (Fin 9)),
      ¬ y555Adjacent (y431Vertex i) (y431Vertex 4) := by decide +kernel

/-- A literal positive word commutes with any original vertex nonadjacent to all its letters. -/
theorem y431PositiveWord_commute (word : List (Fin 9)) (v : Fin 9)
    (h : ∀ i ∈ word, ¬ y555Adjacent (y431Vertex i) (y431Vertex v)) :
    Commute (y431PositiveWord word) (PresentedGroup.of v) := by
  induction word with
  | nil => exact Commute.one_left _
  | cons i word ih =>
    have hi : Commute (PresentedGroup.of i : Y431RPresentation) (PresentedGroup.of v) :=
      y431_generator_commute i v (h i (by simp))
    have ht := ih (fun j hj => h j (by simp [hj]))
    simpa only [y431PositiveWord, List.map_cons, List.prod_cons] using hi.mul_left ht

/-- The literal defining R relation makes F21 commute with the original d1 generator. -/
theorem y431F21_commute_d1 :
    Commute (PresentedGroup.mk y431Relations y431F21) (PresentedGroup.of 3) := by
  have h := PresentedGroup.one_of_mem (rels := y431Relations)
    (show y431R ∈ y431Relations from Or.inr (Or.inr rfl))
  have hr : PresentedGroup.mk y431Relations y431F21 * PresentedGroup.of 3 *
      (PresentedGroup.mk y431Relations y431F21)⁻¹ *
        (PresentedGroup.of 3 : Y431RPresentation)⁻¹ = 1 := by
    simpa only [y431R, map_mul, map_inv, PresentedGroup.of] using h
  have h1 := eq_of_mul_inv_eq_one hr
  have h2 := congrArg
    (fun x => x * PresentedGroup.mk y431Relations y431F21) h1
  change _ * _ = _ * _
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2

/-- Pure original Coxeter commutations make F21 commute with e1. -/
theorem y431F21_commute_e1 :
    Commute (PresentedGroup.mk y431Relations y431F21) (PresentedGroup.of 4) := by
  have h := (y431PositiveWord_commute [0, 5, 1, 8, 6, 2, 7] 4
    y431F21_letters_nonadjacent).pow_left 9
  have hv : y431PositiveWord [0, 5, 1, 8, 6, 2, 7] ^ 9 =
      PresentedGroup.mk y431Relations y431F21 := by
    simpa only [y431E7Positive21, y431PositiveWord_replicate] using y431E7Positive21_value
  rwa [hv] at h

/-- Every original C431 generator lies in the E7 subsystem or is d1 or e1. -/
theorem y431F21_vertex_coverage (v : Fin 9) :
    (∃ i : Fin 7, y431E7Vertex i = v) ∨ v = 3 ∨ v = 4 := by
  revert v
  decide +kernel

/-- F21 commutes with all nine actual original C431 generators, with R used only for d1. -/
theorem y431F21_generator_central (v : Fin 9) :
    Commute (PresentedGroup.mk y431Relations y431F21) (PresentedGroup.of v) := by
  rcases y431F21_vertex_coverage v with ⟨i, rfl⟩ | rfl | rfl
  · exact (y431F21_E7_central i).symm
  · exact y431F21_commute_d1
  · exact y431F21_commute_e1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
