/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationDefinitions

/-! Actual octad-incidence invariants of the code14 and unordered-pair stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Successive actual point stabilizers inside the genuine word14 and pair stabilizer. -/
def generatedFourthPermutationPointStabilizer (k : ℕ) : Subgroup golayAutomorphismSubgroup where
  carrier := {p | p ∈ generatedFourthPermutationFlagStabilizer ∧
    ∀ j : Fin 7, j.val < k → p.val (golayBasePoints j) = golayBasePoints j}
  one_mem' := ⟨generatedFourthPermutationFlagStabilizer.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    intro p q hp hq
    refine ⟨generatedFourthPermutationFlagStabilizer.mul_mem hp.1 hq.1, ?_⟩
    intro j hj
    change p.val (q.val (golayBasePoints j)) = golayBasePoints j
    rw [hq.2 j hj, hp.2 j hj]
  inv_mem' := by
    intro p hp
    refine ⟨generatedFourthPermutationFlagStabilizer.inv_mem hp.1, ?_⟩
    intro j hj
    change p.val.symm (golayBasePoints j) = golayBasePoints j
    have h := congrArg p.val.symm (hp.2 j hj)
    simpa only [p.val.symm_apply_apply] using h.symm

/-- Pattern of an actual octad on the fixed prefix of the faithful seven-point base. -/
def generatedFourthPermutationBasePattern (k : ℕ) (d : Fin 4096) : ℕ :=
  ∑ j : Fin 7, if j.val < k then
    (golayEncoder (golayLabelCoefficients d) (golayBasePoints j)).val * 2 ^ j.val else 0

/-- Intersection size of an actual octad with the genuine code14 word. -/
def generatedFourthPermutationOctadOverlap (d : Fin 4096) : ℕ :=
  ∑ i : Fin 24, (golayEncoder (golayLabelCoefficients d) i).val *
    (golayEncoder (golayLabelCoefficients 14) i).val

/-- Intersection size of an actual octad with the unordered physical pair. -/
def generatedFourthPermutationPairOverlap (d : Fin 4096) : ℕ :=
  ∑ i : Fin 24, if i = 8 ∨ i = 11 then
    (golayEncoder (golayLabelCoefficients d) i).val else 0

/-- All three displayed quantities are invariant under the actual prefix stabilizer. -/
theorem generatedFourth_permutation_profile_invariant (k : ℕ)
    (p : golayAutomorphismSubgroup) (hp : p ∈ generatedFourthPermutationPointStabilizer k)
    (d : Fin 4096) :
    generatedFourthPermutationBasePattern k (golayLabelPermutation p d) =
        generatedFourthPermutationBasePattern k d ∧
      generatedFourthPermutationOctadOverlap (golayLabelPermutation p d) =
        generatedFourthPermutationOctadOverlap d ∧
      generatedFourthPermutationPairOverlap (golayLabelPermutation p d) =
        generatedFourthPermutationPairOverlap d := by
  have hc (i : Fin 24) :
      (golayEncoder (golayLabelCoefficients (golayLabelPermutation p d)) (p.val i)).val =
        (golayEncoder (golayLabelCoefficients d) i).val :=
    congrArg ZMod.val (golayLabelPermutation_coordinate p d i)
  have h14 (i : Fin 24) :
      (golayEncoder (golayLabelCoefficients 14) (p.val i)).val =
        (golayEncoder (golayLabelCoefficients 14) i).val := by
    have h := congrFun hp.1.1 (p.val i)
    change golayEncoder (golayLabelCoefficients 14) (p.val.symm (p.val i)) =
      golayEncoder (golayLabelCoefficients 14) (p.val i) at h
    rw [p.val.symm_apply_apply] at h
    exact congrArg ZMod.val h.symm
  constructor
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < k
    · simp only [hj, ite_true]
      have h := hc (golayBasePoints j)
      rw [hp.2 j hj] at h
      rw [h]
    · simp only [hj, ite_false]
  constructor
  · unfold generatedFourthPermutationOctadOverlap
    rw [← Equiv.sum_comp p.val]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, h14]
  · unfold generatedFourthPermutationPairOverlap
    rw [← Equiv.sum_comp p.val]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hp.1.2 i, hc]

/-- An actual octad-profile class, defined without numerical classification assumptions. -/
def generatedFourthPermutationProfileOctads (k pattern overlap pair : ℕ) : Finset (Fin 4096) :=
  golayOctads.filter (fun d => generatedFourthPermutationBasePattern k d = pattern ∧
    generatedFourthPermutationOctadOverlap d = overlap ∧
    generatedFourthPermutationPairOverlap d = pair)

/-- Count the genuine octads of one profile which contain a given physical coordinate. -/
def generatedFourthPermutationIncidence (k pattern overlap pair : ℕ) (i : Fin 24) : ℕ :=
  ((generatedFourthPermutationProfileOctads k pattern overlap pair).filter
    (fun d => golayEncoder (golayLabelCoefficients d) i = 1)).card

/-- The incidence counts are invariant under genuine actual stabilizer elements. -/
theorem generatedFourth_permutation_incidence_invariant (k : ℕ)
    (p : golayAutomorphismSubgroup) (hp : p ∈ generatedFourthPermutationPointStabilizer k)
    (pattern overlap pair : ℕ) (i : Fin 24) :
    generatedFourthPermutationIncidence k pattern overlap pair i =
      generatedFourthPermutationIncidence k pattern overlap pair (p.val i) := by
  apply Finset.card_equiv (golayLabelPermutation p)
  intro d
  have h := generatedFourth_permutation_profile_invariant k p hp d
  simp only [generatedFourthPermutationProfileOctads, Finset.mem_filter,
    golayLabelPermutation_octad, h.1, h.2.1, h.2.2, golayLabelPermutation_coordinate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
