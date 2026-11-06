/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesCountData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagFrameLinks

/-! Binding every permitted integer letter to its actual lattice isometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual physical letters: four permutation words, eleven code signs, and the normalized lift. -/
def generatedFourthFlagFramesCountGenerator (k : Fin 16) : leechIsomSubgroup :=
  if h : k.val < 4 then (generatedFourthMonomialFiber ⟨k.val, h⟩).val.2
  else if h' : k.val < 15 then
    golaySignIsometry (generatedFourthMonomialSignCode ⟨k.val - 4, by omega⟩)
  else generatedFourthFlagNormalizedLift.val.2

/-- All sixteen letters belong to the exact physical subgroup used in the flag argument. -/
theorem generatedFourthFlagFramesCount_generator_mem (k : Fin 16) :
    generatedFourthFlagFramesCountGenerator k ∈ generatedFourthPhysicalFlagGeneratorSubgroup := by
  unfold generatedFourthFlagFramesCountGenerator
  split_ifs with h h'
  · exact generatedFourthFlagGenerator_monomial_mem _
  · exact generatedFourthFlagGenerator_monomial_le
      (generatedFourth_monomial_sign_witness_mem _)
  · exact generatedFourthFlagGenerator_normalized_mem

/-- The displayed inverse coordinates equal the inverses of the actual permutation words. -/
theorem generatedFourthFlagFramesCount_inverse_actual (k : Fin 4) (i : Fin 24) :
    (generatedFourthMonomialPermutation k).val.symm i =
      generatedFourthFlagFramesCountInverse k i := by
  apply (generatedFourthMonomialPermutation k).val.injective
  rw [Equiv.apply_symm_apply, generatedFourth_monomial_images]
  exact (generatedFourthFlagFramesCount_inverse_certificate k i).symm

/-- The integer numerator of every letter is twice its genuine integral lattice action. -/
theorem generatedFourthFlagFramesCount_action_double (k : Fin 16) (u : leechIntegral) :
    (2 : ℤ) • (leechIntegralAction (generatedFourthFlagFramesCountGenerator k) u).val =
      generatedFourthFlagFramesCountStep k u.val := by
  unfold generatedFourthFlagFramesCountGenerator generatedFourthFlagFramesCountStep
  split_ifs with h h'
  · rw [generatedFourth_monomial_spatial, leechIntegralAction_golayPermutation]
    funext i
    change 2 * u.val ((generatedFourthMonomialPermutation _).val.symm i) = _
    rw [generatedFourthFlagFramesCount_inverse_actual]
  · rw [leechIntegralAction_golaySign]
    rfl
  · exact generatedFourth_flag_lift_integral_double u

/-- Evaluation of the recorded word in the actual physical isometry group. -/
def generatedFourthFlagFramesCountIsometry (j : Fin 63) : leechIsomSubgroup :=
  ((generatedFourthFlagFramesCountWord j).map generatedFourthFlagFramesCountGenerator).prod

/-- Every recorded word lies in the exact physical flag-generator subgroup. -/
theorem generatedFourthFlagFramesCount_isometry_mem (j : Fin 63) :
    generatedFourthFlagFramesCountIsometry j ∈ generatedFourthPhysicalFlagGeneratorSubgroup := by
  apply Subgroup.list_prod_mem
  intro e he
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
  exact generatedFourthFlagFramesCount_generator_mem k

/-- Noninitial actual word evaluations have exactly the recorded acyclic parent factorization. -/
theorem generatedFourthFlagFramesCount_isometry_parent (j : Fin 63) (hj : j ≠ 0) :
    generatedFourthFlagFramesCountIsometry j =
      generatedFourthFlagFramesCountGenerator (generatedFourthFlagFramesCountLetter j) *
        generatedFourthFlagFramesCountIsometry (generatedFourthFlagFramesCountParent j) := by
  simp only [generatedFourthFlagFramesCountIsometry,
    generatedFourthFlagFramesCount_word_certificate j hj, List.map_cons, List.prod_cons]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
