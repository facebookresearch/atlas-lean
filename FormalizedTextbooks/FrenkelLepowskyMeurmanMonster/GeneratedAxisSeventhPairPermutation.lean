/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationPairLift

/-! Unsigned coordinate permutations carry both actual preferred pair families to the same pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem minus_class_index (i j : Fin 24) (h : i ≠ j) :
    griessShortClass (Sum.inl (0, griessPairIndex i j h)) =
      leechReduction (leechCocodeLift (Pi.single i 1 + Pi.single j 1)) := by
  rw [griessPairMinus_class, griessPairIndex_coordinates]
  split_ifs
  · rfl
  · simp only [add_comm]

private theorem integer_single (p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    golayIntegerPermute p (Pi.single i 1) = Pi.single (p i) 1 := by
  ext j
  simp only [golayIntegerPermute, Pi.single_apply]
  simp only [Equiv.symm_apply_eq]

/-- The actual short-label action on either signed pair family is its unsigned coordinate pair. -/
theorem generatedSeventh_unsigned_pair_permutation (p : golayAutomorphismSubgroup)
    (s : Fin 2) (i j : Fin 24) (h : i ≠ j) :
    griessShortPermutation (golayPermutationIsometry p)
      (Sum.inl (s, griessPairIndex i j h)) =
      Sum.inl (s, griessPairIndex (p.val i) (p.val j) (p.val.injective.ne h)) := by
  apply griessShortClass_injective
  rw [griessShortPermutation_class]
  have hminus : leechModTwoAction (golayPermutationIsometry p)
      (griessShortClass (Sum.inl (0, griessPairIndex i j h))) =
      griessShortClass (Sum.inl (0,
        griessPairIndex (p.val i) (p.val j) (p.val.injective.ne h))) := by
    rw [minus_class_index, minus_class_index]
    change leechReduction (leechIntegralAction (golayPermutationIsometry p)
      (leechCocodeLift (Pi.single i 1 + Pi.single j 1))) = _
    rw [generatedSeventh_permutation_cocode_lift]
    congr 2
    ext k
    change (Pi.single i 1 + Pi.single j 1 : Fin 24 → ℤ) (p.val.symm k) = _
    have hi := congrFun (integer_single p.val i) k
    have hj := congrFun (integer_single p.val j) k
    exact congrArg₂ HAdd.hAdd hi hj
  have homega : leechModTwoAction (golayPermutationIsometry p)
      (leechReduction (leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12)))) =
      leechReduction (leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12))) := by
    apply leechHyperbolicCoordinates.injective
    rw [← leechBinaryAction_coordinates, leechSourceFrameLift_hyperbolic,
      generatedSeventh_permutation_omega]
  fin_cases s
  · change leechModTwoAction (golayPermutationIsometry p)
      (griessShortClass (Sum.inl (0, griessPairIndex i j h))) = _
    exact hminus
  · change leechModTwoAction (golayPermutationIsometry p)
      (griessShortClass (Sum.inl (1, griessPairIndex i j h))) =
      griessShortClass (Sum.inl (1,
        griessPairIndex (p.val i) (p.val j) (p.val.injective.ne h)))
    rw [griessPairPlus_class, map_add, hminus, homega, griessPairPlus_class]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
