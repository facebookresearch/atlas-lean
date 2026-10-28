/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source faithfulness of the two exact standard Parker permutation phases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinMonomial

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The cocycle difference defining a source standard Parker automorphism, Seysen (4.0.1). -/
def monsterSourcePermutationThetaDifference (k : Fin 2) (a b : SpinIndex) : ZMod 2 :=
  spinDot (sourceCodeThetaPolynomial (monsterSourcePermutationCode k a))
      (monsterSourcePermutationCode k b) + spinDot (sourceCodeThetaPolynomial a) b

/-- The genuine coordinate permutation preserves the encoded triple-intersection character. -/
theorem monsterSourcePermutation_intersection (k : Fin 2) (a b c : SpinIndex) :
    spinDot (golaySyndrome (fun i =>
      golayEncoder (monsterSourcePermutationCode k a) i *
        golayEncoder (monsterSourcePermutationCode k b) i)) (monsterSourcePermutationCode k c) =
    spinDot (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i)) c := by
  simp only [golaySyndrome_spinDot, monsterSourcePermutationCode_encoder]
  exact Equiv.sum_comp (omegaOrbitPermutation k).symm
    (fun i => golayEncoder a i * golayEncoder b i * golayEncoder c i)

/-- The cocycle difference is additive in its first argument because intersections agree. -/
theorem monsterSourcePermutationThetaDifference_add_left
    (k : Fin 2) (a b c : SpinIndex) :
    monsterSourcePermutationThetaDifference k (a + b) c =
      monsterSourcePermutationThetaDifference k a c +
        monsterSourcePermutationThetaDifference k b c := by
  unfold monsterSourcePermutationThetaDifference
  rw [map_add, sourceCodeThetaPolynomial_add, sourceCodeThetaPolynomial_add]
  simp only [spinDot_add_left]
  rw [monsterSourcePermutation_intersection]
  have hz := CharTwo.add_self_eq_zero
    (spinDot (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i)) c)
  linear_combination hz

/-- Its second argument is additive by the actual dot-product and code linearity. -/
theorem monsterSourcePermutationThetaDifference_add_right
    (k : Fin 2) (a b c : SpinIndex) :
    monsterSourcePermutationThetaDifference k a (b + c) =
      monsterSourcePermutationThetaDifference k a b +
        monsterSourcePermutationThetaDifference k a c := by
  simp only [monsterSourcePermutationThetaDifference, map_add, spinDot_add_right]
  abel

/-- The source cocycle difference as a genuine additive character in the first input. -/
def monsterSourcePermutationThetaLeft (k : Fin 2) (b : SpinIndex) : SpinIndex →+ ZMod 2 where
  toFun a := monsterSourcePermutationThetaDifference k a b
  map_zero' := by simp [monsterSourcePermutationThetaDifference]
  map_add' a c := monsterSourcePermutationThetaDifference_add_left k a c b

/-- The source cocycle difference as a genuine additive character in the second input. -/
def monsterSourcePermutationThetaRight (k : Fin 2) (a : SpinIndex) : SpinIndex →+ ZMod 2 where
  toFun b := monsterSourcePermutationThetaDifference k a b
  map_zero' := by simp [monsterSourcePermutationThetaDifference]
  map_add' b c := monsterSourcePermutationThetaDifference_add_right k a b c

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
