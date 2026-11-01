/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source faithfulness of the exact standard Parker permutation phase p43549632. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinMonomial

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The cocycle difference defining a source standard Parker automorphism, Seysen (4.0.1). -/
def monsterNortonSingerThetaDifference (k : Fin 1) (a b : SpinIndex) : ZMod 2 :=
  spinDot (sourceCodeThetaPolynomial (monsterNortonSingerCode k a))
      (monsterNortonSingerCode k b) + spinDot (sourceCodeThetaPolynomial a) b

/-- The genuine coordinate permutation preserves the encoded triple-intersection character. -/
theorem monsterNortonSinger_intersection (k : Fin 1) (a b c : SpinIndex) :
    spinDot (golaySyndrome (fun i =>
      golayEncoder (monsterNortonSingerCode k a) i *
        golayEncoder (monsterNortonSingerCode k b) i)) (monsterNortonSingerCode k c) =
    spinDot (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i)) c := by
  simp only [golaySyndrome_spinDot, monsterNortonSingerCode_encoder]
  exact Equiv.sum_comp (monsterNortonSingerPermutation k).symm
    (fun i => golayEncoder a i * golayEncoder b i * golayEncoder c i)

/-- The cocycle difference is additive in its first argument because intersections agree. -/
theorem monsterNortonSingerThetaDifference_add_left
    (k : Fin 1) (a b c : SpinIndex) :
    monsterNortonSingerThetaDifference k (a + b) c =
      monsterNortonSingerThetaDifference k a c +
        monsterNortonSingerThetaDifference k b c := by
  unfold monsterNortonSingerThetaDifference
  rw [map_add, sourceCodeThetaPolynomial_add, sourceCodeThetaPolynomial_add]
  simp only [spinDot_add_left]
  rw [monsterNortonSinger_intersection]
  have hz := CharTwo.add_self_eq_zero
    (spinDot (golaySyndrome (fun i => golayEncoder a i * golayEncoder b i)) c)
  linear_combination hz

/-- Its second argument is additive by the actual dot-product and code linearity. -/
theorem monsterNortonSingerThetaDifference_add_right
    (k : Fin 1) (a b c : SpinIndex) :
    monsterNortonSingerThetaDifference k a (b + c) =
      monsterNortonSingerThetaDifference k a b +
        monsterNortonSingerThetaDifference k a c := by
  simp only [monsterNortonSingerThetaDifference, map_add, spinDot_add_right]
  abel

/-- The source cocycle difference as a genuine additive character in the first input. -/
def monsterNortonSingerThetaLeft (k : Fin 1) (b : SpinIndex) : SpinIndex →+ ZMod 2 where
  toFun a := monsterNortonSingerThetaDifference k a b
  map_zero' := by simp [monsterNortonSingerThetaDifference]
  map_add' a c := monsterNortonSingerThetaDifference_add_left k a c b

/-- The source cocycle difference as a genuine additive character in the second input. -/
def monsterNortonSingerThetaRight (k : Fin 1) (a : SpinIndex) : SpinIndex →+ ZMod 2 where
  toFun b := monsterNortonSingerThetaDifference k a b
  map_zero' := by simp [monsterNortonSingerThetaDifference]
  map_add' b c := monsterNortonSingerThetaDifference_add_right k a b c

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
