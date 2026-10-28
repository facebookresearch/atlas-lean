/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The second source permutation lift squares to the actual cocode 0x203.
Its physical permutation is an involution; its full Parker lift is not.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialSourceAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The second actual code equivalence is its own inverse. -/
theorem monsterSourcePermutationP1_code_symm :
    (monsterSourcePermutationCode 1).symm = monsterSourcePermutationCode 1 := by
  apply LinearEquiv.ext
  intro a
  rfl

/-- Its square fixes every actual binary code label. -/
theorem monsterSourcePermutationP1_code_square (a : SpinIndex) :
    monsterSourcePermutationCode 1 (monsterSourcePermutationCode 1 a) = a := by
  have h := (monsterSourcePermutationCode 1).apply_symm_apply a
  rw [monsterSourcePermutationP1_code_symm] at h
  exact h

/-- Applying this involutive coordinate permutation twice cancels the source theta difference. -/
theorem monsterSourcePermutationP1_difference (a b : SpinIndex) :
    monsterSourcePermutationThetaDifference 1 (monsterSourcePermutationCode 1 a)
      (monsterSourcePermutationCode 1 b) = monsterSourcePermutationThetaDifference 1 a b := by
  unfold monsterSourcePermutationThetaDifference
  rw [monsterSourcePermutationP1_code_square, monsterSourcePermutationP1_code_square]
  exact add_comm _ _

/-- The exact phase of the square is a genuine additive character. -/
def monsterSourcePermutationP1SquarePhase : SpinIndex →+ ZMod 2 where
  toFun a := monsterSourcePermutationPhase 1 a +
    monsterSourcePermutationPhase 1 (monsterSourcePermutationCode 1 a)
  map_zero' := by simp [monsterSourcePermutationPhase]
  map_add' a b := by
    rw [map_add, monsterSourcePermutationPhase_polarization,
      monsterSourcePermutationPhase_polarization, monsterSourcePermutationP1_difference]
    have hz := CharTwo.add_self_eq_zero (monsterSourcePermutationThetaDifference 1 a b)
    linear_combination hz

/-- Evaluation retains both exact source cochains in the square. -/
theorem monsterSourcePermutationP1SquarePhase_apply (a : SpinIndex) :
    monsterSourcePermutationP1SquarePhase a = monsterSourcePermutationPhase 1 a +
      monsterSourcePermutationPhase 1 (monsterSourcePermutationCode 1 a) := rfl

/-- Additivity over F₂ gives the actual linear character of the square. -/
def monsterSourcePermutationP1SquarePhaseLinear : SpinIndex →ₗ[ZMod 2] ZMod 2 where
  toFun := monsterSourcePermutationP1SquarePhase
  map_add' := monsterSourcePermutationP1SquarePhase.map_add
  map_smul' c a := by
    have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    obtain rfl | rfl := hc c <;> simp

/-- The concrete source cocode 0x203 as an actual binary character. -/
def monsterSourcePermutationP1SquareCocode : SpinIndex := golayLabelCoefficients 515

/-- Its dot product is an actual linear functional. -/
def monsterSourcePermutationP1SquareCocodeLinear : SpinIndex →ₗ[ZMod 2] ZMod 2 where
  toFun := spinDot monsterSourcePermutationP1SquareCocode
  map_add' a b := spinDot_add_right _ a b
  map_smul' c a := xiSpinDot_smul_right c _ a

/-- Evaluation of the actual square-phase linear functional. -/
theorem monsterSourcePermutationP1SquarePhaseLinear_apply (a : SpinIndex) :
    monsterSourcePermutationP1SquarePhaseLinear a = monsterSourcePermutationP1SquarePhase a := rfl

/-- Evaluation of the actual cocode linear functional. -/
theorem monsterSourcePermutationP1SquareCocodeLinear_apply (a : SpinIndex) :
    monsterSourcePermutationP1SquareCocodeLinear a =
      spinDot monsterSourcePermutationP1SquareCocode a := rfl

set_option maxHeartbeats 2000000 in
-- Check the twelve actual cochain values determining the square character.
/-- The source square phase has exactly the discovered cocode's twelve basis values. -/
theorem monsterSourcePermutationP1SquarePhase_basis : ∀ j : Fin 12,
    monsterSourcePermutationP1SquarePhase (Pi.single j 1) =
      spinDot monsterSourcePermutationP1SquareCocode (Pi.single j 1) := by
  decide +kernel

/-- Linear extension determines the full square character on all 4096 actual spin labels. -/
theorem monsterSourcePermutationP1SquarePhase_character (a : SpinIndex) :
    monsterSourcePermutationPhase 1 a +
      monsterSourcePermutationPhase 1 (monsterSourcePermutationCode 1 a) =
        spinDot monsterSourcePermutationP1SquareCocode a := by
  have h : monsterSourcePermutationP1SquarePhaseLinear =
      monsterSourcePermutationP1SquareCocodeLinear := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simpa only [Pi.basisFun_apply, monsterSourcePermutationP1SquarePhaseLinear_apply,
      monsterSourcePermutationP1SquareCocodeLinear_apply] using
        monsterSourcePermutationP1SquarePhase_basis j
  exact (monsterSourcePermutationP1SquarePhase_apply a).symm.trans
    ((monsterSourcePermutationP1SquarePhaseLinear_apply a).symm.trans
      ((LinearMap.congr_fun h a).trans
        (monsterSourcePermutationP1SquareCocodeLinear_apply a)))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
