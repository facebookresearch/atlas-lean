/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseSources

/-! Every actual original sparse short source has its complete integer numerator over four. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every original nonzero preferred short source coefficient, including its full central phase. -/
def generatedAxisGlobalIntegerOddSourceCoefficient (k : Fin 3)
    (p : GeneratedAxisGlobalOddShortPacketIndex) : ℤ :=
  (if p.1 = 0 then 1 else -1) *
    (if (generatedAxisGlobalPairCoordinates p.2).1 = 0 ∨
      (generatedAxisGlobalPairCoordinates p.2).2 = 0 then -3 else 1) *
    generatedAxisGlobalIntSign (generatedAxisGlobalOddShortRootPhases
      (generatedAxisGlobalOddOtherSparseRoot k) (generatedAxisGlobalOddShortPacketNumber p))

/-- Every original preferred source coordinate, including every genuine zero outside its full support. -/
def generatedAxisGlobalIntegerOddSourceShort (k : Fin 3) (r : GriessShortIndex) : ℤ :=
  match generatedAxisGlobalOddOtherSparseSource k r with
  | none => 0
  | some p => generatedAxisGlobalIntegerOddSourceCoefficient k p

/-- Every integer numerator restores the entire original rational source coefficient. -/
theorem generatedAxisGlobalIntegerOddSourceShort_rat (k : Fin 3) (r : GriessShortIndex) :
    (generatedAxisGlobalIntegerOddSourceShort k r : ℚ) / 4 = generatedAxisGlobalOddOtherSparseShortQ k r := by
  unfold generatedAxisGlobalIntegerOddSourceShort generatedAxisGlobalOddOtherSparseShortQ
  cases generatedAxisGlobalOddOtherSparseSource k r with
  | none => simp
  | some p =>
    simp only [generatedAxisGlobalIntegerOddSourceCoefficient,
      generatedAxisGlobalOddOtherSparseCoefficient, generatedAxisGlobalOddShortCoefficientQ,
      Int.cast_mul, apply_ite, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
