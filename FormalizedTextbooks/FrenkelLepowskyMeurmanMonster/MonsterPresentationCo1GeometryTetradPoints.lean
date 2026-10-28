/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual first-tetrad Conway points and their exact two-valued sign action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTetradVectors

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual Xi-image of the genuine Conway base point. -/
def monsterCo1GeometryTetradPoint : MonsterCo1GeometryPoint :=
  (QuotientGroup.mk co1XiIsometry : Co1) • monsterCo1GeometryBasePoint

/-- This actual point is represented by the actual integral first-tetrad vector. -/
theorem monsterCo1GeometryTetradPoint_value : monsterCo1GeometryTetradPoint.val =
    leechHyperbolicCoordinates (leechReduction monsterCo1GeometryTetradVector) := by
  change co1BinaryAction (QuotientGroup.mk co1XiIsometry) monsterCo1GeometryBasePoint.val = _
  rw [monsterCo1GeometryBasePoint_value, monsterCo1GeometryClass_coordinates]
  rfl

/-- Every genuine codeword sign acts on this point by its literal first-tetrad parity. -/
theorem monsterCo1GeometryTetradPoint_sign (d : golayCode) :
    (monsterCo1GeometrySignClassHom (Multiplicative.ofAdd d) •
      monsterCo1GeometryTetradPoint).val = monsterCo1GeometryTetradPoint.val +
        monsterCo1GeometryTetradParity d • monsterCo1GeometryBasePoint.val := by
  change co1BinaryAction (monsterCo1GeometrySignClassHom (Multiplicative.ofAdd d))
    monsterCo1GeometryTetradPoint.val = _
  rw [monsterCo1GeometryTetradPoint_value, monsterCo1GeometrySignClass_value]
  change co1BinaryAction (QuotientGroup.mk (golaySignIsometry d))
    (leechHyperbolicCoordinates (leechReduction monsterCo1GeometryTetradVector)) = _
  rw [monsterCo1GeometryClass_coordinates]
  change leechHyperbolicCoordinates (leechReduction
    (leechIntegralAction (golaySignIsometry d) monsterCo1GeometryTetradVector)) = _
  rw [monsterCo1GeometryTetradVector_sign, map_add, map_add,
    monsterCo1GeometryTetradFrameChange_binary]

/-- This actual first-tetrad vector has norm eight. -/
theorem monsterCo1GeometryTetradVector_norm :
    leechSquareSum monsterCo1GeometryTetradVector.val = 64 := by
  rw [monsterCo1GeometryTetradVector, leechIntegralAction_squareSum]
  exact leechCoordinateFrameVector_square 0

/-- The actual Xi-image point is distinct from the genuine coordinate-frame base point. -/
theorem monsterCo1GeometryTetradPoint_ne_base :
    monsterCo1GeometryTetradPoint ≠ monsterCo1GeometryBasePoint := by
  intro h
  have hv := congrArg Subtype.val h
  rw [monsterCo1GeometryTetradPoint_value, monsterCo1GeometryBasePoint_value] at hv
  have hclass := leechHyperbolicCoordinates.injective hv
  let u : LeechNormEight := ⟨monsterCo1GeometryTetradVector, monsterCo1GeometryTetradVector_norm⟩
  have hu : u ∈ Set.range leechSignedFrame := by
    rw [← leechNormEight_frameClass_eq_signedFrame]
    exact hclass
  obtain ⟨t, ht⟩ := hu
  have he := congrArg (fun z : LeechNormEight => z.val.val (0 : Fin 24)) ht
  change (leechSignedFrame t).val.val 0 = monsterCo1GeometryTetradVector.val 0 at he
  rw [monsterCo1GeometryTetradVector_coordinates] at he
  simp only [Fin.val_zero, show (0 : ℕ) < 4 by omega, ite_true] at he
  by_cases hs : t.2 = 0 <;> by_cases hi : t.1 = 0
  all_goals simp [leechSignedFrame, hs, leechCoordinateFrameVector, hi] at he

/-- Some actual Golay codeword has odd parity in this literal tetrad. -/
theorem monsterCo1GeometryTetradParity_exists_one :
    ∃ d : golayCode, monsterCo1GeometryTetradParity d = 1 := by
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective
    (fun j : Fin 4 => Fin.castAdd 20 j) (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)) (Pi.single 0 1)
  refine ⟨d, ?_⟩
  unfold monsterCo1GeometryTetradParity
  change (∑ j : Fin 4, (fun j : Fin 4 => d.val (Fin.castAdd 20 j)) j) = 1
  change (fun j : Fin 4 => d.val (Fin.castAdd 20 j)) = Pi.single 0 1 at hd
  rw [hd]
  simp [Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
