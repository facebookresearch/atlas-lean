/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual Q transport of physical spin-delta tensor columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQShortDiagonal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual spin operator takes a delta vector to its translated delta with the full phase. -/
theorem monsterNortonQ_spin_delta (q : Q) (u : SpinIndex) :
    spinOperator q (Pi.single u 1) =
      qSign (toAdd q.coeff + spinDot (spinModulation q) (u + spinTranslation q)) •
        (Pi.single (u + spinTranslation q) 1 : SpinSpace) := by
  have hz : spinTranslation q + spinTranslation q = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero _
  funext t
  have ht : t + spinTranslation q = u ↔ t = u + spinTranslation q := by
    constructor
    · intro h
      have hh := congrArg (fun a : SpinIndex => a + spinTranslation q) h
      simpa only [add_assoc, hz, add_zero] using hh
    · intro h
      rw [h, add_assoc, hz, add_zero]
  change qSign (toAdd q.coeff + spinDot (spinModulation q) t) *
    ((Pi.single u 1 : SpinSpace) (t + spinTranslation q)) = _
  by_cases he : t = u + spinTranslation q
  · subst t
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, ht, ite_true]
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, ht, he, ite_false, mul_zero]

/-- This translated delta is the whole actual Griess tensor image, including the central sign. -/
theorem monsterNortonQ_tensor_delta (q : Q) (u : SpinIndex) (j : Fin 24) :
    (qIntoGenerated q).val (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j)) =
      qSign (toAdd q.coeff + spinDot (spinModulation q) (u + spinTranslation q)) •
        monsterNortonTensorLift (conwaySpinColumn
          (Pi.single (u + spinTranslation q) 1) j) := by
  rw [monsterNortonQ_tensor_coordinates]
  have hp : (fun t i => spinOperator q
      (fun v => conwaySpinColumn (Pi.single u 1) j v i) t) =
        conwaySpinColumn (spinOperator q (Pi.single u 1)) j := by
    funext t i
    by_cases hi : i = j
    · subst i
      simp only [conwaySpinColumn, ite_true]
    · simp only [conwaySpinColumn, hi, ite_false]
      exact congrFun (map_zero (spinRepresentation q)) t
  rw [hp, monsterNortonQ_spin_delta]
  have hs (c : ℝ) (a : SpinSpace) : conwaySpinColumn (c • a) j =
      c • conwaySpinColumn a j := by
    funext t i
    by_cases hi : i = j <;> simp [conwaySpinColumn, hi]
  rw [hs, map_smul]

/-- The first physical tensor delta moves under literal Norton v to its true code translation. -/
theorem monsterNortonV_tensor_delta_zero (j : Fin 24) :
    y555NortonV.val (monsterNortonTensorLift (conwaySpinColumn (Pi.single 0 1) j)) =
      monsterNortonTensorLift (conwaySpinColumn
        (Pi.single (golayLabelCoefficients 1038) 1) j) := by
  have ht : spinTranslation y555NortonVQ = golayLabelCoefficients 1038 := by
    decide +kernel
  have hp : toAdd y555NortonVQ.coeff +
      spinDot (spinModulation y555NortonVQ) (spinTranslation y555NortonVQ) = 0 := by
    decide +kernel
  rw [y555NortonV, monsterNortonQ_tensor_delta, zero_add, hp, qSign_zero, one_smul, ht]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
