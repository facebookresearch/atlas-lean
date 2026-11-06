/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact whole physical tensor-unit pairings for the remaining mixed sparse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQTensorBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualOrthogonal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine unscaled tensor coordinate unit at an actual spin index and physical column. -/
noncomputable def monsterNortonTensorUnit (t : SpinIndex) (i : Fin 24) : GriessSpace :=
  monsterNortonTensorLift (conwaySpinColumn (Pi.single t 1) i)

/-- The actual Griess form on pure tensors is the ordinary unscaled coordinate dot product. -/
theorem monsterNortonTensorLift_form (T U : SpinIndex → Fin 24 → ℝ) :
    griessForm (monsterNortonTensorLift T) (monsterNortonTensorLift U) =
      tensorColumnPairing T U := by
  change griessForm (generatedCentralMinusTensorEquiv.symm T).val
    (generatedCentralMinusTensorEquiv.symm U).val = _
  rw [generatedCentralMinus_griessForm_tensorPairing,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem scalar_delta_product {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (x y : ℝ) :
    (∑ i : I, (if i = a then x else 0) * (if i = b then y else 0)) =
      if a = b then x * y else 0 := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp only [mul_zero]

private theorem tensor_delta_pairing {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (a b : I) (i j : J) :
    (∑ t : I, ∑ k : J,
      (if k = i then (Pi.single a 1 : I → ℝ) t else 0) *
        (if k = j then (Pi.single b 1 : I → ℝ) t else 0)) =
      if a = b ∧ i = j then 1 else 0 := by
  simp_rw [scalar_delta_product]
  by_cases hij : i = j
  · simp only [hij, ite_true]
    simp only [Pi.single_apply, scalar_delta_product, one_mul, and_true]
  · simp only [hij, ite_false, Finset.sum_const_zero, and_false]

/-- Actual tensor units are orthonormal in their original physical spin coordinates. -/
theorem monsterNortonTensorUnit_gram (a b : SpinIndex) (i j : Fin 24) :
    griessForm (monsterNortonTensorUnit a i) (monsterNortonTensorUnit b j) =
      if a = b ∧ i = j then 1 else 0 := by
  rw [monsterNortonTensorUnit, monsterNortonTensorUnit, monsterNortonTensorLift_form]
  exact tensor_delta_pairing a b i j

/-- Every complete actual pure tensor is orthogonal to every original preferred short unit. -/
theorem monsterNortonTensorLift_short_form (T : SpinIndex → Fin 24 → ℝ)
    (r : GriessShortIndex) :
    griessForm (monsterNortonTensorLift T) (monsterNortonPureShort r) = 0 := by
  rw [monsterNortonForm_pureShort_right]
  change (griessConwayEncode (monsterNortonTensorLift T)).2.1 r = 0
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intros; rfl)]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
