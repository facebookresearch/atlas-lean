/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A single exact short diagonal coefficient forces whole-vector fixation in the actual group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem real_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℝ) (i : ι) : (∑ j, X j * (Pi.single i 1 : ι → ℝ) j) = X i := by
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Pairing with an original unit short vector extracts exactly that physical short coordinate. -/
theorem monsterNortonForm_pureShort_right (x : GriessSpace) (r : GriessShortIndex) :
    griessForm x (monsterNortonPureShort r) = monsterNortonShortProjection x r := by
  rw [griessForm_eq_conwayRawForm, monsterNortonPureShort,
    griessConwayEncode_decode _ (by intro i j; rfl)]
  simp only [conwayRawForm, conwayMatrixForm, Matrix.mul_zero, Matrix.trace_zero,
    zero_add, map_zero, add_zero]
  rw [real_sum_single]
  rfl

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Form preservation and positive definiteness turn a maximal diagonal pairing into fixation. -/
theorem monsterNortonGenerated_fix_of_form_diagonal (g : G) (x : GriessSpace)
    (h : griessForm (g.val x) x = griessForm x x) : g.val x = x := by
  have hp := generated_group_preserves_griessForm g x x
  have hs := form_symm x (g.val x)
  have hz : griessForm (g.val x - x) (g.val x - x) = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hp, h, hs, h]
    ring
  exact sub_eq_zero.mp ((griessForm_self_eq_zero_iff _).mp hz)

/-- One exact diagonal short coefficient equal to one proves the entire unit is fixed. -/
theorem monsterNortonGenerated_short_fixed_of_diagonal (g : G) (r : GriessShortIndex)
    (h : monsterNortonShortProjection (g.val (monsterNortonPureShort r)) r = 1) :
    g.val (monsterNortonPureShort r) = monsterNortonPureShort r := by
  apply monsterNortonGenerated_fix_of_form_diagonal
  rw [monsterNortonForm_pureShort_right, h, monsterNortonForm_pureShort_right]
  change 1 = monsterNortonShortProjection (griessConwayDecode (0, (Pi.single r 1, 0))) r
  rw [monsterNortonShortProjection_short, Pi.single_eq_same]

private theorem generated_inverse_apply (g : G) (x : GriessSpace) :
    g.val ((g⁻¹).val x) = x := by
  change g.val (g.val.symm x) = x
  exact LinearEquiv.apply_symm_apply _ _

/-- The diagonal pairing of an actual square equals the pairing of its two half-word images. -/
theorem monsterNortonGenerated_square_form_halves (g : G) (x : GriessSpace) :
    griessForm ((g ^ 2).val x) x = griessForm (g.val x) ((g⁻¹).val x) := by
  have h := generated_group_preserves_griessForm g (g.val x) ((g⁻¹).val x)
  rw [generated_inverse_apply] at h
  rw [pow_two]
  change griessForm (g.val (g.val x)) x = _
  exact h

/-- An exact half-word pairing of one fixes the whole original short unit under the square. -/
theorem monsterNortonGenerated_square_short_fixed_of_halves (g : G) (r : GriessShortIndex)
    (h : griessForm (g.val (monsterNortonPureShort r))
      ((g⁻¹).val (monsterNortonPureShort r)) = 1) :
    (g ^ 2).val (monsterNortonPureShort r) = monsterNortonPureShort r := by
  apply monsterNortonGenerated_short_fixed_of_diagonal
  rw [← monsterNortonForm_pureShort_right, monsterNortonGenerated_square_form_halves, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
