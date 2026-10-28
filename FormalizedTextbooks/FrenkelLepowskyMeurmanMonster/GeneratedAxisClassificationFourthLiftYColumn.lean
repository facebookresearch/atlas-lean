/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftYPhaseFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Square
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerTensor

/-! The genuine involutive orthogonal y82 operator has a four-coordinate column expansion. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Orthogonality and the proved square relation make the actual y82 matrix symmetric. -/
theorem generatedFourth_lift_y_symmetric (v t : SpinIndex) :
    monsterSourceY82Spin.val (Pi.single v 1) t =
      monsterSourceY82Spin.val (Pi.single t 1) v := by
  classical
  have hs : ∀ f : SpinSpace, monsterSourceY82Spin.val (monsterSourceY82Spin.val f) = f := by
    intro f
    have h := congrArg (fun g : SpinHolomorph => g.val f) monsterSourceY82Spin_square
    rw [pow_two] at h
    change monsterSourceY82Spin.val (monsterSourceY82Spin.val f) = f at h
    exact h
  have h := monsterSourceY82Spin.property.2 (Pi.single v 1)
    (monsterSourceY82Spin.val (Pi.single t 1))
  rw [hs] at h
  simpa only [spinPairing, Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- Four addresses in a row of the unchanged original source operator. -/
def generatedFourthLiftYRowAddress (v : SpinIndex) : Fin 4 → SpinIndex :=
  ![generatedFourthLiftYAddress v,
    monsterSpinOmegaFlip (generatedFourthLiftYAddress v),
    generatedFourthLiftYAddress (monsterSpinOmegaFlip v),
    monsterSpinOmegaFlip (generatedFourthLiftYAddress (monsterSpinOmegaFlip v))]

/-- The complete original signed integer coefficient at each row address. -/
def generatedFourthLiftYRowCoefficient (v : SpinIndex) : Fin 4 → ℤ :=
  ![generatedFourthLiftIntSign (v 11) *
      generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast v) *
      generatedFourthLiftIntSign ((generatedFourthLiftYAddress v) 11),
    generatedFourthLiftIntSign (v 11) *
      generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast v),
    generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast (monsterSpinOmegaFlip v)) *
      generatedFourthLiftIntSign ((generatedFourthLiftYAddress (monsterSpinOmegaFlip v)) 11),
    generatedFourthLiftIntSign (generatedFourthLiftYPhaseFast (monsterSpinOmegaFlip v))]

/-- The four row terms agree with the actual source operator for every real state. -/
theorem generatedFourth_lift_y_row (f : SpinSpace) (v : SpinIndex) :
    monsterSourceY82Spin.val f v =
      (∑ s : Fin 4, (generatedFourthLiftYRowCoefficient v s : ℝ) *
        f (generatedFourthLiftYRowAddress v s)) / 2 := by
  rw [generatedFourth_lift_y_numerator]
  simp only [generatedFourthLiftYRowCoefficient, generatedFourthLiftYRowAddress,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Int.cast_mul, generatedFourth_lift_int_sign_real,
    ← generatedFourth_lift_y_phase_fast]
  unfold generatedFourthLiftYNumerator
  ring

/-- A coordinate unit has the same four exact terms, now interpreted as a column. -/
theorem generatedFourth_lift_y_column (v : SpinIndex) :
    monsterSourceY82Spin.val (Pi.single v 1) =
      ∑ s : Fin 4, ((generatedFourthLiftYRowCoefficient v s : ℝ) / 2) •
        (Pi.single (generatedFourthLiftYRowAddress v s) 1 : SpinSpace) := by
  classical
  funext t
  rw [generatedFourth_lift_y_symmetric, generatedFourth_lift_y_row]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : t = generatedFourthLiftYRowAddress v s
  · simp only [h, ite_true]
    ring
  · simp only [h, Ne.symm h, ite_false, mul_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
