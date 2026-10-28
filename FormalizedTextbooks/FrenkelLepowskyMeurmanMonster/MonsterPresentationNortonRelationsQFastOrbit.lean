/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite evaluation of all positive and inverse Norton Q orbits. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCacheInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegralPowers

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Positive actual Norton Q orbits computed by the checked compact evaluator. -/
def monsterNortonUQFastOrbit : ℕ → Q → Q
  | 0, q => q
  | n + 1, q => monsterNortonUQFastImage (monsterNortonUQFastOrbit n q)

/-- The compact recursion is the original complete source Q orbit. -/
theorem monsterNortonUQFastOrbit_eq (n : ℕ) (q : Q) :
    monsterNortonQOrbit n q = monsterNortonUQFastOrbit n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change monsterNortonUQImage (monsterNortonQOrbit n q) =
      monsterNortonUQFastImage (monsterNortonUQFastOrbit n q)
    rw [ih, monsterNortonUQFastImage_eq]

/-- Every positive actual spin power has this exact full-phase evaluator. -/
theorem monsterNortonUQFastOrbit_actual (n : ℕ) (q : Q) :
    spinConjugation (monsterNortonUFiber ^ n).val.1 q = monsterNortonUQFastOrbit n q := by
  rw [monsterNortonQOrbit_eq, monsterNortonUQFastOrbit_eq]

/-- Inverse actual Norton Q orbits, including the inverse generator corrections. -/
def monsterNortonUQInverseFastOrbit : ℕ → Q → Q
  | 0, q => q
  | n + 1, q => monsterNortonUQInverseFastImage (monsterNortonUQInverseFastOrbit n q)

/-- Every inverse actual spin power has this full-phase evaluator without an order assumption. -/
theorem monsterNortonUQInverseFastOrbit_actual (n : ℕ) (q : Q) :
    spinConjugation ((monsterNortonUFiber⁻¹) ^ n).val.1 q =
      monsterNortonUQInverseFastOrbit n q := by
  induction n with
  | zero =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | succ n ih =>
    rw [pow_succ']
    change spinConjugation
      ((monsterNortonUFiber⁻¹).val.1 * ((monsterNortonUFiber⁻¹) ^ n).val.1) q = _
    rw [map_mul]
    change spinConjugation (monsterNortonUFiber⁻¹).val.1
      (spinConjugation ((monsterNortonUFiber⁻¹) ^ n).val.1 q) = _
    rw [ih, monsterNortonUQInverseFastImage_eq]
    rfl

/-- Actual short phases for all positive powers are computed by the compact full-phase orbit. -/
theorem monsterNortonUQFastOrbit_short_phase (n : ℕ) (z : Fin 24 → ℤ) :
    monsterNortonIntegralShortPhase (monsterNortonUFiber ^ n) z =
      Multiplicative.toAdd (monsterNortonUQFastOrbit n (monsterNortonCoordinateQ z)).coeff := by
  unfold monsterNortonIntegralShortPhase
  rw [monsterNortonUQFastOrbit_actual]

/-- Actual short phases for all inverse powers are computed with the exact inverse signs. -/
theorem monsterNortonUQInverseFastOrbit_short_phase (n : ℕ) (z : Fin 24 → ℤ) :
    monsterNortonIntegralShortPhase ((monsterNortonUFiber⁻¹) ^ n) z =
      Multiplicative.toAdd
        (monsterNortonUQInverseFastOrbit n (monsterNortonCoordinateQ z)).coeff := by
  unfold monsterNortonIntegralShortPhase
  rw [monsterNortonUQInverseFastOrbit_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
