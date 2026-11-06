/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastDot24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Exact twelve-bit dot parity evaluates the complete original spin quadratic matrix.
Every diagonal and off-diagonal contribution is retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original complete quadratic matrix, evaluated by exact twelve-bit dot parity. -/
def generatedTwelfthSpinQuadraticFast (rows : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if n.testBit i.val then generatedNinthLowerSpinFastDotTwelve (rows i) n else 0))

/-- Fast parity equals the full original quadratic polynomial for arbitrary matrix rows. -/
theorem generatedTwelfth_spin_quadratic_fast_actual (rows : Fin 12 → ℕ) (n : Fin 4096) :
    (if (generatedTwelfthSpinQuadraticFast rows n.val).testBit 0 then (1 : ZMod 2) else 0) =
      monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase rows) (golayLabelCoefficients n) := by
  unfold generatedTwelfthSpinQuadraticFast monsterMonomialQuadratic generatedTwelfthSpinCompactPhase
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  cases h : n.val.testBit i.val
  · simp [golayLabelCoefficients, h]
  · simpa [generatedNinth_lower_spin_fast_dot_twelve,
      golayLabelCoefficients, monsterCo1GeometryBinaryMaskDecode, golayBooleanCast,
      h, mul_comm] using monsterCo1GeometryBinaryMaskDot_decode 12 (rows i) n.val

/-- The complete original integral quadratic sign is the exact fast parity sign. -/
theorem generatedTwelfth_spin_quadratic_fast_sign (rows : Fin 12 → ℕ) (n : Fin 4096) :
    nortonUIntegerSign
      (monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase rows)
        (golayLabelCoefficients n)) =
      if (generatedTwelfthSpinQuadraticFast rows n.val).testBit 0 then (-1 : ℤ) else 1 := by
  rw [← generatedTwelfth_spin_quadratic_fast_actual]
  cases (generatedTwelfthSpinQuadraticFast rows n.val).testBit 0 <;> simp [nortonUIntegerSign]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
