/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives

/-! Exact complete source spin formulas skip phase evaluation only after proving the input coefficient is zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original Gaussian term retains its actual phase whenever its input contributes. -/
def generatedAxisGlobalOddXiSpinZeroGuard (u : Fin 4096 → ℤ) (k : Fin 4096) : ℤ :=
  ∑ a : XiGrayIndex,
    let c := u (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode a))
    if c = 0 then 0 else
      generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a (golayLabelCoefficients k)) * c

/-- Zero Gaussian input terms contribute exactly zero to the original complete source sum. -/
theorem generatedAxisGlobalOddXiSpinZeroGuard_actual (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddXiSpinZeroGuard u = generatedAxisGlobalOddXiSpinInteger u := by
  funext k
  unfold generatedAxisGlobalOddXiSpinZeroGuard generatedAxisGlobalOddXiSpinInteger
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  split_ifs with hc
  · simp only [hc, mul_zero]
  · rfl

/-- A complete genuine signed monomial pullback evaluates its phase only for a nonzero input. -/
def generatedAxisGlobalOddMonomialSpinZeroGuard (w : List (Fin 2 × Bool))
    (u : Fin 4096 → ℤ) (k : Fin 4096) : ℤ :=
  let r := generatedFourthMonomialWordPull w (golayLabelCoefficients k)
  let c := u (generatedAxisGlobalSpinLabel r.2)
  if c = 0 then 0 else generatedAxisGlobalIntSign r.1 * c

/-- The zero guard is exactly the complete original signed source pullback. -/
theorem generatedAxisGlobalOddMonomialSpinZeroGuard_actual (w : List (Fin 2 × Bool))
    (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddMonomialSpinZeroGuard w u =
      generatedAxisGlobalOddMonomialSpinInteger w u := by
  funext k
  unfold generatedAxisGlobalOddMonomialSpinZeroGuard generatedAxisGlobalOddMonomialSpinInteger
  dsimp only
  split_ifs with hc
  · simp only [hc, mul_zero]
  · rfl

/-- All original signed primitive letters retain their complete source action with exact zero guards. -/
def generatedAxisGlobalOddSpinZeroGuardPrimitive (l : Fin 10)
    (u : Fin 4096 → ℤ) : Fin 4096 → ℤ :=
  ![generatedAxisGlobalOddXiSpinZeroGuard u,
    generatedAxisGlobalOddXiSpinZeroGuard (generatedAxisGlobalOddXiSpinZeroGuard u),
    generatedAxisGlobalOddSignSpinInteger 16 u, generatedAxisGlobalOddSignSpinInteger 16 u,
    generatedAxisGlobalOddSignSpinInteger 32 u, generatedAxisGlobalOddSignSpinInteger 32 u,
    generatedAxisGlobalOddMonomialSpinZeroGuard [(0, false)] u,
    generatedAxisGlobalOddMonomialSpinZeroGuard [(0, true)] u,
    generatedAxisGlobalOddMonomialSpinZeroGuard [(1, false)] u,
    generatedAxisGlobalOddMonomialSpinZeroGuard [(1, true)] u] l

/-- Every guarded complete primitive is the genuine original source operator on every integer input. -/
theorem generatedAxisGlobalOddSpinZeroGuardPrimitive_actual (l : Fin 10)
    (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddSpinZeroGuardPrimitive l u = generatedAxisGlobalOddSpinPrimitive l u := by
  fin_cases l <;>
    simp only [generatedAxisGlobalOddSpinZeroGuardPrimitive, generatedAxisGlobalOddSpinPrimitive,
      generatedAxisGlobalOddXiSpinZeroGuard_actual,
      generatedAxisGlobalOddMonomialSpinZeroGuard_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
