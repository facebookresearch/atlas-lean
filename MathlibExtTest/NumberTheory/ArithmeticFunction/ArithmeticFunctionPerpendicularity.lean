/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ArithmeticFunctionPerpendicularity
import MathlibExt.NumberTheory.ArithmeticFunction.DirichletRealPower

namespace MetaMathlibExt.ArithmeticFunctionPerpendicularityTest

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

private def atOneAndSix : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 1 ∨ n = 6 then 1 else 0, by simp⟩

private theorem atOneAndSix_antimultiplicative : IsAntimultiplicative atOneAndSix := by
  refine ⟨by simp [atOneAndSix], fun p k hp hk => ?_⟩
  have hn6 : p ^ k ≠ 6 := fun heq =>
    (by decide : ¬ IsPrimePow (6 : ℕ)) ((isPrimePow_nat_iff 6).2 ⟨p, k, hp, hk, heq⟩)
  simp [atOneAndSix, hp.ne_one, hk.ne', hn6]

-- The two preservation implications apply at exponent zero and a negative exponent.
example : ∃ pow : ℝ → ArithmeticFunction ℝ → ArithmeticFunction ℝ,
    (pow 0 ↑ζ).IsMultiplicative ∧ IsAntimultiplicative (pow (-1) atOneAndSix) := by
  obtain ⟨pow, hpow, _⟩ := dirichletRealPower_vectorSpace
  have hz : (↑ζ : ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_zeta.natCast
  have ⟨hz₀, hlogz⟩ := hpow 0 ↑ζ hz.map_one
  have ⟨ha₁, hloga⟩ := hpow (-1) atOneAndSix atOneAndSix_antimultiplicative.1
  have preserve := dirichletRealPower_multiplicative_antimultiplicative_subspaces.1
  exact ⟨pow, (preserve _ _ _ hz.map_one hz₀ hlogz).1 hz,
    (preserve _ _ _ atOneAndSix_antimultiplicative.1 ha₁ hloga).2
      atOneAndSix_antimultiplicative⟩

-- Both factors have coefficients away from 1, and the splitting recovers each of them.
example (gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ)
    (hgh : gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = ↑ζ * atOneAndSix) :
    gh = (↑ζ, atOneAndSix) := by
  have hz : (↑ζ : ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_zeta.natCast
  have h₁ : ((↑ζ : ArithmeticFunction ℝ) * atOneAndSix) 1 = 1 := by
    rw [mul_apply_one, hz.map_one, atOneAndSix_antimultiplicative.1, one_mul]
  obtain ⟨_, _, hunique⟩ :=
    dirichletRealPower_multiplicative_antimultiplicative_subspaces.2 _ h₁
  exact (hunique gh hgh).trans
    (hunique (↑ζ, atOneAndSix) ⟨hz, atOneAndSix_antimultiplicative, rfl⟩).symm

-- A multiplicative function splits with antimultiplicative part `1`, the paper's `δ`.
example (gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ)
    (hgh : gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = ↑ζ) :
    gh = (↑ζ, 1) := by
  have hz : (↑ζ : ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_zeta.natCast
  obtain ⟨_, _, hunique⟩ := existsUnique_multiplicative_mul_antimultiplicative _ hz.map_one
  exact (hunique gh hgh).trans (hunique (↑ζ, 1) ⟨hz, isAntimultiplicative_one, mul_one _⟩).symm

-- An antimultiplicative function splits with multiplicative part `1`.
example (gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ)
    (hgh : gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = atOneAndSix) :
    gh = (1, atOneAndSix) := by
  obtain ⟨_, _, hunique⟩ :=
    existsUnique_multiplicative_mul_antimultiplicative _ atOneAndSix_antimultiplicative.1
  exact (hunique gh hgh).trans (hunique (1, atOneAndSix)
    ⟨isMultiplicative_one, atOneAndSix_antimultiplicative, one_mul _⟩).symm

end MetaMathlibExt.ArithmeticFunctionPerpendicularityTest
