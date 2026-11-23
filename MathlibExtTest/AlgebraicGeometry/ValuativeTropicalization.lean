/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.ValuativeTropicalization
import Mathlib.Tactic.NormNum

noncomputable section

open MathlibExt.AlgebraicGeometry.ValuativeTropicalization

private def two : ℚˣ := Units.mk0 2 (by norm_num)

/-- A negative Laurent exponent uses the inverse scalar in the actual
translation map, detecting a wrong sign in the integral closure convention. -/
example : scale (fun _ : Fin 1 => two)
    (AddMonoidAlgebra.single (-(coordinateExponent (0 : Fin 1))) (1 : ℚ)) =
      AddMonoidAlgebra.single (-(coordinateExponent (0 : Fin 1))) (1 / 2 : ℚ) := by
  norm_num [scale, scaledMonomials, characterEval, coordinateExponent,
    Fin.prod_univ_one, Pi.single_apply, two]

/-- An actual point cannot annihilate the unit ideal. -/
example : IsEmpty (Point (⊤ : Ideal (CoordinateRing ℚ 1)) ℚ) := ⟨fun p => by
  have h : p.hom (1 : CoordinateRing ℚ 1) = 0 := p.annihilates (by trivial)
  simp at h⟩

section IntegralEmbedding

variable {K : Type} [Field K] [Valued K NNReal]

/-- The integral translation used by initial degenerations scales the monomial `x` by `t⁻¹`. -/
example (t : Fin 1 → Kˣ) :
    integralEmbedding t (AddMonoidAlgebra.single (coordinateExponent (0 : Fin 1)) 1) =
      AddMonoidAlgebra.single (coordinateExponent (0 : Fin 1)) (((t 0)⁻¹ : Kˣ) : K) := by
  simp [integralEmbedding, scale, scaledMonomials, characterEval, coordinateExponent]

/-- and the monomial `x⁻¹` by `t`, so a reversed sign convention is detected. -/
example (t : Fin 1 → Kˣ) :
    integralEmbedding t (AddMonoidAlgebra.single (-(coordinateExponent (0 : Fin 1))) 1) =
      AddMonoidAlgebra.single (-(coordinateExponent (0 : Fin 1))) ((t 0 : Kˣ) : K) := by
  simp [integralEmbedding, scale, scaledMonomials, characterEval, coordinateExponent]

end IntegralEmbedding
