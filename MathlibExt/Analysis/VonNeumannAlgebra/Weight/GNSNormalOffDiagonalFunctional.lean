/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalDiagonalFunctional
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Original normal-weight GNS off-diagonal coefficients in the actual normal span

Four actual normal diagonal members at x+y, x-y, x+i*y and x-i*y combine
by the original complex polarization identity. Their literal GNS map values
and second-variable-linear pairing give the off-diagonal representation
coefficient on the same original algebra. No desired normality, vector,
GNS model or coefficient-bound certificate is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the original off-diagonal GNS coefficient as an actual normal-functional member. -/
def normalWeightGNSOffDiagonalFunctional (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x y : φ.finiteSquareSubmodule) :
    {ρ : normalFunctionalSpace M // (ρ.val : StrongDual ℂ M) =
      MathlibExt.Analysis.CStarAlgebra.representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap y)} := by
  let D := normalWeightGNSDiagonalFunctional M φ hφ
  let ρ : normalFunctionalSpace M := (4 : ℂ)⁻¹ •
    (D (x + y) - D (x - y) + Complex.I • D (x + Complex.I • y) -
      Complex.I • D (x - Complex.I • y))
  refine ⟨ρ, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  have hD (z : φ.finiteSquareSubmodule) :
      (D z : StrongDual ℂ M) a = ⟪φ.gnsMap z, (φ.gnsLeftStarAlgHom a) (φ.gnsMap z)⟫_ℂ := by
    exact normalWeightGNSDiagonalFunctional_apply M φ hφ z a
  change (4 : ℂ)⁻¹ • ((D (x + y) : StrongDual ℂ M) a - (D (x - y) : StrongDual ℂ M) a +
    Complex.I • (D (x + Complex.I • y) : StrongDual ℂ M) a -
    Complex.I • (D (x - Complex.I • y) : StrongDual ℂ M) a) = _
  rw [hD, hD, hD, hD, MathlibExt.Analysis.CStarAlgebra.representationCoefficient_apply]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end VonNeumannAlgebra
