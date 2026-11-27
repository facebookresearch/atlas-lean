/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.MinimalDiscriminant

open IsDedekindDomain NumberField

namespace WeierstrassCurve

variable {L : Type} [Field L] [NumberField L]

-- `δ_v` is attained and minimal, for any elliptic curve over a number field.
example (W : WeierstrassCurve L) [W.IsElliptic] (v : HeightOneSpectrum (𝓞 L)) :
    ∃ C : VariableChange L, (C • W).IsIntegralAt v ∧
      v.valuation L (C • W).Δ = WithZero.exp (-(W.minimalDiscriminantOrd v : ℤ)) :=
  W.exists_minimalDiscriminantOrd v

-- Finitely many places with `δ_v ≠ 0`, and invariance under variable changes.
example (W : WeierstrassCurve L) [W.IsElliptic] (C : VariableChange L) :
    {v : HeightOneSpectrum (𝓞 L) | W.minimalDiscriminantOrd v ≠ 0}.Finite ∧
      (C • W).minimalDiscriminant = W.minimalDiscriminant :=
  ⟨W.finite_minimalDiscriminantOrd_ne_zero, W.minimalDiscriminant_variableChange C⟩

-- An equation with coefficients in `𝓞 L` is integral at every place; for instance
-- `y² = x³ - x` (`a₄ = -1`).
example (v : HeightOneSpectrum (𝓞 L)) : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve L).IsIntegralAt v := by
  have h : v.valuation L (-1) ≤ 1 := by
    rw [Valuation.map_neg, Valuation.map_one]
  refine ⟨?_, ?_, ?_, h, ?_⟩ <;> simp

-- For such an equation with `Δ ≠ 0`, `δ_v` is at most `ord_v(Δ)`.
example (W : WeierstrassCurve L) [W.IsElliptic] (v : HeightOneSpectrum (𝓞 L))
    (h : W.IsIntegralAt v) :
    v.valuation L W.Δ ≤ WithZero.exp (-(W.minimalDiscriminantOrd v : ℤ)) := by
  simpa using W.minimalDiscriminantOrd_le v 1 (by simpa using h)

end WeierstrassCurve
