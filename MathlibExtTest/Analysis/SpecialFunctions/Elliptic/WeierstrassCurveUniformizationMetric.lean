/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.WeierstrassCurveUniformizationMetric

open MeasureTheory
open scoped UpperHalfPlane

#check @PeriodPair.covolume
#check @PeriodPair.covolume_congr
#check @PeriodPair.covolume_eq
#check @PeriodPair.covolume_pos
#check @PeriodPair.covolume_ofTau
#check @PeriodPair.covolume_ofTau_upperHalfPlane
#check @PeriodPair.covolume_eq_of_lattice_eq_smul
#check @PeriodPair.weierstrassCurve
#check @PeriodPair.weierstrassCurve_Δ
#check @PeriodPair.isElliptic_weierstrassCurve
#check @PeriodPair.equation_weierstrassP_derivWeierstrassP
#check @PeriodPair.norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul
#check @WeierstrassCurve.UniformizationDatum
#check @WeierstrassCurve.UniformizationDatum.normSq
#check @WeierstrassCurve.UniformizationDatum.normSq_pos
#check @WeierstrassCurve.UniformizationDatum.discriminant_eq
#check @WeierstrassCurve.UniformizationDatum.Δ_ne_zero
#check @WeierstrassCurve.UniformizationDatum.isElliptic
#check @WeierstrassCurve.UniformizationDatum.normSq_pow_six
#check @WeierstrassCurve.UniformizationDatum.log_normSq
#check @WeierstrassCurve.UniformizationDatum.normSq_eq_of_lattice_eq_smul
#check @WeierstrassCurve.UniformizationDatum.normSq_eq_of_isHomothetic
#check @WeierstrassCurve.UniformizationDatum.normSq_pow_six_of_isHomothetic_ofTau
#check @WeierstrassCurve.UniformizationDatum.variableChange
#check @WeierstrassCurve.UniformizationDatum.normSq_variableChange

namespace PeriodPair

-- The square lattice `ℤ + ℤi` has covolume `1`.
example (hI : Complex.I.im ≠ 0) : (ofTau Complex.I hI).covolume = 1 := by
  rw [covolume_ofTau]
  simp

-- `(1, 2 + 3i)` has covolume `3`.
example (hτ : (2 + 3 * Complex.I).im ≠ 0) : (ofTau (2 + 3 * Complex.I) hτ).covolume = 3 := by
  rw [covolume_ofTau]
  norm_num

-- Scaling a period pair by `α` multiplies the covolume by `‖α‖²`.
example (L : PeriodPair) (α : ℂˣ) : (L.scale α).covolume = ‖(α : ℂ)‖ ^ 2 * L.covolume :=
  covolume_eq_of_lattice_eq_smul α.ne_zero (L.lattice_scale α)

-- The fundamental parallelogram has measure the covolume.
example (L : PeriodPair) : volume (L.fundamentalParallelogram 0) = ENNReal.ofReal L.covolume := by
  rw [volume_fundamentalParallelogram, covolume_eq]

-- The curve of a lattice is elliptic, with no hypothesis.
example (L : PeriodPair) : L.weierstrassCurve.IsElliptic := inferInstance

-- `‖Δ‖ covol⁶` is unchanged by scaling.
example (L : PeriodPair) (α : ℂˣ) :
    ‖(L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2‖ * (L.scale α).covolume ^ 6 =
      ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ * L.covolume ^ 6 :=
  norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul α.ne_zero (L.lattice_scale α)

-- The coefficients of the Weierstrass curve of a period pair.
example (L : PeriodPair) :
    L.weierstrassCurve.a₄ = -L.g₂ / 4 ∧ L.weierstrassCurve.a₆ = -L.g₃ / 4 :=
  ⟨rfl, rfl⟩

end PeriodPair

namespace WeierstrassCurve.UniformizationDatum

-- The tautological datum `(L, 1)` for the Weierstrass curve of `L` has squared norm `covol(L)`.
example (L : PeriodPair) :
    (⟨L, 1, one_smul _ _⟩ : L.weierstrassCurve.UniformizationDatum).normSq = L.covolume := by
  simp [normSq, show (1 : VariableChange ℂ).u = 1 from rfl]

-- Transporting along a variable change with `u = 2` multiplies the squared norm by `4`.
example (W : WeierstrassCurve ℂ) (D : W.UniformizationDatum) (C' : VariableChange ℂ)
    (hu : (C'.u : ℂ) = 2) : (D.variableChange C').normSq = 4 * D.normSq := by
  rw [normSq_variableChange, hu]
  norm_num

-- Two data for `W` whose lattices differ by scaling give the same squared norm.
example (W : WeierstrassCurve ℂ) (D : W.UniformizationDatum) (α : ℂˣ)
    (D' : W.UniformizationDatum) (hL : D'.L = D.L.scale α) : D'.normSq = D.normSq :=
  normSq_eq_of_lattice_eq_smul D D' α.ne_zero (hL ▸ D.L.lattice_scale α)

-- A curve with a uniformization datum has nonzero discriminant.
example (W : WeierstrassCurve ℂ) (D : W.UniformizationDatum) : W.Δ ≠ 0 := D.Δ_ne_zero

end WeierstrassCurve.UniformizationDatum
