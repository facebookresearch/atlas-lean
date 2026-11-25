/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The basic reproduction number `R₀ = ρ(F V⁻¹)`: definition

For a compartmental epidemic model with `F` the matrix of new infections and `V` the matrix of
the other transfers between infected compartments at a disease-free equilibrium, van den
Driessche and Watmough (2002) define the **basic reproduction number** as the spectral radius
of the next-generation matrix `F V⁻¹`. This file holds only that definition, so that every
library may state results about it. The threshold theory (`R₀ < 1` iff `F - V` is Hurwitz, for
`F ≥ 0` and `V` a nonsingular M-matrix) is in `Domains.Biology.Epidemiology.NextGenerationMatrix`.

## References

* P. van den Driessche and J. Watmough, *Reproduction numbers and sub-threshold endemic
  equilibria for compartmental models of disease transmission*, Math. Biosci. 180 (2002)
  29–48, Eq. (4).
-/

@[expose] public section

namespace MathlibExt.Biology.Epidemiology.NextGenerationMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **basic reproduction number** `R₀ = ρ(F V⁻¹)`: the spectral radius (largest modulus of
a complex eigenvalue) of the next-generation matrix `F V⁻¹` (van den Driessche–Watmough 2002,
Eq. (4)). It is meaningful when `V` is invertible (for a nonsingular M-matrix it is). -/
noncomputable def R0 (F V : Matrix ι ι ℝ) : ℝ :=
  (spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ))).toReal

end MathlibExt.Biology.Epidemiology.NextGenerationMatrix
