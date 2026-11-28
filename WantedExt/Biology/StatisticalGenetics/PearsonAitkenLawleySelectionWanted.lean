/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pearson–Aitken–Lawley selection formulas

Selection that acts on a random vector `X` only, by reweighting the population with a density
`w(X)`, changes the law of `X` but not the regression of `Y` on `X`. When `Y = a + B X + E`
with a residual `E` independent of `X`, the residual keeps its law and its independence of
`X`, the selected means of `Y` follow the regression (Aitken 1934, (5)), and the selected
covariance blocks are `Cov*(X, Y) = Cov*(X) Bᵀ` and `Cov*(Y) = B Cov*(X) Bᵀ + Cov(E)`. With
`B = Σ_YX Σ_XX⁻¹` and `Cov(E) = Σ_YY - Σ_YX Σ_XX⁻¹ Σ_XY` these are Aitken's blocks (7),
`Σ*_XY = Σ*_XX Σ_XX⁻¹ Σ_XY` and `Σ*_YY = Σ_YY - Σ_YX (Σ_XX⁻¹ - Σ_XX⁻¹ Σ*_XX Σ_XX⁻¹) Σ_XY`.

This module records the residual-preservation prerequisite (`indepFun_and_map_residual_selected`)
and the algebraic block identity (`aitken_block_identity`) as `theorem_wanted`; the downstream
selected mean and covariance theorems are tracked as planned roadmap pages depending on residual
preservation. A jointly Gaussian `(X, Y)` with nonsingular `Σ_XX` has such a representation; that
is the conditioning theorem of `MathlibExt.Probability.Distributions.GaussianConditioning` and is
not restated here. Pearson's scalar formulas (1903) are the one-variable case.

Sources: A. C. Aitken, "Note on selection from a multivariate normal population", Proc.
Edinburgh Math. Soc. (2) 4 (1934) 106–110, equations (5) and (7); K. Pearson, "Mathematical
contributions to the theory of evolution XI. On the influence of natural selection on the
variability and correlation of organs", Phil. Trans. R. Soc. A 200 (1903) 1–66; D. N. Lawley,
"A note on Karl Pearson's selection formulae", Proc. R. Soc. Edinburgh A 62 (1943) 28–30.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.LinearAlgebra.Matrix.AitkenBlockIdentity

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}

/-- The selected population: `μ` reweighted by the selection density `w`, evaluated at the
selected-on vector `X`. -/
noncomputable def selectedMeasure (μ : Measure Ω) (X : Ω → Fin p → ℝ)
    (w : (Fin p → ℝ) → ℝ≥0∞) : Measure Ω :=
  μ.withDensity fun ω => w (X ω)

/-- The response vector `Y = a + B X + E` of the linear regression model. -/
def response (a : Fin q → ℝ) (B : Matrix (Fin q) (Fin p) ℝ) (X : Ω → Fin p → ℝ)
    (E : Ω → Fin q → ℝ) (ω : Ω) : Fin q → ℝ :=
  a + B *ᵥ X ω + E ω

/-- **Selection on `X` preserves the residual** (Lawley 1943; Aitken 1934, p. 108). Let `μ` be a
probability measure on `Ω`, let `X : Ω → ℝ^p` and `E : Ω → ℝ^q` be measurable and independent
under `μ`, and let the selection density `w : ℝ^p → [0, ∞]` be measurable with
`∫⁻ w(X) dμ = 1`. Then under the selected measure `ν = w(X) · μ` the residual `E` is still
independent of `X`, and its law under `ν` equals its law under `μ`.

Source: Lawley (1943); Aitken (1934), p. 108. -/
public theorem_wanted indepFun_and_map_residual_selected (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin p → ℝ) (E : Ω → Fin q → ℝ) (w : (Fin p → ℝ) → ℝ≥0∞)
    (hX : Measurable X) (hE : Measurable E) (hw : Measurable w) (hind : IndepFun X E μ)
    (hnorm : ∫⁻ ω, w (X ω) ∂μ = 1) :
    IndepFun X E (selectedMeasure μ X w) ∧ (selectedMeasure μ X w).map E = μ.map E

end WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted
