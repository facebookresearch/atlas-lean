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

A jointly Gaussian `(X, Y)` with nonsingular `Σ_XX` has such a representation; that is the
conditioning theorem of `MathlibExt.Probability.Distributions.GaussianConditioning` and is
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

/-- **Selected means** (Aitken 1934, (5)). Let `μ` be a probability measure on `Ω`, let
`X : Ω → ℝ^p` and `E : Ω → ℝ^q` be measurable and independent under `μ`, let every coordinate
of `E` be `μ`-integrable with mean `0`, and let `Y = a + B X + E` for a vector `a : ℝ^q` and a
matrix `B : ℝ^{q×p}`. Let the selection density `w : ℝ^p → [0, ∞]` be measurable with
`∫⁻ w(X) dμ = 1`, and let every coordinate of `X` be integrable under the selected measure
`ν = w(X) · μ`. Then for every coordinate `j`, `∫ Y_j dν = a_j + ∑_k B_{jk} ∫ X_k dν`.

Source: Aitken (1934), p. 109, equation (5). -/
public theorem_wanted integral_response_selected (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin p → ℝ) (E : Ω → Fin q → ℝ) (a : Fin q → ℝ) (B : Matrix (Fin q) (Fin p) ℝ)
    (w : (Fin p → ℝ) → ℝ≥0∞) (hX : Measurable X) (hE : Measurable E) (hw : Measurable w)
    (hind : IndepFun X E μ) (hnorm : ∫⁻ ω, w (X ω) ∂μ = 1)
    (hXint : ∀ i, Integrable (fun ω => X ω i) (selectedMeasure μ X w))
    (hEint : ∀ j, Integrable (fun ω => E ω j) μ) (hEmean : ∀ j, ∫ ω, E ω j ∂μ = 0) (j : Fin q) :
    ∫ ω, response a B X E ω j ∂(selectedMeasure μ X w) =
      a j + ∑ k, B j k * ∫ ω, X ω k ∂(selectedMeasure μ X w)

/-- **Selected covariance blocks** (Aitken 1934, (7), in regression form). Let `μ` be a
probability measure on `Ω`, let `X : Ω → ℝ^p` and `E : Ω → ℝ^q` be measurable and independent
under `μ`, let every coordinate of `E` be square-integrable under `μ`, and let
`Y = a + B X + E` for a vector `a : ℝ^q` and a matrix `B : ℝ^{q×p}`. Let the selection density
`w : ℝ^p → [0, ∞]` be measurable with `∫⁻ w(X) dμ = 1`, and let every coordinate of `X` be
square-integrable under the selected measure `ν = w(X) · μ`. Then for all coordinates `i`, `j`,
* `Cov_ν(X_i, Y_j) = ∑_k Cov_ν(X_i, X_k) B_{jk}`, and
* `Cov_ν(Y_i, Y_j) = ∑_k ∑_l B_{ik} Cov_ν(X_k, X_l) B_{jl} + Cov_μ(E_i, E_j)`.

Source: Aitken (1934), p. 109, equation (7); Lawley (1943). -/
public theorem_wanted covariance_selected (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin p → ℝ) (E : Ω → Fin q → ℝ) (a : Fin q → ℝ) (B : Matrix (Fin q) (Fin p) ℝ)
    (w : (Fin p → ℝ) → ℝ≥0∞) (hX : Measurable X) (hE : Measurable E) (hw : Measurable w)
    (hind : IndepFun X E μ) (hnorm : ∫⁻ ω, w (X ω) ∂μ = 1)
    (hX2 : ∀ i, MemLp (fun ω => X ω i) 2 (selectedMeasure μ X w))
    (hE2 : ∀ j, MemLp (fun ω => E ω j) 2 μ) :
    (∀ i j, cov[fun ω => X ω i, fun ω => response a B X E ω j; selectedMeasure μ X w] =
        ∑ k, cov[fun ω => X ω i, fun ω => X ω k; selectedMeasure μ X w] * B j k) ∧
      ∀ i j, cov[fun ω => response a B X E ω i, fun ω => response a B X E ω j;
          selectedMeasure μ X w] =
        (∑ k, ∑ l, B i k * cov[fun ω => X ω k, fun ω => X ω l; selectedMeasure μ X w] * B j l) +
          cov[fun ω => E ω i, fun ω => E ω j; μ]

/-- **Aitken's block identity** (Aitken 1934, (7)). Let `Σ_XX` be a symmetric `p × p` real
matrix with nonzero determinant, let `Σ_XY` be a `p × q` and `Σ_YY` a `q × q` real matrix, and
let `V` be any `p × p` real matrix (the selected covariance of `X`). Put `B = Σ_XYᵀ Σ_XX⁻¹`.
Then `V Bᵀ = V Σ_XX⁻¹ Σ_XY`, and
`B V Bᵀ + (Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY) = Σ_YY - Σ_XYᵀ (Σ_XX⁻¹ - Σ_XX⁻¹ V Σ_XX⁻¹) Σ_XY`.
So the regression-form blocks of `covariance_selected`, with the population regression
coefficient `B` and residual covariance `Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY`, are Aitken's blocks.

Source: Aitken (1934), p. 109, equation (7). -/
public theorem_wanted aitken_block_identity (Sxx : Matrix (Fin p) (Fin p) ℝ)
    (Sxy : Matrix (Fin p) (Fin q) ℝ) (Syy : Matrix (Fin q) (Fin q) ℝ)
    (V : Matrix (Fin p) (Fin p) ℝ) (hsym : Sxx.IsSymm) (hdet : IsUnit Sxx.det) :
    V * (Sxyᵀ * Sxx⁻¹)ᵀ = V * Sxx⁻¹ * Sxy ∧
      Sxyᵀ * Sxx⁻¹ * V * (Sxyᵀ * Sxx⁻¹)ᵀ + (Syy - Sxyᵀ * Sxx⁻¹ * Sxy) =
        Syy - Sxyᵀ * (Sxx⁻¹ - Sxx⁻¹ * V * Sxx⁻¹) * Sxy

end WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted
