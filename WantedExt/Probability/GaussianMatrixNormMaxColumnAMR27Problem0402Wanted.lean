/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Norms of Gaussian matrices and their columns (Bandeira, Open Problem 4.2)

Bandeira, Ten Lectures and Forty-Two Open Problems, Open Problem 4.2 (Latała-Riemer-Schütt): for a
symmetric matrix `X ∈ ℝ^{d × d}` with otherwise independent Gaussian entries, prove or disprove `E
‖X‖ ≲ E max_k ‖X e_k‖₂`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace MathlibExt.Probability.GaussianMatrixNormMaxColumnAMR27Problem0402Wanted

/-!
Source: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science
(2015-2016), Open Problem 4.2, https://afonsobandeira.wordpress.com/2015/10/25/10l42concentration/.
UnsolvedMath record UM-02800402 (`AMR-027-0402`), dataset ulamai/UnsolvedMath v1.8.0.

The entries `X i j = b i j g_{min(i,j), max(i,j)}` (symmetric `b`, independent standard Gaussians
`g`) are independent centered Gaussians on and above the diagonal with arbitrary variances `b i j ^
2`, the setting of the problem and of Latała-van Handel-Youssef. `‖X‖` is the spectral norm
(`Matrix.Norms.L2Operator`) and `≲` means `≤ C ·` with a universal constant `C`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

/-- The symmetric Gaussian matrix with independent centered entries `X i j = b i j g (min i j)
(max i j)` (`i ≤ j`) of variances `b i j ^ 2`, for a symmetric `b`. -/
def gaussianMatrix {d : ℕ} (b : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => b i j * g (min i j) (max i j)

/-- The largest Euclidean norm of a column, `max_k ‖A e_k‖₂`. -/
noncomputable def maxColumnNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ k : Fin d, Real.sqrt (∑ i, A i k ^ 2)

/-- The Latała-Riemer-Schütt problem, with a positive answer: there is a universal constant `C`
such that every symmetric Gaussian matrix `X` with independent centered entries of arbitrary
variances satisfies `E ‖X‖ ≤ C E max_k ‖X e_k‖₂` (`‖X‖` the spectral norm, `g` independent standard
Gaussians). -/
def gaussianMatrixNormLeMaxColumn : Prop :=
  ∃ C : ℝ, ∀ (d : ℕ) (b : Matrix (Fin d) (Fin d) ℝ), b.IsSymm →
    ∫ g, ‖gaussianMatrix b g‖ ∂(Measure.pi fun _ : Fin d => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1) ≤
      C * ∫ g, maxColumnNorm (gaussianMatrix b g) ∂(Measure.pi fun _ : Fin d =>
        Measure.pi fun _ : Fin d => gaussianReal 0 1)

/--
Resolved true: Latała, van Handel and Youssef prove, for symmetric matrices with independent
centered Gaussian entries of arbitrary variances, `E ‖X‖ ≍ E max_i (∑_j X_ij²)^{1/2}` with universal
constants (the case `p = ∞` of their main theorem), which settles Latała's conjecture. Source: A. S.
Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science (2015-2016),
Open Problem 4.2, https://afonsobandeira.wordpress.com/2015/10/25/10l42concentration/; resolution:
R. Latała, R. van Handel and P. Youssef, The dimension-free structure of nonhomogeneous random
matrices, Invent. Math. 214 (2018); arXiv:1711.00807, abstract: for a symmetric random matrix X with
independent centered Gaussian entries, E‖X‖_{S_p} ≍ E[(∑ᵢ (∑ⱼ X_ij²)^{p/2})^{1/p}] with universal
constants for 2 ≤ p ≤ ∞; the case p = ∞ (spectral norm, E maxᵢ (∑ⱼ X_ij²)^{1/2}) settles the
conjecture of the first author, https://doi.org/10.1007/s00222-018-0817-x.
-/
public theorem_wanted gaussianMatrixNormLeMaxColumn_holds : gaussianMatrixNormLeMaxColumn

end MathlibExt.Probability.GaussianMatrixNormMaxColumnAMR27Problem0402Wanted
