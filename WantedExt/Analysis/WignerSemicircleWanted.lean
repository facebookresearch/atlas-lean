/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wigner semicircle law

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.WignerSemicircle` — wigner_semicircle (manifest `manifests/problems/wigner_semicircle.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.WignerSemicircleWanted` namespace. Mathematical
statements are unchanged. Source: E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (Gaussian case). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.WignerSemicircleWanted
namespace Analysis
namespace WignerSemicircleProblem

/-!
# Wigner semicircle law

For an iid family `X i j : Ω → ℝ` (`i ≤ j`) of mean-`0`, variance-`1`
random variables, the empirical spectral measure of the rescaled
real-symmetric matrix `W_n / √n` (with `W_n(i, j) = X (min i j) (max i j)`)
converges weakly, almost surely as `n → ∞`, to the **semicircle measure**
on `[−2, 2]` with density `√(4 − x²) / (2π)`. Wigner 1955 for the
Gaussian case; Pastur 1972 extended it to all variances under finite
second moments. §102 in Knill's *Some Fundamental Theorems in
Mathematics*.

Weak convergence is encoded against bounded continuous test functions:
almost surely `∫ f dμ_n → ∫ f dμ_∞` for every bounded continuous `f`.
The integrability hypotheses on the entries make the mean and variance
identities genuine (mathlib's Bochner integral defaults to `0` on
non-integrable integrands, so a bare `∫ X² = 1` is satisfiable
vacuously without them).
-/

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

/-- **Empirical spectral measure of a Hermitian matrix.** Let $W$ be a Hermitian $n \times n$
complex matrix with real eigenvalues $\lambda_1, \dots, \lambda_n$, listed with multiplicity. The
empirical spectral measure of $W$ is the measure $\frac{1}{n} \sum_{j=1}^{n} \delta_{\lambda_j}$
on $\mathbb{R}$, where $\delta_\lambda$ is the Dirac measure at $\lambda$; for $n = 0$ it is the
zero measure. -/
noncomputable def empiricalSpectralMeasureHerm {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ j : Fin n, Measure.dirac (hW.eigenvalues j)

/-- **Semicircle distribution.** The semicircle distribution is the measure $\sigma$ on
$\mathbb{R}$ given by $\sigma(A) = \int_{A \cap [-2, 2]} \frac{\sqrt{4 - x^2}}{2\pi} \, dx$ for
every measurable set $A \subseteq \mathbb{R}$.

Since $\int_{-2}^{2} \sqrt{4 - x^2} \, dx = 2\pi$, it is a probability measure. -/
noncomputable def semicircleLaw : Measure ℝ :=
  (volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (Real.sqrt (4 - x ^ 2) / (2 * Real.pi)))

/-- **Wigner matrix.** Let $X_{ij} : \Omega \to \mathbb{R}$, for $i, j \in \mathbb{N}$, be real
functions on a set $\Omega$. For $n \in \mathbb{N}$ and $\omega \in \Omega$, the Wigner matrix
$W_n(\omega)$ is the $n \times n$ complex matrix, with rows and columns indexed by
$\{0, \dots, n - 1\}$, whose entry at $(i, j)$ is the real number
$X_{\min(i, j)\, \max(i, j)}(\omega)$. Only the $X_{ij}$ with $i \le j$ are used, and the matrix
is real symmetric. -/
noncomputable def wignerMatrix {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((X (min (i : ℕ) j) (max (i : ℕ) j) ω : ℝ) : ℂ)

/-- **Wigner matrices are Hermitian.** For every family of real functions
$X_{ij} : \Omega \to \mathbb{R}$, $i, j \in \mathbb{N}$, on a set $\Omega$, every $n \in \mathbb{N}$
and every $\omega \in \Omega$, the Wigner matrix $W_n(\omega)$ is Hermitian.

The matrix is in fact real symmetric: its entry at $(i, j)$ is the real number
$X_{\min(i, j)\, \max(i, j)}(\omega)$, and $\min$ and $\max$ are symmetric in their arguments. -/
lemma wignerMatrix_isHermitian {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : (wignerMatrix X n ω).IsHermitian := by
  ext i j
  simp [wignerMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal,
    min_comm (i : ℕ) j, max_comm (i : ℕ) j]

/- **Wigner's semicircle law** (Wigner 1955). For an iid family of
mean-`0`, variance-`1` real random variables, the empirical spectral
measure of the rescaled real-symmetric matrix `W_n / √n` converges
weakly, almost surely, to the semicircle measure on `[−2, 2]`. -/
/-- **Wigner's semicircle law.** Let $(\Omega, \mu)$ be a probability space and let
$X_{ij} : \Omega \to \mathbb{R}$, for $i, j \in \mathbb{N}$, be measurable functions. Suppose that
the family $(X_{ij})_{i \le j}$ is mutually independent, that all $X_{ij}$ with $i \le j$ have the
same distribution, and that for $i \le j$ both $X_{ij}$ and $X_{ij}^2$ are integrable with
$\mathbb{E}[X_{ij}] = 0$ and $\mathbb{E}[X_{ij}^2] = 1$. For $n \in \mathbb{N}$ and
$\omega \in \Omega$, let $W_n(\omega)$ be the Wigner matrix of $X$ and let $L_n(\omega)$ be the
image of its empirical spectral measure under $x \mapsto x / \sqrt{n}$ (for $n \ge 1$, the
empirical spectral measure of $W_n(\omega) / \sqrt{n}$). Then for $\mu$-almost every $\omega$,
every bounded continuous function $f : \mathbb{R} \to \mathbb{R}$ satisfies
$$\int f \, dL_n(\omega) \to \int f \, d\sigma \quad (n \to \infty),$$
where $\sigma$ is the semicircle distribution.

Source: E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (Gaussian case). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `wigner_semicircle`. -/
public theorem_wanted wigner_semicircle
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (_hX_meas : ∀ i j, Measurable (X i j))
    (_hX_indep : iIndepFun
      (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (_hX_iid : ∀ i j i' j', i ≤ j → i' ≤ j' →
      ProbabilityTheory.IdentDistrib (X i j) (X i' j') μ μ)
    (_hX_int : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (_hX_sq_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 2) μ)
    (_hX_mean : ∀ i j, i ≤ j → ∫ ω, X i j ω ∂μ = 0)
    (_hX_var : ∀ i j, i ≤ j → ∫ ω, (X i j ω) ^ 2 ∂μ = 1) :
    ∀ᵐ ω ∂μ,
      ∀ (f : ℝ → ℝ), Continuous f → (∃ M, ∀ x, ‖f x‖ ≤ M) →
        Tendsto
          (fun n : ℕ =>
            ∫ x, f x ∂ (empiricalSpectralMeasureHerm
              (wignerMatrix_isHermitian X n ω)).map
                (fun x : ℝ => x / Real.sqrt n))
          atTop (𝓝 (∫ x, f x ∂semicircleLaw))

end WignerSemicircleProblem
end Analysis

end MathlibExt.Analysis.WignerSemicircleWanted
