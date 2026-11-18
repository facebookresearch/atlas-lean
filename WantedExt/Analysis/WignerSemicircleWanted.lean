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
statements are unchanged. ATLAS changes: the Wigner 1955 source note now says what that paper
proves, Tao's statement of this almost-sure form is cited, and the proved bridge
`semicircleLaw_eq_semicircleReal` to `ProbabilityTheory.semicircleReal` and the resulting
`IsProbabilityMeasure` instance are added. Source: E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (the expected moments of the eigenvalue distribution of random-sign real symmetric matrices, with zero diagonal and off-diagonal entries ±v, converge to the semicircle moments; extended to a wider class in Ann. of Math. 67 (1958)). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Probability.Distributions.Semicircle

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
on `[−2, 2]` with density `√(4 − x²) / (2π)`. Wigner 1955 proved
convergence of the expected moments for random-sign symmetric
matrices; Pastur 1972 extended it to all variances under finite
second moments. §102 in Knill's *Some Fundamental Theorems in
Mathematics*.
Tao, *Topics in Random Matrix Theory*, Theorem 2.4.2, states this almost-sure form.

Weak convergence is encoded against bounded continuous test functions:
almost surely `∫ f dμ_n → ∫ f dμ_∞` for every bounded continuous `f`.
The integrability hypotheses on the entries make the mean and variance
identities genuine (mathlib's Bochner integral defaults to `0` on
non-integrable integrands, so a bare `∫ X² = 1` is satisfiable
vacuously without them).
-/

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

/-- Empirical spectral measure of a Hermitian matrix `W` on the real
eigenvalues: `(1/n) · ∑_j δ_{λ_j}`. -/
noncomputable def empiricalSpectralMeasureHerm {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ j : Fin n, Measure.dirac (hW.eigenvalues j)

/-- The **Wigner semicircle measure** on `ℝ`: probability measure with
density `√(4 − x²) / (2π)` supported on `[−2, 2]`. -/
noncomputable def semicircleLaw : Measure ℝ :=
  (volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (Real.sqrt (4 - x ^ 2) / (2 * Real.pi)))

set_option linter.dupNamespace false in
/-- The semicircle measure of this problem is the semicircle distribution
`ProbabilityTheory.semicircleReal`, whose moments are the Catalan numbers. -/
theorem semicircleLaw_eq_semicircleReal : semicircleLaw = ProbabilityTheory.semicircleReal :=
  rfl

set_option linter.dupNamespace false in
/-- The semicircle measure is a probability measure. -/
instance isProbabilityMeasure_semicircleLaw : IsProbabilityMeasure semicircleLaw := by
  rw [semicircleLaw_eq_semicircleReal]; infer_instance

/-- `n × n` real-symmetric random matrix built from the upper-
triangular half of `X : ℕ → ℕ → Ω → ℝ`. -/
noncomputable def wignerMatrix {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((X (min (i : ℕ) j) (max (i : ℕ) j) ω : ℝ) : ℂ)

/-- The Wigner matrix is Hermitian (in fact real symmetric: `min`/`max`
are symmetric in their arguments, and the entries are real). -/
lemma wignerMatrix_isHermitian {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : (wignerMatrix X n ω).IsHermitian := by
  ext i j
  simp [wignerMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal,
    min_comm (i : ℕ) j, max_comm (i : ℕ) j]

/- **Wigner's semicircle law** (Wigner 1955). For an iid family of
mean-`0`, variance-`1` real random variables, the empirical spectral
measure of the rescaled real-symmetric matrix `W_n / √n` converges
weakly, almost surely, to the semicircle measure on `[−2, 2]`. -/
/-- Source: E. Wigner, 'Characteristic vectors of bordered matrices with infinite dimensions', Ann. of Math. (2) 62 (1955) 548–564 (the expected moments of the eigenvalue distribution of random-sign real symmetric matrices, with zero diagonal and off-diagonal entries ±v, converge to the semicircle moments; extended to a wider class in Ann. of Math. 67 (1958)). Pastur's universality extending to all variances with finite second moments: L. Pastur, 'On the spectrum of random matrices', Teor. Mat. Fiz. 10 (1972) 102–112. Listed as §102 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). This almost-sure form, for i.i.d. upper-triangular entries of mean 0 and variance 1, is T. Tao, *Topics in Random Matrix Theory*, AMS GSM 132 (2012), Theorem 2.4.2, which allows the diagonal entries a different law. Via leanprover/lean-eval@38361be, problem `wigner_semicircle`. -/
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
