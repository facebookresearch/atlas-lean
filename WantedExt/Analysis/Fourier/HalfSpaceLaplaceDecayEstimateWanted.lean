/-
# Decay of bounded harmonic extensions of Schwartz data in a half space

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_72.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_72 … := by sorry` into the Batteries `theorem_wanted`
`exists_abs_le_inv_one_add_abs_of_harmonic_lowerHalfSpace`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions;
corrected the statement: added the boundedness hypothesis `hu_bdd`, without which the statement
is false (uniqueness for the half-space Dirichlet problem needs a bounded solution).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted

/-- The Euclidean plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)
/-- Euclidean three-space. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The closed lower half-space `{p | p 2 ≤ 0}`. -/
abbrev LowerHalfSpace : Set R3 := {p : R3 | p 2 ≤ 0}
/-- The open lower half-space `{p | p 2 < 0}`. -/
abbrev OpenLowerHalfSpace : Set R3 := {p : R3 | p 2 < 0}

/-- The point `(x 0, x 1, z)` of three-space. -/
noncomputable def point3 (x : R2) (z : ℝ) : R3 :=
  EuclideanSpace.single (0 : Fin 3) (x 0) +
    EuclideanSpace.single (1 : Fin 3) (x 1) +
      EuclideanSpace.single (2 : Fin 3) z

/-- Let $\phi:\mathbb{R}^2\to\mathbb{R}$ be a Schwartz function. Consider the Laplace's equation in
half space as follows,
\[
\left\{
\begin{aligned}
\Delta_{x,y,z}u(x,y,z) &= 0, && (x,y,z)\in \mathbb{R}^3_-:=\mathbb{R}^2\times[0,-\infty)\\
u\big|_{z=0} &= \phi\\
\lim_{z\to -\infty}\sup_{x,y\in\mathbb{R}}|u(x,y,z)| &= 0
\end{aligned}
\right.
\]
Prove that, there exists an constant $C(\phi)$, which depends on $\phi$, such that the following
estimate holds,
\[
\forall z\in[0,-\infty),\ \sup_{x,y\in\mathbb{R}}|u(x,y,z)|\le C(\phi)(1+|z|)^{-1}.
\]

Lean variant: the source hypotheses do not force `u` to be bounded, and without that the decay bound
fails (add to the Poisson extension of `φ` the harmonic function `Im G(x₁ + i z)` built from
Newman's entire function `G`, which vanishes on `z = 0` and as `z → -∞` but is unbounded near the
boundary); the standard implicit hypothesis `hu_bdd`, that `u` is bounded on the closed half-space,
is added.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_72.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem_wanted exists_abs_le_inv_one_add_abs_of_harmonic_lowerHalfSpace
  (φ : SchwartzMap R2 ℝ)
  (u : R3 → ℝ)
  (hu_harmonic : InnerProductSpace.HarmonicOnNhd u OpenLowerHalfSpace)
  (hu_cont : ContinuousOn u LowerHalfSpace)
  (hu_bdd : ∃ M : ℝ, ∀ p ∈ LowerHalfSpace, |u p| ≤ M)
  (hu_boundary : ∀ x : R2, u (point3 x 0) = φ x)
  (hu_decay :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z : ℝ in Filter.atBot, ∀ x : R2, |u (point3 x z)| < ε) :
  ∃ C : ℝ, 0 < C ∧
    ∀ z : ℝ, z ≤ 0 →
      ∀ x : R2, |u (point3 x z)| ≤ C * (1 + |z|)⁻¹

end MathlibExt.Analysis.Fourier.HalfSpaceLaplaceDecayEstimateWanted
