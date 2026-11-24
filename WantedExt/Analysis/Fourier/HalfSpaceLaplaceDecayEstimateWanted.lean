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

/-- **The Euclidean plane.** The Euclidean plane $\mathbb{R}^2$ is the space of pairs of real
numbers with the Euclidean inner product and norm. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)
/-- **Euclidean three-space.** Euclidean three-space $\mathbb{R}^3$ is the space of triples of
real numbers with the Euclidean inner product and norm. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **Closed lower half-space.** The closed lower half-space is the set of points
$(p_1, p_2, p_3)$ of Euclidean three-space $\mathbb{R}^3$ with $p_3 \le 0$. -/
abbrev LowerHalfSpace : Set R3 := {p : R3 | p 2 ≤ 0}
/-- **Open lower half-space.** The open lower half-space is the set of points $(p_1, p_2, p_3)$
of Euclidean three-space $\mathbb{R}^3$ with $p_3 < 0$. -/
abbrev OpenLowerHalfSpace : Set R3 := {p : R3 | p 2 < 0}

/-- **Appending a third coordinate.** For a point $x = (x_1, x_2)$ of the Euclidean plane
$\mathbb{R}^2$ and a real number $z$, this is the point $(x_1, x_2, z)$ of Euclidean three-space
$\mathbb{R}^3$. -/
noncomputable def point3 (x : R2) (z : ℝ) : R3 :=
  EuclideanSpace.single (0 : Fin 3) (x 0) +
    EuclideanSpace.single (1 : Fin 3) (x 1) +
      EuclideanSpace.single (2 : Fin 3) z

/-- **Decay of bounded harmonic extensions of Schwartz data in a half-space.** Write a point of
$\mathbb{R}^3$ as $(x, z)$ with $x = (x_1, x_2) \in \mathbb{R}^2$ and $z \in \mathbb{R}$. Let
$\phi : \mathbb{R}^2 \to \mathbb{R}$ be a Schwartz function and let
$u : \mathbb{R}^3 \to \mathbb{R}$ be harmonic at every point of the open lower half-space
$\{(x, z) : z < 0\}$, continuous on the closed lower half-space $\{(x, z) : z \le 0\}$ and bounded
there, with $u(x, 0) = \phi(x)$ for every $x \in \mathbb{R}^2$. Suppose that $u(x, z) \to 0$ as
$z \to -\infty$ uniformly in $x$: for every $\varepsilon > 0$ there is $z_0$ such that
$|u(x, z)| < \varepsilon$ for all $z \le z_0$ and all $x \in \mathbb{R}^2$. Then there is a
constant $C > 0$ such that $|u(x, z)| \le C (1 + |z|)^{-1}$ for all $z \le 0$ and all
$x \in \mathbb{R}^2$.

Boundedness of $u$ is not among the hypotheses of the source problem, but the bound fails without
it: adding to the Poisson extension of $\phi$ the harmonic function $\operatorname{Im} G(x_1 + iz)$
built from Newman's entire function $G$, which vanishes on $z = 0$ and as $z \to -\infty$ but is
unbounded near the boundary, gives a counterexample.

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
