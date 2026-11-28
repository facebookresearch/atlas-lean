/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_22.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; MA-ProofBench, L. Pu et al., arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_22.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted the
benchmark theorem `ma_proofbench_l1_22`, whose proof there is a placeholder, into the Batteries
wanted-theorem declaration `exists_bound_of_symmetric_linearMap_to_strongDual` (a statement
without a proof); moved the informal problem statement docstring onto it and placed the
declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system. Further changes in this file: that
wanted declaration is now a `theorem` with a proof, its docstring is restated, and `public import
Mathlib` is replaced by narrower imports; the statement itself is unchanged.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A symmetric linear map from a Banach space to its dual is bounded

Let `E` be a real Banach space and let `T : E → E*` be a linear map into the strong dual
`E* = StrongDual ℝ E` that is symmetric: `(T x) y = (T y) x` for all `x, y : E`. Then `T` is
bounded: there is `C ≥ 0` with `‖T x‖ ≤ C * ‖x‖` for all `x`, where `‖T x‖` is the operator
norm of the functional `T x`.

The proof is the closed graph argument of the Hellinger–Toeplitz theorem (compare Mathlib's
`LinearMap.IsSymmetric.continuous`, the case of a symmetric operator on a Hilbert space). Both
`E` and `E*` are Banach spaces. If `uₙ → x` and `T uₙ → φ` in `E*`, then for each `y : E`,
`(T uₙ) y` tends to `φ y`, and by symmetry `(T uₙ) y = (T y) uₙ` tends to `(T y) x = (T x) y`.
Hence `φ = T x`, the graph of `T` is closed, and `T` is continuous
(`LinearMap.continuous_of_seq_closed_graph`); its operator norm is a bound.

## Main results

* `exists_bound_of_symmetric_linearMap_to_strongDual`: a symmetric linear map from a real
  Banach space to its strong dual is bounded. This is the MA-ProofBench problem
  `ma_proofbench_l1_22`, formerly a `WantedExt` entry.

## Implementation notes

`Mathlib.Analysis.InnerProductSpace.Basic` is imported publicly so that the statement elaborates
to the same term as under `import Mathlib`, where it was first stated: the `NormedSpace ℝ ℝ`
instance in the operator norm `‖T x‖` is then found through the inner product space structure
`RCLike.toInnerProductSpaceReal` of `ℝ` over itself.
-/

public section

open Filter Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted

universe u

/-- **A symmetric linear map from a Banach space to its dual is bounded.** Let $E$ be a real
Banach space with dual space $E^*$ of continuous linear functionals, and let $T : E \to E^*$ be
a linear map that is symmetric: $(Tx)(y) = (Ty)(x)$ for all $x, y \in E$. Then $T$ is bounded:
there is a constant $C \ge 0$ such that $\|Tx\| \le C \|x\|$ for all $x \in E$, where $\|Tx\|$
is the operator norm of the functional $Tx$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_22.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_bound_of_symmetric_linearMap_to_strongDual
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →ₗ[ℝ] StrongDual ℝ E) (hsym : ∀ x y : E, (T x) y = (T y) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  -- The graph of `T` is sequentially closed, so `T` is continuous by the closed graph theorem.
  have hT : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun u x φ hu hTu => ?_
    ext y
    -- `(T (u n)) y` tends to `φ y`, and, being `(T y) (u n)`, also to `(T y) x = (T x) y`.
    have h₁ : Tendsto (fun n => (T (u n)) y) atTop (𝓝 (φ y)) :=
      ((ContinuousLinearMap.apply ℝ ℝ y).continuous.tendsto φ).comp hTu
    have h₂ : Tendsto (fun n => (T (u n)) y) atTop (𝓝 ((T y) x)) := by
      simp_rw [hsym _ y]
      exact ((T y).continuous.tendsto x).comp hu
    rw [tendsto_nhds_unique h₁ h₂, hsym]
  -- A continuous linear map is bounded by its operator norm.
  let S : E →L[ℝ] StrongDual ℝ E := ⟨T, hT⟩
  exact ⟨‖S‖, S.opNorm_nonneg, S.le_opNorm⟩

end MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted
