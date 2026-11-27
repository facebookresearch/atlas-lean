/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_42.lean` (openbmb/ma-proofbench at commit
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

Attribution and modification notice: the statement of
`not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace` below is taken from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_42.lean` (MA-ProofBench, L. Pu et al., *MA-ProofBench: A
Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench), distributed under the MIT
License above. Changes made: converted the benchmark theorem `ma_proofbench_l2_42`, whose proof
there is a placeholder, into the Batteries wanted-theorem declaration
`not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace` (a statement without a
proof); moved the informal problem statement docstring onto it and placed the declarations in
namespace `MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparableWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system. Further changes in this
file: that wanted declaration is now a `theorem` with a proof, and `public import Mathlib` is
replaced by narrower imports; the statement and its docstring are unchanged.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Kernel of a compact operator on a nonseparable Hilbert space

Let `A` be a compact operator on a complex Hilbert space `H`. If `H` is not separable, then
neither is the kernel of `A`.

The range of a compact operator is separable: it is covered by the images of the balls of radius
`n : ℕ`, each of which lies in a compact set. The operator `A† ∘L A` is compact and self-adjoint
and has the same kernel as `A`, so `(ker A)ᗮ` is the closure of its range and is separable. If
`ker A` were separable too, then so would be `H = ker A ⊔ (ker A)ᗮ`, which is spanned by the
union of these two separable sets.

## Main statements

* `not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace`: the result above.
  This is the MA-ProofBench problem `ma_proofbench_l2_42`, formerly a `WantedExt` entry.

## Implementation notes

`Mathlib.Analysis.InnerProductSpace.Basic` and `Mathlib.Analysis.Normed.Operator.Compact.Basic`,
which provide complex inner product spaces and `IsCompactOperator`, are imported publicly; under
them the statement elaborates to the same term as under `import Mathlib`, where it was first
stated. `Mathlib.Analysis.InnerProductSpace.Adjoint`, which only the proof uses, is imported
privately.

## References

* L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem Proving in
  Mathematical Analysis*, arXiv:2606.13782, Level II, problem `ma_proofbench_l2_42`.
-/

@[expose] public section

open TopologicalSpace

namespace MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparableWanted

/-- The range of a compact operator between normed spaces is separable: it is covered by the
images of the balls of radius `n : ℕ`, each of which lies in a compact set. -/
private theorem isSeparable_range_of_isCompactOperator {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsSeparable (Set.range T) := by
  have hball (n : ℕ) : IsSeparable (T '' Metric.ball 0 n) := by
    obtain ⟨K, hK, hTK⟩ := hT.image_ball_subset_compact (f := T.toLinearMap) n
    exact hK.isSeparable.mono hTK
  refine (IsSeparable.iUnion hball).mono ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact Set.mem_iUnion.2 ⟨n, x, mem_ball_zero_iff.2 hn, rfl⟩

/-- **The kernel of a compact operator on a nonseparable Hilbert space is nonseparable.** Let
$H$ be a complex Hilbert space that is not separable and let $A : H \to H$ be a compact operator.
Then the kernel $\ker A$ is not separable.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Special
classes of linear operators), `benchmark/level2/ma_proofbench_l2_42.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem not_separableSpace_ker_of_isCompactOperator_of_not_separableSpace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H)
    (hH : ¬ SeparableSpace H)
    (hA : IsCompactOperator A) :
    ¬ SeparableSpace (A.ker) := by
  intro hK
  -- `A† ∘L A` is self-adjoint and has the same kernel as `A`, so `(ker A)ᗮ` is the closure of
  -- its range, which is separable since `A† ∘L A` is compact.
  have hperp : A.kerᗮ = (A.adjoint ∘L A).range.topologicalClosure := by
    rw [← ContinuousLinearMap.ker_adjoint_comp_self A, ContinuousLinearMap.orthogonal_ker,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hsep₁ : IsSeparable (A.ker : Set H) := .of_subtype _
  have hsep₂ : IsSeparable (A.kerᗮ : Set H) := by
    rw [hperp, Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact (isSeparable_range_of_isCompactOperator (hA.clm_comp A.adjoint)).closure
  -- So `H = ker A ⊔ (ker A)ᗮ`, the span of the union of two separable sets, is separable.
  refine hH (isSeparable_univ_iff.1 ?_)
  have h := (hsep₁.union hsep₂).span (R := ℂ)
  rwa [Submodule.span_union, Submodule.span_eq, Submodule.span_eq,
    Submodule.sup_orthogonal_of_hasOrthogonalProjection, Submodule.top_coe] at h

end MathlibExt.Analysis.OperatorTheory.CompactOperatorKernelNonseparableWanted
