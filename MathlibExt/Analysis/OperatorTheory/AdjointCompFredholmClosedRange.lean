/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_23.lean` (openbmb/ma-proofbench, commit 31bab4c).
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

The theorem statement is adapted from this problem using Mathlib's Fredholm predicate.

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
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import MathlibExt.Analysis.InnerProductSpace.ClosedRangeAdjoint

/-!
# Closed range from a Fredholm Gram operator

If the range of `T† ∘L T` is closed, it equals the orthogonal complement of its kernel.
Since this kernel equals the kernel of `T`, the range of `T† ∘L T` contains the closure
of the range of `T†`. The closed range theorem for adjoints then applies.
-/

public section

open scoped InnerProduct

namespace MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted

/-- **Closed range from a Fredholm $T^*T$.** Let $X$ and $Y$ be complex Hilbert spaces and let
$T : X \to Y$ be a bounded linear operator with Hilbert space adjoint $T^* : Y \to X$. If
$T^*T : X \to X$ is a Fredholm operator, then the range of $T$ is closed in $Y$.

Here a Fredholm operator is a bounded linear operator that is open onto its range, whose range is
closed and of finite codimension, and whose kernel is finite-dimensional and has a closed
complement. The source asks only for a finite-dimensional kernel and a range of finite
codimension; between Hilbert spaces the two agree, since a finite-codimensional range of a bounded
operator is closed.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_23.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
theorem isClosed_range_of_isFredholm_adjoint_comp {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (T : X →L[ℂ] Y)
    (hFredholm : (ContinuousLinearMap.adjoint T ∘L T).IsFredholm) :
    IsClosed (LinearMap.range T.toLinearMap : Set Y) := by
  apply T.isClosed_range_adjoint_iff.mpr
  apply isClosed_of_closure_subset
  change T†.range.topologicalClosure ≤ T†.range
  calc
    T†.range.topologicalClosure = T.kerᗮ := T.orthogonal_ker.symm
    _ = (T† ∘L T).kerᗮ := by rw [T.ker_adjoint_comp_self]
    _ = (T† ∘L T).range := by
      rw [ContinuousLinearMap.orthogonal_ker, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint,
        hFredholm.isClosed_range.submodule_topologicalClosure_eq]
    _ ≤ T†.range := LinearMap.range_comp_le_range ..

end MathlibExt.Analysis.OperatorTheory.AdjointCompFredholmClosedRangeWanted
