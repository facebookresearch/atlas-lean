/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_85.lean` (openbmb/ma-proofbench, commit 31bab4c).
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

The theorem statement and its informal description are adapted from this problem.

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
import MathlibExt.Analysis.InnerProductSpace.ClosedRangeAdjoint

/-!
# Closed range of the Hilbert space adjoint

A bounded linear map between complex Hilbert spaces with closed range has an adjoint
with closed range.
-/

public section

namespace MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted

/-- **Closed range passes to the Hilbert space adjoint.** Let $X$ and $Y$ be complex Hilbert spaces
and let $A : X \to Y$ be a bounded linear operator with Hilbert space adjoint $A^* : Y \to X$. If
the range of $A$ is closed in $Y$, then the range of $A^*$ is closed in $X$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_85.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem isClosed_range_adjoint_of_isClosed_range {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : X →L[ℂ] Y)
    (hRan : IsClosed (LinearMap.range A.toLinearMap : Set Y)) :
    IsClosed (LinearMap.range A.adjoint.toLinearMap : Set X) :=
  A.isClosed_range_adjoint_of_isClosed_range hRan

end MathlibExt.Analysis.OperatorTheory.HilbertAdjointClosedRangeWanted
