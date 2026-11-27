/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_60.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement.
Authors: L. Pu et al. (MA-ProofBench).
Licensed under the MIT License:

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
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weakly bounded sets of operators are bounded

For each fixed `f`, apply Banach–Steinhaus to the functionals `g ↦ ⟪A f, g⟫` on the codomain.
Their norms are `‖A f‖`, so a second application on the domain bounds the operator norms `‖A‖`.
-/

public section

namespace MathlibExt.Analysis.OperatorTheory.WeaklyBoundedOperatorFamilyBoundedWanted

/-- **Weakly bounded sets of operators are bounded.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $H$ and $K$ be Hilbert spaces over $\mathbb{K}$, and let $Q$ be a set of
bounded linear operators from $H$ to $K$. Suppose $Q$ is weakly bounded: for every $f \in H$
and $g \in K$ there is a real number $\alpha$ such that $|\langle A f, g \rangle| \le \alpha$
for all $A \in Q$. Then $Q$ is bounded in operator norm: there is a real number $M$ such that
$\|A\| \le M$ for all $A \in Q$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_60.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_bound_opNorm_of_forall_inner_bounded (𝕜 : Type*) [RCLike 𝕜]
    (H K : Type*) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (Q : Set (H →L[𝕜] K))
    (hQ : ∀ f : H, ∀ g : K, ∃ α : ℝ, ∀ A : H →L[𝕜] K, A ∈ Q → ‖inner 𝕜 (A f) g‖ ≤ α) :
    ∃ M : ℝ, ∀ A : H →L[𝕜] K, A ∈ Q → ‖A‖ ≤ M := by
  have hpoint (f : H) : ∃ C : ℝ, ∀ A : Q, ‖A.val f‖ ≤ C := by
    have hcoeff (g : K) : ∃ C : ℝ, ∀ A : Q, ‖innerSL 𝕜 (A.val f) g‖ ≤ C := by
      obtain ⟨C, hC⟩ := hQ f g
      exact ⟨C, fun A ↦ hC A A.property⟩
    simpa only [innerSL_apply_norm] using
      (banach_steinhaus (g := fun A : Q ↦ innerSL 𝕜 (A.val f)) hcoeff)
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun A : Q ↦ A.val) hpoint
  exact ⟨M, fun A hA ↦ hM ⟨A, hA⟩⟩

end MathlibExt.Analysis.OperatorTheory.WeaklyBoundedOperatorFamilyBoundedWanted
