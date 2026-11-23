/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_49.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement and its informal description.
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

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

public import Mathlib.Analysis.InnerProductSpace.Calculus
import MathlibExt.Analysis.InnerProductSpace.NormDerivative

/-!
# Velocity of a unit-norm curve

The orthogonality of velocity and position on the unit sphere specializes to Euclidean three-space.
-/

public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.Calculus.UnitNormCurveDerivOrthogonalWanted

open MathlibExt.Analysis.InnerProductSpace.NormDerivative

/-- **A unit-norm curve in $\mathbb{R}^3$ is orthogonal to its derivative.** Let
$f : \mathbb{R} \to \mathbb{R}^3$ be a differentiable map such that $\|f(t)\| = 1$ for every real
$t$, where $\|\cdot\|$ is the Euclidean norm. Then $\langle f'(t), f(t) \rangle = 0$ for every
real $t$, where $\langle \cdot, \cdot \rangle$ is the standard inner product on $\mathbb{R}^3$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_49.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem inner_deriv_self_eq_zero_of_norm_eq_one
    (f : ℝ → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f) (hnorm : ∀ t : ℝ, ‖f t‖ = 1) :
    ∀ t : ℝ, ⟪deriv f t, f t⟫_ℝ = 0 := by
  intro t
  rw [real_inner_comm]
  exact re_inner_self_deriv_eq_zero_of_forall_norm_eq_one (K := ℝ) hf hnorm t

end MathlibExt.Analysis.Calculus.UnitNormCurveDerivOrthogonalWanted
