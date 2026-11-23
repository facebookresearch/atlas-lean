/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_55.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement.
Authors: Lushi Pu et al. (MA-ProofBench, arXiv:2606.13782).
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

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.RCLike.Basic

public section

namespace MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted

/-- **Lower bound from the numerical range.** Let $H$ be a complex Hilbert space with inner
product $\langle \cdot, \cdot \rangle$, conjugate-linear in the first argument and linear in the
second, and let $T : H \to H$ be a bounded linear operator. Let
$N(T) = \{\langle \psi, T\psi \rangle : \psi \in H,\ \|\psi\| = 1\} \subseteq \mathbb{C}$ be the
numerical range of $T$, and for $z \in \mathbb{C}$ let $d(z, N(T))$ be the infimum of the
distances from $z$ to the points of $N(T)$, taken to be $0$ when $N(T)$ is empty. Then for every
$\psi \in H$ and every $z \in \mathbb{C}$, $\|(T - zI)\psi\| \ge d(z, N(T))\,\|\psi\|$, where $I$
is the identity operator on $H$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_55.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem infDist_numericalRange_mul_norm_le_norm_sub_smul_apply
    (H : Type*)
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (T : H →L[ℂ] H)
    (N : Set ℂ)
    (hN : N = {w : ℂ | ∃ ψ : H, ‖ψ‖ = 1 ∧ inner ℂ ψ (T ψ) = w}) :
    ∀ ψ : H, ∀ z : ℂ,
      ‖(T - z • ContinuousLinearMap.id ℂ H) ψ‖ ≥ Metric.infDist z N * ‖ψ‖ := by
  intro ψ z
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  let u := (‖ψ‖⁻¹ : ℂ) • ψ
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hψ
  have hmem : inner ℂ u (T u) ∈ N := hN ▸ ⟨u, hu, rfl⟩
  let S := T - z • ContinuousLinearMap.id ℂ H
  apply (le_div_iff₀ (norm_pos_iff.mpr hψ)).mp
  calc
    Metric.infDist z N ≤ dist z (inner ℂ u (T u)) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖inner ℂ u (S u)‖ := by
      rw [dist_comm, dist_eq_norm]
      simp [S, hu]
    _ ≤ ‖u‖ * ‖S u‖ := norm_inner_le_norm _ _
    _ = ‖S ψ‖ / ‖ψ‖ := by simp [hu, u, norm_smul, div_eq_inv_mul]

end MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted
