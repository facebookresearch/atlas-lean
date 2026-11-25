/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_55.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the statement of
`infDist_numericalRange_mul_norm_le_norm_sub_smul_apply`.
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

public import MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Lower bound from the numerical range

For a bounded linear operator `T` on a complex inner product space, the values `⟪ψ, T ψ⟫` at
unit vectors `ψ` form the numerical range of `T`. For every vector `ψ` and every `z : ℂ`, the
distance from `z` to this set, times `‖ψ‖`, is at most `‖(T - z • id) ψ‖`.

`ToeplitzHausdorffWanted.numericalRange T` collects instead the values `⟪T x, x⟫` at unit
vectors `x`. Since Mathlib's inner product is conjugate-linear in its first argument, these are
the complex conjugates of the values `⟪x, T x⟫`, so in terms of that set the bound reads
`infDist (conj z) (numericalRange T) * ‖ψ‖ ≤ ‖(T - z • id) ψ‖`.

## Main statements

* `infDist_conj_numericalRange_mul_norm_le_norm_sub_smul_apply`: the bound in terms of
  `ToeplitzHausdorffWanted.numericalRange`, on every complex inner product space.
* `infDist_numericalRange_mul_norm_le_norm_sub_smul_apply`: the MA-ProofBench statement, with
  the numerical range written as the set of values `⟪ψ, T ψ⟫` at unit vectors `ψ`. It follows
  from the first, and keeps the source's hypothesis `CompleteSpace H`, which its proof does not
  use.
-/

public section

namespace MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted

open scoped ComplexConjugate
open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted
  (numericalRange inner_mem_numericalRange)

/-- **Lower bound from the numerical range, conjugate form.** Let $H$ be a complex inner
product space, whose inner product $\langle \cdot, \cdot \rangle$ is conjugate-linear in its
first argument and linear in its second, let $T : H \to H$ be a bounded linear operator and let
$W(T) = \{\langle T x, x \rangle : x \in H,\ \|x\| = 1\} \subseteq \mathbb{C}$ be its numerical
range. For $z \in \mathbb{C}$ let $d(\overline{z}, W(T))$ be the infimum of the distances from
the complex conjugate $\overline{z}$ to the points of $W(T)$, taken to be $0$ when $W(T)$ is
empty. Then for every $\psi \in H$, $d(\overline{z}, W(T))\,\|\psi\| \le \|(T - zI)\psi\|$,
where $I$ is the identity operator on $H$. The space $H$ need not be complete.

The conjugate appears because $\langle T x, x \rangle$ is the complex conjugate of
$\langle x, T x \rangle$: $W(T)$ is the complex conjugate of the set
$\{\langle x, T x \rangle : \|x\| = 1\}$ used in
`infDist_numericalRange_mul_norm_le_norm_sub_smul_apply`. -/
theorem infDist_conj_numericalRange_mul_norm_le_norm_sub_smul_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (ψ : H) (z : ℂ) :
    Metric.infDist (conj z) (numericalRange T) * ‖ψ‖ ≤
      ‖(T - z • ContinuousLinearMap.id ℂ H) ψ‖ := by
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  let u := (‖ψ‖⁻¹ : ℂ) • ψ
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hψ
  let S := T - z • ContinuousLinearMap.id ℂ H
  rw [← le_div_iff₀ (norm_pos_iff.mpr hψ)]
  calc
    Metric.infDist (conj z) (numericalRange T) ≤ dist (conj z) (inner ℂ (T u) u) :=
      Metric.infDist_le_dist_of_mem (inner_mem_numericalRange T hu)
    _ = ‖inner ℂ (S u) u‖ := by
      rw [dist_comm, dist_eq_norm]
      simp [S, hu]
    _ ≤ ‖S u‖ * ‖u‖ := norm_inner_le_norm _ _
    _ = ‖S ψ‖ / ‖ψ‖ := by simp [hu, u, norm_smul, div_eq_inv_mul]

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
  have hN' : N = conj '' numericalRange T := by
    rw [hN]
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, inner_mem_numericalRange T hx, inner_conj_symm _ _⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (inner_conj_symm _ _).symm⟩
  have hdist : Metric.infDist z N = Metric.infDist (conj z) (numericalRange T) := by
    rw [hN', ← Metric.infDist_image Complex.isometry_conj (x := conj z), Complex.conj_conj]
  rw [ge_iff_le, hdist]
  exact infDist_conj_numericalRange_mul_norm_le_norm_sub_smul_apply T ψ z

end MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted
