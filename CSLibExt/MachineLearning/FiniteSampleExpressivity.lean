/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Order.Basic

/-!
# Finite-sample expressivity of two-layer ReLU networks

A two-layer network with ReLU activations, `c(x) = ∑ⱼ wⱼ max(⟪a, x⟫ - bⱼ, 0)` on a real inner
product space `E`, with `n` hidden units, a direction `a ∈ E` and `b, w ∈ ℝ^n` (`2 n + d` weights
when `E = ℝ^d`), can represent any function on a sample of
`n` distinct points (C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep
learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Theorem 1). The proof
projects the points on a direction `a` that separates them and interleaves thresholds with the
projections, so that the matrix `[max(xᵢ - bⱼ, 0)]` is lower triangular with a positive diagonal
(ibid., Appendix C, Lemma 1).

Such networks can therefore fit any labelling of a training sample, random labels included, so
uniform convergence over all networks of this size gives no useful guarantee at sample size `n`;
this is the starting point of the paper.

## Main definitions

- `reluNet a b w x`: the two-layer ReLU network `∑ⱼ wⱼ max(⟪a, x⟫ - bⱼ, 0)`.

## Main results

- `det_relu_matrix_ne_zero`: Lemma 1 (full rank of the interleaved ReLU matrix).
- `exists_reluNet_eq`: Theorem 1, for distinct sample points in a real inner product space.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace CSLibExt.MachineLearning.FiniteSampleExpressivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Two-layer ReLU network.** The function `c(x) = ∑ⱼ wⱼ max(⟪a, x⟫ - bⱼ, 0)` computed by a
network with one hidden layer of `m` ReLU units sharing the input weight vector `a`, with biases
`b` and output weights `w`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Appendix C, proof of Theorem 1
(the function `c`). -/
noncomputable def reluNet {m : ℕ} (a : E) (b w : Fin m → ℝ) (x : E) : ℝ :=
  ∑ j, w j * max (⟪a, x⟫_ℝ - b j) 0

/-- **The interleaved ReLU matrix has full rank.** If `bᵢ < xᵢ` for every `i` and `xᵢ < bⱼ`
whenever `i < j` (the interleaving `b₁ < x₁ < b₂ < x₂ < ⋯ < bₙ < xₙ`), then the matrix
`A = [max(xᵢ - bⱼ, 0)]ᵢⱼ` is lower triangular with positive diagonal, so `det A ≠ 0`.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Appendix C, Lemma 1 (first
claim; the eigenvalue claim is not formalized here). -/
theorem det_relu_matrix_ne_zero {n : ℕ} (x b : Fin n → ℝ) (hdiag : ∀ i, b i < x i)
    (hlow : ∀ i j, i < j → x i < b j) :
    (Matrix.of fun i j => max (x i - b j) 0).det ≠ 0 := by
  have hL : (Matrix.of fun i j => max (x i - b j) 0).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.of_apply]
    exact max_eq_right (by linarith [hlow i j hij'])
  rw [hL.det_ne_zero_iff]
  intro i
  simp only [Matrix.diag_apply, Matrix.of_apply]
  exact (lt_max_of_lt_left (sub_pos.mpr (hdiag i))).ne'

/-- A direction on which distinct points have distinct projections. -/
private theorem exists_inner_injective {n : ℕ} {x : Fin n → E} (hx : Function.Injective x) :
    ∃ a : E, Function.Injective fun i => ⟪a, x i⟫_ℝ := by
  let ι := {p : Fin n × Fin n // p.1 ≠ p.2}
  let p : ι → Submodule ℝ E := fun q => (ℝ ∙ (x q.1.1 - x q.1.2))ᗮ
  have hp : ∀ q, p q ≠ ⊤ := by
    intro q htop
    have hmem : x q.1.1 - x q.1.2 ∈ p q := by rw [htop]; trivial
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hmem
    have hne : x q.1.1 - x q.1.2 ≠ 0 := sub_ne_zero.mpr (hx.ne q.2)
    exact hne (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hmem))
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨a, fun i j hij => ?_⟩
  by_contra hne
  apply ha ⟨(i, j), hne⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm, inner_sub_right]
  simpa [sub_eq_zero] using hij

/-- **Finite-sample expressivity of two-layer ReLU networks.** Let `x₁, …, xₙ` be distinct points
of a real inner product space `E` and `y ∈ ℝⁿ` any targets. Then there are a direction `a ∈ E`
and `b, w ∈ ℝⁿ` such that the two-layer ReLU network `c(x) = ∑ⱼ wⱼ max(⟪a, x⟫ - bⱼ, 0)`
(`reluNet`) satisfies `c(xᵢ) = yᵢ` for every `i`. In `ℝ^d` the network has `2 n + d` weights.

Source: C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning
requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Theorem 1 (stated for samples
`S ⊆ ℝ^d` with `|S| = n`, that is, `n` distinct points, as here; the proof in Appendix C works in
any real inner product space). -/
theorem exists_reluNet_eq {n : ℕ} {x : Fin n → E} (hx : Function.Injective x) (y : Fin n → ℝ) :
    ∃ (a : E) (b w : Fin n → ℝ), ∀ i, reluNet a b w (x i) = y i := by
  obtain ⟨a, ha⟩ := exists_inner_injective hx
  set z : Fin n → ℝ := fun i => ⟪a, x i⟫_ℝ with hz
  -- a margin smaller than every gap between distinct projections
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ q : {p : Fin n × Fin n // p.1 ≠ p.2},
      δ < |z q.1.1 - z q.1.2| := by
    rw [eventually_all]
    intro q
    have hpos : 0 < |z q.1.1 - z q.1.2| := abs_pos.mpr (sub_ne_zero.mpr (ha.ne q.2))
    exact (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδgap, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδpos' : 0 < δ := hδpos
  set b : Fin n → ℝ := fun j => z j - δ with hb
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => max (z i - b j) 0 with hA
  -- `A` is invertible: sorting the projections makes it lower triangular
  have hdet : A.det ≠ 0 := by
    set σ := Tuple.sort z
    have hmono : StrictMono (z ∘ σ) :=
      (Tuple.monotone_sort z).strictMono_of_injective (ha.comp σ.injective)
    have hsub : A.submatrix σ σ = Matrix.of fun i j => max ((z ∘ σ) i - (b ∘ σ) j) 0 := by
      ext i j; simp [hA]
    rw [← Matrix.det_submatrix_equiv_self σ, hsub]
    refine det_relu_matrix_ne_zero _ _ (fun i => by simp [hb, hδpos']) (fun i j hij => ?_)
    have hlt : z (σ i) < z (σ j) := hmono hij
    have hgap := hδgap ⟨(σ j, σ i), fun h => (σ.injective h ▸ hij).false⟩
    simp only at hgap
    rw [abs_of_pos (sub_pos.mpr hlt)] at hgap
    simp only [Function.comp_apply, hb]
    linarith
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨a, b, A⁻¹.mulVec y, fun i => ?_⟩
  have hsol : A.mulVec (A⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  have hi := congrFun hsol i
  rw [← hi]
  simp only [reluNet, Matrix.mulVec, dotProduct, hA, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end CSLibExt.MachineLearning.FiniteSampleExpressivity
