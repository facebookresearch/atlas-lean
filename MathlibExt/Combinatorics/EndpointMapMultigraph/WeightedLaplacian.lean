/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.OrientedIncidence
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted Laplacians of finite multigraphs

For a finite multigraph given by endpoint maps `end₁ end₂ : E → V` and real edge weights
`w : E → ℝ`, the weighted Laplacian is `L = B · diag(w) · Bᵀ`, where `B` is the oriented
incidence matrix of `MathlibExt.Combinatorics.EndpointMapMultigraph.OrientedIncidence`. This is
the matrix `L_G = ∑_{(a,b) ∈ E} w_{a,b} (δ_a - δ_b)(δ_a - δ_b)ᵀ` of D. A. Spielman, *Spectral
and Algebraic Graph Theory* (draft of 2 April 2025), equation (3.3). Parallel edges add their
weights; a loop has a zero incidence column and contributes nothing.

Main results:

* `dotProduct_mulVec_laplacian`: the Laplacian quadratic form
  `xᵀ L x = ∑_e w_e (x(end₁ e) - x(end₂ e))²` (Spielman, (3.1));
* `laplacian_mulVec_one`: constant vectors lie in the kernel;
* `posSemidef_laplacian`: nonnegative weights give a positive semidefinite Laplacian;
* `posSemidef_laplacian_sub_of_le`: raising weights raises the Laplacian in the Loewner order
  (Spielman, Section 6.2);
* `laplacian_mulVec_eq_zero_iff`, `rank_laplacian_add_card_connectedComponent`: with positive
  weights and no loops, the kernel consists of the vectors constant on connected components, so
  rank plus the number of components equals the number of vertices;
* `indicator_dotProduct_mulVec_laplacian`: the quadratic form of the indicator of `S` is the
  weight of the cut of `S`;
* `mul_card_mul_card_compl_le_of_forall`: the easy direction of Cheeger's inequality, stated for
  any lower bound on Rayleigh quotients over vectors orthogonal to the constants
  (Spielman, Theorem 20.1.1).
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] (end₁ end₂ : E → V)

/-- **Weighted Laplacian of a multigraph.** For endpoint maps `end₁ end₂ : E → V` and edge weights
`w : E → ℝ`, the matrix `B · diag(w) · Bᵀ` where `B` is the oriented incidence matrix; it equals
`∑_e w_e (δ_{end₁ e} - δ_{end₂ e})(δ_{end₁ e} - δ_{end₂ e})ᵀ` (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, equation (3.3)). -/
noncomputable def laplacian (w : E → ℝ) : Matrix V V ℝ :=
  orientedIncidence end₁ end₂ * diagonal w * (orientedIncidence end₁ end₂)ᵀ

/-- **The weighted Laplacian is symmetric.** -/
theorem laplacian_transpose (w : E → ℝ) : (laplacian end₁ end₂ w)ᵀ = laplacian end₁ end₂ w := by
  simp [laplacian, Matrix.transpose_mul, Matrix.mul_assoc]

/-- **The weighted Laplacian is additive in the weights.** -/
theorem laplacian_add (w w' : E → ℝ) :
    laplacian end₁ end₂ (w + w') = laplacian end₁ end₂ w + laplacian end₁ end₂ w' := by
  rw [laplacian, laplacian, laplacian,
    show diagonal (w + w') = diagonal w + diagonal w' from (Matrix.diagonal_add _ _).symm,
    Matrix.mul_add, Matrix.add_mul]

/-- **The weighted Laplacian is linear in the weights: subtraction.** -/
theorem laplacian_sub (w w' : E → ℝ) :
    laplacian end₁ end₂ (w - w') = laplacian end₁ end₂ w - laplacian end₁ end₂ w' := by
  rw [laplacian, laplacian, laplacian,
    show diagonal (w - w') = diagonal w - diagonal w' from (Matrix.diagonal_sub _ _).symm,
    Matrix.mul_sub, Matrix.sub_mul]

variable [Fintype V]

/-- **Laplacian quadratic form.** For every real vector `x`,
`xᵀ L x = ∑_e w_e (x(end₁ e) - x(end₂ e))²` (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, equation (3.1)). -/
theorem dotProduct_mulVec_laplacian (w : E → ℝ) (x : V → ℝ) :
    x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) = ∑ e, w e * (x (end₁ e) - x (end₂ e)) ^ 2 := by
  have h : x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) =
      (x ᵥ* orientedIncidence end₁ end₂) ⬝ᵥ
        (diagonal w *ᵥ (x ᵥ* orientedIncidence end₁ end₂)) := by
    rw [laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
  rw [h]
  simp only [dotProduct, mulVec_diagonal, vecMul_orientedIncidence_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **Constants are in the kernel of the Laplacian.** `L 1 = 0`. -/
theorem laplacian_mulVec_one (w : E → ℝ) : laplacian end₁ end₂ w *ᵥ 1 = 0 := by
  have h : (orientedIncidence end₁ end₂)ᵀ *ᵥ (1 : V → ℝ) = 0 := by
    funext e
    rw [Matrix.mulVec_transpose, vecMul_orientedIncidence_apply]
    simp
  rw [laplacian, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

omit [Fintype V] in
/-- **The Laplacian of nonnegative weights is positive semidefinite** (D. A. Spielman, *Spectral
and Algebraic Graph Theory*, draft of 2 April 2025, Section 3.1: the quadratic form (3.1) is a sum
of nonnegative terms). -/
theorem posSemidef_laplacian [Finite V] {w : E → ℝ} (hw : 0 ≤ w) :
    (laplacian end₁ end₂ w).PosSemidef := by
  have := Fintype.ofFinite V
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · simpa [Matrix.IsHermitian] using laplacian_transpose end₁ end₂ w
  · rw [star_trivial, dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)

omit [Fintype V] in
/-- **Loewner monotonicity in the weights.** If `w ≤ w'` edgewise then `L_{w'} - L_w` is positive
semidefinite: increasing edge weights (in particular adding edges) can only increase the
Laplacian in the Loewner order (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of
2 April 2025, Section 6.2). -/
theorem posSemidef_laplacian_sub_of_le [Finite V] {w w' : E → ℝ} (h : w ≤ w') :
    (laplacian end₁ end₂ w' - laplacian end₁ end₂ w).PosSemidef := by
  rw [← laplacian_sub]
  exact posSemidef_laplacian end₁ end₂ (sub_nonneg.mpr h)

/-- **Kernel of the Laplacian.** For a loopless finite multigraph with positive edge weights, a
real vector `x` satisfies `L x = 0` if and only if `x` is constant on each connected component
(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, proof of Lemma
3.1.1). -/
theorem laplacian_mulVec_eq_zero_iff {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) (x : V → ℝ) :
    laplacian end₁ end₂ w *ᵥ x = 0 ↔
      ∀ u v, (underlyingGraph end₁ end₂).Reachable u v → x u = x v := by
  rw [← vecMul_orientedIncidence_eq_zero_iff end₁ end₂ hloop]
  constructor
  · intro hx
    have hq : ∑ e, w e * (x (end₁ e) - x (end₂ e)) ^ 2 = 0 := by
      rw [← dotProduct_mulVec_laplacian, hx, dotProduct_zero]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e _ => mul_nonneg (hw e).le (sq_nonneg (x (end₁ e) - x (end₂ e))))).1 hq
    funext e
    have he := hterm e (Finset.mem_univ e)
    rw [vecMul_orientedIncidence_apply, Pi.zero_apply]
    rcases mul_eq_zero.1 he with h | h
    · exact absurd h (hw e).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
  · intro hx
    rw [laplacian, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, hx, Matrix.mulVec_zero]

/-- **Rank of the Laplacian plus number of components.** For a loopless finite multigraph with
positive edge weights, the rank of its weighted Laplacian plus the number of connected components
equals the number of vertices; equivalently the multiplicity of the eigenvalue `0` is the number
of components. This extends D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April
2025, Lemma 3.1.1, whose proof shows that for a connected graph the constants span the kernel. -/
theorem rank_laplacian_add_card_connectedComponent {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) :
    (laplacian end₁ end₂ w).rank +
        Nat.card (underlyingGraph end₁ end₂).ConnectedComponent = Fintype.card V := by
  classical
  set B := orientedIncidence end₁ end₂
  set D : Matrix E E ℝ := diagonal fun e => Real.sqrt (w e)
  have hD : IsUnit D.det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun e _ => (Real.sqrt_pos.2 (hw e)).ne'
  have hL : laplacian end₁ end₂ w = (B * D) * (B * D)ᵀ := by
    have hDD : D * Dᵀ = diagonal w := by
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext e
      exact Real.mul_self_sqrt (hw e).le
    rw [laplacian, ← hDD, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, B]
  rw [hL, Matrix.rank_self_mul_transpose, Matrix.rank_mul_eq_left_of_isUnit_det D B hD]
  exact rank_orientedIncidence_add_card_connectedComponent end₁ end₂ hloop

/-- **Indicator vector of a vertex set.** The real vector equal to `1` on `S` and `0` off `S`. -/
def indicator (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

/-- **Quadratic form of an indicator is the cut weight.** For every vertex set `S`,
`1_Sᵀ L 1_S` is the total weight of the edges with exactly one endpoint in `S`
(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, proof of Theorem
20.1.1). -/
theorem indicator_dotProduct_mulVec_laplacian (w : E → ℝ) (S : Finset V) :
    indicator S ⬝ᵥ (laplacian end₁ end₂ w *ᵥ indicator S) = ∑ e ∈ cut end₁ end₂ S, w e := by
  classical
  rw [dotProduct_mulVec_laplacian, cut, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h₁ : end₁ e ∈ S <;> by_cases h₂ : end₂ e ∈ S <;> simp [indicator, h₁, h₂]

/-- **Easy direction of Cheeger's inequality.** Let `λ` be a lower bound for the Rayleigh quotient
`xᵀ L x / xᵀ x` over all nonzero `x` orthogonal to the constant vector (the second-smallest
Laplacian eigenvalue is the best such bound, by Courant–Fischer). Then for every vertex set `S`,
`λ · |S| · |V \ S| ≤ |V| · w(∂S)`, where `w(∂S)` is the weight of the cut of `S`. With `s = |S|/|V|`
this is `w(∂S)/|S| ≥ λ (1 - s)`, D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2
April 2025, Theorem 20.1.1 (stated there for unit weights); in particular `θ_G ≥ λ/2`. -/
theorem mul_card_mul_card_compl_le_of_forall (w : E → ℝ) {lam : ℝ}
    (hlam : ∀ x : V → ℝ, x ⬝ᵥ 1 = 0 → lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x))
    (S : Finset V) :
    lam * S.card * (Finset.univ \ S).card ≤
      (Fintype.card V : ℝ) * ∑ e ∈ cut end₁ end₂ S, w e := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  set s : ℝ := (S.card : ℝ) with hs_def
  have hcompl : ((Finset.univ \ S).card : ℝ) = n - s := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.cast_sub (Finset.card_le_univ S)]
  set x : V → ℝ := n • indicator S - s • (1 : V → ℝ) with hx
  have hsum1 : indicator S ⬝ᵥ (1 : V → ℝ) = s := by
    simp [indicator, dotProduct, Finset.sum_ite_mem, s]
  have hone : (1 : V → ℝ) ⬝ᵥ (1 : V → ℝ) = n := by simp [dotProduct, n]
  have hxo : x ⬝ᵥ 1 = 0 := by
    rw [hx, sub_dotProduct, smul_dotProduct, smul_dotProduct, hsum1, hone, smul_eq_mul,
      smul_eq_mul]
    ring
  have hind : indicator S ⬝ᵥ indicator S = s := by
    simp [indicator, dotProduct, Finset.sum_ite_mem, s]
  have hxx : x ⬝ᵥ x = n * s * (n - s) := by
    rw [hx]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hind, hsum1, hone, dotProduct_comm (1 : V → ℝ) (indicator S)]
    ring
  have hLx : laplacian end₁ end₂ w *ᵥ x = n • (laplacian end₁ end₂ w *ᵥ indicator S) := by
    rw [hx, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, laplacian_mulVec_one,
      smul_zero, sub_zero]
  have hxLx : x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) = n ^ 2 * ∑ e ∈ cut end₁ end₂ S, w e := by
    have hsym : (1 : V → ℝ) ⬝ᵥ (laplacian end₁ end₂ w *ᵥ indicator S) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose,
        laplacian_mulVec_one, zero_dotProduct]
    rw [hLx, dotProduct_smul, hx, sub_dotProduct, smul_dotProduct, smul_dotProduct, hsym,
      indicator_dotProduct_mulVec_laplacian, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have key := hlam x hxo
  rw [hxx, hxLx] at key
  rw [hcompl]
  rcases (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ n).eq_or_lt with hn | hn
  · -- no vertices: `S` is empty
    have hsn : s ≤ n := Nat.cast_le.2 (Finset.card_le_univ S)
    have hs : s = 0 := le_antisymm (hn ▸ hsn) (Nat.cast_nonneg _)
    have hn0 : n = 0 := hn.symm
    rw [hs, hn0]
    simp
  · have : n * (lam * s * (n - s)) ≤ n * (n * ∑ e ∈ cut end₁ end₂ S, w e) := by
      nlinarith [key]
    exact le_of_mul_le_mul_left this hn

end EndpointMapMultigraph
