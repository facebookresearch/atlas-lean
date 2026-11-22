/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import MathlibExt.Analysis.InnerProductSpace.CourantFischer
public import Mathlib.Analysis.Matrix.Hermitian

import MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic connectivity of a weighted multigraph

The second-smallest eigenvalue `λ₂` of the weighted Laplacian `L` of a finite multigraph
(`MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian`), defined through the
eigenvalues of the symmetric operator `toEuclideanLin L` on `EuclideanSpace ℝ V`, listed in
decreasing order. This file connects the graph to the Courant–Fischer theorem of
`MathlibExt.Analysis.InnerProductSpace.CourantFischer`:

* `algebraicConnectivity_mul_le`: `λ₂ ‖x‖² ≤ xᵀ L x` for every `x` orthogonal to the constants
  (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 3.2, from
  Theorem 2.0.1);
* `algebraicConnectivity_mul_card_mul_card_compl_le`: the easy direction of Cheeger's inequality,
  `λ₂ |S| |V \ S| ≤ |V| w(∂S)` (Spielman, Theorem 20.1.1, weighted form);
* `algebraicConnectivity_pos_iff`: for positive weights and at least two vertices, `λ₂ > 0` if
  and only if the multigraph is connected (Spielman, Lemma 3.1.1);
* `eigenvalues_laplacian_le_of_posSemidef`, `eigenvalues_laplacian_mono`,
  `algebraicConnectivity_mono`: Laplacian eigenvalues are monotone in the Loewner order and in the
  weights (Spielman, Lemma 6.2.1 and Corollary 6.2.2), from Weyl's inequality.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix MathlibExt.Analysis.InnerProductSpace.CourantFischer
open scoped InnerProductSpace

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]
  (end₁ end₂ : E → V)

/-- **The Laplacian as a symmetric operator.** The Euclidean-space operator of the weighted
Laplacian is symmetric. -/
theorem isSymmetric_toEuclideanLin_laplacian (w : E → ℝ) :
    (toEuclideanLin (laplacian end₁ end₂ w)).IsSymmetric := by
  rw [isSymmetric_toEuclideanLin_iff]
  simpa [Matrix.IsHermitian] using laplacian_transpose end₁ end₂ w

/-- **Algebraic connectivity.** The second-smallest eigenvalue `λ₂` of the weighted Laplacian
`laplacian end₁ end₂ w`, i.e. the eigenvalue of index `|V| - 2` in the decreasing enumeration
`LinearMap.IsSymmetric.eigenvalues`; it is set to `0` when there are fewer than two vertices
(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Lemma 3.1.1, where
the eigenvalues are written `0 = λ₁ ≤ λ₂ ≤ ⋯ ≤ λₙ`). -/
noncomputable def algebraicConnectivity (w : E → ℝ) : ℝ :=
  if h : 2 ≤ Fintype.card V then
    (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w).eigenvalues finrank_euclideanSpace
      ⟨Fintype.card V - 2, by omega⟩
  else 0

omit [DecidableEq E] [Fintype E] in
/-- The Rayleigh form of the operator of a matrix `M` at `toLp v` is `vᵀ M v`. -/
theorem rayleighForm_toLp (M : Matrix V V ℝ) (v : V → ℝ) :
    rayleighForm (toEuclideanLin M) (WithLp.toLp 2 v) = v ⬝ᵥ (M *ᵥ v) := by
  simp [rayleighForm, Matrix.toLpLin_toLp, EuclideanSpace.inner_toLp_toLp]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- The squared norm of `toLp v` is `v ⬝ᵥ v`. -/
private theorem norm_toLp_sq (v : V → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ V)‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
  simp

/-- **`λ₂` bounds the Rayleigh quotient on vectors orthogonal to the constants.** For nonnegative
weights and every real `x` with `∑ x = 0`, `λ₂ · xᵀx ≤ xᵀ L x` (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, Section 3.2: the Courant–Fischer theorem, Theorem
2.0.1, gives `λ₂ = min_{x ⊥ 1} xᵀLx / xᵀx` because `1` spans an eigenvector of `λ₁ = 0`). -/
theorem algebraicConnectivity_mul_le {w : E → ℝ} (hw : 0 ≤ w) {x : V → ℝ} (hx : x ⬝ᵥ 1 = 0) :
    algebraicConnectivity end₁ end₂ w * (x ⬝ᵥ x) ≤ x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) := by
  set L := laplacian end₁ end₂ w
  have hq : 0 ≤ x ⬝ᵥ (L *ᵥ x) := by
    rw [dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  have hxx : 0 ≤ x ⬝ᵥ x := by
    simpa [dotProduct] using Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (x i)
  unfold algebraicConnectivity
  split_ifs with h2
  swap
  · simpa using hq
  set n := Fintype.card V
  set hT := isSymmetric_toEuclideanLin_laplacian end₁ end₂ w
  set lam := hT.eigenvalues finrank_euclideanSpace ⟨n - 2, by omega⟩
  by_cases hlam : lam ≤ 0
  · nlinarith
  push Not at hlam
  by_cases hx0 : x = 0
  · simp [hx0]
  -- the plane spanned by `1` and `x`
  set u : EuclideanSpace ℝ V := WithLp.toLp 2 (1 : V → ℝ)
  set v : EuclideanSpace ℝ V := WithLp.toLp 2 x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hone : (1 : V → ℝ) ⬝ᵥ (1 : V → ℝ) = n := by simp [dotProduct, n]
  have hindep : LinearIndependent ℝ ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hab' : a • (1 : V → ℝ) + b • x = 0 := by
      have := congrArg WithLp.ofLp hab
      simpa [u, v] using this
    have h1 := congrArg (· ⬝ᵥ (1 : V → ℝ)) hab'
    simp only [add_dotProduct, smul_dotProduct, hone, hx, smul_eq_mul, mul_zero, add_zero,
      zero_dotProduct] at h1
    have ha : a = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hn0.ne'
    refine ⟨ha, ?_⟩
    rw [ha, zero_smul, zero_add] at hab'
    rcases smul_eq_zero.1 hab' with h | h
    · exact h
    · exact absurd h hx0
  set W := Submodule.span ℝ (Set.range ![u, v])
  have hW : Module.finrank ℝ W = n - (n - 2) := by
    rw [finrank_span_eq_card hindep, Fintype.card_fin]
    omega
  obtain ⟨y, hyW, hy1, hle⟩ :=
    exists_unit_ge_of_submodule hT finrank_euclideanSpace (k := n - 2) (by omega) W hW
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hyW
  set a := c 0
  set b := c 1
  set z : V → ℝ := a • (1 : V → ℝ) + b • x
  have hyz : y = WithLp.toLp 2 z := by
    rw [← hc, Fin.sum_univ_two]
    simp [u, v, z, a, b]
  have hL1 : L *ᵥ (1 : V → ℝ) = 0 := laplacian_mulVec_one end₁ end₂ w
  have h1Lx : (1 : V → ℝ) ⬝ᵥ (L *ᵥ x) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose, hL1,
      zero_dotProduct]
  have hR : rayleighForm (toEuclideanLin L) y = b ^ 2 * (x ⬝ᵥ (L *ᵥ x)) := by
    rw [hyz, rayleighForm_toLp]
    simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, hL1, smul_zero, zero_add,
      add_dotProduct, smul_dotProduct, dotProduct_smul, h1Lx, smul_eq_mul]
    ring
  have hN : a ^ 2 * n + b ^ 2 * (x ⬝ᵥ x) = 1 := by
    have h := norm_toLp_sq z
    rw [← hyz, hy1] at h
    have hx1 : (1 : V → ℝ) ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hx
    simp only [z, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hone, hx,
      hx1, smul_eq_mul] at h
    linarith
  have hb : b ^ 2 * (x ⬝ᵥ x) ≤ 1 := by nlinarith [sq_nonneg a]
  change lam ≤ rayleighForm (toEuclideanLin L) y at hle
  rw [hR] at hle
  nlinarith [mul_le_mul_of_nonneg_left hle hxx, mul_le_mul_of_nonneg_left hb hq]

/-- **Easy direction of Cheeger's inequality, eigenvalue form.** For nonnegative weights and every
vertex set `S`, `λ₂ · |S| · |V \ S| ≤ |V| · w(∂S)`; with `s = |S|/|V|` this reads
`w(∂S)/|S| ≥ λ₂ (1 - s)`, hence the isoperimetric ratio satisfies `θ_G ≥ λ₂/2`
(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 20.1.1,
stated there for unit weights). -/
theorem algebraicConnectivity_mul_card_mul_card_compl_le {w : E → ℝ} (hw : 0 ≤ w)
    (S : Finset V) :
    algebraicConnectivity end₁ end₂ w * S.card * (Finset.univ \ S).card ≤
      Fintype.card V * ∑ e ∈ cut end₁ end₂ S, w e :=
  mul_card_mul_card_compl_le_of_forall end₁ end₂ w
    (fun _ hx => algebraicConnectivity_mul_le end₁ end₂ hw hx) S

/-- **`λ₂ > 0` exactly for connected graphs.** For a loopless finite multigraph with positive
edge weights and at least two vertices, the second-smallest Laplacian eigenvalue is positive if
and only if the multigraph is connected (D. A. Spielman, *Spectral and Algebraic Graph Theory*,
draft of 2 April 2025, Lemma 3.1.1). -/
theorem algebraicConnectivity_pos_iff {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) (h2 : 2 ≤ Fintype.card V) :
    0 < algebraicConnectivity end₁ end₂ w ↔ (underlyingGraph end₁ end₂).Connected := by
  classical
  have hw0 : 0 ≤ w := fun e => (hw e).le
  constructor
  · -- a component `C` with a vertex outside it has an empty cut
    intro hpos
    have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, hne⟩
    by_contra huv
    set C : Finset V := Finset.univ.filter fun z => (underlyingGraph end₁ end₂).Reachable u z
    have hcut : cut end₁ end₂ C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and, C] at he
      have hr : (underlyingGraph end₁ end₂).Reachable (end₁ e) (end₂ e) :=
        (underlyingGraph_adj_of_ne end₁ end₂ (hloop e)).reachable
      by_cases h₁ : (underlyingGraph end₁ end₂).Reachable u (end₁ e)
      · have h₂ := h₁.trans hr
        simp [h₁, h₂] at he
      · have h₂ : ¬ (underlyingGraph end₁ end₂).Reachable u (end₂ e) :=
          fun h => h₁ (h.trans hr.symm)
        simp [h₁, h₂] at he
    have hC : 1 ≤ C.card := Finset.card_pos.2 ⟨u, by simp [C]⟩
    have hCc : 1 ≤ (Finset.univ \ C).card := Finset.card_pos.2 ⟨v, by simp [C, huv]⟩
    have key := algebraicConnectivity_mul_card_mul_card_compl_le end₁ end₂ hw0 C
    rw [hcut, Finset.sum_empty, mul_zero] at key
    have hC' : (1 : ℝ) ≤ C.card := by exact_mod_cast hC
    have hCc' : (1 : ℝ) ≤ (Finset.univ \ C).card := by exact_mod_cast hCc
    nlinarith [mul_pos (mul_pos hpos (by linarith : (0 : ℝ) < C.card))
      (by linarith : (0 : ℝ) < (Finset.univ \ C).card)]
  · -- a nonzero vector orthogonal to `1` in the bottom two-dimensional eigenspace
    intro hconn
    by_contra hnpos
    push Not at hnpos
    set L := laplacian end₁ end₂ w
    set hT := isSymmetric_toEuclideanLin_laplacian end₁ end₂ w
    have hlam : hT.eigenvalues finrank_euclideanSpace ⟨Fintype.card V - 2, by omega⟩ ≤ 0 := by
      have h := hnpos
      unfold algebraicConnectivity at h
      simpa only [h2, ↓reduceDIte] using h
    have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨W, hWdim, hWle, -⟩ :=
      exists_tail_submodule hT finrank_euclideanSpace (k := Fintype.card V - 2) (by omega)
    set u : EuclideanSpace ℝ V := WithLp.toLp 2 (1 : V → ℝ)
    have hu : u ≠ 0 := by
      intro h
      have := congrArg (fun y : EuclideanSpace ℝ V => y (Classical.arbitrary V)) h
      simp [u] at this
    have hperp : Module.finrank ℝ (ℝ ∙ u)ᗮ = Fintype.card V - 1 := by
      have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
      rw [finrank_span_singleton hu, finrank_euclideanSpace] at h
      omega
    have hdim : 1 ≤ Module.finrank ℝ ↥(W ⊓ (ℝ ∙ u)ᗮ) := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ u)ᗮ
      have hle : Module.finrank ℝ ↥(W ⊔ (ℝ ∙ u)ᗮ) ≤ Fintype.card V := by
        have h := Submodule.finrank_le (W ⊔ (ℝ ∙ u)ᗮ)
        rwa [finrank_euclideanSpace] at h
      omega
    obtain ⟨y, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
    have hyE0 : (y : EuclideanSpace ℝ V) ≠ 0 := by exact_mod_cast hy0
    have hyW : (y : EuclideanSpace ℝ V) ∈ W := (Submodule.mem_inf.mp y.2).1
    have hyperp : (y : EuclideanSpace ℝ V) ∈ (ℝ ∙ u)ᗮ := (Submodule.mem_inf.mp y.2).2
    set z : V → ℝ := WithLp.ofLp (y : EuclideanSpace ℝ V)
    have hyz : (y : EuclideanSpace ℝ V) = WithLp.toLp 2 z := rfl
    -- the Rayleigh form of `y` vanishes
    have hnorm : 0 < ‖(y : EuclideanSpace ℝ V)‖ := norm_pos_iff.mpr hyE0
    have hR : rayleighForm (toEuclideanLin L) (y : EuclideanSpace ℝ V) ≤ 0 := by
      have hunit := hWle (((‖(y : EuclideanSpace ℝ V)‖⁻¹ : ℝ)) • (y : EuclideanSpace ℝ V))
        (W.smul_mem _ hyW) (by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le),
            inv_mul_cancel₀ hnorm.ne'])
      have hsmul := rayleighForm_smul (toEuclideanLin L) ‖(y : EuclideanSpace ℝ V)‖⁻¹
        (y : EuclideanSpace ℝ V)
      simp only [RCLike.ofReal_real_eq_id, id] at hsmul
      rw [hsmul] at hunit
      have hpos : 0 < ‖(y : EuclideanSpace ℝ V)‖⁻¹ ^ 2 := by positivity
      by_contra hc
      push Not at hc
      linarith [mul_pos hpos hc]
    rw [hyz, rayleighForm_toLp, dotProduct_mulVec_laplacian] at hR
    have hq : ∑ e, w e * (z (end₁ e) - z (end₂ e)) ^ 2 = 0 :=
      le_antisymm hR (Finset.sum_nonneg fun e _ => mul_nonneg (hw0 e) (sq_nonneg _))
    have hLz : L *ᵥ z = 0 := by
      rw [laplacian_mulVec_eq_zero_iff end₁ end₂ hw hloop]
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun e _ => mul_nonneg (hw0 e) (sq_nonneg (z (end₁ e) - z (end₂ e))))).1 hq
      rw [← vecMul_orientedIncidence_eq_zero_iff end₁ end₂ hloop]
      funext e
      have he := hterm e (Finset.mem_univ e)
      rw [vecMul_orientedIncidence_apply, Pi.zero_apply]
      rcases mul_eq_zero.1 he with h | h
      · exact absurd h (hw e).ne'
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    -- so `z` is constant, and orthogonal to `1`, hence zero
    have hconst := (laplacian_mulVec_eq_zero_iff end₁ end₂ hw hloop z).1 hLz
    obtain ⟨v₀⟩ := hconn.nonempty
    have hzc : z = fun _ => z v₀ := funext fun t => hconst t v₀ (hconn.preconnected t v₀)
    have hz1 : z ⬝ᵥ (1 : V → ℝ) = 0 := by
      have h := (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hyperp
      rw [hyz, EuclideanSpace.inner_toLp_toLp] at h
      simpa using h
    rw [hzc] at hz1
    have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    simp only [dotProduct, Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hz1
    have hzv : z v₀ = 0 := by
      rcases mul_eq_zero.1 hz1 with h | h
      · exact absurd h hn0.ne'
      · exact h
    apply hyE0
    rw [hyz, hzc, hzv]
    rfl

omit [DecidableEq E] [Fintype E] in
/-- Every eigenvalue of the operator of a positive semidefinite real matrix is nonnegative. -/
private theorem eigenvalues_nonneg_of_posSemidef {M : Matrix V V ℝ} (hM : M.PosSemidef)
    (hS : (toEuclideanLin M).IsSymmetric) (k : Fin (Fintype.card V)) :
    0 ≤ hS.eigenvalues finrank_euclideanSpace k := by
  obtain ⟨-, -, -, x, -, -, hx⟩ := exists_tail_submodule hS finrank_euclideanSpace k.isLt
  rw [← hx, show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl, rayleighForm_toLp]
  have := (posSemidef_iff_dotProduct_mulVec.1 hM).2 (WithLp.ofLp x)
  simpa using this

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Eigenvalues of equal symmetric operators agree, whatever the symmetry proofs. -/
private theorem eigenvalues_congr {T₁ T₂ : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V}
    (h : T₁ = T₂) (h₁ : T₁.IsSymmetric) (h₂ : T₂.IsSymmetric) :
    h₁.eigenvalues finrank_euclideanSpace = h₂.eigenvalues finrank_euclideanSpace := by
  subst h
  rfl

/-- **Laplacian eigenvalues are monotone in the Loewner order.** If `L_{w'} - L_w` is positive
semidefinite, then each eigenvalue of `L_w` (in the decreasing enumeration) is at most the
corresponding eigenvalue of `L_{w'}`; with `G = (V, E, w')` and `H = (V, E, w)` this is
D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Lemma 6.2.1 for
`c = 1` (`G ≽ H` implies `λ_k(G) ≥ λ_k(H)` for all `k`), proved here from Weyl's inequality. -/
theorem eigenvalues_laplacian_le_of_posSemidef {w w' : E → ℝ}
    (h : (laplacian end₁ end₂ w' - laplacian end₁ end₂ w).PosSemidef) (k : Fin (Fintype.card V)) :
    (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w).eigenvalues finrank_euclideanSpace k ≤
      (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w').eigenvalues finrank_euclideanSpace k := by
  have hS : (toEuclideanLin (laplacian end₁ end₂ w' - laplacian end₁ end₂ w)).IsSymmetric := by
    rw [isSymmetric_toEuclideanLin_iff]
    exact h.1
  have hb : Fintype.card V - 1 < Fintype.card V := by have := k.isLt; omega
  have hweyl := MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum.le_weyl_eigenvalue_add
    (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w) hS finrank_euclideanSpace k.isLt hb
    (by omega)
  have hsum : toEuclideanLin (laplacian end₁ end₂ w) +
      toEuclideanLin (laplacian end₁ end₂ w' - laplacian end₁ end₂ w) =
        toEuclideanLin (laplacian end₁ end₂ w') := by
    rw [← map_add, add_sub_cancel]
  have hidx : (⟨k + (Fintype.card V - 1) - (Fintype.card V - 1), by omega⟩ :
      Fin (Fintype.card V)) = k := Fin.ext (by simp)
  rw [eigenvalues_congr hsum ((isSymmetric_toEuclideanLin_laplacian end₁ end₂ w).add hS)
    (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w'), hidx] at hweyl
  have h0 := eigenvalues_nonneg_of_posSemidef h hS ⟨Fintype.card V - 1, hb⟩
  linarith

/-- **Raising weights raises every Laplacian eigenvalue.** If `w ≤ w'` edgewise, each eigenvalue
of `L_w` is at most the corresponding eigenvalue of `L_{w'}`: removing an edge or decreasing its
weight can only decrease the Laplacian eigenvalues (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Corollary 6.2.2). -/
theorem eigenvalues_laplacian_mono {w w' : E → ℝ} (hle : w ≤ w') (k : Fin (Fintype.card V)) :
    (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w).eigenvalues finrank_euclideanSpace k ≤
      (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w').eigenvalues finrank_euclideanSpace k :=
  eigenvalues_laplacian_le_of_posSemidef end₁ end₂ (posSemidef_laplacian_sub_of_le end₁ end₂ hle) k

/-- **Algebraic connectivity is monotone in the weights.** If `w ≤ w'` edgewise then
`λ₂(L_w) ≤ λ₂(L_{w'})` (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April
2025, Corollary 6.2.2 for `k = 2`). -/
theorem algebraicConnectivity_mono {w w' : E → ℝ} (hle : w ≤ w') :
    algebraicConnectivity end₁ end₂ w ≤ algebraicConnectivity end₁ end₂ w' := by
  unfold algebraicConnectivity
  split_ifs with h2
  · exact eigenvalues_laplacian_mono end₁ end₂ hle _
  · exact le_rfl

end EndpointMapMultigraph
