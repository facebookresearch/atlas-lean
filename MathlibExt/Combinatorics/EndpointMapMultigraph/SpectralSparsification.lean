/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import MathlibExt.LinearAlgebra.Matrix.SpectralSparsification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Twice-Ramanujan spectral sparsifiers

Linear-size spectral sparsifiers (Batson, Spielman and Srivastava, *Twice-Ramanujan
sparsifiers*, SIAM J. Comput. 41 (2012), arXiv:0808.0163, Theorems 3.1 and 1.1), stated in the
Loewner order, the first for rank-one decompositions of the identity and the second for the
weighted Laplacian `EndpointMapMultigraph.laplacian`. The first, the vector form, is proved in
`MathlibExt.LinearAlgebra.Matrix.SpectralSparsification`; the second is proved here.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.SpectralSparsificationWanted

open EndpointMapMultigraph Matrix

/-- Sparsify the squared Euclidean norm on a subspace by reweighting its coordinates. -/
private theorem sparsify_subspace {m : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    {d : ℝ} (hd : 1 < d) :
    ∃ s : Fin m → ℝ, 0 ≤ s ∧
      ((Finset.univ.filter fun i => s i ≠ 0).card : ℝ) ≤ d * Module.finrank ℝ W ∧
      ∀ y : W, (∑ i, (y.val i) ^ 2) ≤ ∑ i, s i * (y.val i) ^ 2 ∧
        (∑ i, s i * (y.val i) ^ 2) ≤
          ((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) * ∑ i, (y.val i) ^ 2 := by
  let b := stdOrthonormalBasis ℝ W
  let v (i : Fin m) (j : Fin (Module.finrank ℝ W)) := (b j).val i
  -- The rows of the basis matrix give a rank-one decomposition of the identity.
  have hv : ∑ i, vecMulVec (v i) (v i) = 1 := by
    ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    change inner ℝ (b j).val (b k).val = _ at h
    simpa [v, Matrix.sum_apply, vecMulVec_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using h
  obtain ⟨s, hs, hcard, hlo, hhi⟩ := exists_sparse_reweighting hd v hv
  refine ⟨s, hs, hcard, fun y => ?_⟩
  let z := WithLp.ofLp (b.repr y)
  have hz (i : Fin m) : z ⬝ᵥ v i = y.val i := by
    have h := congrArg (fun t : W => WithLp.ofLp t.val i) (b.sum_repr y)
    simpa [z, v, dotProduct, Submodule.coe_sum, WithLp.ofLp_sum] using h
  have quad (t : Fin m → ℝ) :
      z ⬝ᵥ ((∑ i, t i • vecMulVec (v i) (v i)) *ᵥ z) = ∑ i, t i * (y.val i) ^ 2 := by
    simp only [sum_mulVec, smul_mulVec, vecMulVec_mulVec, dotProduct_sum, dotProduct_smul,
      op_smul_eq_mul, smul_eq_mul, dotProduct_comm (v _) z, hz, sq]
  have unitQuad : z ⬝ᵥ ((1 : Matrix _ _ ℝ) *ᵥ z) = ∑ i, (y.val i) ^ 2 := by
    simpa only [one_smul, hv, one_mul] using quad (fun _ => 1)
  have lo := hlo.dotProduct_mulVec_nonneg z
  have hi := hhi.dotProduct_mulVec_nonneg z
  simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
    smul_eq_mul, quad, unitQuad, sub_nonneg] at lo hi
  exact ⟨lo, hi⟩

/-- A map on vertex potentials that kills constants has rank at most the vertex count minus one,
including for an empty vertex type. -/
private theorem finrank_range_le_card_sub_one {V M : Type*} [Fintype V] [AddCommGroup M]
    [Module ℝ M] (F : (V → ℝ) →ₗ[ℝ] M) (hF : F 1 = 0) :
    Module.finrank ℝ (LinearMap.range F) ≤ Fintype.card V - 1 := by
  have hr := F.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hr
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [Fintype.card_of_isEmpty] at hr
    omega
  · have hk : 0 < Module.finrank ℝ (LinearMap.ker F) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨1, hF⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩
    omega

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- **Twice-Ramanujan sparsifiers.** For every `d > 1`, every weighted graph `G` on `n ≥ 1`
vertices has a reweighted subgraph `H` (its weights `w'` are supported on edges of `G`) with at
most `⌈d (n - 1)⌉` edges such that `L_G ≼ L_H ≼ κ L_G` for `κ = (d + 1 + 2√d) / (d + 1 - 2√d)`
(Batson, Spielman and Srivastava, *Twice-Ramanujan sparsifiers*, arXiv:0808.0163, Theorem 1.1).
It is stated here for multigraphs, which follows from the graph case by merging parallel edges;
`n - 1` is truncated subtraction, which only matters for the empty graph. -/
theorem exists_twice_ramanujan_sparsifier (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w)
    {d : ℝ} (hd : 1 < d) :
    ∃ w' : E → ℝ, 0 ≤ w' ∧ (∀ e, w e = 0 → w' e = 0) ∧
      (Finset.univ.filter fun e => w' e ≠ 0).card ≤
        ⌈d * ((Fintype.card V - 1 : ℕ) : ℝ)⌉₊ ∧
      (laplacian end₁ end₂ w' - laplacian end₁ end₂ w).PosSemidef ∧
      (((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) • laplacian end₁ end₂ w -
        laplacian end₁ end₂ w').PosSemidef := by
  classical
  let edge := (Fintype.equivFin E).symm
  let F : (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card E)) :=
    { toFun x := WithLp.toLp 2 fun i =>
        Real.sqrt (w (edge i)) * (x (end₁ (edge i)) - x (end₂ (edge i)))
      map_add' x y := by ext i; dsimp; ring
      map_smul' c x := by ext i; dsimp; ring }
  have hr : Module.finrank ℝ (LinearMap.range F) ≤ Fintype.card V - 1 := by
    apply finrank_range_le_card_sub_one
    ext i
    simp [F]
  obtain ⟨s, hs, hcard, happrox⟩ := sparsify_subspace (LinearMap.range F) hd
  let w' (e : E) := s (edge.symm e) * w e
  have hw' : 0 ≤ w' := fun e => mul_nonneg (hs _) (hw e)
  refine ⟨w', hw', fun e he => by simp [w', he], ?_, ?_⟩
  · have hsupport : (Finset.univ.filter fun e => w' e ≠ 0).card ≤
        (Finset.univ.filter fun i => s i ≠ 0).card := by
      apply Finset.card_le_card_of_injOn edge.symm _ edge.symm.injective.injOn
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mul_ne_zero_iff.mp
        (Finset.mem_filter.mp he).2).1⟩
    apply hsupport.trans
    apply (Nat.cast_le (α := ℝ)).mp
    exact hcard.trans ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr)
      (zero_le_one.trans hd.le)).trans (Nat.le_ceil _))
  · -- The squared norm of the weighted edge differences is the Laplacian quadratic form.
    have energy (t : Fin (Fintype.card E) → ℝ) (x : V → ℝ) :
        ∑ i, t i * (F x i) ^ 2 =
          x ⬝ᵥ (laplacian end₁ end₂ (fun e => t (edge.symm e) * w e) *ᵥ x) := by
      rw [dotProduct_mulVec_laplacian, ← edge.sum_comp _]
      simp [F, mul_pow, Real.sq_sqrt (hw _), mul_assoc]
    have orig (x : V → ℝ) : ∑ i, (F x i) ^ 2 = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x) := by
      simpa only [one_mul] using energy (fun _ => 1) x
    have bounds (x : V → ℝ) := happrox ⟨F x, x, rfl⟩
    have hL := (posSemidef_laplacian end₁ end₂ hw).isHermitian
    have hL' := (posSemidef_laplacian end₁ end₂ hw').isHermitian
    constructor
    · apply PosSemidef.of_dotProduct_mulVec_nonneg (hL'.sub hL)
      intro x
      rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg, ← orig x, ← energy s x]
      exact (bounds x).1
    · apply PosSemidef.of_dotProduct_mulVec_nonneg ((hL.smul (IsSelfAdjoint.all _)).sub hL')
      intro x
      rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg, smul_mulVec, dotProduct_smul,
        smul_eq_mul, ← orig x, ← energy s x]
      exact (bounds x).2

end MathlibExt.GraphTheory.SpectralSparsificationWanted
