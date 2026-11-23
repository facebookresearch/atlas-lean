/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationEdgeWordNormalization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationVertexWeight

/-!
# Realized signed edges and nonsingular vertex stars

This file inserts an explicit pause into the realized path of one signed
edge.  It proves that the first half lies in the source vertex star and the
second half lies in the target vertex star.  Forward and reverse traversals
retain the same actual simplicial edge; equality steps are stationary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.RealizationEdgeWord.SignedChain

variable {X : SSet.{u}}

/-- Pause on the first and final quarter and traverse affinely in between. -/
def boundaryPause (t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1 / 2)

theorem continuous_boundaryPause : Continuous boundaryPause :=
  continuous_projIcc.comp (by fun_prop)

theorem monotone_boundaryPause : Monotone boundaryPause := by
  intro a b hab
  apply Set.monotone_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  linarith

@[simp]
theorem boundaryPause_zero : boundaryPause 0 = 0 := by
  apply Subtype.ext
  norm_num [boundaryPause, Set.coe_projIcc]

@[simp]
theorem boundaryPause_one : boundaryPause 1 = 1 := by
  apply Subtype.ext
  norm_num [boundaryPause, Set.coe_projIcc]

@[simp, nolint simpNF]
theorem boundaryPause_half :
    boundaryPause ⟨1 / 2, by constructor <;> norm_num⟩ =
      ⟨1 / 2, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  norm_num [boundaryPause, Set.coe_projIcc]

theorem boundaryPause_eq_zero_of_le_quarter (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 4) : boundaryPause t = 0 := by
  rw [boundaryPause, Set.projIcc_of_le_left]
  · rfl
  · linarith

theorem boundaryPause_eq_one_of_three_quarters_le (t : unitInterval)
    (ht : 3 / 4 ≤ (t : ℝ)) : boundaryPause t = 1 := by
  rw [boundaryPause, Set.projIcc_of_right_le]
  · rfl
  · linarith

theorem boundaryPause_eq_affine (t : unitInterval)
    (hleft : 1 / 4 ≤ (t : ℝ)) (hright : (t : ℝ) ≤ 3 / 4) :
    boundaryPause t =
      ⟨2 * (t : ℝ) - 1 / 2, by constructor <;> linarith⟩ := by
  apply Subtype.ext
  rw [boundaryPause, Set.coe_projIcc]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Realized signed-edge path with stationary endpoint buffers. -/
def bufferedSignedEdgePath {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y) :
    _root_.Path (SSet.realizedVertex x) (SSet.realizedVertex y) :=
  (signedEdgeRealizedPath e).reparam boundaryPause
    continuous_boundaryPause boundaryPause_zero boundaryPause_one

/-- Endpoint-fixed homotopy from the original signed-edge path to its
buffered reparameterization. -/
def bufferedSignedEdgeHomotopy {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    (signedEdgeRealizedPath e).Homotopy (bufferedSignedEdgePath e) :=
  _root_.Path.Homotopy.reparam (signedEdgeRealizedPath e) boundaryPause
    continuous_boundaryPause boundaryPause_zero boundaryPause_one

end SSet.RealizationEdgeWord.SignedChain

namespace SSet

/-- Standard-simplex coordinate of one realized edge-path parameter. -/
private def realizedEdgeStdPoint (t : unitInterval) :
    Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.homeomorphI.symm t

@[simp]
private theorem realizedEdgeStdPoint_weight_zero (t : unitInterval) :
    (realizedEdgeStdPoint t).weights 0 = 1 - (t : ℝ) := by
  have hsum : (realizedEdgeStdPoint t).weights 0 +
      (realizedEdgeStdPoint t).weights 1 = 1 := by
    exact (realizedEdgeStdPoint t).total_fin_two
  have h1 : (realizedEdgeStdPoint t).weights 1 = (t : ℝ) := by
    have h := congrArg Subtype.val
      (Convexity.StdSimplex.homeomorphI.apply_symm_apply t)
    rw [Convexity.StdSimplex.homeomorphI_apply_coe] at h
    exact h
  rw [h1] at hsum
  linarith

@[simp]
private theorem realizedEdgeStdPoint_weight_one (t : unitInterval) :
    (realizedEdgeStdPoint t).weights 1 = (t : ℝ) := by
  have h := congrArg Subtype.val
    (Convexity.StdSimplex.homeomorphI.apply_symm_apply t)
  rw [Convexity.StdSimplex.homeomorphI_apply_coe] at h
  exact h

/-- An edge with distinct endpoints is nondegenerate. -/
theorem edge_nonDegenerate_of_ne {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) (hxy : x ≠ y) :
    e.edge ∈ X.nonDegenerate 1 := by
  rw [mem_nonDegenerate_iff_notMem_degenerate]
  intro hdeg
  rw [mem_degenerate_iff] at hdeg
  obtain ⟨m, hm, f, hf, hz⟩ := hdeg
  have hm0 : m = 0 := by omega
  subst m
  have hf0 : f = SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
  have hz' : e.edge ∈
      Set.range (X.map (SimplexCategory.σ (0 : Fin 1)).op) := by
    simpa [hf0] using hz
  rcases hz' with ⟨z, hz⟩
  have hzs : X.σ 0 z = e.edge := hz
  apply hxy
  calc
    x = X.δ 1 e.edge := e.src_eq.symm
    _ = X.δ 1 (X.σ 0 z) := by rw [hzs]
    _ = z := X.δ_comp_σ_succ_apply 0 z
    _ = X.δ 0 (X.σ 0 z) := (X.δ_comp_σ_self_apply 0 z).symm
    _ = X.δ 0 e.edge := by rw [hzs]
    _ = y := e.tgt_eq

/-- Exact sigma presentation of a point on a realized nondegenerate edge. -/
private theorem realizedEdgePath_apply_eq_sigmaToTop
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)
    (he : e.edge ∈ X.nonDegenerate 1) (t : unitInterval) :
    TopCat.pathEquiv (SSet.realizedEdgePath e) t =
      SSet.sigmaToTop X ⟨SSet.N.mk e.edge he, realizedEdgeStdPoint t⟩ := by
  unfold TopCat.pathEquiv SSet.realizedEdgePath SSet.sigmaToTop
  rfl

private theorem simplexVertex_edge_zero
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)
    (he : e.edge ∈ X.nonDegenerate 1) :
    simplexVertex X (SSet.N.mk e.edge he) 0 = x := by
  unfold simplexVertex
  change (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x
  have hzero : SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ (1 : Fin 2)) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  calc
    _ = (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.δ (1 : Fin 2))) := congrArg _ hzero
    _ = X.δ 1 e.edge := rfl
    _ = x := e.src_eq

private theorem simplexVertex_edge_one
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)
    (he : e.edge ∈ X.nonDegenerate 1) :
    simplexVertex X (SSet.N.mk e.edge he) 1 = y := by
  unfold simplexVertex
  change (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y
  have hone : SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.δ (0 : Fin 2)) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  calc
    _ = (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.δ (0 : Fin 2))) := congrArg _ hone
    _ = X.δ 0 e.edge := rfl
    _ = y := e.tgt_eq

/-- Before its target endpoint, a realized nonloop edge lies in the positive
star of its source vertex. -/
theorem realizedEdgePath_mem_sourceStar_of_lt_one
    {X : SSet.{u}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : X.Edge x y) (hxy : x ≠ y)
    (t : unitInterval) (ht : (t : ℝ) < 1) :
    TopCat.pathEquiv (SSet.realizedEdgePath e) t ∈
      SSet.nonsingularVertexStar X x := by
  classical
  have he : e.edge ∈ X.nonDegenerate 1 := edge_nonDegenerate_of_ne e hxy
  rw [realizedEdgePath_apply_eq_sigmaToTop e he]
  rw [mem_nonsingularVertexStar_iff]
  erw [realizationVertexWeight_sigma,
    Convexity.StdSimplex.weights_map_apply]
  refine Finset.sum_pos' (fun i _ => (realizedEdgeStdPoint t).nonneg i)
    ⟨0, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact simplexVertex_edge_zero e he
  · change 0 < (realizedEdgeStdPoint t).weights (0 : Fin 2)
    rw [realizedEdgeStdPoint_weight_zero]
    linarith

/-- After its source endpoint, a realized nonloop edge lies in the positive
star of its target vertex. -/
theorem realizedEdgePath_mem_targetStar_of_pos
    {X : SSet.{u}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : X.Edge x y) (hxy : x ≠ y)
    (t : unitInterval) (ht : 0 < (t : ℝ)) :
    TopCat.pathEquiv (SSet.realizedEdgePath e) t ∈
      SSet.nonsingularVertexStar X y := by
  classical
  have he : e.edge ∈ X.nonDegenerate 1 := edge_nonDegenerate_of_ne e hxy
  rw [realizedEdgePath_apply_eq_sigmaToTop e he]
  rw [mem_nonsingularVertexStar_iff]
  erw [realizationVertexWeight_sigma,
    Convexity.StdSimplex.weights_map_apply]
  refine Finset.sum_pos' (fun i _ => (realizedEdgeStdPoint t).nonneg i)
    ⟨1, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact simplexVertex_edge_one e he
  · change 0 < (realizedEdgeStdPoint t).weights (1 : Fin 2)
    rw [realizedEdgeStdPoint_weight_one]
    exact ht

/-- In a nonsingular simplicial set, an actual edge whose endpoints agree is
the degenerate identity edge. -/
theorem edge_eq_id_of_nonsingular
    {X : SSet.{u}} [X.Nonsingular] {x : X _⦋0⦌}
    (e : X.Edge x x) : e = SSet.Edge.id x := by
  classical
  by_cases he : e.edge ∈ X.nonDegenerate 1
  · have hfaces : X.δ 1 e.edge = X.δ 0 e.edge :=
      e.src_eq.trans e.tgt_eq.symm
    have hindex : (1 : Fin 2) = 0 :=
      SSet.Nonsingular.δ_injective e.edge he 1 0 hfaces
    omega
  · have hdeg : e.edge ∈ X.degenerate 1 := by
      by_contra hnot
      exact he ((X.mem_nonDegenerate_iff_notMem_degenerate e.edge).2 hnot)
    rw [X.mem_degenerate_iff] at hdeg
    obtain ⟨m, hm, f, hf, z, hz⟩ := hdeg
    have hm0 : m = 0 := by omega
    subst m
    have hf0 : f = SimplexCategory.σ (0 : Fin 1) := Subsingleton.elim _ _
    subst f
    have hzs : X.σ 0 z = e.edge := hz
    have hzx : z = x := by
      calc
        z = X.δ 1 (X.σ 0 z) := (X.δ_comp_σ_succ_apply 0 z).symm
        _ = X.δ 1 e.edge := by rw [hzs]
        _ = x := e.src_eq
    apply SSet.Edge.ext
    rw [SSet.Edge.id_edge, ← hzs, hzx]


end SSet

namespace SSet.RealizationEdgeWord.SignedChain

variable {X : SSet.{u}}

/-- A signed-edge realization stays in its source star before the terminal
parameter.  Reverse data reuses the stored edge with the symmetric interval
parameter. -/
theorem signedEdgeRealizedPath_mem_sourceStar_of_lt_one
    [X.Finite] [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (t : unitInterval)
    (ht : (t : ℝ) < 1) :
    signedEdgeRealizedPath e t ∈ SSet.nonsingularVertexStar X x := by
  rcases e with ⟨e | e⟩
  · change TopCat.pathEquiv (SSet.realizedEdgePath e) t ∈
      SSet.nonsingularVertexStar X x
    by_cases hxy : x = y
    · subst y
      rw [SSet.edge_eq_id_of_nonsingular e,
        SSet.realizedEdgePath_id_eq_refl]
      exact SSet.realizedVertex_mem_nonsingularVertexStar X x
    · exact SSet.realizedEdgePath_mem_sourceStar_of_lt_one e hxy t ht
  · rcases e with e | h
    · change (TopCat.pathEquiv (SSet.realizedEdgePath e)).symm t ∈
        SSet.nonsingularVertexStar X x
      by_cases hxy : x = y
      · subst y
        rw [SSet.edge_eq_id_of_nonsingular e,
          SSet.realizedEdgePath_id_eq_refl]
        exact SSet.realizedVertex_mem_nonsingularVertexStar X x
      · apply SSet.realizedEdgePath_mem_targetStar_of_pos e (Ne.symm hxy)
          (unitInterval.symm t)
        rw [unitInterval.coe_symm_eq]
        linarith
    · rcases h with ⟨h⟩
      subst y
      exact SSet.realizedVertex_mem_nonsingularVertexStar X x

/-- A signed-edge realization stays in its target star after the initial
parameter. -/
theorem signedEdgeRealizedPath_mem_targetStar_of_pos
    [X.Finite] [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (t : unitInterval)
    (ht : 0 < (t : ℝ)) :
    signedEdgeRealizedPath e t ∈ SSet.nonsingularVertexStar X y := by
  rcases e with ⟨e | e⟩
  · change TopCat.pathEquiv (SSet.realizedEdgePath e) t ∈
      SSet.nonsingularVertexStar X y
    by_cases hxy : x = y
    · subst y
      rw [SSet.edge_eq_id_of_nonsingular e,
        SSet.realizedEdgePath_id_eq_refl]
      exact SSet.realizedVertex_mem_nonsingularVertexStar X x
    · exact SSet.realizedEdgePath_mem_targetStar_of_pos e hxy t ht
  · rcases e with e | h
    · change (TopCat.pathEquiv (SSet.realizedEdgePath e)).symm t ∈
        SSet.nonsingularVertexStar X y
      by_cases hxy : x = y
      · subst y
        rw [SSet.edge_eq_id_of_nonsingular e,
          SSet.realizedEdgePath_id_eq_refl]
        exact SSet.realizedVertex_mem_nonsingularVertexStar X x
      · apply SSet.realizedEdgePath_mem_sourceStar_of_lt_one e (Ne.symm hxy)
          (unitInterval.symm t)
        rw [unitInterval.coe_symm_eq]
        linarith
    · rcases h with ⟨h⟩
      subst y
      exact SSet.realizedVertex_mem_nonsingularVertexStar X x

@[simp]
theorem bufferedSignedEdgePath_apply {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (t : unitInterval) :
    bufferedSignedEdgePath e t = signedEdgeRealizedPath e (boundaryPause t) :=
  rfl

private theorem boundaryPause_lt_one_of_le_half (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) : (boundaryPause t : ℝ) < 1 := by
  let half : unitInterval :=
    ⟨1 / 2, by constructor <;> norm_num⟩
  have htle : t ≤ half := by
    exact ht
  have hp := monotone_boundaryPause htle
  change (boundaryPause t : ℝ) ≤ (boundaryPause half : ℝ) at hp
  rw [boundaryPause_half] at hp
  exact hp.trans_lt (by norm_num)

private theorem boundaryPause_pos_of_half_le (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) : 0 < (boundaryPause t : ℝ) := by
  let half : unitInterval :=
    ⟨1 / 2, by constructor <;> norm_num⟩
  have htle : half ≤ t := by
    exact ht
  have hp := monotone_boundaryPause htle
  change (boundaryPause half : ℝ) ≤ (boundaryPause t : ℝ) at hp
  rw [boundaryPause_half] at hp
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact hhalf.trans_le hp

/-- The first closed half of a buffered signed edge lies in its source
vertex star. -/
theorem bufferedSignedEdgePath_mem_sourceStar_of_le_half
    [X.Finite] [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    bufferedSignedEdgePath e t ∈ SSet.nonsingularVertexStar X x := by
  rw [bufferedSignedEdgePath_apply]
  exact signedEdgeRealizedPath_mem_sourceStar_of_lt_one e _
    (boundaryPause_lt_one_of_le_half t ht)

/-- The second closed half of a buffered signed edge lies in its target
vertex star. -/
theorem bufferedSignedEdgePath_mem_targetStar_of_half_le
    [X.Finite] [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    bufferedSignedEdgePath e t ∈ SSet.nonsingularVertexStar X y := by
  rw [bufferedSignedEdgePath_apply]
  exact signedEdgeRealizedPath_mem_targetStar_of_pos e _
    (boundaryPause_pos_of_half_le t ht)

end SSet.RealizationEdgeWord.SignedChain

end
