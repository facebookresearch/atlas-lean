/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationNonsingularSignedEdgeStar

/-!
# Tests for nonsingular signed-edge star intervals

These tests cover the exact pause map, realized forward/reverse/equality
traversals, every edge of `Delta[2]`, sharp raw-path endpoints, universes,
parallel edges, and the singular circle and collapsed-sphere scope gates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

open SSet
open SSet.RealizationEdgeWord.SignedChain

private def half : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

private def quarter : unitInterval :=
  ⟨1 / 4, by constructor <;> norm_num⟩

private def threeQuarters : unitInterval :=
  ⟨3 / 4, by constructor <;> norm_num⟩

section Pause

example : boundaryPause 0 = 0 := by simp

example : boundaryPause quarter = 0 := by
  apply boundaryPause_eq_zero_of_le_quarter
  rfl

example : boundaryPause half = half := by
  exact boundaryPause_half

example : boundaryPause threeQuarters = 1 := by
  apply boundaryPause_eq_one_of_three_quarters_le
  rfl

example : boundaryPause 1 = 1 := by simp

example : boundaryPause
      ⟨1 / 3, by constructor <;> norm_num⟩ =
    ⟨1 / 6, by constructor <;> norm_num⟩ := by
  rw [boundaryPause_eq_affine]
  · apply Subtype.ext
    norm_num
  · norm_num
  · norm_num

example {s t : unitInterval} (h : s ≤ t) :
    boundaryPause s ≤ boundaryPause t :=
  monotone_boundaryPause h

end Pause

private noncomputable def standardVertex (n : ℕ) (i : Fin (n + 1)) :
    (Δ[n] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

private noncomputable def standardEdge (n : ℕ)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (Δ[n] : SSet.{u}).Edge (standardVertex n i) (standardVertex n j) :=
  SSet.Edge.mk (SSet.stdSimplex.edge n i j hij)
    (by apply SSet.stdSimplex.obj₀Equiv.injective; rfl)
    (by apply SSet.stdSimplex.obj₀Equiv.injective; rfl)

private structure BufferedContract {X : SSet.{u}} [X.Finite]
    [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) : Prop where
  sourceQuarter :
    bufferedSignedEdgePath e quarter ∈ SSet.nonsingularVertexStar X x
  sourceHalf :
    bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X x
  targetHalf :
    bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X y
  targetThreeQuarters :
    bufferedSignedEdgePath e threeQuarters ∈
      SSet.nonsingularVertexStar X y

private theorem bufferedContract {X : SSet.{u}} [X.Finite]
    [X.Nonsingular] {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) : BufferedContract e where
  sourceQuarter :=
    bufferedSignedEdgePath_mem_sourceStar_of_le_half e quarter (by
      norm_num [quarter])
  sourceHalf :=
    bufferedSignedEdgePath_mem_sourceStar_of_le_half e half (by
      norm_num [half])
  targetHalf :=
    bufferedSignedEdgePath_mem_targetStar_of_half_le e half (by
      norm_num [half])
  targetThreeQuarters :=
    bufferedSignedEdgePath_mem_targetStar_of_half_le e threeQuarters (by
      norm_num [threeQuarters])

section GenericClients

example {X : SSet.{u}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    bufferedSignedEdgePath e t ∈ SSet.nonsingularVertexStar X x :=
  bufferedSignedEdgePath_mem_sourceStar_of_le_half e t ht

example {X : SSet.{u}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y)
    (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    bufferedSignedEdgePath e t ∈ SSet.nonsingularVertexStar X y :=
  bufferedSignedEdgePath_mem_targetStar_of_half_le e t ht

example {X : SSet.{1}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y) :
    bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X x ∧
      bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X y :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half e half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le e half (by norm_num [half])⟩

example {X : SSet.{0}} [X.Finite] [X.Nonsingular]
    {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y) :
    bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X x ∧
      bufferedSignedEdgePath e half ∈ SSet.nonsingularVertexStar X y :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half e half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le e half (by norm_num [half])⟩

example {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    (signedEdgeRealizedPath e).Homotopy (bufferedSignedEdgePath e) :=
  bufferedSignedEdgeHomotopy e

example {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    bufferedSignedEdgePath e 0 = SSet.realizedVertex x :=
  (bufferedSignedEdgePath e).source

example {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    bufferedSignedEdgePath e 1 = SSet.realizedVertex y :=
  (bufferedSignedEdgePath e).target

example {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y)
    (t : unitInterval) :
    bufferedSignedEdgePath (SSet.SignedEdge.ofEq h) t =
      SSet.realizedVertex x := by
  subst y
  rfl

example {X : SSet.{u}} [X.Nonsingular] {x : X _⦋0⦌}
    (e : X.Edge x x) : e = SSet.Edge.id x :=
  SSet.edge_eq_id_of_nonsingular e

example {X : SSet.{u}} [X.Nonsingular] {x : X _⦋0⦌}
    (e : X.Edge x x) (t : unitInterval) :
    bufferedSignedEdgePath (SSet.SignedEdge.forward e) t =
      SSet.realizedVertex x := by
  rw [SSet.edge_eq_id_of_nonsingular e, bufferedSignedEdgePath_apply]
  change TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x))
      (boundaryPause t) = SSet.realizedVertex x
  rw [SSet.realizedEdgePath_id_eq_refl]
  rfl

example {X : SSet.{u}} [X.Nonsingular] {x : X _⦋0⦌}
    (e : X.Edge x x) (t : unitInterval) :
    bufferedSignedEdgePath (SSet.SignedEdge.reverse e) t =
      SSet.realizedVertex x := by
  rw [SSet.edge_eq_id_of_nonsingular e, bufferedSignedEdgePath_apply]
  change (TopCat.pathEquiv
      (SSet.realizedEdgePath (SSet.Edge.id x))).symm
        (boundaryPause t) = SSet.realizedVertex x
  rw [SSet.realizedEdgePath_id_eq_refl]
  rfl

end GenericClients

section DeltaOne

private abbrev v0 : (Δ[1] : SSet.{u}) _⦋0⦌ := standardVertex 1 0
private abbrev v1 : (Δ[1] : SSet.{u}) _⦋0⦌ := standardVertex 1 1

private noncomputable abbrev e01 : (Δ[1] : SSet.{u}).Edge v0 v1 :=
  standardEdge 1 0 1 (by decide)

private theorem v0_ne_v1 : v0.{u} ≠ v1.{u} := by
  intro h
  have h' : (0 : Fin 2) = 1 := congrArg
    (fun z => SSet.stdSimplex.obj₀Equiv z) h
  exact Fin.zero_ne_one h'

example : BufferedContract (SSet.SignedEdge.forward e01.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.reverse e01.{u}) :=
  bufferedContract _

example : bufferedSignedEdgePath (SSet.SignedEdge.forward e01.{u}) 0 ∈
    SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v0 :=
  bufferedSignedEdgePath_mem_sourceStar_of_le_half _ 0 (by norm_num)

example : bufferedSignedEdgePath (SSet.SignedEdge.forward e01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v0 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.forward e01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v1 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.forward e01.{u}) 1 ∈
    SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v1 :=
  bufferedSignedEdgePath_mem_targetStar_of_half_le _ 1 (by norm_num)

example : bufferedSignedEdgePath (SSet.SignedEdge.reverse e01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v1 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.reverse e01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v0 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : TopCat.pathEquiv (SSet.realizedEdgePath e01.{u}) 1 ∉
    SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v0 := by
  rw [show TopCat.pathEquiv (SSet.realizedEdgePath e01.{u}) 1 =
      SSet.realizedVertex v1 from
    (TopCat.pathEquiv (SSet.realizedEdgePath e01.{u})).target]
  rw [SSet.mem_nonsingularVertexStar_iff,
    SSet.realizationVertexWeight_realizedVertex]
  simp [Ne.symm v0_ne_v1]

example : TopCat.pathEquiv (SSet.realizedEdgePath e01.{u}) 0 ∉
    SSet.nonsingularVertexStar (Δ[1] : SSet.{u}) v1 := by
  rw [show TopCat.pathEquiv (SSet.realizedEdgePath e01.{u}) 0 =
      SSet.realizedVertex v0 from
    (TopCat.pathEquiv (SSet.realizedEdgePath e01.{u})).source]
  rw [SSet.mem_nonsingularVertexStar_iff,
    SSet.realizationVertexWeight_realizedVertex]
  simp [v0_ne_v1]

example (t : unitInterval) :
    bufferedSignedEdgePath (SSet.SignedEdge.identity v0.{u}) t =
      SSet.realizedVertex v0 := by
  rfl

example (t : unitInterval) :
    bufferedSignedEdgePath
        (SSet.SignedEdge.forward (SSet.Edge.id v0.{u})) t =
      SSet.realizedVertex v0 := by
  rw [bufferedSignedEdgePath_apply]
  change TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id v0))
      (boundaryPause t) = SSet.realizedVertex v0
  rw [SSet.realizedEdgePath_id_eq_refl]
  rfl

example (t : unitInterval) :
    bufferedSignedEdgePath
        (SSet.SignedEdge.reverse (SSet.Edge.id v0.{u})) t =
      SSet.realizedVertex v0 := by
  rw [bufferedSignedEdgePath_apply]
  change (TopCat.pathEquiv
      (SSet.realizedEdgePath (SSet.Edge.id v0))).symm
        (boundaryPause t) = SSet.realizedVertex v0
  rw [SSet.realizedEdgePath_id_eq_refl]
  rfl

example : SSet.edge_eq_id_of_nonsingular (SSet.Edge.id v0.{u}) = rfl := by
  apply Subsingleton.elim

end DeltaOne

section DeltaTwo

private abbrev w0 : (Δ[2] : SSet.{u}) _⦋0⦌ := standardVertex 2 0
private abbrev w1 : (Δ[2] : SSet.{u}) _⦋0⦌ := standardVertex 2 1
private abbrev w2 : (Δ[2] : SSet.{u}) _⦋0⦌ := standardVertex 2 2

private noncomputable abbrev f01 : (Δ[2] : SSet.{u}).Edge w0 w1 :=
  standardEdge 2 0 1 (by decide)

private noncomputable abbrev f12 : (Δ[2] : SSet.{u}).Edge w1 w2 :=
  standardEdge 2 1 2 (by decide)

private noncomputable abbrev f02 : (Δ[2] : SSet.{u}).Edge w0 w2 :=
  standardEdge 2 0 2 (by decide)

example : BufferedContract (SSet.SignedEdge.forward f01.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.reverse f01.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.forward f12.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.reverse f12.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.forward f02.{u}) :=
  bufferedContract _

example : BufferedContract (SSet.SignedEdge.reverse f02.{u}) :=
  bufferedContract _

example : bufferedSignedEdgePath (SSet.SignedEdge.forward f01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w0 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.forward f01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w1 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.reverse f01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w1 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.reverse f01.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w0 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.forward f12.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w1 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.forward f12.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w2 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.reverse f12.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w2 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.reverse f12.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w1 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.forward f02.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w0 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.forward f02.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w2 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

example : bufferedSignedEdgePath (SSet.SignedEdge.reverse f02.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w2 ∧
    bufferedSignedEdgePath (SSet.SignedEdge.reverse f02.{u}) half ∈
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) w0 :=
  ⟨bufferedSignedEdgePath_mem_sourceStar_of_le_half _ half (by norm_num [half]),
    bufferedSignedEdgePath_mem_targetStar_of_half_le _ half (by norm_num [half])⟩

end DeltaTwo

section ParallelEdges

/-- Two genuinely distinct actual edges with common endpoints retain their
own signed data while satisfying the same endpoint-star contract. -/
example {K : SSet.{u}} [K.Finite] [K.Nonsingular]
    {x y : K _⦋0⦌} (e₀ e₁ : K.Edge x y) (hne : e₀ ≠ e₁) :
    BufferedContract (SSet.SignedEdge.forward e₀) ∧
      BufferedContract (SSet.SignedEdge.forward e₁) ∧ e₀ ≠ e₁ :=
  ⟨bufferedContract _, bufferedContract _, hne⟩

example {K : SSet.{u}} [K.Finite] [K.Nonsingular]
    {x y : K _⦋0⦌} (e₀ e₁ : K.Edge x y) (hne : e₀ ≠ e₁) :
    BufferedContract (SSet.SignedEdge.reverse e₀) ∧
      BufferedContract (SSet.SignedEdge.reverse e₁) ∧ e₀ ≠ e₁ :=
  ⟨bufferedContract _, bufferedContract _, hne⟩

end ParallelEdges

section SimplicialCircleGate

private noncomputable abbrev s1Diagram :=
  parallelPair (SSet.stdSimplex.δ 0 : (Δ[0] : SSet) ⟶ Δ[1])
    (SSet.stdSimplex.δ 1)

private noncomputable def s1Quotient : (Δ[1] : SSet) ⟶ SSet.S1 :=
  colimit.ι s1Diagram WalkingParallelPair.one

private noncomputable def s1Loop : SSet.S1 _⦋1⦌ :=
  SSet.yonedaEquiv s1Quotient

private theorem s1Loop_faces :
    SSet.S1.δ 0 s1Loop = SSet.S1.δ 1 s1Loop := by
  unfold s1Loop
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp,
    ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  change (s1Diagram.map WalkingParallelPairHom.left ≫
      colimit.ι s1Diagram WalkingParallelPair.one) =
    (s1Diagram.map WalkingParallelPairHom.right ≫
      colimit.ι s1Diagram WalkingParallelPair.one)
  exact (colimit.w s1Diagram WalkingParallelPairHom.left).trans
    (colimit.w s1Diagram WalkingParallelPairHom.right).symm

private noncomputable def s1Vertex : SSet.S1 _⦋0⦌ :=
  SSet.S1.δ 1 s1Loop

private noncomputable def s1LoopEdge : SSet.S1.Edge s1Vertex s1Vertex :=
  SSet.Edge.mk s1Loop rfl s1Loop_faces

/-- The quotient loop is retained as signed algebraic data, but this test
does not apply any nonsingular-star theorem to it. -/
example : SSet.SignedEdge SSet.S1 s1Vertex s1Vertex :=
  SSet.SignedEdge.forward s1LoopEdge

/-- error: failed to synthesize
  S1.Nonsingular -/
#guard_msgs (error, substring := true) in
#synth SSet.S1.Nonsingular

end SimplicialCircleGate

section CollapsedBoundarySphereGate

private noncomputable def boundaryCollapse :
    (SSet.boundary 2 : SSet.Subcomplex (Δ[2] : SSet)).toSSet ⟶
      (Δ[0] : SSet) :=
  SSet.stdSimplex.isTerminalObj₀.from _

private noncomputable def collapsedBoundarySphere : SSet :=
  pushout (SSet.boundary 2).ι boundaryCollapse

private noncomputable def sphereQuotient :
    (Δ[2] : SSet) ⟶ collapsedBoundarySphere :=
  pushout.inl (SSet.boundary 2).ι boundaryCollapse

private noncomputable def collapsedBoundaryPoint :
    (Δ[0] : SSet) ⟶ collapsedBoundarySphere :=
  pushout.inr (SSet.boundary 2).ι boundaryCollapse

/-- The entire simplicial boundary leg becomes the point leg.  This is an
algebraic collapse gate only. -/
example : (SSet.boundary 2).ι ≫ sphereQuotient =
    boundaryCollapse ≫ collapsedBoundaryPoint :=
  pushout.condition

/-- error: failed to synthesize
  collapsedBoundarySphere.Nonsingular -/
#guard_msgs (error, substring := true) in
#synth collapsedBoundarySphere.Nonsingular

end CollapsedBoundarySphereGate

#print axioms SSet.realizedEdgePath_mem_sourceStar_of_lt_one
#print axioms SSet.realizedEdgePath_mem_targetStar_of_pos
#print axioms SSet.edge_eq_id_of_nonsingular
#print axioms signedEdgeRealizedPath_mem_sourceStar_of_lt_one
#print axioms signedEdgeRealizedPath_mem_targetStar_of_pos
#print axioms bufferedSignedEdgePath_mem_sourceStar_of_le_half
#print axioms bufferedSignedEdgePath_mem_targetStar_of_half_le

end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

end
