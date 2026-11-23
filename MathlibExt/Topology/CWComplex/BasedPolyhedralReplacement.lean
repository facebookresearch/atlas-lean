/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.StationaryDyadicGlobalRetractions
public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization

/-!
# Actual based maps from the two common-space strong deformations

The input is the given Hausdorff classical CW model and an actual zero-cell
identifier. Every model, map, point and homotopy is derived from the public
common-space constructors. The unchanged literal vertex dictionary is colocated
with the map/relative-homotopy construction and the complete public constructor.

The constructor uses the actual common-space strong deformations and the
selected canonical weak/face-nerve realization dictionary.
-/

noncomputable section
open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped Simplicial
universe u

namespace ActualBasedPolyhedralReplacementVertexDictionary

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private abbrev unionData := Topology.CWComplex.commonDimensionUnion.{u, u} X
private abbrev successorData := Topology.CWComplex.commonSuccessorSystem X

private def initialVertex (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ((successorData X).stages 0).vertices := (unionData X).initialVertices.symm j

private theorem initialVertex_eq (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    initialVertex X j = (successorData X).initialVertices.symm j :=
  congrArg (fun e : ((successorData X).stages 0).vertices ≃
    Topology.CWComplex.cell (Set.univ : Set X) 0 => e.symm j) (unionData X).initialVertices_eq

private theorem initialVertex_singleton_mem (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    {initialVertex X j} ∈ ((successorData X).stages 0).polyhedron := by
  have h := (successorData X).initialSingleton_mem j
  exact (congrArg (fun v : ((successorData X).stages 0).vertices =>
    ({v} : Finset ((successorData X).stages 0).vertices) ∈
      ((successorData X).stages 0).polyhedron) (initialVertex_eq X j)).mpr h

/-- The literal image in the actual vertex colimit of the specified stage-zero vertex. -/
private def actualVertex (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (unionData X).vertexCocone.pt := (unionData X).stageVertexEmbedding 0 (initialVertex X j)

private theorem actualVertex_leg (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    actualVertex X j = (unionData X).vertexCocone.ι.app 0 (initialVertex X j) :=
  (unionData X).stageVertexEmbedding_leg 0 (initialVertex X j)

private theorem actualVertex_singleton_mem (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    {actualVertex X j} ∈ (unionData X).polyhedron := by
  refine ((unionData X).polyhedron_faces {actualVertex X j}).mpr
    ⟨0, {initialVertex X j}, initialVertex_singleton_mem X j, ?_⟩
  simp only [Finset.map_singleton, actualVertex]

private theorem initialZero_point (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ((successorData X).zeroPolyhedral j 0).point =
      Convexity.StdSimplex.single (initialVertex X j) := by
  have h := congrArg
    (fun p : ((successorData X).stages 0).polyhedron.Realization => p.point)
    ((successorData X).initial_zero_vertex j)
  change ((successorData X).zeroPolyhedral j 0).point =
    Convexity.StdSimplex.single ((successorData X).initialVertices.symm j) at h
  exact h.trans (congrArg
    (fun v : ((successorData X).stages 0).vertices => Convexity.StdSimplex.single (R := ℝ) v)
    (initialVertex_eq X j).symm)

private theorem zeroPolyhedral_point (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ((unionData X).zeroPolyhedral j).point = Convexity.StdSimplex.single (actualVertex X j) := by
  have h0 := congrArg
    (fun p : (unionData X).polyhedron.Realization => p.point)
    ((unionData X).zeroPolyhedral_initial j)
  have h1 := (unionData X).polyhedralStageInclusion_point 0 ((successorData X).zeroPolyhedral j 0)
  have h2 := congrArg
    (fun p : Convexity.StdSimplex ℝ ((successorData X).stages 0).vertices =>
      p.map ((unionData X).stageVertexEmbedding 0)) (initialZero_point X j)
  have h3 := Convexity.StdSimplex.map_single (R := ℝ) (initialVertex X j)
    ((unionData X).stageVertexEmbedding 0)
  exact h0.trans (h1.trans (h2.trans h3))

private def weakVertex (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (unionData X).polyhedron.Realization :=
  Realization.vertex ((unionData X).polyhedron) (actualVertex X j) (actualVertex_singleton_mem X j)

private theorem weakVertex_eq_zeroPolyhedral (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    weakVertex X j = (unionData X).zeroPolyhedral j := by
  apply Realization.ext
  change Convexity.StdSimplex.single (actualVertex X j) = ((unionData X).zeroPolyhedral j).point
  exact (zeroPolyhedral_point X j).symm

private def nerveVertex (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (faceNerve ((unionData X).polyhedron)) _⦋0⦌ :=
  faceNerveVertex ((unionData X).polyhedron) (actualVertex X j) (actualVertex_singleton_mem X j)

private theorem affine_realizedVertex_eq_zeroPolyhedral
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    Realization.affineHomeomorph ((unionData X).polyhedron)
        (SSet.realizedVertex (nerveVertex X j)) =
      (unionData X).zeroPolyhedral j :=
  (Realization.affineHomeomorph_vertex ((unionData X).polyhedron)
    (actualVertex X j) (actualVertex_singleton_mem X j)).trans (weakVertex_eq_zeroPolyhedral X j)

private theorem affine_symm_zeroPolyhedral (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (Realization.affineHomeomorph ((unionData X).polyhedron)).symm
        ((unionData X).zeroPolyhedral j) =
      SSet.realizedVertex (nerveVertex X j) := by
  have h := congrArg (Realization.affineHomeomorph ((unionData X).polyhedron)).symm
    (weakVertex_eq_zeroPolyhedral X j)
  exact h.symm.trans (Realization.affineHomeomorph_symm_vertex ((unionData X).polyhedron)
    (actualVertex X j) (actualVertex_singleton_mem X j))

private theorem weakVertex_common_image (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (unionData X).polyhedralEnd (weakVertex X j) =
      (unionData X).originalEnd (Topology.CWComplex.map (C := (Set.univ : Set X)) 0 j 0) :=
  (congrArg (unionData X).polyhedralEnd (weakVertex_eq_zeroPolyhedral X j)).trans
    ((unionData X).zero_ends_value j)

private theorem nerveVertex_common_image (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (unionData X).polyhedralEnd
      (Realization.affineHomeomorph ((unionData X).polyhedron)
          (SSet.realizedVertex (nerveVertex X j))) =
        (unionData X).originalEnd (Topology.CWComplex.map (C := (Set.univ : Set X)) 0 j 0) :=
  (congrArg (unionData X).polyhedralEnd (affine_realizedVertex_eq_zeroPolyhedral X j)).trans
    ((unionData X).zero_ends_value j)

private theorem weakVertex_is_zeroCell (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ∃ a : Topology.CWComplex.cell (Set.univ : Set (unionData X).polyhedron.Realization) 0,
      ∀ q : Fin 0 → ℝ, Topology.CWComplex.map 0 a q = weakVertex X j :=
  Realization.vertex_is_classical_zeroCell ((unionData X).polyhedron)
    (actualVertex X j) (actualVertex_singleton_mem X j)

private theorem nerveVertex_is_zeroCell (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ∃ a :
        Topology.CWComplex.cell (Set.univ : Set
          (SSet.toTop.obj (faceNerve ((unionData X).polyhedron)))) 0,
      ∀ q : Fin 0 → ℝ, Topology.CWComplex.map 0 a q = SSet.realizedVertex (nerveVertex X j) :=
  realizedFaceNerveVertex_is_classical_zeroCell ((unionData X).polyhedron)
    (actualVertex X j) (actualVertex_singleton_mem X j)

end ActualBasedPolyhedralReplacementVertexDictionary
end

noncomputable section
open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped unitInterval Simplicial

universe u

namespace ActualBasedPolyhedralReplacement

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

private abbrev unionData := commonDimensionUnion.{u, u} X
private abbrev deformationData := stationaryDyadicGlobalRetractions X
private abbrev model := (unionData X).polyhedron
private abbrev modelSpace : Type u := (model X).Realization
private abbrev nerveSpace : TopCat.{u} := SSet.toTop.obj (faceNerve (model X))

private def originalPoint (j : cell (Set.univ : Set X) 0) : X :=
  map (C := (Set.univ : Set X)) 0 j (0 : Fin 0 → ℝ)

private def modelPoint (j : cell (Set.univ : Set X) 0) : modelSpace X :=
  (unionData X).zeroPolyhedral j

private theorem commonPoint (j : cell (Set.univ : Set X) 0) :
    (unionData X).polyhedralEnd (modelPoint X j) =
      (unionData X).originalEnd (originalPoint X j) :=
  (unionData X).zero_ends_value j

private def toPolyhedron : C(X, modelSpace X) :=
  (deformationData X).polyhedralRetraction.comp (unionData X).originalEnd

private def fromPolyhedron : C(modelSpace X, X) :=
  (deformationData X).originalRetraction.comp (unionData X).polyhedralEnd

private theorem toPolyhedron_point (j : cell (Set.univ : Set X) 0) :
    toPolyhedron X (originalPoint X j) = modelPoint X j := by
  have h := congrArg (deformationData X).polyhedralRetraction (commonPoint X j)
  exact h.symm.trans ((deformationData X).polyhedralRetraction_end (modelPoint X j))

private theorem fromPolyhedron_point (j : cell (Set.univ : Set X) 0) :
    fromPolyhedron X (modelPoint X j) = originalPoint X j :=
  (congrArg (deformationData X).originalRetraction (commonPoint X j)).trans
    ((deformationData X).originalRetraction_end (originalPoint X j))

private def originalFamily : C(unitInterval × X, X) :=
  (deformationData X).originalRetraction.comp
    ((deformationData X).polyhedralHomotopy.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.fst : C(unitInterval × X, unitInterval)).prodMk
        ((unionData X).originalEnd.comp ContinuousMap.snd)))

private theorem originalFamily_apply (t : unitInterval) (x : X) :
    originalFamily X (t, x) = (deformationData X).originalRetraction
      ((deformationData X).polyhedralHomotopy (t, (unionData X).originalEnd x)) := rfl

private theorem originalFamily_zero (x : X) : originalFamily X (0, x) = x :=
  (congrArg (deformationData X).originalRetraction
    ((deformationData X).polyhedralHomotopy.apply_zero ((unionData X).originalEnd x))).trans
      ((deformationData X).originalRetraction_end x)

private theorem originalFamily_one (x : X) :
    originalFamily X (1, x) = fromPolyhedron X (toPolyhedron X x) :=
  congrArg (deformationData X).originalRetraction
    ((deformationData X).polyhedralHomotopy.apply_one ((unionData X).originalEnd x))

private theorem originalFamily_point (j : cell (Set.univ : Set X) 0) (t : unitInterval) :
    originalFamily X (t, originalPoint X j) = originalPoint X j := by
  have hx : (unionData X).originalEnd (originalPoint X j) ∈
      Set.range (unionData X).polyhedralEnd := ⟨modelPoint X j, commonPoint X j⟩
  exact (congrArg (deformationData X).originalRetraction
    ((deformationData X).polyhedralHomotopy.eq_fst t hx)).trans
      ((deformationData X).originalRetraction_end (originalPoint X j))

private def originalForwardHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel (ContinuousMap.id X)
      ((fromPolyhedron X).comp (toPolyhedron X)) {originalPoint X j} := by
  refine
    { toFun := originalFamily X
      continuous_toFun := (originalFamily X).continuous
      map_zero_left := originalFamily_zero X
      map_one_left := originalFamily_one X
      prop' := ?_ }
  intro t x hx
  have h : x = originalPoint X j := Set.mem_singleton_iff.mp hx
  subst x
  exact originalFamily_point X j t

private def originalInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((fromPolyhedron X).comp (toPolyhedron X))
      (ContinuousMap.id X) {originalPoint X j} :=
  (originalForwardHomotopy X j).symm

private def polyhedralFamily : C(unitInterval × modelSpace X, modelSpace X) :=
  (deformationData X).polyhedralRetraction.comp
    ((deformationData X).originalHomotopy.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.fst : C(unitInterval × modelSpace X, unitInterval)).prodMk
        ((unionData X).polyhedralEnd.comp ContinuousMap.snd)))

private theorem polyhedralFamily_apply (t : unitInterval) (p : modelSpace X) :
    polyhedralFamily X (t, p) = (deformationData X).polyhedralRetraction
      ((deformationData X).originalHomotopy (t, (unionData X).polyhedralEnd p)) := rfl

private theorem polyhedralFamily_zero (p : modelSpace X) :
    polyhedralFamily X (0, p) = p :=
  (congrArg (deformationData X).polyhedralRetraction
    ((deformationData X).originalHomotopy.apply_zero ((unionData X).polyhedralEnd p))).trans
      ((deformationData X).polyhedralRetraction_end p)

private theorem polyhedralFamily_one (p : modelSpace X) :
    polyhedralFamily X (1, p) = toPolyhedron X (fromPolyhedron X p) :=
  congrArg (deformationData X).polyhedralRetraction
    ((deformationData X).originalHomotopy.apply_one ((unionData X).polyhedralEnd p))

private theorem polyhedralFamily_point (j : cell (Set.univ : Set X) 0) (t : unitInterval) :
    polyhedralFamily X (t, modelPoint X j) = modelPoint X j := by
  have hp : (unionData X).polyhedralEnd (modelPoint X j) ∈
      Set.range (unionData X).originalEnd := ⟨originalPoint X j, (commonPoint X j).symm⟩
  exact (congrArg (deformationData X).polyhedralRetraction
    ((deformationData X).originalHomotopy.eq_fst t hp)).trans
      ((deformationData X).polyhedralRetraction_end (modelPoint X j))

private def polyhedralForwardHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (modelSpace X))
      ((toPolyhedron X).comp (fromPolyhedron X)) {modelPoint X j} := by
  refine
    { toFun := polyhedralFamily X
      continuous_toFun := (polyhedralFamily X).continuous
      map_zero_left := polyhedralFamily_zero X
      map_one_left := polyhedralFamily_one X
      prop' := ?_ }
  intro t p hp
  have h : p = modelPoint X j := Set.mem_singleton_iff.mp hp
  subst p
  exact polyhedralFamily_point X j t

private def polyhedralInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((toPolyhedron X).comp (fromPolyhedron X))
      (ContinuousMap.id (modelSpace X)) {modelPoint X j} :=
  (polyhedralForwardHomotopy X j).symm

private def affineHomeomorph : nerveSpace X ≃ₜ modelSpace X :=
  Realization.affineHomeomorph (model X)

private def nervePoint (j : cell (Set.univ : Set X) 0) : nerveSpace X :=
  (affineHomeomorph X).symm (modelPoint X j)

private def toNerve : C(X, nerveSpace X) :=
  ((affineHomeomorph X).symm : C(modelSpace X, nerveSpace X)).comp (toPolyhedron X)

private def fromNerve : C(nerveSpace X, X) :=
  (fromPolyhedron X).comp (affineHomeomorph X : C(nerveSpace X, modelSpace X))

private theorem toNerve_point (j : cell (Set.univ : Set X) 0) :
    toNerve X (originalPoint X j) = nervePoint X j :=
  congrArg (affineHomeomorph X).symm (toPolyhedron_point X j)

private theorem fromNerve_point (j : cell (Set.univ : Set X) 0) :
    fromNerve X (nervePoint X j) = originalPoint X j :=
  (congrArg (fromPolyhedron X) ((affineHomeomorph X).apply_symm_apply (modelPoint X j))).trans
    (fromPolyhedron_point X j)

private theorem nerve_original_composite :
    (fromPolyhedron X).comp (toPolyhedron X) = (fromNerve X).comp (toNerve X) := by
  apply ContinuousMap.ext
  intro x
  exact (congrArg (fromPolyhedron X)
    ((affineHomeomorph X).apply_symm_apply (toPolyhedron X x))).symm

private def nerveOriginalInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((fromNerve X).comp (toNerve X))
      (ContinuousMap.id X) {originalPoint X j} :=
  (originalInverseHomotopy X j).cast (nerve_original_composite X) rfl

private def nerveFamily : C(unitInterval × nerveSpace X, nerveSpace X) :=
  ((affineHomeomorph X).symm : C(modelSpace X, nerveSpace X)).comp
    ((polyhedralFamily X).comp
      ((ContinuousMap.fst : C(unitInterval × nerveSpace X, unitInterval)).prodMk
        ((affineHomeomorph X : C(nerveSpace X, modelSpace X)).comp ContinuousMap.snd)))

private theorem nerveFamily_apply (t : unitInterval) (p : nerveSpace X) :
    nerveFamily X (t, p) = (affineHomeomorph X).symm
      (polyhedralFamily X (t, affineHomeomorph X p)) := rfl

private theorem nerveFamily_zero (p : nerveSpace X) : nerveFamily X (0, p) = p :=
  (congrArg (affineHomeomorph X).symm (polyhedralFamily_zero X (affineHomeomorph X p))).trans
    ((affineHomeomorph X).symm_apply_apply p)

private theorem nerveFamily_one (p : nerveSpace X) :
    nerveFamily X (1, p) = toNerve X (fromNerve X p) :=
  congrArg (affineHomeomorph X).symm (polyhedralFamily_one X (affineHomeomorph X p))

private theorem nerveFamily_point (j : cell (Set.univ : Set X) 0) (t : unitInterval) :
    nerveFamily X (t, nervePoint X j) = nervePoint X j := by
  have hn := (affineHomeomorph X).apply_symm_apply (modelPoint X j)
  exact (congrArg (fun p => (affineHomeomorph X).symm (polyhedralFamily X (t, p))) hn).trans
    (congrArg (affineHomeomorph X).symm (polyhedralFamily_point X j t))

private def nerveForwardHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (nerveSpace X))
      ((toNerve X).comp (fromNerve X)) {nervePoint X j} := by
  refine
    { toFun := nerveFamily X
      continuous_toFun := (nerveFamily X).continuous
      map_zero_left := nerveFamily_zero X
      map_one_left := nerveFamily_one X
      prop' := ?_ }
  intro t p hp
  have h : p = nervePoint X j := Set.mem_singleton_iff.mp hp
  subst p
  exact nerveFamily_point X j t

private def nervePolyhedralInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((toNerve X).comp (fromNerve X))
      (ContinuousMap.id (nerveSpace X)) {nervePoint X j} :=
  (nerveForwardHomotopy X j).symm

private theorem toPolyhedron_literal_point (j : cell (Set.univ : Set X) 0) :
    toPolyhedron X (originalPoint X j) =
      Realization.vertex (model X)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j) :=
  (toPolyhedron_point X j).trans
    (ActualBasedPolyhedralReplacementVertexDictionary.weakVertex_eq_zeroPolyhedral X j).symm

private theorem fromPolyhedron_literal_point (j : cell (Set.univ : Set X) 0) :
    fromPolyhedron X
        (Realization.vertex (model X)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j)) =
      originalPoint X j :=
  (congrArg (fromPolyhedron X)
    (ActualBasedPolyhedralReplacementVertexDictionary.weakVertex_eq_zeroPolyhedral X j)).trans
      (fromPolyhedron_point X j)

private def literalPolyhedralInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((toPolyhedron X).comp (fromPolyhedron X))
      (ContinuousMap.id (modelSpace X))
      {Realization.vertex (model X)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j)} := by
  have h : modelPoint X j =
      Realization.vertex (model X)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
        (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j) :=
    (ActualBasedPolyhedralReplacementVertexDictionary.weakVertex_eq_zeroPolyhedral X j).symm
  simpa only [h] using polyhedralInverseHomotopy X j

private theorem toNerve_literal_point (j : cell (Set.univ : Set X) 0) :
    toNerve X (originalPoint X j) =
      SSet.realizedVertex (ActualBasedPolyhedralReplacementVertexDictionary.nerveVertex X j) :=
  (toNerve_point X j).trans
    (ActualBasedPolyhedralReplacementVertexDictionary.affine_symm_zeroPolyhedral X j)

private theorem fromNerve_literal_point (j : cell (Set.univ : Set X) 0) :
    fromNerve X
        (SSet.realizedVertex (ActualBasedPolyhedralReplacementVertexDictionary.nerveVertex X j)) =
      originalPoint X j :=
  (congrArg (fromNerve X)
    (ActualBasedPolyhedralReplacementVertexDictionary.affine_symm_zeroPolyhedral X j).symm).trans
      (fromNerve_point X j)

private def literalNerveInverseHomotopy (j : cell (Set.univ : Set X) 0) :
    ContinuousMap.HomotopyRel ((toNerve X).comp (fromNerve X))
      (ContinuousMap.id (nerveSpace X))
      {SSet.realizedVertex (ActualBasedPolyhedralReplacementVertexDictionary.nerveVertex X j)} := by
  have h : nervePoint X j =
      SSet.realizedVertex (ActualBasedPolyhedralReplacementVertexDictionary.nerveVertex X j) :=
    ActualBasedPolyhedralReplacementVertexDictionary.affine_symm_zeroPolyhedral X j
  simpa only [h] using nervePolyhedralInverseHomotopy X j

end ActualBasedPolyhedralReplacement
end


noncomputable section
open Topology PreAbstractSimplicialComplex
open scoped unitInterval Simplicial

universe u

namespace Topology.CWComplex

/-- An actual weak polyhedral model of the given CW space, at its specified zero cell.
The maps, both ordinary inverse homotopies and the literal face-nerve dictionary are outputs. -/
public structure BasedPolyhedralReplacementData (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (j : cell (Set.univ : Set X) 0) where
  /-- The label type on which the polyhedral model's simplicial complex is built. -/
  vertices : Type u
  /-- The simplicial complex whose realization models `X`. -/
  polyhedron : PreAbstractSimplicialComplex vertices
  /-- The base vertex: `{vertex}` is a face of `polyhedron` (`vertex_mem`), corresponding to the
  zero cell `j`. -/
  vertex : vertices
  /-- The distinguished vertex spans a singleton face of `polyhedron`. -/
  vertex_mem : {vertex} ∈ polyhedron
  /-- The map from `X` to the realization of `polyhedron`, sending the point of the zero cell `j`
  to the base vertex (`toPolyhedron_point`). -/
  toPolyhedron : C(X, polyhedron.Realization)
  /-- The map from the realization of `polyhedron` back to `X`, sending the base vertex to the
  point of the zero cell `j` (`fromPolyhedron_point`). -/
  fromPolyhedron : C(polyhedron.Realization, X)
  /-- The map to the polyhedron sends the point of the original zero cell `j`
  to the distinguished realized vertex. -/
  toPolyhedron_point : toPolyhedron (map (C := (Set.univ : Set X)) 0 j 0) =
    Realization.vertex polyhedron vertex vertex_mem
  /-- The map from the polyhedron sends the distinguished realized vertex to
  the point of the original zero cell `j`. -/
  fromPolyhedron_point : fromPolyhedron (Realization.vertex polyhedron vertex vertex_mem) =
    map (C := (Set.univ : Set X)) 0 j 0
  /-- A homotopy from `fromPolyhedron ∘ toPolyhedron` to the identity of `X`, fixing the point of
  the zero cell `j`. -/
  originalHomotopy : ContinuousMap.HomotopyRel (fromPolyhedron.comp toPolyhedron)
    (ContinuousMap.id X) {map (C := (Set.univ : Set X)) 0 j 0}
  /-- A homotopy from `toPolyhedron ∘ fromPolyhedron` to the identity of the realization, fixing
  the base vertex. -/
  polyhedralHomotopy : ContinuousMap.HomotopyRel (toPolyhedron.comp fromPolyhedron)
    (ContinuousMap.id polyhedron.Realization) {Realization.vertex polyhedron vertex vertex_mem}
  /-- A zero cell of the realization of `polyhedron`, as a CW complex, whose point is the base
  vertex (`polyhedralZeroCell_value`). -/
  polyhedralZeroCell : cell (Set.univ : Set polyhedron.Realization) 0
  /-- Every coordinate point of the chosen polyhedral zero cell has value
  equal to the distinguished realized vertex. -/
  polyhedralZeroCell_value : ∀ q : Fin 0 → ℝ,
    map (C := (Set.univ : Set polyhedron.Realization)) 0 polyhedralZeroCell q =
      Realization.vertex polyhedron vertex vertex_mem
  /-- The `0`-simplex of the face nerve of `polyhedron` given by the base vertex
  (`nerveVertex_eq`). -/
  nerveVertex : (faceNerve polyhedron) _⦋0⦌
  /-- The selected nerve vertex is the face-nerve vertex of the distinguished
  singleton face. -/
  nerveVertex_eq : nerveVertex = faceNerveVertex polyhedron vertex vertex_mem
  /-- The homeomorphism from the geometric realization of the face nerve to the realization of
  `polyhedron` (`Realization.affineHomeomorph`, by `faceNerveHomeomorph_eq`); it matches
  `nerveVertex` with the base vertex. -/
  faceNerveHomeomorph : SSet.toTop.obj (faceNerve polyhedron) ≃ₜ polyhedron.Realization
  /-- The face-nerve comparison is the canonical affine realization
  homeomorphism of `polyhedron`. -/
  faceNerveHomeomorph_eq : faceNerveHomeomorph = Realization.affineHomeomorph polyhedron
  /-- The face-nerve homeomorphism sends the realized selected nerve vertex to
  the distinguished polyhedral vertex. -/
  faceNerveHomeomorph_vertex : faceNerveHomeomorph (SSet.realizedVertex nerveVertex) =
    Realization.vertex polyhedron vertex vertex_mem
  /-- The inverse face-nerve homeomorphism sends the distinguished polyhedral
  vertex to the realized selected nerve vertex. -/
  faceNerveHomeomorph_inverse_vertex :
    faceNerveHomeomorph.symm (Realization.vertex polyhedron vertex vertex_mem) =
      SSet.realizedVertex nerveVertex
  /-- The map from `X` to the geometric realization of the face nerve, sending the point of the
  zero cell `j` to the realized `nerveVertex` (`toNerve_point`). -/
  toNerve : C(X, SSet.toTop.obj (faceNerve polyhedron))
  /-- The map from the realized face nerve back to `X`, sending the realized `nerveVertex` to the
  point of the zero cell `j` (`fromNerve_point`). -/
  fromNerve : C(SSet.toTop.obj (faceNerve polyhedron), X)
  /-- The map to the face nerve sends the point of the original zero cell `j`
  to the realized selected nerve vertex. -/
  toNerve_point : toNerve (map (C := (Set.univ : Set X)) 0 j 0) =
    SSet.realizedVertex nerveVertex
  /-- The map from the face nerve sends the realized selected nerve vertex to
  the point of the original zero cell `j`. -/
  fromNerve_point : fromNerve (SSet.realizedVertex nerveVertex) =
    map (C := (Set.univ : Set X)) 0 j 0
  /-- A homotopy from `fromNerve ∘ toNerve` to the identity of `X`, fixing the point of the zero
  cell `j`. -/
  nerveOriginalHomotopy : ContinuousMap.HomotopyRel (fromNerve.comp toNerve)
    (ContinuousMap.id X) {map (C := (Set.univ : Set X)) 0 j 0}
  /-- A homotopy from `toNerve ∘ fromNerve` to the identity of the realized face nerve, fixing the
  realized `nerveVertex`. -/
  nerveHomotopy : ContinuousMap.HomotopyRel (toNerve.comp fromNerve)
    (ContinuousMap.id (SSet.toTop.obj (faceNerve polyhedron))) {SSet.realizedVertex nerveVertex}

end Topology.CWComplex
end

noncomputable section
open Topology PreAbstractSimplicialComplex ActualBasedPolyhedralReplacement
open scoped unitInterval Simplicial

universe u

namespace Topology.CWComplex

/-- Construct the actual based polyhedral replacement from the given CW model and zero cell.
The literal vertex dictionary, both global inverse families, and the face-nerve transport
are derived from the public common-space construction. -/
public def basedPolyhedralReplacement (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (j : cell (Set.univ : Set X) 0) :
    BasedPolyhedralReplacementData X j := by
  exact
    { vertices := (unionData X).vertexCocone.pt
      polyhedron := model X
      vertex := ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j
      vertex_mem := by
        exact ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j
      toPolyhedron := toPolyhedron X
      fromPolyhedron := fromPolyhedron X
      toPolyhedron_point := by
        exact toPolyhedron_literal_point X j
      fromPolyhedron_point := by
        exact fromPolyhedron_literal_point X j
      originalHomotopy := originalInverseHomotopy X j
      polyhedralHomotopy := literalPolyhedralInverseHomotopy X j
      polyhedralZeroCell := Classical.choose
        (ActualBasedPolyhedralReplacementVertexDictionary.weakVertex_is_zeroCell X j)
      polyhedralZeroCell_value := by
        intro q
        exact Classical.choose_spec
          (ActualBasedPolyhedralReplacementVertexDictionary.weakVertex_is_zeroCell X j) q
      nerveVertex := ActualBasedPolyhedralReplacementVertexDictionary.nerveVertex X j
      nerveVertex_eq := by
        rfl
      faceNerveHomeomorph := affineHomeomorph X
      faceNerveHomeomorph_eq := by
        rfl
      faceNerveHomeomorph_vertex := by
        exact Realization.affineHomeomorph_vertex (model X)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j)
      faceNerveHomeomorph_inverse_vertex := by
        exact Realization.affineHomeomorph_symm_vertex (model X)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex X j)
          (ActualBasedPolyhedralReplacementVertexDictionary.actualVertex_singleton_mem X j)
      toNerve := toNerve X
      fromNerve := fromNerve X
      toNerve_point := by
        exact toNerve_literal_point X j
      fromNerve_point := by
        exact fromNerve_literal_point X j
      nerveOriginalHomotopy := nerveOriginalInverseHomotopy X j
      nerveHomotopy := literalNerveInverseHomotopy X j }

end Topology.CWComplex
end
