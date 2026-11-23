/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.BasedPolyhedralReplacement

noncomputable section
open Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped unitInterval Simplicial
universe u

#check Topology.CWComplex.BasedPolyhedralReplacementData
#print axioms Topology.CWComplex.BasedPolyhedralReplacementData
#check Topology.CWComplex.basedPolyhedralReplacement
#print axioms Topology.CWComplex.basedPolyhedralReplacement

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
  (j : cell (Set.univ : Set X) 0)

example :
    let d := basedPolyhedralReplacement X j
    d.toPolyhedron (map (C := (Set.univ : Set X)) 0 j 0) =
      Realization.vertex d.polyhedron d.vertex d.vertex_mem :=
  (basedPolyhedralReplacement X j).toPolyhedron_point

example :
    let d := basedPolyhedralReplacement X j
    d.fromPolyhedron (Realization.vertex d.polyhedron d.vertex d.vertex_mem) =
      map (C := (Set.univ : Set X)) 0 j 0 :=
  (basedPolyhedralReplacement X j).fromPolyhedron_point

example :
    let d := basedPolyhedralReplacement X j
    ContinuousMap.HomotopyRel (d.fromPolyhedron.comp d.toPolyhedron)
      (ContinuousMap.id X) {map (C := (Set.univ : Set X)) 0 j 0} :=
  (basedPolyhedralReplacement X j).originalHomotopy

example :
    let d := basedPolyhedralReplacement X j
    ContinuousMap.HomotopyRel (d.toPolyhedron.comp d.fromPolyhedron)
      (ContinuousMap.id d.polyhedron.Realization)
      {Realization.vertex d.polyhedron d.vertex d.vertex_mem} :=
  (basedPolyhedralReplacement X j).polyhedralHomotopy

example (t : unitInterval) :
    let d := basedPolyhedralReplacement X j
    d.originalHomotopy (t, map (C := (Set.univ : Set X)) 0 j 0) =
      map (C := (Set.univ : Set X)) 0 j 0 :=
  (basedPolyhedralReplacement X j).originalHomotopy.eq_snd t (by simp)

example (t : unitInterval) :
    let d := basedPolyhedralReplacement X j
    d.polyhedralHomotopy (t, Realization.vertex d.polyhedron d.vertex d.vertex_mem) =
      Realization.vertex d.polyhedron d.vertex d.vertex_mem :=
  (basedPolyhedralReplacement X j).polyhedralHomotopy.eq_snd t (by simp)

example :
    let d := basedPolyhedralReplacement X j
    d.toNerve (map (C := (Set.univ : Set X)) 0 j 0) = SSet.realizedVertex d.nerveVertex ∧
      d.fromNerve (SSet.realizedVertex d.nerveVertex) = map (C := (Set.univ : Set X)) 0 j 0 :=
  ⟨(basedPolyhedralReplacement X j).toNerve_point,
    (basedPolyhedralReplacement X j).fromNerve_point⟩

example :
    let d := basedPolyhedralReplacement X j
    ContinuousMap.HomotopyRel (d.fromNerve.comp d.toNerve)
      (ContinuousMap.id X) {map (C := (Set.univ : Set X)) 0 j 0} :=
  (basedPolyhedralReplacement X j).nerveOriginalHomotopy

example :
    let d := basedPolyhedralReplacement X j
    ContinuousMap.HomotopyRel (d.toNerve.comp d.fromNerve)
      (ContinuousMap.id (SSet.toTop.obj (faceNerve d.polyhedron)))
      {SSet.realizedVertex d.nerveVertex} :=
  (basedPolyhedralReplacement X j).nerveHomotopy

example (q : Fin 0 → ℝ) :
    let d := basedPolyhedralReplacement X j
    map (C := (Set.univ : Set d.polyhedron.Realization)) 0 d.polyhedralZeroCell q =
      Realization.vertex d.polyhedron d.vertex d.vertex_mem :=
  (basedPolyhedralReplacement X j).polyhedralZeroCell_value q

example :
    let d := basedPolyhedralReplacement X j
    d.faceNerveHomeomorph (SSet.realizedVertex d.nerveVertex) =
        Realization.vertex d.polyhedron d.vertex d.vertex_mem ∧
      d.faceNerveHomeomorph.symm (Realization.vertex d.polyhedron d.vertex d.vertex_mem) =
        SSet.realizedVertex d.nerveVertex :=
  ⟨(basedPolyhedralReplacement X j).faceNerveHomeomorph_vertex,
    (basedPolyhedralReplacement X j).faceNerveHomeomorph_inverse_vertex⟩

end
