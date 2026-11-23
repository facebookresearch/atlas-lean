/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.CommonZeroSkeleton

/-! Actual importing clients of the constructed zero-skeleton data. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology
open scoped unitInterval

universe u

#check Topology.CWComplex.commonZeroSkeleton
#print axioms Topology.CWComplex.commonZeroSkeleton
#check Topology.CWComplex.CommonZeroSkeletonData
#print axioms Topology.CWComplex.CommonZeroSkeletonData
#check Topology.CWComplex.CommonZeroSkeletonData.ext
#print axioms Topology.CWComplex.CommonZeroSkeletonData.ext
#check Topology.CWComplex.CommonZeroSkeletonData.homeomorph
#print axioms Topology.CWComplex.CommonZeroSkeletonData.homeomorph
#check Topology.CWComplex.CommonZeroSkeletonData.initialHomotopy
#print axioms Topology.CWComplex.CommonZeroSkeletonData.initialHomotopy
#check Topology.CWComplex.CommonZeroSkeletonData.polyhedronHomotopy
#print axioms Topology.CWComplex.CommonZeroSkeletonData.polyhedronHomotopy
#check Topology.CWComplex.CommonZeroSkeletonData.homeomorph_vertex
#print axioms Topology.CWComplex.CommonZeroSkeletonData.homeomorph_vertex
#check Topology.CWComplex.CommonZeroSkeletonData.initialHomotopy_stationary
#print axioms Topology.CWComplex.CommonZeroSkeletonData.initialHomotopy_stationary
#check Topology.CWComplex.CommonZeroSkeletonData.polyhedronHomotopy_stationary
#print axioms Topology.CWComplex.CommonZeroSkeletonData.polyhedronHomotopy_stationary
#check Topology.CWComplex.CommonZeroSkeletonData.discreteTopology
#print axioms Topology.CWComplex.CommonZeroSkeletonData.discreteTopology
#check Topology.CWComplex.CommonZeroSkeletonData.nonempty_cwComplex
#print axioms Topology.CWComplex.CommonZeroSkeletonData.nonempty_cwComplex

namespace CommonZeroSkeletonTests

private abbrev zeroPolyhedron (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :
    PreAbstractSimplicialComplex (Topology.RelCWComplex.cell (Set.univ : Set X) 0) :=
  (⊥ : AbstractSimplicialComplex (Topology.RelCWComplex.cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex

private abbrev zeroSpace (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :=
  CWComplex.skeletonTop X 1

private def vertex (X : TopCat.{u}) [CWComplex (Set.univ : Set X)]
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) 0) : (zeroPolyhedron X).Realization :=
  PreAbstractSimplicialComplex.Realization.vertex (zeroPolyhedron X) j
    ((⊥ : AbstractSimplicialComplex (Topology.RelCWComplex.cell (Set.univ : Set X) 0)).singleton_mem j)

-- The chosen actual homeomorphism retains every ORIGINAL characteristic zero-cell point.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) 0) :
    let d := CWComplex.commonZeroSkeleton X
    (d.homeomorph (vertex X j)).val = Topology.RelCWComplex.map 0 j (0 : Fin 0 → ℝ) := by
  exact (CWComplex.commonZeroSkeleton X).homeomorph_vertex j

-- Its inverse returns the literal polyhedral vertex from EVERY actual zero-dimensional disk point.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) 0)
    (p : (CWComplex.classicalCellDiskPair.{u} 0).fst) :
    let d := CWComplex.commonZeroSkeleton X
    d.homeomorph.symm (CWComplex.characteristicDiskToSkeleton 0 j p) = vertex X j := by
  let d := CWComplex.commonZeroSkeleton X
  apply d.homeomorph.injective
  rw [d.homeomorph.apply_symm_apply]
  apply Subtype.ext
  change Topology.RelCWComplex.map 0 j p.down.val = (d.homeomorph (vertex X j)).val
  have hp : p.down.val = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
  rw [hp]
  exact (d.homeomorph_vertex j).symm

-- Both complete inverse identities concern the WHOLE actual weak polyhedron and zero skeleton.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (w : (zeroPolyhedron X).Realization) (z : zeroSpace X) :
    let d := CWComplex.commonZeroSkeleton X
    d.homeomorph.symm (d.homeomorph w) = w ∧ d.homeomorph (d.homeomorph.symm z) = z := by
  exact ⟨(CWComplex.commonZeroSkeleton X).homeomorph.symm_apply_apply w,
    (CWComplex.commonZeroSkeleton X).homeomorph.apply_symm_apply z⟩

-- Both common initial retraction families are stationary at ALL times and ALL original stage points.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (t : unitInterval) (z : zeroSpace X) :
    let d := CWComplex.commonZeroSkeleton X
    d.initialHomotopy (t, z) = z ∧ d.polyhedronHomotopy (t, z) = z := by
  let d := CWComplex.commonZeroSkeleton X
  exact ⟨d.initialHomotopy_stationary t z, d.polyhedronHomotopy_stationary t z⟩

-- Actual entire curried endpoints, including the included inverse of the POLYHEDRAL end.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    let d := CWComplex.commonZeroSkeleton X
    d.initialHomotopy.toHomotopy.curry 0 = ContinuousMap.id (zeroSpace X) ∧
      d.initialHomotopy.toHomotopy.curry 1 = ContinuousMap.id (zeroSpace X) ∧
      d.polyhedronHomotopy.toHomotopy.curry 0 = ContinuousMap.id (zeroSpace X) ∧
      d.polyhedronHomotopy.toHomotopy.curry 1 =
        (d.homeomorph : C((zeroPolyhedron X).Realization, zeroSpace X)).comp
          (d.homeomorph.symm : C(zeroSpace X, (zeroPolyhedron X).Realization)) := by
  let d := CWComplex.commonZeroSkeleton X
  exact ⟨d.initialHomotopy.toHomotopy.curry_zero, d.initialHomotopy.toHomotopy.curry_one,
    d.polyhedronHomotopy.toHomotopy.curry_zero, d.polyhedronHomotopy.toHomotopy.curry_one⟩

-- Discreteness and actual classical CW data on the original common zero space are CONCLUSIONS.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    DiscreteTopology (zeroSpace X) ∧ Nonempty (CWComplex (Set.univ : Set (zeroSpace X))) := by
  let d := CWComplex.commonZeroSkeleton X
  let _ := d.discreteTopology
  exact ⟨inferInstance, d.nonempty_cwComplex⟩

-- The actual constructor also covers an EMPTY zero-cell set; no hidden selected label is required.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    [IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) 0)] : IsEmpty (zeroSpace X) := by
  let d := CWComplex.commonZeroSkeleton X
  refine ⟨fun z => ?_⟩
  let w : (zeroPolyhedron X).Realization := d.homeomorph.symm z
  exact isEmptyElim (Classical.choice w.point.nonempty)

-- Equality of the actual comparison determines the complete stationary construction.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (d e : CWComplex.CommonZeroSkeletonData X) (h : d.homeomorph = e.homeomorph) : d = e := by
  exact CWComplex.CommonZeroSkeletonData.ext h

end CommonZeroSkeletonTests
