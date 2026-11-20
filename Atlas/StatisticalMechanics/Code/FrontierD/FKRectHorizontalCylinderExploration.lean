/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderCrossings
import Code.FK.ClusterExplorationFreeBoundary










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


noncomputable def fkRectHorizontalCylinderBottomRoots
    (R : FKRectTorus) (S : Finset (Fin R.width)) : Finset R.Vertex :=
  S.image fun x => (x, fkRectBottomRow R)



def FKRectHorizontalCylinderExploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) (v : R.Vertex) : Prop :=
  FK.ClusterExploredVertex (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S) v


def FKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :=
  FK.ClusterUnexploredVertex (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S)

noncomputable instance instFintypeFKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Fintype (FKRectHorizontalCylinderUnexploredVertex R rho S) :=
  FK.instFintypeClusterUnexploredVertex
    (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S)

noncomputable instance instDecidableEqFKRectHorizontalCylinderUnexploredVertex
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    DecidableEq (FKRectHorizontalCylinderUnexploredVertex R rho S) :=
  Classical.decEq _

theorem fkRectHorizontalCylinder_bottomRoot_mem
    (R : FKRectTorus) (S : Finset (Fin R.width)) {x : Fin R.width}
    (hx : x ∈ S) :
    (x, fkRectBottomRow R) ∈ fkRectHorizontalCylinderBottomRoots R S := by
  classical
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem fkRectHorizontalCylinderExploredVertex_iff
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) (v : R.Vertex) :
    FKRectHorizontalCylinderExploredVertex R rho S v ↔
      ∃ x ∈ S,
        (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
          (x, fkRectBottomRow R) v := by
  classical
  constructor
  · rintro ⟨r, hr, hrv⟩
    rw [fkRectHorizontalCylinderBottomRoots, Finset.mem_image] at hr
    rcases hr with ⟨x, hx, rfl⟩
    exact ⟨x, hx, hrv⟩
  · rintro ⟨x, hx, hxv⟩
    exact ⟨(x, fkRectBottomRow R),
      fkRectHorizontalCylinder_bottomRoot_mem R S hx, hxv⟩


theorem not_horizontalCylinderExplored_of_fresh_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (T S : Finset (Fin R.width))
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
    (hST : S ⊆ T) {x : Fin R.width} (hxT : x ∈ T) (hxS : x ∉ S)
    {v : R.Vertex}
    (hxv : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) v) :
    ¬ FKRectHorizontalCylinderExploredVertex R rho S v := by
  rw [fkRectHorizontalCylinderExploredVertex_iff]
  rintro ⟨y, hyS, hyv⟩
  have hyT := hST hyS
  have hxy : x ≠ y := by
    intro h
    exact hxS (h ▸ hyS)
  exact hW.2 x hxT y hyT hxy (hxv.trans hyv.symm)


theorem not_horizontalCylinderExplored_fresh_source
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (T S : Finset (Fin R.width))
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
    (hST : S ⊆ T) {x : Fin R.width} (hxT : x ∈ T) (hxS : x ∉ S) :
    ¬ FKRectHorizontalCylinderExploredVertex R rho S
      (x, fkRectBottomRow R) := by
  apply not_horizontalCylinderExplored_of_fresh_reachable
    R rho pair T S hW hST hxT hxS
  exact SimpleGraph.Reachable.refl _



theorem horizontalCylinderUnexplored_openAdj_of_fresh_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (T S : Finset (Fin R.width))
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
    (hST : S ⊆ T) {x : Fin R.width} (hxT : x ∈ T) (hxS : x ∉ S)
    {u v : R.Vertex}
    (hxu : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) u)
    (huv : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Adj u v) :
    (FK.openSub
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.ocd_innerRestrict
        (Subtype.val :
          FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex)
        rho)).Adj
      (⟨u, not_horizontalCylinderExplored_of_fresh_reachable
        R rho pair T S hW hST hxT hxS hxu⟩)
      (⟨v, not_horizontalCylinderExplored_of_fresh_reachable
        R rho pair T S hW hST hxT hxS (hxu.trans huv.reachable)⟩) := by
  rw [FK.openSub_adj]
  refine ⟨huv.1, ?_⟩
  rw [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk]
  exact huv.2



theorem horizontalCylinderUnexplored_reachable_of_fresh_pair
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (T S : Finset (Fin R.width))
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
    (hST : S ⊆ T) {x : Fin R.width} (hxT : x ∈ T) (hxS : x ∉ S) :
    ∃ source target : FKRectHorizontalCylinderUnexploredVertex R rho S,
      source.1 = (x, fkRectBottomRow R) ∧
      target.1 = (pair x, fkRectTopRow R) ∧
      (FK.openSub
        (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
          (fkRectHorizontalCylinderBottomRoots R S))
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex)
          rho)).Reachable source target := by
  let bottom : R.Vertex := (x, fkRectBottomRow R)
  let top : R.Vertex := (pair x, fkRectTopRow R)
  have hbt := hW.1 x hxT
  let freshVertex : ∀ {v : R.Vertex},
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable bottom v ->
        FKRectHorizontalCylinderUnexploredVertex R rho S :=
    fun {v} hv =>
      ⟨v, not_horizontalCylinderExplored_of_fresh_reachable
        R rho pair T S hW hST hxT hxS hv⟩
  let liftWalk : ∀ {u v : R.Vertex}
      (p : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Walk u v)
      (hbu : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
        bottom u),
      (FK.openSub
        (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
          (fkRectHorizontalCylinderBottomRoots R S))
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex)
          rho)).Walk
        (freshVertex hbu) (freshVertex (hbu.trans p.reachable)) := by
    intro u v p
    induction p with
    | nil =>
        intro hbu
        exact SimpleGraph.Walk.nil
    | @cons u v w huv p ih =>
        intro hbu
        exact SimpleGraph.Walk.cons
          (horizontalCylinderUnexplored_openAdj_of_fresh_reachable
            R rho pair T S hW hST hxT hxS hbu huv)
          (ih (hbu.trans huv.reachable))
  refine ⟨
    ⟨bottom, not_horizontalCylinderExplored_of_fresh_reachable
      R rho pair T S hW hST hxT hxS (SimpleGraph.Reachable.refl bottom)⟩,
    ⟨top, not_horizontalCylinderExplored_of_fresh_reachable
      R rho pair T S hW hST hxT hxS hbt⟩, rfl, rfl, ?_⟩
  exact hbt.elim fun p =>
    ⟨liftWalk p (SimpleGraph.Reachable.refl bottom)⟩



theorem fkRectHorizontalCylinder_condBcProb_eq_freeUnexplored
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace
      (Sym2 (FKRectHorizontalCylinderUnexploredVertex R rho S))) :
    FK.condBcProb (fkRectHorizontalCylinderGraph R)
        (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False))
        p q
        (FK.clusterUnexploredPairEdges
          (fkRectHorizontalCylinderGraph R) rho
          (fkRectHorizontalCylinderBottomRoots R S)) rho
        (@FK.ocd_psiExt
          (FKRectHorizontalCylinderUnexploredVertex R rho S) R.Vertex
          (FK.instFintypeClusterUnexploredVertex
            (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S))
          (by infer_instance)
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex)
          rho omega) =
      FK.fkProb
        (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
          (fkRectHorizontalCylinderBottomRoots R S)) p q omega := by
  exact FK.clusterExploration_condBcProb_eq_free
    (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S) hp hp1 hq omega



theorem fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (Sym2 (FKRectHorizontalCylinderUnexploredVertex R rho S)))) :
    (∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex) ⁻¹'
          A).indicator (fun _ => (1 : Real)) sigma *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (StatMech.Lattice.boundaryCliqueGraph
            (fun _ : R.Vertex => False)) p q
          (FK.clusterUnexploredPairEdges
            (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) rho sigma) =
      ∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb
            (FK.clusterUnexploredGraph
              (fkRectHorizontalCylinderGraph R) rho
              (fkRectHorizontalCylinderBottomRoots R S)) p q omega := by
  exact FK.clusterExploration_condBcProb_innerEvent_eq_free
    (fkRectHorizontalCylinderGraph R) rho
    (fkRectHorizontalCylinderBottomRoots R S) hp hp1 hq A

end

end StatMech.FrontierD
