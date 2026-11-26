/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.CondensedMatter.IsingModel.KWClosedWalkParity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure

/-!
# Closed dual walks bound regions

Equivalence of the region-boundary property of closed dual walks with their cycle-parity property,
and the reduction of the region-boundary property on `ℤ²` to a boundary-edge matching hypothesis.

## i. Overview

For a primal graph `Gp`, a dual graph `Gd` on the same vertex type and an edge correspondence `ψ`,
`DualWalkBoundsRegion Gp Gd ψ` says that the pullback of every closed walk of `Gd` is the set of
edges of `Gp` with endpoints on different sides of some region. On a preconnected `Gp` this is
equivalent to `ClosedDualWalkParity` (every pulled-back closed walk meets every cycle of `Gp` an
even number of times): the parity configuration of an even set is a region whose boundary is that
set.

On `ℤ²` with `ψ = crossEdge`, the region-boundary property follows from
`LatticeDualWalkHasBdEdgeRegion Gd` (the pullback of every closed walk of `Gd` is the boundary-edge
set `bdEdge S` of some set of sites), and that in turn follows from `DualWalkLeftRegionMatch` for
every closed walk (the pullback is the boundary of the inside region `jec_leftRegion Vc` of some
lattice loop).

Headline fidelity:
- `dualWalkBoundsRegion_iff_closedDualWalkParity` is unconditional (given preconnectedness and
  the edge-correspondence hypothesis `hsymm`).
- `dualWalkBoundsRegion_lattice_of_bdEdgeMatch` is conditional on
  `hbridge : LatticeDualWalkHasBdEdgeRegion Gd`. The library proves that predicate only for
  edgeless `Gd` (`latticeDualWalkHasBdEdgeRegion_of_edgeless`).
- `latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch` is conditional on
  `DualWalkLeftRegionMatch W` for every closed walk `W`, which is not proved for any graph with
  a nontrivial closed walk.

## ii. Key results

- `StatMech.Ising.dualWalkBoundsRegion_iff_closedDualWalkParity` : region boundary ↔ cycle parity
- `StatMech.Ising.LatticeDualWalkHasBdEdgeRegion` : the boundary-edge matching hypothesis on `ℤ²`
- `StatMech.Ising.dualWalkBoundsRegion_lattice_of_bdEdgeMatch` : the lattice reduction
- `StatMech.Ising.DualWalkLeftRegionMatch` : matching with the inside of a lattice loop

## iii. Table of contents

- A. Region boundaries and cycle parity
- B. Realisation on the square lattice

## iv. References

- H. A. Kramers, G. H. Wannier, "Statistics of the two-dimensional ferromagnet. Part I",
  Phys. Rev. 60 (1941) 252–262
-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising

section Equivalence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

/-! ## A. Region boundaries and cycle parity -/

/-- On a preconnected primal graph, cycle parity of pulled-back closed dual walks gives the
region-boundary property. -/
lemma closedDualWalkParity_to_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    DualWalkBoundsRegion Gp Gd ψ := by
  intro w W
  set δ : Finset (Sym2 V) := (W.edges.toFinset).image ψ.symm with hδdef
  have hev : EvenOnCycles Gp δ := hlink W
  have hδsub : δ ⊆ Gp.edgeFinset := by
    intro e he
    rw [hδdef, Finset.mem_image] at he
    obtain ⟨g, hg, rfl⟩ := he
    have hgd : g ∈ Gd.edgeFinset := by
      rw [List.mem_toFinset] at hg
      rw [SimpleGraph.mem_edgeFinset]
      exact W.edges_subset_edgeSet hg
    exact hsymm g hgd
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  set S : ConfigSpace V := parityConfig Gp δ hG v₀ with hSdef
  refine ⟨S, ?_⟩
  intro u v huv
  have hcut : cutEdges Gp S = δ := cutEdges_parityConfig hev hG v₀ hδsub
  rw [← hcut]
  exact mem_cutEdges_iff Gp _ huv

/-- On a preconnected primal graph, closed dual walks bound regions if and only if their pullbacks
meet every primal cycle an even number of times. -/
theorem dualWalkBoundsRegion_iff_closedDualWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset) :
    DualWalkBoundsRegion Gp Gd ψ ↔ ClosedDualWalkParity Gp Gd ψ :=
  ⟨fun hreg => closedDualWalkParity_of_boundsRegion ψ hreg,
   fun hlink => closedDualWalkParity_to_boundsRegion hG ψ hsymm hlink⟩

end Equivalence

section LatticeRealisation

open StatMech.Lattice

/-! ## B. Realisation on the square lattice -/

/-- A lattice edge lies in the `crossEdge` pullback of a closed walk iff its image is an edge of the
walk. -/
lemma crossEdge_pullback_iff {Gd : SimpleGraph (Site 2)} {w : Site 2}
    (W : Gd.Walk w w) (u v : Site 2) :
    s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ crossEdge s(u, v) ∈ W.edges := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, hgeq⟩
    rw [List.mem_toFinset] at hg
    have : g = crossEdge s(u, v) := by rw [← hgeq, Equiv.apply_symm_apply]
    rw [this] at hg; exact hg
  · intro he
    exact ⟨crossEdge s(u, v), List.mem_toFinset.mpr he, crossEdge.symm_apply_apply _⟩

-- The instance binder is kept so that existing callers and the statement are unchanged.
set_option linter.unusedDecidableInType false in
/-- If the pullback of `W` is the boundary-edge set of `S`, it is the boundary of a two-colouring.
-/
lemma latticeSide_boundsRegion_of_pullback_eq_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (S : Set (Site 2)) {w : Site 2}
    (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
    ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) :=
  ⟨latticeSide S, fun h =>
    latticeSide_isRegion_of_pullback_eq_bdEdge crossEdge S W (fun h' => hpull h') h⟩

/-- Every closed walk of `Gd` pulls back under `crossEdge` to the boundary-edge set `bdEdge S` of
some set of sites `S`. -/
def LatticeDualWalkHasBdEdgeRegion (Gd : SimpleGraph (Site 2)) [DecidableRel Gd.Adj] : Prop :=
  ∀ {w : Site 2} (W : Gd.Walk w w), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))

/-- On `ℤ²`, closed walks of `Gd` bound regions, conditional on `LatticeDualWalkHasBdEdgeRegion Gd`.
-/
theorem dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hbridge : LatticeDualWalkHasBdEdgeRegion Gd) :
    DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge := by
  intro w W
  obtain ⟨S, hS⟩ := hbridge W
  exact latticeSide_boundsRegion_of_pullback_eq_bdEdge S W (fun h => hS h)

/-- `LatticeDualWalkHasBdEdgeRegion` holds for an edgeless dual graph. -/
lemma latticeDualWalkHasBdEdgeRegion_of_edgeless
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (hGd : Gd.edgeSet = ∅) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  refine ⟨(∅ : Set (Site 2)), ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image crossEdge.symm = (∅ : Finset (Sym2 (Site 2))) := by
    rw [hnil]; simp
  rw [hempty]
  simp only [Finset.notMem_empty, bdEdge_mk, Set.mem_empty_iff_false, iff_true, not_false_iff]

/-- The pullback of the closed walk `W` is the boundary-edge set of the inside region
`jec_leftRegion Vc` of some lattice loop `Vc`. -/
def DualWalkLeftRegionMatch {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    {w : Site 2} (W : Gd.Walk w w) : Prop :=
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge (jec_leftRegion Vc) s(u, v))

/-- `DualWalkLeftRegionMatch` for every closed walk implies `LatticeDualWalkHasBdEdgeRegion`. -/
lemma latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  obtain ⟨a, Vc, hVc⟩ := hmatch W
  exact ⟨jec_leftRegion Vc, fun h => hVc h⟩

end LatticeRealisation

end Ising

end StatMech
