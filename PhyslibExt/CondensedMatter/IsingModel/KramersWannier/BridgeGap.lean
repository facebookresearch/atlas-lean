/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingWitness
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.EventToCut

/-!
# The gap between face-region separation and inside-region boundaries

Bookkeeping for the two halves of the claim that the edge set of a closed lattice walk is the
boundary of its inside region, and a parity obstruction for vertex cuts.

## i. Overview

For a closed lattice walk `Vc`, every boundary edge of the inside region `jec_leftRegion Vc`
touches `Vc` (the easy half, `StatMech.Lattice.jec_leftRegion_bdEdge_support` in MathlibExt). The
converse direction, that every edge of `Vc` is a
boundary edge of the inside (`jbw_hard_gap Vc`), fails in general: `ceo_shiftSquare` is a
counterexample. The boundary of a single site has odd degree at a neighbour
(`jbw_vertexCut_not_even`), so a vertex cut is not an even edge set.

Headline fidelity:
- `jbw_vertexCut_not_even` is unconditional. The reachability and easy-half facts used here are the
  MathlibExt lemmas `jed_reachable_of_separated` and `jec_leftRegion_bdEdge_support`.
- `jbw_hard_gap_of_windingMatch` is vacuous: its hypothesis `kwc_PrimalWalkLeftRegionMatch` is
  refuted by `StatMech.Walls.ceo_primalWalkLeftRegionMatch_false`.
- In `jbw_jed_insufficient` the third conjunct is an implication from the same false hypothesis.

## ii. Key results

- `StatMech.Walls.jbw_bdEdgeSet` : boundary edges of a set of sites
- `StatMech.Walls.jbw_vertexCut_not_even` : the boundary of a site is not even
- `StatMech.Walls.jbw_hard_gap` : every edge of a loop is a boundary edge of its inside
- `StatMech.Walls.jbw_jed_insufficient` : summary of the three facts

## iii. Table of contents

- A. Boundary edges of a site
- B. The two halves of the inside-boundary matching

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable

/-! ## A. Boundary edges of a site -/

/-- The set of lattice edges with exactly one endpoint in `S`. -/
def jbw_bdEdgeSet (S : Set (Site 2)) : Set (Sym2 (Site 2)) := {e | bdEdge S e}

@[simp] lemma jbw_mem_bdEdgeSet (S : Set (Site 2)) (e : Sym2 (Site 2)) :
    e ∈ jbw_bdEdgeSet S ↔ bdEdge S e := Iff.rfl

/-- The one-site set `{0}`. -/
def jbw_singleton : Set (Site 2) := {origin 2}

/-- The boundary of the site `0` meets `(1, 0)` in exactly one edge, so it is not even there. -/
lemma jbw_vertexCut_not_even :
    ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0]) := by
  classical
  have hdeg : jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0] = 1 := by
    rw [jce_degree]
    have hset : (Finset.univ.filter
        (fun i : Fin 4 => s(![(1 : ℤ), 0], jce_nbr ![(1 : ℤ), 0] i)
          ∈ jbw_bdEdgeSet jbw_singleton)) = {1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        jbw_mem_bdEdgeSet, bdEdge_mk, jbw_singleton, Set.mem_singleton_iff, jce_nbr,
        origin_eq_zerozero]
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, site2_eq, Fin.isValue,
          Fin.ext_iff, Fin.val_one] <;> first | omega | tauto
    rw [hset]; rfl
  rw [hdeg]; decide

/-! ## B. The two halves of the inside-boundary matching -/

/-- Every edge of the closed walk `Vc` is a boundary edge of its inside region. -/
def jbw_hard_gap {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    s(u, v) ∈ Vc.edges.toFinset → bdEdge (jec_leftRegion Vc) s(u, v)

/-- `jbw_hard_gap` together with the converse inclusion is the edge-set/boundary matching for `Vc`.
-/
lemma jbw_hardGap_iff_windingBody {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (jbw_hard_gap Vc ∧
      ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset)
    ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))) := by
  constructor
  · rintro ⟨hf, hb⟩ u v hadj
    exact ⟨fun h => hf hadj h, fun h => hb hadj h⟩
  · intro h
    exact ⟨fun hadj he => (h hadj).mp he, fun hadj hb => (h hadj).mpr hb⟩

/-- `kwc_PrimalWalkLeftRegionMatch` gives `jbw_hard_gap` for every loop. Vacuous: the hypothesis is
false. -/
lemma jbw_hard_gap_of_windingMatch (hmatch : kwc_PrimalWalkLeftRegionMatch)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : jbw_hard_gap Vc := by
  intro u v hadj he
  exact (hmatch Vc hadj).mp he

/-- Summary: a vertex cut is not even, face-region separation gives reachability, and (vacuously)
the left-region matching gives the hard half. -/
theorem jbw_jed_insufficient :
    (¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0])) ∧
    (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2),
        (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
        (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
        ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧
    (kwc_PrimalWalkLeftRegionMatch →
      ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc) :=
  ⟨jbw_vertexCut_not_even, StatMech.Lattice.jed_reachable_of_separated,
    fun h _ Vc => jbw_hard_gap_of_windingMatch h Vc⟩

end Walls

end StatMech
