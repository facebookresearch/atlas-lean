/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/HypercubeC4/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The theorem statement uses the seven-cube lower bound from the “Known values” section at
commit e2e19eef093a77882da57f348def029533ec2d5e.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A four-cycle-free subgraph of the seven-cube with 304 edges

We prove the lower bound on the hypercube Turán number using the signed cube construction
of M. Minamoto, arXiv:2603.29127v5, §6. A 128-bit word gives a spin at each vertex.
An edge in direction `i` is retained when the XOR of its two spins equals the parity
of the coordinates below `i`. For the word below the degrees sum to 608, and any two
distinct neighbors of a vertex have only that vertex as a common neighbor.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

private abbrev Vertex := Fin 128

private def bits (x : Vertex) : BitVec 7 := BitVec.ofFin x

private def flip (x : Vertex) (i : Fin 7) : Vertex :=
  (bits x ^^^ BitVec.twoPow 7 i).toFin

private def lowerParity (x : Vertex) : ℕ → Bool
  | 0 => false
  | i + 1 => lowerParity x i ^^ x.val.testBit i

-- Bit x of this independently found spin assignment is the spin at vertex x.
private def spin (x : Vertex) : Bool :=
  (0x1282f80e8cdbd30c33357227023c3fa8 : ℕ).testBit x

private def neighbors (x : Vertex) : List Vertex :=
  ((List.finRange 7).filter fun i => (spin x ^^ spin (flip x i)) == lowerParity x i).map (flip x)

private def witness : SimpleGraph Vertex where
  Adj x y := y ∈ neighbors x
  symm := ⟨by
    have h : ∀ x : Vertex, ∀ y ∈ neighbors x, x ∈ neighbors y := by decide +kernel
    exact fun x y => h x y⟩
  loopless := ⟨by decide +kernel⟩

private def inCube : witness.Copy (hypercubeGraph 7) where
  toHom := {
    toFun := fun x i => (bits x).getLsbD i
    map_rel' := by
      intro x y h
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
      rw [hypercubeGraph_adj]
      have hbits (j : Fin 7) : (bits (flip x i)).getLsbD j =
          ((bits x).getLsbD j ^^ decide (j = i)) := by
        change (bits x ^^^ BitVec.twoPow 7 i).getLsbD j = _
        simp [Fin.ext_iff]
      refine ⟨i, ?_, ?_⟩
      · change (bits x).getLsbD i ≠ (bits (flip x i)).getLsbD i
        rw [hbits]
        simp
      · intro j hj
        by_contra hji
        rw [hbits] at hj
        simp [hji] at hj }
  injective' := by
    intro x y h
    exact congrArg BitVec.toFin (BitVec.eq_of_getLsbD_eq fun i hi => congrFun h ⟨i, hi⟩)

-- The endpoints of non-backtracking two-step walks from x, grouped by the first step.
private def onward (x a : Vertex) := (neighbors a).filter (· != x)

private theorem distinct_endpoints :
    ∀ x : Vertex, ((neighbors x).flatMap (onward x)).Nodup := by decide +kernel

private theorem witness_free : (cycleGraph 4).Free witness := by
  rintro ⟨f⟩
  have edge (i j : Fin 4) (h : (cycleGraph 4).Adj i j) : f j ∈ neighbors (f i) :=
    f.toHom.map_adj h
  have h13 : f 1 ≠ f 3 := f.injective.ne (by decide)
  have h20 : f 2 ≠ f 0 := f.injective.ne (by decide)
  have hd := (List.nodup_flatMap.mp (distinct_endpoints (f 0))).2
  have disj := hd.forall (edge 0 1 (by decide)) (edge 0 3 (by decide)) h13
  apply disj (a := f 2)
  · simp [onward, h20, edge 1 2 (by decide)]
  · simp [onward, h20, edge 3 2 (by decide)]

private theorem witness_count : witness.edgeSet.ncard = 304 := by
  let : DecidableRel witness.Adj := fun x y => inferInstanceAs (Decidable (y ∈ neighbors x))
  have hn (x : Vertex) : witness.neighborFinset x = (neighbors x).toFinset := by
    ext y
    rw [mem_neighborFinset, List.mem_toFinset]
    rfl
  have hd : (∑ x : Vertex, (neighbors x).toFinset.card) = 608 := by decide +kernel
  simp_rw [← hn, card_neighborFinset_eq_degree, witness.sum_degrees_eq_twice_card_edges] at hd
  rw [← witness.coe_edgeFinset, Set.ncard_coe_finset]
  omega

/-- **Lower bound for four-cycle-free subgraphs of the seven-dimensional hypercube.** Let $Q_7$
be the $7$-dimensional hypercube and $C_4$ the cycle on four vertices. The largest number
$\mathrm{ex}(Q_7, C_4)$ of edges of a subgraph of $Q_7$ that contains no copy of $C_4$ is at
least $304$.

The bound is witnessed by an explicit construction.

Source: M. Minamoto, *C₄-free subgraphs of the hypercubes Q₆, Q₇, and Q₈*,
arXiv:2603.29127 (2026); listed in SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem le_hypercubeTuranNumber_seven_cycleGraph_four :
    304 ≤ hypercubeTuranNumber 7 (cycleGraph 4) := by
  have hfree := (free_congr_right inCube.isoToSubgraph).mp witness_free
  apply le_trans _ (le_hypercubeTuranNumber 7 inCube.toSubgraph hfree)
  rw [Copy.toSubgraph, Subgraph.edgeSet_map, Subgraph.edgeSet_top,
    Set.ncard_image_of_injective _ (Sym2.map.injective inCube.injective), witness_count]

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
