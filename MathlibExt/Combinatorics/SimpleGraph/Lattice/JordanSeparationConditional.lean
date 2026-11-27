/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ClosedContourSeparation

/-!
# Jordan separation for closed lattice walks, assuming each side is connected

Let `Vc` be a closed walk in the square lattice `ℤ²`. Its inside `jec_leftRegion Vc`, by the
even–odd rule, is the set of sites `z` whose ray count `jec_rayCount z Vc` is odd: the leftward
horizontal ray from the face centre `z - (1/2, 1/2)` crosses `Vc` an odd number of times. Removing
the barrier edges (lattice edges with exactly one endpoint inside) gives `latticeMinusBarrier`.
No path in it joins the inside to the outside, sites far to the right of `Vc` are outside, and the
ray parity is constant on its connected components.

The predicate `jsc_JordanSeparates Vc` packages the remaining Jordan-curve input: the inside is
nonempty and each side is connected in `latticeMinusBarrier`. Under it, the barrier graph has
exactly two connected components. The same conclusion holds for a finite open cluster whose
boundary is the inside of some closed walk, assuming its outside is connected.

## Main definitions

* `StatMech.Lattice.jsc_JordanSeparates Vc`: the inside of `Vc` is nonempty and each of the inside
  and the outside is connected after the barrier edges are removed.
* `StatMech.Lattice.jsc_unitSquareLoop`: the closed walk around the unit square
  `(0,0) → (0,1) → (1,1) → (1,0) → (0,0)`.

## Main results

* `StatMech.Lattice.jsc_exists_outside`: some site to the right of `Vc` is outside.
* `StatMech.Lattice.jsc_inside_not_reachable_outside`, `StatMech.Lattice.jsc_side_constant`:
  the barrier graph never joins sites of different ray parity.
* `StatMech.Lattice.jsc_separation_of_JordanSeparates`: under `jsc_JordanSeparates Vc`, removing the
  barrier leaves exactly two components, and inside and outside are not joined.
* `StatMech.Lattice.jsc_cycle_separation`: for a cycle, additionally the combinatorial face count is
  two.
* `StatMech.Lattice.jsc_separation_of_loopBridge`: a finite cluster that is the inside of a closed
  walk and has connected outside splits the barrier graph into two components.
* `StatMech.Lattice.jsc_JordanSeparates_inside_satisfiable`: the unit square loop has a site of odd
  ray count, so the first clause of `jsc_JordanSeparates` is satisfiable.

The connectivity of each side is a hypothesis throughout; it is the hard half of the Jordan curve
theorem and is not proved here. Compare `StatMech.Lattice.ccs_closedLoop_two_components`, of which
`jsc_two_components_of_connected` is a restatement with the far outside site chosen.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The first coordinates of the sites of a walk are bounded above. See also
`StatMech.Lattice.rlc_support_bound`, which bounds both coordinates in absolute value for closed
walks. -/
theorem jsc_walk_col_bound {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a b) :
    ∃ M : ℤ, ∀ p ∈ Vc.support, p 0 ≤ M := by
  classical
  refine ⟨(Vc.support.map (fun p => p 0)).foldr max 0, ?_⟩
  intro p hp
  have hmem : p 0 ∈ Vc.support.map (fun p => p 0) := List.mem_map_of_mem hp
  have hkey : ∀ (l : List ℤ) (x : ℤ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; exact absurd hx (List.not_mem_nil)
    | cons c t ih =>
      intro x hx
      rw [List.foldr_cons]
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)
  exact hkey _ _ hmem

/-- Every closed walk has an outside site `q` lying strictly to the right of all its sites. -/
theorem jsc_exists_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ q : Site 2, q ∉ jec_leftRegion Vc ∧ ∀ p ∈ Vc.support, p 0 ≤ q 0 - 1 := by
  obtain ⟨M, hM⟩ := jsc_walk_col_bound Vc
  refine ⟨![M + 1, 0], ?_, ?_⟩
  · rw [jec_mem_leftRegion, not_not]
    refine jec_ray_even_far Vc ![M + 1, 0] ?_
    intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega
  · intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega

/-- After removing the barrier edges of the inside of `Vc`, no path joins a site of odd ray count
to a site of even ray count. -/
theorem jsc_inside_not_reachable_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : ¬ Even (jec_rayCount x Vc)) (hy : Even (jec_rayCount y Vc)) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc)
    (by rw [jec_mem_leftRegion]; exact hx)
    (by rw [jec_mem_leftRegion, not_not]; exact hy)

/-- Ray-count parity is constant on connected components of the barrier graph. -/
theorem jsc_side_constant {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  have hb := barrier_sameSide_of_reachable (jec_leftRegion Vc) h
  simp only [jec_mem_leftRegion] at hb
  exact not_iff_not.mp hb

/-- If the inside of `Vc` is nonempty and the inside and the outside are each connected in the
barrier graph, the barrier graph has exactly two connected components. -/
theorem jsc_two_components_of_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨q, _hq, hqfar⟩ := jsc_exists_outside Vc
  exact ccs_closedLoop_two_components Vc hp hqfar hin hout

/-- The Jordan-separation hypothesis for a closed walk `Vc`: some site has odd ray count (the inside
is nonempty), any two inside sites are joined in the barrier graph, and any two outside sites are
joined in the barrier graph. -/
def jsc_JordanSeparates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ p, ¬ Even (jec_rayCount p Vc)) ∧
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) ∧
    (∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)

/-- **Jordan separation, conditional form.** If the closed walk `Vc` satisfies
`jsc_JordanSeparates`, then removing the barrier edges of its inside leaves exactly two connected
components, some site is outside, and no inside site is joined to an outside site. The
connectivity of each side, the substantial part of the Jordan curve theorem (C. Jordan, 1887), is
assumed through `jsc_JordanSeparates`, not proved. -/
theorem jsc_separation_of_JordanSeparates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : jsc_JordanSeparates Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 ∧
      (∃ q : Site 2, q ∉ jec_leftRegion Vc) ∧
      (∀ x y : Site 2, ¬ Even (jec_rayCount x Vc) → Even (jec_rayCount y Vc) →
        ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := h
  obtain ⟨q, hq, _⟩ := jsc_exists_outside Vc
  exact ⟨jsc_two_components_of_connected Vc hp hin hout, ⟨q, hq⟩,
    fun x y hx hy => jsc_inside_not_reachable_outside Vc hx hy⟩

/-- For a lattice cycle satisfying `jsc_JordanSeparates`, the combinatorial face count of the cycle
is two and the barrier graph of its inside has exactly two components. The face count holds for
every cycle (`StatMech.Lattice.jcs_cycle_faceCount_eq_two`); only the second part uses the
hypothesis. -/
theorem jsc_cycle_separation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (hsep : jsc_JordanSeparates Vc) :
    faceCount Vc.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := hsep
  exact ⟨jcs_cycle_faceCount_eq_two Vc hcyc, jsc_two_components_of_connected Vc hp hin hout⟩

/-- A finite open cluster that is the inside of some closed walk (`ccs_OrbitIsLoop`) and whose
outside is connected in the barrier graph splits the barrier graph into exactly two components, the
cluster being the inside of a closed walk. Connectedness of the inside is automatic for a cluster;
the outside connectivity is a hypothesis. -/
theorem jsc_separation_of_loopBridge {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite)
    (hloop : ccs_OrbitIsLoop (cluster 2 ω o))
    (hout : ∀ s t : Site 2, s ∉ cluster 2 ω o → t ∉ cluster 2 ω o →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable s t) :
    Nat.card (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent = 2 ∧
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
        cluster 2 ω o = jec_leftRegion Vc := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  have hpin : o ∈ cluster 2 ω o := self_mem_cluster ω o
  have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hqout : beacon 2 R ∉ cluster 2 ω o := (exterior_subset_compl (cluster 2 ω o) R hR) hbe
  refine ccs_cluster_two_components (K := cluster 2 ω o) hloop hpin hqout ?_ hout
  intro s t hs ht; exact cluster_reachable_in_barrier o hs ht

/-- The closed walk `(0,0) → (0,1) → (1,1) → (1,0) → (0,0)` around the unit square. -/
noncomputable def jsc_unitSquareLoop : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 0] ![0, 1] :=
    (jec_vsegUp 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 1] ![1, 0] :=
    ((jec_vsegUp 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![1, 0] ![0, 0] :=
    ((jec_hsegRight 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))

/-- The site `(1, 1)`, labelling the unit square `[0, 1]²`, has ray count one with respect to the
unit square loop. -/
theorem jsc_unitSquareLoop_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop) := by
  have hcount : jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop = 1 := by
    unfold jsc_unitSquareLoop
    simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
      jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  rw [hcount]; decide

/-- Some closed walk has a site of odd ray count. This shows the first clause of
`jsc_JordanSeparates` is satisfiable; the two connectivity clauses are not checked here. -/
theorem jsc_JordanSeparates_inside_satisfiable :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ∃ p, ¬ Even (jec_rayCount p Vc) :=
  ⟨_, jsc_unitSquareLoop, _, jsc_unitSquareLoop_inside_odd⟩

end Lattice

end StatMech
