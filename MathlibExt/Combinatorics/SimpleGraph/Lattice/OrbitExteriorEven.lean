/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitLoopBridge

/-!
# Sites outside a boundary orbit loop have even ray count

The parity of the ray count of a closed walk is constant along lattice paths avoiding it, and it is
even at sites left of the whole walk. Hence a site joined to such a far site by a path avoiding the
face loop of a boundary orbit is outside the loop. If every site outside `K` is joined this way, the
complement of `K` lies outside the loop.

## Main results

* `StatMech.Lattice.oee_rayParity_const_along_walk`: ray parity is constant along paths avoiding the
  loop.
* `StatMech.Lattice.oee_farLeft_even`: sites left of the loop have even ray count.
* `StatMech.Lattice.oee_exterior_even`: sites joined to a far-left site avoiding the loop have even
  ray count.
* `StatMech.Lattice.oee_outsideHalf_of_exteriorEq`: under that connectivity, all sites outside `K`
  have even ray count.
* `StatMech.Lattice.owr_exists_not_exteriorHyp`: for finite nonempty `K`, that connectivity fails
  for the leftward dart out of a leftmost site of `K`.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

theorem oee_rayParity_const_along_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w hadj q ih =>
    have hu : u ∉ Vc.support := hp u (by simp)
    have hv : v ∉ Vc.support := hp v (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    exact (jec_localConstancy Vc hadj hu hv).trans (ih htail)

theorem oee_rayCount_eq_zero_of_farLeft (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (z : Site 2)
    (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
    jec_rayCount z (olb_orbitLoop K hK e he) = 0 :=
  jec_rayCount_eq_zero_of_right z (olb_orbitLoop K hK e he) hfar

theorem oee_farLeft_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (z : Site 2)
    (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  rw [oee_rayCount_eq_zero_of_farLeft K hK e he z hfar]
  exact Nat.even_iff.mpr rfl

theorem oee_exterior_even (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {z z0 : Site 2}
    (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)
    (hfar : ∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  have hbase : Even (jec_rayCount z0 (olb_orbitLoop K hK e he)) :=
    oee_farLeft_even K hK e he z0 hfar
  have hconst := oee_rayParity_const_along_walk (olb_orbitLoop K hK e he) p hp
  exact hconst.mpr hbase

/-- The exterior hypothesis `hExt` of `oee_outsideHalf_of_exteriorEq` (every site outside `K` is
joined, by a lattice path avoiding the support of the orbit loop of `e`, to a site weakly left of
that loop) fails for some boundary dart of every finite nonempty `K`. Take `c ∈ K` with least
first coordinate and `e` the dart from `c` to `c - (1,0)`: the face label
`dartFace e = c - (1,1)` lies outside `K` and on the orbit loop of `e`, so no path from it avoids
the loop. In particular `hExt` cannot hold for all boundary darts of a finite nonempty set. -/
theorem owr_exists_not_exteriorHyp (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ (e : Dart) (he : IsBoundaryDart K e),
      ¬ ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
        (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0) := by
  obtain ⟨c, hc, hmin⟩ := Set.exists_min_image K (fun z : Site 2 => z 0) hK hne
  have hnot : ∀ z : Site 2, z 0 < c 0 → z ∉ K := fun z hz hzK =>
    absurd (hmin z hzK) (not_le.mpr hz)
  have hg : unitWt (![-1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  have he : IsBoundaryDart K (mkDart c ![-1, 0] hg) :=
    ⟨by rw [mkDart_tail]; exact hc, hnot _ (by simp)⟩
  refine ⟨mkDart c ![-1, 0] hg, he, fun hExt => ?_⟩
  have hface : dartFace (mkDart c ![-1, 0] hg) 0 = c 0 - 1 := by
    rw [dartFace_of_dir_left _ (mkDart_dir _ _ _)]; simp
  obtain ⟨z0, p, hp, -⟩ := hExt (dartFace (mkDart c ![-1, 0] hg))
    (hnot _ (by rw [hface]; omega))
  exact hp _ p.start_mem_support (olb_orbitLoop K hK _ he).start_mem_support

/-- If every site outside `K` is joined, by a lattice path avoiding the orbit loop of `e`, to a
site weakly left of the whole loop, then every site outside `K` has even ray count with respect
to that loop. The hypothesis `hExt` fails whenever some vertex of the orbit loop `olb_orbitLoop
K hK e he` lies outside `K`: a path from that vertex starts on the loop. This happens for the
leftward dart out of a site of `K` with least first coordinate, for every finite nonempty `K`
(`StatMech.Lattice.owr_exists_not_exteriorHyp`), and for every boundary dart of a single site.
Whether `hExt` can hold for some other dart is not settled, so the statement is kept. -/
theorem oee_outsideHalf_of_exteriorEq (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
    ∀ z, z ∉ K → Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
  intro z hz
  obtain ⟨z0, p, hp, hfar⟩ := hExt z hz
  exact oee_exterior_even K hK e he p hp hfar

end Lattice

end StatMech
