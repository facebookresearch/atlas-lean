/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchStarHull

/-!
# Local turns, convex corners, and winding witnesses

Let `K` be a set of sites of `ℤ²` and `a` a boundary dart of `K`. The total turn of the boundary
orbit of `a` is the sum over faces of the local turn at each face (`usc_localTurn`). If every face
is visited at most once (`usc_FaceMultiplicityOne`, which holds for star hulls), each local turn is
`1`, `0` or `-1`. So an orbit with total turn `±4` has a face whose local turn has the same sign
(a convex corner of the contour) and, for turn `1`, a dart there whose diagonal site lies in `K`.

A winding witness is a site of `K` lying inside the face loop of the orbit by the even–odd rule
(odd ray count). If one of the orbit's dart tails is such a site (`wwit_TailOdd`), it is a witness;
for star hulls this feeds the boundary-matching criterion
`pbs_bdEdgeMatch_starHull_of_winding`. The unit square loop has the site `(1, 1)` inside.

## Main definitions

* `StatMech.Lattice.wwit_cornerCell e`: the site diagonally ahead of the dart `e`.
* `StatMech.Lattice.wwit_TailOdd K hK a`: some dart tail of the orbit of `a` has odd ray count with
  respect to the face loop of the orbit.
* `StatMech.Lattice.wwit_unitSquareLoop`: the closed walk around the unit square
  `(0,0) → (0,1) → (1,1) → (1,0) → (0,0)`.

## Main results

* `StatMech.Lattice.wwit_localTurn_mem`: without repeated faces, every local turn is `1`, `0` or
  `-1`.
* `StatMech.Lattice.wwit_exists_convex_corner`,
  `StatMech.Lattice.wwit_starHull_exists_convex_corner`: an orbit with total turn `±4` and no
  repeated faces has a face of local turn `±1` of the matching sign.
* `StatMech.Lattice.wwit_dart_of_localTurn_one`: a face of local turn `1` carries a dart of turn
  `1`.
* `StatMech.Lattice.wwit_winding_witness_of_tailOdd`: a dart tail with odd ray count is a winding
  witness.
* `StatMech.Lattice.wwit_starHull_bdEdgeMatch_of_tailOdd`: for star hulls, an odd dart tail plus
  connectivity hypotheses gives `pww_BdEdgeMatch`.
* `StatMech.Lattice.wwit_unitSquareLoop_inside_odd`: `(1, 1)` has ray count one with respect to the
  unit square loop.
-/

@[expose] public section

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice

/-- The local turn at a face visited exactly once is `1`, `0` or `-1`. -/
theorem wwit_singleVisit_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2) (i : ℕ)
    (h : usc_visitSet K a f = {i}) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  rw [usc_singleVisit_local_turn K a f i h]
  exact turnZ_mem K _

/-- If no face is visited twice by the orbit, every local turn is `1`, `0` or `-1`. -/
theorem wwit_localTurn_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  classical
  rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
  · right; left
    unfold usc_localTurn
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty]
  · have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
    exact wwit_singleVisit_localTurn_mem K a f i hi

/-- A finite sum of values in `{1, 0, -1}` equal to `4` has a term equal to `1`. See also
`Finset.exists_lt_of_sum_lt`. -/
theorem wwit_exists_pos_of_sum_eq_four {s : Finset (Site 2)} (g : Site 2 → ℤ)
    (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
    (hsum : ∑ f ∈ s, g f = 4) :
    ∃ f ∈ s, g f = 1 := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ f ∈ s, g f ≤ 0 := by
    intro f hf
    rcases hg f hf with h | h | h
    · exact absurd h (hcon f hf)
    · omega
    · omega
  have : (∑ f ∈ s, g f) ≤ 0 := Finset.sum_nonpos hle
  omega

/-- A finite sum of values in `{1, 0, -1}` equal to `-4` has a term equal to `-1`. -/
theorem wwit_exists_neg_of_sum_eq_negFour {s : Finset (Site 2)} (g : Site 2 → ℤ)
    (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
    (hsum : ∑ f ∈ s, g f = -4) :
    ∃ f ∈ s, g f = -1 := by
  by_contra hcon
  push Not at hcon
  have hge : ∀ f ∈ s, 0 ≤ g f := by
    intro f hf
    rcases hg f hf with h | h | h
    · omega
    · omega
    · exact absurd h (hcon f hf)
  have : (0 : ℤ) ≤ ∑ f ∈ s, g f := Finset.sum_nonneg hge
  omega

/-- An orbit with no repeated faces and total turn `±4` has a face of local turn `1` (total `4`) or
`-1` (total `-4`). -/
theorem wwit_exists_convex_corner (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (hturn : TurningIsFullRevolution K a) :
    (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = 1) ∨
      (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = -1) := by
  have hsum := (usc_totalTurnZ_eq_sum_localTurn K a).symm
  rcases hturn with h4 | hm4
  · left
    rw [h4] at hsum
    exact wwit_exists_pos_of_sum_eq_four (usc_localTurn K a)
      (fun f _ => wwit_localTurn_mem K a hmult f) hsum
  · right
    rw [hm4] at hsum
    exact wwit_exists_neg_of_sum_eq_negFour (usc_localTurn K a)
      (fun f _ => wwit_localTurn_mem K a hmult f) hsum

/-- Every local turn of a boundary orbit of a star hull is `1`, `0` or `-1`. -/
theorem wwit_starHull_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2) :
    usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨
      usc_localTurn (ndt_StarHull K) a f = -1 :=
  wwit_localTurn_mem (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) f

/-- A boundary orbit of a star hull with total turn `±4` has a face of local turn of the matching
sign. -/
theorem wwit_starHull_exists_convex_corner (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hturn : TurningIsFullRevolution (ndt_StarHull K) a) :
    (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨
      (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) :=
  wwit_exists_convex_corner (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) hturn

/-- With no repeated faces, a face of local turn `1` is the face of a unique dart of the orbit, and
that dart has turn `1`. -/
theorem wwit_dart_of_localTurn_one (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) (hf1 : usc_localTurn K a f = 1) :
    ∃ i : ℕ, i ∈ usc_visitSet K a f ∧
      dartFace ((dartNext K)^[i] a.1) = f ∧ turnZ K ((dartNext K)^[i] a.1) = 1 := by
  classical
  have hpos : 1 ≤ (usc_visitSet K a f).card := by
    by_contra hcon
    push Not at hcon
    have h0 : (usc_visitSet K a f).card = 0 := by omega
    rw [Finset.card_eq_zero] at h0
    rw [usc_localTurn, h0, Finset.sum_empty] at hf1
    exact absurd hf1 (by norm_num)
  have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
  have himem : i ∈ usc_visitSet K a f := by rw [hi]; exact Finset.mem_singleton_self i
  have hface : dartFace ((dartNext K)^[i] a.1) = f := by
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at himem
    exact himem.2
  have hturn : turnZ K ((dartNext K)^[i] a.1) = 1 := by
    have := usc_singleVisit_local_turn K a f i hi
    rw [hf1] at this
    exact this.symm
  exact ⟨i, himem, hface, hturn⟩

/-- If the turn at `e` is `1`, the site diagonally ahead of `e` lies in `K`. -/
theorem wwit_cornerCell_mem (K : Set (Site 2)) (e : Dart) (hturn : turnZ K e = 1) :
    e.head + (-rot90Fun e.dir) ∈ K := by
  classical
  unfold turnZ at hturn
  by_contra hmem
  rw [ite_eq_right hmem] at hturn
  split_ifs at hturn with hb
  all_goals simp_all

/-- The site diagonally ahead of the dart `e`: `e.head` moved a quarter turn clockwise from
`e.dir`. -/
noncomputable def wwit_cornerCell (e : Dart) : Site 2 := e.head + (-rot90Fun e.dir)

@[simp] theorem wwit_cornerCell_def (e : Dart) :
    wwit_cornerCell e = e.head + (-rot90Fun e.dir) := rfl

/-- Some dart tail of the boundary orbit of `a` has odd ray count with respect to the face loop of
the orbit, i.e. lies inside it by the even–odd rule. -/
def wwit_TailOdd (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (olb_orbitLoop K hK a.1 a.2))

/-- Winding witness: under `wwit_TailOdd`, some site of `K` lies inside the face loop of the orbit
by the even–odd rule. Immediate from the hypothesis, which already names such a site among the dart
tails. -/
theorem wwit_winding_witness_of_tailOdd (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hprim : wwit_TailOdd K hK a) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := by
  obtain ⟨i, hodd⟩ := hprim
  exact ⟨((dartNext K)^[i] a.1).tail, (iterate_isBoundaryDart K a.1 a.2 i).tail_mem, hodd⟩

/-- For a finite star hull, an odd dart tail of the orbit, together with an exterior escape
hypothesis (every site outside reaches a site left of the loop avoiding it) and an interior
connectivity hypothesis (every site inside reaches that tail avoiding the loop), shows that the
star hull and the inside of its face loop have the same boundary edges. -/
theorem wwit_starHull_bdEdgeMatch_of_tailOdd (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (i : ℕ)
    (hodd : ¬ Even (jec_rayCount ((dartNext (ndt_StarHull K))^[i] a.1).tail
      (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)))
    (hExt : ∀ z, z ∉ ndt_StarHull K → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support) ∧
      (∀ q ∈ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support, z0 0 ≤ q 0))
    (hInt : ∀ z, z ∈ ndt_StarHull K →
      ∃ p : (hypercubicLattice 2).Walk z ((dartNext (ndt_StarHull K))^[i] a.1).tail,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support)) :
    pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2) :=
  pbs_bdEdgeMatch_starHull_of_winding K hSK a.1 a.2 hExt
    (iterate_isBoundaryDart (ndt_StarHull K) a.1 a.2 i).tail_mem hodd hInt

/-- The closed walk `(0,0) → (0,1) → (1,1) → (1,0) → (0,0)` around the unit square. -/
noncomputable def wwit_unitSquareLoop : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 0] ![0, 1] :=
    (jec_vsegUp 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 1] ![1, 0] :=
    ((jec_vsegUp 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![1, 0] ![0, 0] :=
    ((jec_hsegRight 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))

/-- The site `(1, 1)` has odd ray count (one) with respect to the unit square loop. -/
theorem wwit_unitSquareLoop_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) := by
  have hcount : jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
    unfold wwit_unitSquareLoop
    simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
      jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  rw [hcount]
  decide

end Lattice

end StatMech
