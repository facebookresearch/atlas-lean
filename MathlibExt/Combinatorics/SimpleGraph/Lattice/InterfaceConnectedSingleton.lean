/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnected

/-!
# Rotation of boundary darts about a site, and the single-site case of `InterfaceConnected`

Let `K` be a set of sites of `ℤ²` and `v ∉ K`. When the sites `v - r d`, `v - r² d`, … obtained by
rotating a direction `d` counterclockwise about `v` lie in `K`, the successor map `dartNext K` turns
a boundary dart with head `v` about `v`, one quarter turn per step; so every boundary dart with head
`v` whose direction lies on that arc is in the same orbit. For a single site `K = {c}` the successor
of a boundary dart is the next dart out of `c` in clockwise order, so the four boundary darts of
`{c}` form one orbit and `{c}` satisfies `InterfaceConnected`.

## Main definitions

* `StatMech.Lattice.facingDart v g hg`: the dart with direction `g` and head `v`, for a unit
  vector `g`.

## Main results

* `StatMech.Lattice.ifc_facing_rotateArc_sameOrbit`: if the sites on a counterclockwise arc about
  `v` lie in `K`, iterating `dartNext K` from a boundary dart with head `v` rotates it about `v`.
* `StatMech.Lattice.ifc_unit_four_cases`: the unit vectors of `ℤ²` are the four axis directions.
* `StatMech.Lattice.ifc_singleton_sameOrbit`: the boundary darts of a single site form one orbit.
* `StatMech.Lattice.ifc_interfaceConnected`: a single site satisfies `InterfaceConnected`.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The dart from `v - g` to `v`: it has direction `g` and head `v`, for a unit vector `g`. -/
noncomputable def facingDart (v g : Site 2) (hg : unitWt g = 1) : Dart := mkDart (v - g) g hg

@[simp] theorem facingDart_head (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).head = v := by
  unfold facingDart; rw [mkDart_head]; abel

@[simp] theorem facingDart_dir (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).dir = g := by
  unfold facingDart; rw [mkDart_dir]

@[simp] theorem facingDart_tail (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).tail = v - g := by
  unfold facingDart; rw [mkDart_tail]

/-- The dart `facingDart v g hg` is a boundary dart of `K` when `v - g ∈ K` and `v ∉ K`. -/
theorem facingDart_isBoundary (K : Set (Site 2)) (v g : Site 2) (hg : unitWt g = 1)
    (htail : v - g ∈ K) (hv : v ∉ K) : IsBoundaryDart K (facingDart v g hg) := by
  refine ⟨?_, ?_⟩
  · rw [facingDart_tail]; exact htail
  · rw [facingDart_head]; exact hv

/-- Let `d` be a dart with head `v`. If the sites `v - r^(j+1) d.dir`, `j < k`, lie in `K` (with `r
= rot90Fun` the counterclockwise quarter turn), then the first `k` iterates of `d` under `dartNext
K` are inner corners: each successor turns about `v`. -/
theorem ifc_arc_to_innerCorner (K : Set (Site 2)) (d : Dart) (v : Site 2) (hv : d.head = v) :
    ∀ k : ℕ, (∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) →
      (∀ j < k, IsInnerCorner K ((dartNext K)^[j] d)) := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro harc j hj
    have harcm : ∀ j' < m, v - rot90Fun^[j' + 1] d.dir ∈ K := fun j' hj' => harc j' (by omega)
    have hcornerm : ∀ j' < m, IsInnerCorner K ((dartNext K)^[j'] d) := ih harcm
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact hcornerm j hjm
    · have hjeq : j = m := by omega
      subst hjeq
      have hfix := dartNext_iterate_head_fixed K d j hcornerm
      unfold IsInnerCorner
      rw [hfix.1, hfix.2, hv]
      have heq : v + (-rot90Fun (rot90Fun^[j] d.dir)) = v - rot90Fun^[j + 1] d.dir := by
        rw [← Function.iterate_succ_apply' rot90Fun j d.dir]; abel
      rw [heq]; exact harc j (by omega)

/-- Rotation about a site along an arc of `K`. Let `d` be a boundary dart of `K` with head `v` in
the orbit of `e`. If the sites `v - r^(j+1) d.dir`, `j < k`, lie in `K`, then the `k`-th iterate of
`d` is a boundary dart in the orbit of `e` with head `v` and direction `r^k d.dir`. -/
theorem ifc_facing_rotateArc_sameOrbit (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (v : Site 2) (hv : d.head = v)
    (hsame : SameOrbit K e d) (k : ℕ)
    (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) :
    ∃ d' : Dart, IsBoundaryDart K d' ∧ d'.head = v ∧ d'.dir = rot90Fun^[k] d.dir ∧
      SameOrbit K e d' := by
  have hcorner : ∀ j < k, IsInnerCorner K ((dartNext K)^[j] d) :=
    ifc_arc_to_innerCorner K d v hv k harc
  have hfix := dartNext_iterate_isBoundary_head_fixed K d hd k hcorner
  refine ⟨(dartNext K)^[k] d, hfix.1, by rw [hfix.2.1, hv], hfix.2.2, ?_⟩
  obtain ⟨n, hn⟩ := hsame
  exact ⟨k + n, by rw [Function.iterate_add_apply, hn]⟩

/-- Under the hypotheses of `ifc_facing_rotateArc_sameOrbit`, every boundary dart with head `v` and
direction `r^k d.dir` lies in the orbit of `e`. -/
theorem ifc_orbitVertexSaturate_contiguous (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (v : Site 2) (hv : d.head = v)
    (hsame : SameOrbit K e d) (k : ℕ)
    (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K)
    (d' : Dart) (_hd' : IsBoundaryDart K d') (hv' : d'.head = v)
    (hdir' : d'.dir = rot90Fun^[k] d.dir) :
    SameOrbit K e d' := by
  obtain ⟨d'', _, hh'', hdd'', hsame''⟩ := ifc_facing_rotateArc_sameOrbit K e d hd v hv hsame k harc
  have hdeq : d'' = d' := dart_eq_of_head_dir (by rw [hh'', hv']) (by rw [hdd'', hdir'])
  rwa [hdeq] at hsame''

/-- For a single site `c`, the successor of a boundary dart `e` of `{c}` is the dart out of `c`
whose direction is `e.dir` turned clockwise by a quarter turn. See also `dartNext_ucDart0` and
its siblings, the explicit computation for `unitCell = {0}`. -/
theorem ifc_dartNext_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    (dartNext ({c} : Set (Site 2)) e).tail = c ∧
      (dartNext ({c} : Set (Site 2)) e).dir = -rot90Fun e.dir := by
  have htail : e.tail = c := he.1
  have hA : e.head + (-rot90Fun e.dir) ∉ ({c} : Set (Site 2)) := by
    simp only [Set.mem_singleton_iff]
    intro h
    have key : e.dir = rot90Fun e.dir := by
      have h1 : e.head - e.tail = rot90Fun e.dir := by rw [htail, ← h]; abel
      rw [Dart.dir_def]; exact h1
    exact rot90Fun_dartDir_ne_dartDir e key.symm
  have hB : e.tail + (-rot90Fun e.dir) ∉ ({c} : Set (Site 2)) := by
    simp only [Set.mem_singleton_iff, htail]
    intro h
    have hz : (-rot90Fun e.dir : Site 2) = 0 := by
      exact add_left_cancel (a := c) (b := -rot90Fun e.dir) (c := 0) (by rw [add_zero]; exact h)
    exact neg_rot90Fun_dartDir_ne_zero e hz
  exact ⟨by rw [dartNext_left_tail _ e hA hB, htail], by rw [dartNext_left_dir _ e hA hB]⟩

/-- For a single site `c`, the `n`-th iterate of a boundary dart `e` under `dartNext {c}` leaves `c`
in the direction `e.dir` turned clockwise `n` times. -/
theorem ifc_dartNext_singleton_iterate (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) (n : ℕ) :
    ((dartNext ({c} : Set (Site 2)))^[n] e).tail = c ∧
      ((dartNext ({c} : Set (Site 2)))^[n] e).dir = (fun x => -rot90Fun x)^[n] e.dir := by
  induction n with
  | zero => exact ⟨he.1, rfl⟩
  | succ m ih =>
    have hbd : IsBoundaryDart ({c} : Set (Site 2)) ((dartNext ({c} : Set (Site 2)))^[m] e) :=
      iterate_isBoundaryDart _ e he m
    rw [Function.iterate_succ_apply']
    have hstep := ifc_dartNext_singleton c _ hbd
    exact ⟨hstep.1, by rw [hstep.2, ih.2, Function.iterate_succ_apply']⟩

/-- The unit vectors of `ℤ²` (those of `ℓ¹` norm one) are `(1,0)`, `(-1,0)`, `(0,1)` and `(0,-1)`.
See also `StatMech.Lattice.dartDir_cases`, the same statement for the direction of a dart. -/
theorem ifc_unit_four_cases (g : Site 2) (hg : unitWt g = 1) :
    g = ![1, 0] ∨ g = ![-1, 0] ∨ g = ![0, 1] ∨ g = ![0, -1] := by
  unfold unitWt at hg
  rw [Fin.sum_univ_two] at hg
  have hcase : ((g 0).natAbs = 1 ∧ (g 1).natAbs = 0) ∨ ((g 0).natAbs = 0 ∧ (g 1).natAbs = 1) := by
    omega
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hb' : g 1 = 0 := by omega
    rcases Int.natAbs_eq_iff.mp ha with h | h
    · left; funext i; fin_cases i <;> simp_all
    · right; left; funext i; fin_cases i <;> simp_all
  · have ha' : g 0 = 0 := by omega
    rcases Int.natAbs_eq_iff.mp hb with h | h
    · right; right; left; funext i; fin_cases i <;> simp_all
    · right; right; right; funext i; fin_cases i <;> simp_all

/-- Repeated clockwise quarter turns carry any unit vector of `ℤ²` to any other. -/
theorem ifc_singleton_cover (g0 g1 : Site 2) (h0 : unitWt g0 = 1) (h1 : unitWt g1 = 1) :
    ∃ n : ℕ, (fun x => -rot90Fun x)^[n] g0 = g1 := by
  rcases ifc_unit_four_cases g0 h0 with rfl | rfl | rfl | rfl <;>
  rcases ifc_unit_four_cases g1 h1 with rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩

/-- The four boundary darts of a single site `c` form one orbit of `dartNext {c}`. -/
theorem ifc_singleton_sameOrbit (c : Site 2) (e f : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e)
    (hf : IsBoundaryDart ({c} : Set (Site 2)) f) :
    SameOrbit ({c} : Set (Site 2)) e f := by
  obtain ⟨n, hn⟩ := ifc_singleton_cover e.dir f.dir (unitWt_dir e) (unitWt_dir f)
  refine ⟨n, ?_⟩
  have hiter := ifc_dartNext_singleton_iterate c e he n
  have htail : ((dartNext ({c} : Set (Site 2)))^[n] e).tail = f.tail := by rw [hiter.1, hf.1]
  have hdir : ((dartNext ({c} : Set (Site 2)))^[n] e).dir = f.dir := by rw [hiter.2, hn]
  exact dart_eq_of_tail_dir htail hdir

/-- A single site satisfies `InterfaceConnected`: all its boundary darts lie in one orbit. -/
theorem ifc_interfaceConnected (c : Site 2) : InterfaceConnected ({c} : Set (Site 2)) := by
  intro e f he hf _hreach
  exact ifc_singleton_sameOrbit c e f he hf

end Lattice

end StatMech
