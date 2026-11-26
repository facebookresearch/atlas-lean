/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullWinding

/-!
# Leftmost vertical steps come from leftward darts

Let `m` be the leftmost column of a finite set `K`. A vertical step of the face loop of a boundary
orbit (two consecutive faces in the same column) in a column at most `m - 1` must come from a
leftward dart: a rightward dart there would have a site of `K` left of column `m` below it. So if
the orbit has some vertical step in a column at most `m - 1` (`lmo_OrbitReachesLeftmost`), its
leftmost vertical step comes from a leftward dart and, when its face loop is a cycle, the orbit
has a winding witness. A leftward boundary dart whose tail lies in column `m` provides such a step.

The lexicographically least site of a finite nonempty set has no site of the set directly to its
left or directly below it; its leftward dart is a boundary dart.

## Main definitions

* `StatMech.Lattice.lmo_lexKey z`: the lexicographic key `(z 0, z 1)` of a site.
* `StatMech.Lattice.lmo_OrbitReachesLeftmost K a m`: the face loop of the orbit of `a` has a
  vertical step in a column at most `m - 1`.

## Main results

* `StatMech.Lattice.lmo_lexMinCell`: a finite nonempty set has a site in its leftmost column with
  no site of the set directly to its left or directly below it.
* `StatMech.Lattice.lmo_vertStep_left_of_minCol`: vertical steps left of the leftmost column come
  from leftward darts.
* `StatMech.Lattice.lmo_windingWitness_of_reachesLeftmost`: an orbit whose face loop is a cycle
  and reaches left of the leftmost column has a winding witness.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The lexicographic key `(z 0, z 1)` of a site: first column, then row. -/
noncomputable def lmo_lexKey (z : Site 2) : ℤ ×ₗ ℤ := toLex (z 0, z 1)

/-- A finite nonempty set has a site `z₀` in its leftmost column such that neither `z₀ - (1, 0)` nor
`z₀ - (0, 1)` lies in the set (the lexicographically least site). See also `exists_extremeCell`
for the top-row, leftmost site. -/
theorem lmo_lexMinCell (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K ∧ (![z₀ 0, z₀ 1 - 1] : Site 2) ∉ K ∧
      (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  classical
  have hKf : hK.toFinset.Nonempty := by rw [Set.Finite.toFinset_nonempty]; exact hne
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := hK.toFinset.exists_min_image lmo_lexKey hKf
  rw [Set.Finite.mem_toFinset] at hz₀mem
  have hmin : ∀ w ∈ K, lmo_lexKey z₀ ≤ lmo_lexKey w := fun w hw =>
    hz₀min w (Set.Finite.mem_toFinset _ |>.mpr hw)
  refine ⟨z₀, hz₀mem, ?_, ?_, ?_⟩
  · intro hin
    have := hmin _ hin
    rw [lmo_lexKey, lmo_lexKey] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · omega
  · intro hin
    have := hmin _ hin
    rw [lmo_lexKey, lmo_lexKey] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · obtain ⟨_, h2⟩ := h; omega
  · intro w hw
    have := hmin w hw
    rw [lmo_lexKey, lmo_lexKey] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · obtain ⟨h1, _⟩ := h; omega

/-- The head of the leftward dart at `z₀` is `(z₀ 0 - 1, z₀ 1)`. -/
theorem lmo_leftDartAt_head (z₀ : Site 2) :
    (leftDart z₀).head = ![z₀ 0 - 1, z₀ 1] := by
  rw [leftDart, mkDart_head]; funext i; fin_cases i <;> (simp; try ring)

/-- The leftward dart at a site of `K` is a boundary dart when the site to its left is not in
`K`. -/
theorem lmo_leftDartAt_isBoundaryDart {K : Set (Site 2)} {z₀ : Site 2} (hz₀ : z₀ ∈ K)
    (hwest : (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K) :
    IsBoundaryDart K (leftDart z₀) := by
  refine ⟨?_, ?_⟩
  · rw [leftDart_tail]; exact hz₀
  · rw [lmo_leftDartAt_head]; exact hwest

/-- The face to the left of the leftward dart at `z₀` is `(z₀ 0 - 1, z₀ 1 - 1)`. -/
theorem lmo_leftDartAt_face (z₀ : Site 2) :
    dartFace (leftDart z₀) = ![z₀ 0 - 1, z₀ 1 - 1] := by
  rw [dartFace_of_dir_left _ (leftDart_dir z₀), leftDart_tail]

/-- If every site of `K` lies in column at least `m`, a vertical step of a boundary dart of `K` in a
column at most `m - 1` comes from a leftward dart. -/
theorem lmo_vertStep_left_of_minCol {K : Set (Site 2)} (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    {e : Dart} (he : IsBoundaryDart K e)
    (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
    (hcol : (dartFace e) 0 ≤ m - 1) :
    e.dir = ![-1, 0] := by
  rcases shw_vertStep_dir K e hvert with hd | hd
  · exfalso
    have h := (npd_corners_right he hd).1
    rw [npd_P00] at h
    have := hm _ h
    simp only [Matrix.cons_val_zero] at this
    omega
  · exact hd

/-- The face loop of the orbit of `a` has a vertical step in a column at most `m - 1`. -/
def lmo_OrbitReachesLeftmost (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) :
    Prop :=
  ∃ k < dartOrbitPeriod K a,
    ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
    (dartFace ((dartNext K)^[k] a.1)) 0 ≤ m - 1

/-- If all sites of `K` lie in column at least `m` and the orbit reaches column `m - 1` with a
vertical step, its leftmost vertical step comes from a leftward dart. -/
theorem lmo_minVertStepLeft_of_reachesLeftmost (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    (hreach : lmo_OrbitReachesLeftmost K a m) :
    shw_MinVertStepLeft K a := by
  classical
  obtain ⟨k0, hk0, hv0, hcol0⟩ := hreach
  set p := dartOrbitPeriod K a with hp
  set S := (Finset.range p).filter
    (fun k => (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0)
    with hS
  have hSne : S.Nonempty :=
    ⟨k0, by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩⟩
  obtain ⟨k, hkS, hkmin⟩ :=
    S.exists_min_image (fun k => (dartFace ((dartNext K)^[k] a.1)) 0) hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hkS
  obtain ⟨hklt, hkv⟩ := hkS
  have hkmin' : ∀ j < p,
      (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
        (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0 := by
    intro j hj hvj
    exact hkmin j (by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hvj⟩)
  have hk0S : k0 ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩
  have hcolk : (dartFace ((dartNext K)^[k] a.1)) 0 ≤ m - 1 :=
    le_trans (hkmin k0 hk0S) hcol0
  have hbk : IsBoundaryDart K ((dartNext K)^[k] a.1) := iterate_isBoundaryDart K a.1 a.2 k
  have hkv' : (dartFace ((dartNext K)^[k] a.1)) 0
      = (dartFace (dartNext K ((dartNext K)^[k] a.1))) 0 := by
    rwa [← Function.iterate_succ_apply' (dartNext K) k a.1]
  have hleft : ((dartNext K)^[k] a.1).dir = ![-1, 0] :=
    lmo_vertStep_left_of_minCol m hm hbk hkv' hcolk
  exact ⟨k, hklt, hkv, hkmin', hleft⟩

/-- An orbit whose face loop is a cycle and which has a vertical step left of the leftmost column of
`K` has a winding witness. -/
theorem lmo_windingWitness_of_reachesLeftmost (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K a).IsCycle)
    (hreach : lmo_OrbitReachesLeftmost K a m) :
    wei_WindingWitness K a :=
  shw_windingWitness_of_minLeft K a hcyc
    (lmo_minVertStepLeft_of_reachesLeftmost K a m hm hreach)

/-- The unit cell lies in column at least `0`. -/
theorem lmo_unitCell_minColumn : ∀ w ∈ unitCell, (0 : ℤ) ≤ w 0 := by
  intro w hw
  rw [unitCell, Set.mem_singleton_iff] at hw
  rw [hw]; simp

/-- The unit cell orbit has a vertical step in column `-1`. -/
theorem lmo_unitCell_reachesLeftmost :
    lmo_OrbitReachesLeftmost unitCell ucBase 0 := by
  refine ⟨2, ?_, ?_, ?_⟩
  · rw [unitCell_orbitPeriod_eq_four]; norm_num
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2,
        mpl_dartFace_iterate_ucDart3]; rfl
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2]
    change (-1 : ℤ) ≤ (0 : ℤ) - 1; norm_num

/-- The face column of a leftward dart is one left of its tail. -/
theorem lmo_face_col_left {e : Dart} (hd : e.dir = ![-1, 0]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_left e hd]; simp

/-- The face column of an upward dart is one left of its tail. -/
theorem lmo_face_col_up {e : Dart} (hd : e.dir = ![0, 1]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_up e hd]; simp

/-- The face column of a rightward dart is the column of its tail. -/
theorem lmo_face_col_right {e : Dart} (hd : e.dir = ![1, 0]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_right e hd]; simp

/-- The face column of a downward dart is the column of its tail. -/
theorem lmo_face_col_down {e : Dart} (hd : e.dir = ![0, -1]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_down e hd]; simp

/-- If the orbit of `a` contains a leftward dart with tail in column `m`, it has a vertical step in
column `m - 1`. -/
theorem lmo_reachesLeftmost_of_left_tail (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ)
    {k : ℕ} (hk : k < dartOrbitPeriod K a)
    (htail : ((dartNext K)^[k] a.1).tail 0 = m)
    (hd : ((dartNext K)^[k] a.1).dir = ![-1, 0]) :
    lmo_OrbitReachesLeftmost K a m := by
  refine ⟨k, hk, ?_, ?_⟩
  · rw [show (dartNext K)^[k + 1] a.1 = dartNext K ((dartNext K)^[k] a.1) from by
        rw [Function.iterate_succ_apply']]
    exact shw_vertStep_left K _ hd
  · rw [lmo_face_col_left hd, htail]

end Lattice

end StatMech
