/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Lattice.UniqueInfiniteComponent
import Code.FK.InfiniteVolume

open Set SimpleGraph

namespace StatMech.FrontierB

open Lattice


def setCoordinates {d : ℕ} (x y : Site d) (T : Finset (Fin d)) : Site d :=
  fun i => if i ∈ T then y i else x i

@[simp] theorem setCoordinates_empty {d : ℕ} (x y : Site d) :
    setCoordinates x y ∅ = x := by
  funext i
  simp [setCoordinates]

@[simp] theorem setCoordinates_univ {d : ℕ} (x y : Site d) :
    setCoordinates x y Finset.univ = y := by
  funext i
  simp [setCoordinates]

theorem setCoordinates_insert {d : ℕ} (x y : Site d)
    (T : Finset (Fin d)) (j : Fin d) (hj : j ∉ T) :
    setCoordinates x y (insert j T) =
      Function.update (setCoordinates x y T) j (y j) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [setCoordinates, hj]
  · simp [setCoordinates, hij]

theorem setCoordinates_mem_box {d n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (T : Finset (Fin d)) :
    setCoordinates x y T ∈ box d n := by
  intro i
  by_cases hi : i ∈ T
  · simp [setCoordinates, hi, hy i]
  · simp [setCoordinates, hi, hx i]

private theorem int_natAbs_le_of_between {a b z : ℤ} {n : ℕ}
    (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n)
    (hz : min a b ≤ z ∧ z ≤ max a b) :
    z.natAbs ≤ n := by
  have ha' : -(n : ℤ) ≤ a ∧ a ≤ n := by
    have h : |a| ≤ (n : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast ha
    exact abs_le.mp h
  have hb' : -(n : ℤ) ≤ b ∧ b ≤ n := by
    have h : |b| ≤ (n : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hb
    exact abs_le.mp h
  have hz' : -(n : ℤ) ≤ z ∧ z ≤ n := by
    constructor
    · exact le_trans (le_min ha'.1 hb'.1) hz.1
    · exact hz.2.trans (max_le ha'.2 hb'.2)
  have habs : |z| ≤ (n : ℤ) := abs_le.mpr hz'
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs


theorem box_reachable_setCoordinates {d n : ℕ}
    (x y : Site d) (hx : x ∈ box d n) (hy : y ∈ box d n)
    (T : Finset (Fin d)) :
    ((hypercubicLattice d).induce (box d n)).Reachable
      ⟨x, hx⟩
      ⟨setCoordinates x y T, setCoordinates_mem_box hx hy T⟩ := by
  induction T using Finset.induction_on with
  | empty =>
      simpa using
        (SimpleGraph.Reachable.refl
          (⟨x, hx⟩ : box d n))
  | @insert j T hj ih =>
      let q := setCoordinates x y T
      have hq : q ∈ box d n := setCoordinates_mem_box hx hy T
      have hjq : q j = x j := by simp [q, setCoordinates, hj]
      have htgt : Function.update q j (y j) ∈ box d n := by
        rw [← setCoordinates_insert x y T j hj]
        exact setCoordinates_mem_box hx hy (insert j T)
      have hseg : ∀ z : ℤ,
          (min (q j) (y j) ≤ z ∧ z ≤ max (q j) (y j)) →
            Function.update q j z ∈ box d n := by
        intro z hz i
        by_cases hij : i = j
        · subst i
          rw [Function.update_self]
          exact int_natAbs_le_of_between
            (by rw [hjq]; exact hx j) (hy j) hz
        · rw [Function.update_of_ne hij]
          exact hq i
      have hstep := segment_gen (box d n) j q (y j) hq htgt hseg
      have hchain := ih.trans hstep
      have hval := setCoordinates_insert x y T j hj
      have heq :
          (⟨setCoordinates x y (insert j T),
              setCoordinates_mem_box hx hy (insert j T)⟩ : box d n) =
            ⟨Function.update q j (y j), htgt⟩ :=
        Subtype.ext hval
      rw [heq]
      exact hchain


theorem boxGraph_preconnected (d n : ℕ) :
    (StatMech.FK.boxGraph d n).Preconnected := by
  intro x y
  change ((hypercubicLattice d).induce (box d n)).Reachable x y
  have h := box_reachable_setCoordinates x.1 y.1 x.2 y.2 Finset.univ
  simpa using h


noncomputable def boxGraphPath (d n : ℕ)
    (x y : StatMech.FK.boxVerts d n) :
    (StatMech.FK.boxGraph d n).Walk x y :=
  (boxGraph_preconnected d n x y).some.toPath

theorem boxGraphPath_isPath (d n : ℕ)
    (x y : StatMech.FK.boxVerts d n) :
    (boxGraphPath d n x y).IsPath :=
  SimpleGraph.Path.isPath _

end StatMech.FrontierB
