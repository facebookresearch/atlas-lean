/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceDomino
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanSingleCycle

/-!
# Simple boundary orbits: unit cell and domino

A boundary orbit has no pinch (`OrbitFaceNoPinch`) when two darts of the orbit with the same face
also have the same direction. This is equivalent to the faces along the orbit being distinct, so the
orbit traces a closed walk of faces without repeated vertices. The file verifies this for the unit
cell and the domino, whose face loops are cycles.

## Main definitions

* `StatMech.Lattice.OrbitFaceNoPinch K a`: darts of the orbit of `a` sharing a face share a
  direction.
* `StatMech.Lattice.unitCellFaceLoop`, `StatMech.Lattice.dominoFaceLoop`: the face loops of the unit
  cell and the domino.

## Main results

* `StatMech.Lattice.dartFace_eq_of_dir_eq`: a dart is determined by its face and direction.
* `StatMech.Lattice.orbitFace_injOn_iff_dir_collision`: the faces along an orbit are distinct iff
  the orbit has no pinch.
* `StatMech.Lattice.unitCellFaceLoop_isCycle`, `StatMech.Lattice.dominoFaceLoop_isCycle`: the face
  loops of the unit cell and the domino are cycles.
-/

@[expose] public section

open SimpleGraph Function Set

namespace StatMech

namespace Lattice

theorem dartFace_tail_of_dir_right (e : Dart) (hd : e.dir = ![1, 0]) :
    e.tail = ![dartFace e 0, dartFace e 1] := by
  rw [dartFace_of_dir_right e hd]; funext i; fin_cases i <;> simp

theorem dartFace_tail_of_dir_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
  rw [dartFace_of_dir_left e hd]; funext i; fin_cases i <;> simp

theorem dartFace_tail_of_dir_up (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1] := by
  rw [dartFace_of_dir_up e hd]; funext i; fin_cases i <;> simp

theorem dartFace_tail_of_dir_down (e : Dart) (hd : e.dir = ![0, -1]) :
    e.tail = ![dartFace e 0, dartFace e 1 + 1] := by
  rw [dartFace_of_dir_down e hd]; funext i; fin_cases i <;> simp

theorem dartFace_eq_of_dir_eq {e₁ e₂ : Dart} (hdir : e₁.dir = e₂.dir)
    (hface : dartFace e₁ = dartFace e₂) : e₁ = e₂ := by
  apply dart_eq_of_tail_dir _ hdir
  rcases dartDir_cases e₁ with hd | hd | hd | hd <;>
    [ (rw [dartFace_of_dir_right e₁ hd, dartFace_of_dir_right e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_left e₁ hd, dartFace_of_dir_left e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_up e₁ hd, dartFace_of_dir_up e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_down e₁ hd, dartFace_of_dir_down e₂ (hdir ▸ hd)] at hface) ] <;>
  · have h0 := congrFun hface 0
    have h1 := congrFun hface 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    funext i
    fin_cases i
    · change e₁.tail 0 = e₂.tail 0; omega
    · change e₁.tail 1 = e₂.tail 1; omega

theorem orbitDart_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNext K)^[k] a.1) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj h
  simp only [mem_Iio] at hi hj
  simp only at h
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]
    exact h
  have hmp : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  exact Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (by rw [← hmp]; exact hi)) (Set.mem_Iio.mpr (by rw [← hmp]; exact hj)) hsub

/-- Darts in one period of the orbit of `a` that have the same face also have the same direction. -/
def OrbitFaceNoPinch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ i ∈ Set.Iio (dartOrbitPeriod K a), ∀ j ∈ Set.Iio (dartOrbitPeriod K a),
    dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) →
      ((dartNext K)^[i] a.1).dir = ((dartNext K)^[j] a.1).dir

theorem orbitFace_injOn_of_noPinch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : OrbitFaceNoPinch K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj hface
  simp only at hface
  have hdir := h i hi j hj hface
  have hdart : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    dartFace_eq_of_dir_eq hdir hface
  exact orbitDart_injOn K a hi hj hdart

theorem orbitFace_noPinch_of_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  have hij : i = j := hinj hi hj hface
  rw [hij]

theorem orbitFace_injOn_iff_dir_collision (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔
      OrbitFaceNoPinch K a :=
  ⟨orbitFace_noPinch_of_injOn K a, orbitFace_injOn_of_noPinch K a⟩

theorem ucFace0 : dartFace ucDart0 = ![0, 0] := by
  rw [dartFace_of_dir_right _ ucDart0_dir, ucDart0_tail]; funext i; fin_cases i <;> simp

theorem ucFace1 : dartFace ucDart1 = ![0, -1] := by
  rw [dartFace_of_dir_down _ ucDart1_dir, ucDart1_tail]; funext i; fin_cases i <;> simp

theorem ucFace2 : dartFace ucDart2 = ![-1, -1] := by
  rw [dartFace_of_dir_left _ ucDart2_dir, ucDart2_tail]; funext i; fin_cases i <;> simp

theorem ucFace3 : dartFace ucDart3 = ![-1, 0] := by
  rw [dartFace_of_dir_up _ ucDart3_dir, ucDart3_tail]; funext i; fin_cases i <;> simp

theorem unitCell_orbitFace_injOn :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucDart0)) (Set.Iio 4) := by
  have e0 : dartFace ((dartNext unitCell)^[0] ucDart0) = ![0, 0] := by
    rw [Function.iterate_zero_apply]; exact ucFace0
  have e1 : dartFace ((dartNext unitCell)^[1] ucDart0) = ![0, -1] := by
    rw [iterate_ucDart_1]; exact ucFace1
  have e2 : dartFace ((dartNext unitCell)^[2] ucDart0) = ![-1, -1] := by
    rw [iterate_ucDart_2]; exact ucFace2
  have e3 : dartFace ((dartNext unitCell)^[3] ucDart0) = ![-1, 0] := by
    rw [iterate_ucDart_3]; exact ucFace3
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  interval_cases a <;> interval_cases b <;>
    simp only [e0, e1, e2, e3] at hab ⊢ <;>
    (exfalso; rw [funext_iff, Fin.forall_fin_two] at hab; simp at hab)

/-- The closed walk of faces around the unit cell, of length four. -/
noncomputable def unitCellFaceLoop :
    (faceBoundaryGraph unitCell).Walk (dartFace ucDart0) (dartFace ucDart0) :=
  (dartOrbitFaceWalk unitCell ucDart0 ucDart0_boundary 4).copy rfl (by rw [iterate_ucDart_4])

theorem unitCellFaceLoop_isCycle : unitCellFaceLoop.IsCycle :=
  orbitFaceWalk_isCycle unitCell ucDart0 ucDart0_boundary 4 (by norm_num)
    iterate_ucDart_4 unitCell_orbitFace_injOn

theorem dmFace0 : dartFace dmD0 = ![0, -1] := by
  rw [dartFace_of_dir_down _ dmD0_dir, dmD0_tail]; funext i; fin_cases i <;> simp

theorem dmFace1 : dartFace dmD1 = ![-1, -1] := by
  rw [dartFace_of_dir_left _ dmD1_dir, dmD1_tail]; funext i; fin_cases i <;> simp

theorem dmFace2 : dartFace dmD2 = ![-1, 0] := by
  rw [dartFace_of_dir_up _ dmD2_dir, dmD2_tail]; funext i; fin_cases i <;> simp

theorem dmFace3 : dartFace dmD3 = ![0, 0] := by
  rw [dartFace_of_dir_up _ dmD3_dir, dmD3_tail]; funext i; fin_cases i <;> simp

theorem dmFace4 : dartFace dmD4 = ![1, 0] := by
  rw [dartFace_of_dir_right _ dmD4_dir, dmD4_tail]; funext i; fin_cases i <;> simp

theorem dmFace5 : dartFace dmD5 = ![1, -1] := by
  rw [dartFace_of_dir_down _ dmD5_dir, dmD5_tail]; funext i; fin_cases i <;> simp

theorem domino_orbitFace_injOn :
    Set.InjOn (fun k => dartFace ((dartNext domino)^[k] dmD0)) (Set.Iio 6) := by
  have e0 : dartFace ((dartNext domino)^[0] dmD0) = ![0, -1] := by
    rw [Function.iterate_zero_apply]; exact dmFace0
  have e1 : dartFace ((dartNext domino)^[1] dmD0) = ![-1, -1] := by
    rw [iterate_dmD_1]; exact dmFace1
  have e2 : dartFace ((dartNext domino)^[2] dmD0) = ![-1, 0] := by
    rw [iterate_dmD_2]; exact dmFace2
  have e3 : dartFace ((dartNext domino)^[3] dmD0) = ![0, 0] := by
    rw [iterate_dmD_3]; exact dmFace3
  have e4 : dartFace ((dartNext domino)^[4] dmD0) = ![1, 0] := by
    rw [iterate_dmD_4]; exact dmFace4
  have e5 : dartFace ((dartNext domino)^[5] dmD0) = ![1, -1] := by
    rw [iterate_dmD_5]; exact dmFace5
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  interval_cases a <;> interval_cases b <;>
    simp only [e0, e1, e2, e3, e4, e5] at hab ⊢ <;>
    (exfalso; rw [funext_iff, Fin.forall_fin_two] at hab; simp at hab)

/-- The closed walk of faces around the domino, of length six. -/
noncomputable def dominoFaceLoop :
    (faceBoundaryGraph domino).Walk (dartFace dmD0) (dartFace dmD0) :=
  (dartOrbitFaceWalk domino dmD0 dmD0_boundary 6).copy rfl (by rw [iterate_dmD_6])

theorem dominoFaceLoop_isCycle : dominoFaceLoop.IsCycle :=
  orbitFaceWalk_isCycle domino dmD0 dmD0_boundary 6 (by norm_num)
    iterate_dmD_6 domino_orbitFace_injOn

end Lattice

end StatMech
