/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.jc7core
import Code.Walls.jc7loopiscycle
import Code.Walls.jc7loopseparates
import Code.Walls.jc7ivtnohop
import Code.Walls.jc7getverteqdartface
import Code.Walls.jc5_core
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.DartOrbit

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice


















def jc8_shelfRow (r : Site 2) : ℤ := r 1 - 1



def jc8_descentBand (r : Site 2) : Set (Site 2) := {x | x 1 ≤ r 1 - 2}



def jc8_touchingBand (r : Site 2) : Set (Site 2) := {x | r 1 - 1 ≤ x 1}


@[simp] theorem jc8_mem_descentBand (r x : Site 2) :
    x ∈ jc8_descentBand r ↔ x 1 ≤ r 1 - 2 := Iff.rfl


@[simp] theorem jc8_mem_touchingBand (r x : Site 2) :
    x ∈ jc8_touchingBand r ↔ r 1 - 1 ≤ x 1 := Iff.rfl



theorem jc8_descentBand_below_shelf (r x : Site 2) (hx : x ∈ jc8_descentBand r) :
    x 1 < jc8_shelfRow r := by
  rw [jc8_mem_descentBand] at hx
  unfold jc8_shelfRow
  omega



theorem jc8_touchingBand_above_shelf (r x : Site 2) (hx : x ∈ jc8_touchingBand r) :
    jc8_shelfRow r ≤ x 1 := by
  rw [jc8_mem_touchingBand] at hx
  unfold jc8_shelfRow
  omega














theorem jc8_band_separation (r u v : Site 2)
    (hu : u 1 ≤ r 1 - 2) (hv : r 1 - 1 ≤ v 1) :
    u 1 < v 1 := by omega







theorem jc8_band_ne (r u v : Site 2)
    (hu : u 1 ≤ r 1 - 2) (hv : r 1 - 1 ≤ v 1) :
    u ≠ v := by
  intro heq
  have : u 1 < v 1 := jc8_band_separation r u v hu hv
  rw [heq] at this
  exact lt_irrefl _ this





theorem jc8_bands_disjoint (r : Site 2) :
    Disjoint (jc8_descentBand r) (jc8_touchingBand r) := by
  rw [Set.disjoint_left]
  intro x hxd hxt
  rw [jc8_mem_descentBand] at hxd
  rw [jc8_mem_touchingBand] at hxt
  omega




theorem jc8_band_separation_mem (r u v : Site 2)
    (hu : u ∈ jc8_descentBand r) (hv : v ∈ jc8_touchingBand r) :
    u 1 < v 1 ∧ u ≠ v := by
  rw [jc8_mem_descentBand] at hu
  rw [jc8_mem_touchingBand] at hv
  exact ⟨jc8_band_separation r u v hu hv, jc8_band_ne r u v hu hv⟩
















def jc8_DescentStaysLow (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ) : Prop :=
  (olb_orbitLoop K hK e he).getVert i 1 ≤ r 1 - 2









def jc8_TouchingFaceBand (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ) : Prop :=
  ¬ jc4_FootprintFree K ⟨e, he⟩ r j →
    r 1 - 1 ≤ (olb_orbitLoop K hK e he).getVert j 1




















theorem jc8_descentFace_below_touchingFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 :=
  jc8_band_separation r _ _ hlow (hband htouch)





theorem jc8_descentFace_ne_touchingFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j :=
  jc8_band_ne r _ _ hlow (hband htouch)













theorem jc8_twoRowBands (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hlow : jc8_DescentStaysLow K hK e he r i)
    (hband : jc8_TouchingFaceBand K hK e he r j)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert i ∈ jc8_descentBand r ∧
      (olb_orbitLoop K hK e he).getVert j ∈ jc8_touchingBand r ∧
      (olb_orbitLoop K hK e he).getVert i 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧
      (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [jc8_mem_descentBand]; exact hlow
  · rw [jc8_mem_touchingBand]; exact hband htouch
  · exact jc8_descentFace_below_touchingFace K hK e he r i j hlow hband htouch
  · exact jc8_descentFace_ne_touchingFace K hK e he r i j hlow hband htouch












theorem jc8_touchingFaceBand_of_free (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hfree : jc4_FootprintFree K ⟨e, he⟩ r j) :
    jc8_TouchingFaceBand K hK e he r j := by
  intro htouch
  exact absurd hfree htouch



theorem jc8_descentStaysLow_of_row (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ)
    (hrow : (olb_orbitLoop K hK e he).getVert i 1 ≤ r 1 - 2) :
    jc8_DescentStaysLow K hK e he r i := hrow






theorem jc8_separation_nonvacuous :
    ((![0, 0] : Site 2)) 1 < ((![0, 3] : Site 2)) 1 ∧
      ((![0, 0] : Site 2)) ≠ ((![0, 3] : Site 2)) := by
  refine ⟨?_, ?_⟩
  · 
    
    exact jc8_band_separation (![0, 4] : Site 2) (![0, 0] : Site 2) (![0, 3] : Site 2)
      (by norm_num) (by norm_num)
  · exact jc8_band_ne (![0, 4] : Site 2) (![0, 0] : Site 2) (![0, 3] : Site 2)
      (by norm_num) (by norm_num)










@[simp] theorem jc8_shelfRow_eq (r : Site 2) : jc8_shelfRow r = r 1 - 1 := rfl





theorem jc8_shelfRow_separates (r : Site 2) :
    r 1 - 2 < jc8_shelfRow r ∧ jc8_shelfRow r = r 1 - 1 := by
  unfold jc8_shelfRow; omega







































end Walls

end StatMech
