/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Walls.jc4_firstreturnK
import Code.Walls.jc4_tailnotprobed
import Code.Walls.jc5_core
import Code.Walls.jc5_footprintdartsfinite
import Code.Walls.jc6_ivt
import Code.Walls.jc7ivtnohop
import Code.Walls.jc7getverteqdartface
import Code.Walls.jc7loopiscycle
import Code.Walls.jc7loopseparates
import Code.Walls.jc7stepfacebridge
import Code.Lattice.ContourLinksExits
import Code.Lattice.DartOrbit

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc7_head_eq (e : Dart) : e.head = e.tail + e.dir := by
  rw [Dart.dir_def]; abel




theorem jc7_face_row_le_one_of_tail (e : Dart) :
    (dartFace e 1 - e.tail 1).natAbs ≤ 1 := by
  rcases dartDir_cases e with h | h | h | h
  · rw [dartFace_of_dir_right e h]; simp
  · rw [dartFace_of_dir_left e h]; simp
  · rw [dartFace_of_dir_up e h]; simp
  · rw [dartFace_of_dir_down e h]; simp





theorem jc7_face_row_dist_tailTravel_le_two (e : Dart) :
    (dartFace e 1 - jc_tailTravel e 1).natAbs ≤ 2 := by
  rw [jc_tailTravel_eq]
  rcases dartDir_cases e with h | h | h | h <;>
  · first
      | rw [dartFace_of_dir_right e h]
      | rw [dartFace_of_dir_left e h]
      | rw [dartFace_of_dir_up e h]
      | rw [dartFace_of_dir_down e h]
    simp only [Pi.add_apply, Pi.neg_apply, h, rot90Fun,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    omega




theorem jc7_face_row_dist_headTravel_le_two (e : Dart) :
    (dartFace e 1 - jc_headTravel e 1).natAbs ≤ 2 := by
  rw [jc_headTravel_eq, jc7_head_eq e]
  rcases dartDir_cases e with h | h | h | h <;>
  · first
      | rw [dartFace_of_dir_right e h]
      | rw [dartFace_of_dir_left e h]
      | rw [dartFace_of_dir_up e h]
      | rw [dartFace_of_dir_down e h]
    simp only [Pi.add_apply, Pi.neg_apply, h, rot90Fun,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    omega




theorem jc7_footprint_row_le_one (r x : Site 2) (hx : x ∈ jc3_earFootprint r) :
    (x 1 - r 1).natAbs ≤ 1 := by
  rw [jc3_mem_earFootprint] at hx
  rcases hx with h | h | h | h | h <;> subst h
  · simp
  all_goals
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega





















theorem jc7_touching_face_row_band (r : Site 2) (e : Dart)
    (h : jc5_ProbesEarFootprint r e) :
    (dartFace e 1 - r 1).natAbs ≤ 3 := by
  rcases h with hhead | htail
  · have h1 : (dartFace e 1 - jc_headTravel e 1).natAbs ≤ 2 :=
      jc7_face_row_dist_headTravel_le_two e
    have h2 : (jc_headTravel e 1 - r 1).natAbs ≤ 1 := jc7_footprint_row_le_one r _ hhead
    omega
  · have h1 : (dartFace e 1 - jc_tailTravel e 1).natAbs ≤ 2 :=
      jc7_face_row_dist_tailTravel_le_two e
    have h2 : (jc_tailTravel e 1 - r 1).natAbs ≤ 1 := jc7_footprint_row_le_one r _ htail
    omega



theorem jc7_touching_face_row_band' (r : Site 2) (e : Dart)
    (h : jc5_ProbesEarFootprint r e) :
    r 1 - 3 ≤ dartFace e 1 ∧ dartFace e 1 ≤ r 1 + 3 := by
  have := jc7_touching_face_row_band r e h
  omega
















theorem jc7_touching_iff_probes (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    ¬ jc4_FootprintFree K a r i ↔
      jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
  unfold jc4_FootprintFree
  exact jc5_not_avoidsEarFootprint_iff_probes r _





theorem jc7_touching_orbitFace_row_band (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (i : ℕ)
    (h : ¬ jc4_FootprintFree K a r i) :
    (dartFace ((dartNext K)^[i] a.1) 1 - r 1).natAbs ≤ 3 :=
  jc7_touching_face_row_band r _ ((jc7_touching_iff_probes K a r i).mp h)










theorem jc7_touching_loopVert_row_band (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (h : ¬ jc4_FootprintFree K ⟨e, he⟩ r i) :
    ((olb_orbitLoop K hK e he).getVert i 1 - r 1).natAbs ≤ 3 := by
  rw [jc7_getVert_eq_dartFace K hK e he i hi]
  exact jc7_touching_orbitFace_row_band K ⟨e, he⟩ r i h


















def jc7_SinglePass (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
    ¬ jc4_FootprintFree K a r j




theorem jc7_singlePass_iff_touchingConvex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    jc7_SinglePass K a r ↔ jc5_TouchingConvex K a r :=
  Iff.rfl




theorem jc7_touchingConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hsp : jc7_SinglePass K a r) : jc5_TouchingConvex K a r :=
  hsp





theorem jc7_noReentry_of_singlePass (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc5_NoReentry K a r :=
  jc5_noReentry_of_convex K a r ha0 (jc7_touchingConvex K a r hsp)








theorem jc7_tailFootprintFree_of_singlePass (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex)
      (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) :=
  jc5_tailFootprintFree_of_convex K a r hex ha0 (jc7_touchingConvex K a r hsp)




theorem jc7_excursionConfined_of_singlePass (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc5_ExcursionConfined K a r hex :=
  jc5_excursionConfined_of_convex K a r hex ha0 (jc7_touchingConvex K a r hsp)














theorem jc7core_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite) : jc6_SingleCycle K :=
  jc7_orbit_isCycle K hK






theorem jc7core_getVert_eq_dartFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ) (hn : n ≤ (olb_orbitLoop K hK e he).length) :
    (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) :=
  jc7_getVert_eq_dartFace K hK e he n hn






theorem jc7core_loop_separates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd







theorem jc7core_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ :=
  jc7_subStretch_cannot_hop K hK e he hu hv ρ hmiss













theorem jc7_singlePass_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc7_SinglePass K a r := by
  intro i j k _ _ hi _
  exact absurd (hfoot i) hi




theorem jc7_touchingConvex_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_TouchingConvex K a r :=
  jc7_touchingConvex K a r (jc7_singlePass_of_disjoint K a r hfoot)







theorem jc7_band_vacuous_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) (i : ℕ) :
    jc4_FootprintFree K a r i :=
  hfoot i




















































end Walls

end StatMech
