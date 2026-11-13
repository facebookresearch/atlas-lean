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
import Code.Walls.jc7core
import Code.Walls.jc7loopiscycle
import Code.Walls.jc7loopseparates
import Code.Walls.jc7ivtnohop
import Code.Walls.jc7getverteqdartface
import Code.Walls.jc8touchingfaceband
import Code.Walls.jc8tworowbands
import Code.Walls.jc8crossparityleftregion
import Code.Walls.jc8bdedgelandssupport
import Code.Walls.jc8cyclenodup
import Code.Walls.jc8subarcwalk
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.DartOrbit

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice



















theorem jc8c_touchingFace_ne_descentFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j)
    (u : Site 2) (hu : u 1 ≤ r 1 - 4) :
    u 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧ u ≠ (olb_orbitLoop K hK e he).getVert j := by
  have hlow : r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 :=
    jc8tf_touchingFace_lower K hK e he r j hj htouch
  refine ⟨by omega, ?_⟩
  intro heq
  rw [heq] at hu
  omega





theorem jc8c_distinct_touch_descent (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i j : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
    (hdesc : (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 - 4) :
    (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j :=
  fun h => (jc8c_touchingFace_ne_descentFace K hK e he r i hi hti
    ((olb_orbitLoop K hK e he).getVert j) hdesc).2 h.symm

















def jc8c_SideDichotomy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) : Prop :=
  (∀ j, j ≤ (olb_orbitLoop K hK e he).length → ¬ jc4_FootprintFree K ⟨e, he⟩ r j →
      (olb_orbitLoop K hK e he).getVert j ∈ jec_leftRegion (olb_orbitLoop K hK e he)) ∧
  (∀ j, j ≤ (olb_orbitLoop K hK e he).length → jc4_FootprintFree K ⟨e, he⟩ r j →
      (olb_orbitLoop K hK e he).getVert j ∉ jec_leftRegion (olb_orbitLoop K hK e he))









def jc8c_InsideInterval (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
    k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
    (olb_orbitLoop K hK e he).getVert i ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    (olb_orbitLoop K hK e he).getVert k ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    (olb_orbitLoop K hK e he).getVert j ∈ jec_leftRegion (olb_orbitLoop K hK e he)







theorem jc8c_crossCount_ge_one_touch_to_free (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hdich : jc8c_SideDichotomy K hK e he r)
    {j₀ j₁ : ℕ} (hj₀ : j₀ ≤ (olb_orbitLoop K hK e he).length)
    (hj₁ : j₁ ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j₀)
    (hfree : jc4_FootprintFree K ⟨e, he⟩ r j₁)
    (w : (hypercubicLattice 2).Walk ((olb_orbitLoop K hK e he).getVert j₀)
      ((olb_orbitLoop K hK e he).getVert j₁)) :
    1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w :=
  jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w
    (hdich.1 j₀ hj₀ htouch) (hdich.2 j₁ hj₁ hfree)














theorem jc8c_touchingConvex_window (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hdich : jc8c_SideDichotomy K hK e he r)
    (hint : jc8c_InsideInterval K hK e he)
    (i j k : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (hk : k ≤ (olb_orbitLoop K hK e he).length)
    (hij : i < j) (hjk : j < k)
    (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
    (htk : ¬ jc4_FootprintFree K ⟨e, he⟩ r k) :
    ¬ jc4_FootprintFree K ⟨e, he⟩ r j := by
  
  have hInsideI := hdich.1 i hi hti
  have hInsideK := hdich.1 k hk htk
  
  have hInsideJ := hint i j k hi hj hk hij hjk hInsideI hInsideK
  
  intro hfree
  exact hdich.2 j hj hfree hInsideJ












def jc8c_InsideIntervalResidue (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) : Prop :=
  jc8c_SideDichotomy K hK e he r ∧ jc8c_InsideInterval K hK e he













theorem jc8c_touchingConvex_of_residue_windowed (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hres : jc8c_InsideIntervalResidue K hK e he r) :
    ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
      k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r j :=
  fun i j k hi hj hk hij hjk hti htk =>
    jc8c_touchingConvex_window K hK e he r hres.1 hres.2 i j k hi hj hk hij hjk hti htk


















def jc8c_FaceSideDichotomy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) : Prop :=
  (∀ i, ¬ jc4_FootprintFree K ⟨e, he⟩ r i →
      dartFace ((dartNext K)^[i] e) ∈ jec_leftRegion (olb_orbitLoop K hK e he)) ∧
  (∀ i, jc4_FootprintFree K ⟨e, he⟩ r i →
      dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he))





def jc8c_FaceInsideInterval (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Prop :=
  ∀ i j k, i < j → j < k →
    dartFace ((dartNext K)^[i] e) ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    dartFace ((dartNext K)^[k] e) ∈ jec_leftRegion (olb_orbitLoop K hK e he) →
    dartFace ((dartNext K)^[j] e) ∈ jec_leftRegion (olb_orbitLoop K hK e he)


def jc8c_FaceResidue (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) : Prop :=
  jc8c_FaceSideDichotomy K hK e he r ∧ jc8c_FaceInsideInterval K hK e he










theorem jc8c_touchingConvex (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hres : jc8c_FaceResidue K hK e he r) :
    jc5_TouchingConvex K ⟨e, he⟩ r := by
  obtain ⟨⟨hTI, hFO⟩, hint⟩ := hres
  intro i j k hij hjk hti htk
  
  have hInsideI := hTI i hti
  have hInsideK := hTI k htk
  
  have hInsideJ := hint i j k hij hjk hInsideI hInsideK
  
  intro hfree
  exact hFO j hfree hInsideJ






theorem jc8c_excursionConfined (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K ⟨e, he⟩ r i)
    (ha0 : ¬ jc4_FootprintFree K ⟨e, he⟩ r 0)
    (hres : jc8c_FaceResidue K hK e he r) :
    jc5_ExcursionConfined K ⟨e, he⟩ r hex :=
  jc5_excursionConfined_of_convex K ⟨e, he⟩ r hex ha0 (jc8c_touchingConvex K hK e he r hres)











theorem jc8c_windowedConvex_of_disjoint (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i) :
    ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
      k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r j :=
  fun i _ _ _ _ _ _ _ hti _ => absurd (hfoot i) hti












theorem jc8c_faceResidue_of_disjoint_empty (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
    (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    jc8c_FaceResidue K hK e he r :=
  ⟨⟨fun i hti => absurd (hfoot i) hti, fun i _ => hempty i⟩,
    fun i _ _ _ _ hI _ => absurd hI (hempty i)⟩





theorem jc8c_touchingConvex_of_disjoint_empty (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
    (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    jc5_TouchingConvex K ⟨e, he⟩ r :=
  jc8c_touchingConvex K hK e he r (jc8c_faceResidue_of_disjoint_empty K hK e he r hfoot hempty)












theorem jc8c_contour_face_count_eq_one (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {n : ℕ} (hn0 : 0 < n) (hnp : n < jc7_choosePeriod K hK e he) :
    (olb_orbitLoop K hK e he).support.count (dartFace ((dartNext K)^[n] e)) = 1 :=
  jc8_contour_face_count_eq_one K hK e he hp hinj hn0 hnp



theorem jc8c_bdEdge_lands_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jc8_bdEdge_lands_support K hK e he hadj hbd



theorem jc8c_crossCount_ge_one_of_opposite (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
    (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w :=
  jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w hx hy



theorem jc8c_bands_disjoint (r : Site 2) :
    Disjoint (jc8_descentBand r) (jc8_touchingBand r) :=
  jc8_bands_disjoint r



theorem jc8c_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ :=
  jc7_subStretch_cannot_hop K hK e he hu hv ρ hmiss



theorem jc8c_touchingFace_lower (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 :=
  jc8tf_touchingFace_lower K hK e he r j hj htouch





















































end Walls

end StatMech
