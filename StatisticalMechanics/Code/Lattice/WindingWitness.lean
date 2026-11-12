/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.BdEdgeMatchStarHull

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice











theorem wwit_singleVisit_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2) (i : ℕ)
    (h : usc_visitSet K a f = {i}) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  rw [usc_singleVisit_local_turn K a f i h]
  exact turnZ_mem K _





theorem wwit_localTurn_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  classical
  rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
  · 
    right; left
    unfold usc_localTurn
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty]
  · 
    have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
    exact wwit_singleVisit_localTurn_mem K a f i hi




theorem wwit_localTurn_mem_orbitFaces (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hmult : usc_FaceMultiplicityOne K a)
    (f : Site 2) (_hf : f ∈ usc_orbitFaces K a) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 :=
  wwit_localTurn_mem K a hmult f











theorem wwit_localTurn_sum_eq_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f
      = totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  (usc_totalTurnZ_eq_sum_localTurn K a).symm





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







theorem wwit_exists_convex_corner (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (hturn : TurningIsFullRevolution K a) :
    (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = 1) ∨
      (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = -1) := by
  have hsum := wwit_localTurn_sum_eq_totalTurn K a
  rcases hturn with h4 | hm4
  · left
    rw [h4] at hsum
    exact wwit_exists_pos_of_sum_eq_four (usc_localTurn K a)
      (fun f hf => wwit_localTurn_mem_orbitFaces K a hmult f hf) hsum
  · right
    rw [hm4] at hsum
    exact wwit_exists_neg_of_sum_eq_negFour (usc_localTurn K a)
      (fun f hf => wwit_localTurn_mem_orbitFaces K a hmult f hf) hsum











theorem wwit_starHull_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2) :
    usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨
      usc_localTurn (ndt_StarHull K) a f = -1 :=
  wwit_localTurn_mem (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) f






theorem wwit_starHull_exists_convex_corner (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hturn : TurningIsFullRevolution (ndt_StarHull K) a) :
    (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨
      (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) :=
  wwit_exists_convex_corner (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) hturn














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







theorem wwit_cornerCell_mem (K : Set (Site 2)) (e : Dart) (hturn : turnZ K e = 1) :
    e.head + (-rot90Fun e.dir) ∈ K := by
  classical
  unfold turnZ at hturn
  by_contra hmem
  rw [if_neg hmem] at hturn
  split_ifs at hturn with hb
  all_goals simp_all




noncomputable def wwit_cornerCell (e : Dart) : Site 2 := e.head + (-rot90Fun e.dir)

@[simp] theorem wwit_cornerCell_def (e : Dart) :
    wwit_cornerCell e = e.head + (-rot90Fun e.dir) := rfl














theorem wwit_orbit_tail_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (i : ℕ) :
    ((dartNext K)^[i] a.1).tail ∈ K :=
  (iterate_isBoundaryDart K a.1 a.2 i).tail_mem











def wwit_TailOdd (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (olb_orbitLoop K hK a.1 a.2))






theorem wwit_winding_witness_of_tailOdd (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hprim : wwit_TailOdd K hK a) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := by
  obtain ⟨i, hodd⟩ := hprim
  exact ⟨((dartNext K)^[i] a.1).tail, wwit_orbit_tail_mem K a i, hodd⟩












theorem wwit_starHull_winding_witness (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hprim : wwit_TailOdd (ndt_StarHull K) hSK a) :
    ∃ z₀ : Site 2, z₀ ∈ ndt_StarHull K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)) :=
  wwit_winding_witness_of_tailOdd (ndt_StarHull K) hSK a hprim








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
    (wwit_orbit_tail_mem (ndt_StarHull K) a i) hodd hInt














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
