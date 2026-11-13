/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.NoPinchDual
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.StarHullWinding
import Code.Lattice.WindingEarInduction

open Set SimpleGraph Function

namespace StatMech

namespace Lattice









noncomputable def lmo_lexKey (z : Site 2) : ℤ ×ₗ ℤ := toLex (z 0, z 1)





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









noncomputable def lmo_leftDartAt (z₀ : Site 2) : Dart :=
  mkDart z₀ ![-1, 0] (by simp [unitWt, Fin.sum_univ_two])

@[simp] theorem lmo_leftDartAt_dir (z₀ : Site 2) : (lmo_leftDartAt z₀).dir = ![-1, 0] := by
  rw [lmo_leftDartAt, mkDart_dir]

@[simp] theorem lmo_leftDartAt_tail (z₀ : Site 2) : (lmo_leftDartAt z₀).tail = z₀ := by
  rw [lmo_leftDartAt, mkDart_tail]

theorem lmo_leftDartAt_head (z₀ : Site 2) :
    (lmo_leftDartAt z₀).head = ![z₀ 0 - 1, z₀ 1] := by
  rw [lmo_leftDartAt, mkDart_head]; funext i; fin_cases i <;> (simp; try ring)



theorem lmo_leftDartAt_isBoundaryDart {K : Set (Site 2)} {z₀ : Site 2} (hz₀ : z₀ ∈ K)
    (hwest : (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K) :
    IsBoundaryDart K (lmo_leftDartAt z₀) := by
  refine ⟨?_, ?_⟩
  · rw [lmo_leftDartAt_tail]; exact hz₀
  · rw [lmo_leftDartAt_head]; exact hwest


theorem lmo_leftDartAt_face (z₀ : Site 2) :
    dartFace (lmo_leftDartAt z₀) = ![z₀ 0 - 1, z₀ 1 - 1] := by
  rw [dartFace_of_dir_left _ (lmo_leftDartAt_dir z₀), lmo_leftDartAt_tail]










theorem lmo_vertStep_dir {K : Set (Site 2)} (e : Dart)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exfalso; rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega
  · exfalso; rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega











theorem lmo_vertStep_left_of_minCol {K : Set (Site 2)} (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    {e : Dart} (he : IsBoundaryDart K e)
    (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
    (hcol : (dartFace e) 0 ≤ m - 1) :
    e.dir = ![-1, 0] := by
  rcases lmo_vertStep_dir e hvert with hd | hd
  · exfalso
    have h := (npd_corners_right he hd).1
    rw [npd_P00] at h
    have := hm _ h
    simp only [Matrix.cons_val_zero] at this
    omega
  · exact hd



















def lmo_OrbitReachesLeftmost (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) :
    Prop :=
  ∃ k < dartOrbitPeriod K a,
    ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
    (dartFace ((dartNext K)^[k] a.1)) 0 ≤ m - 1










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















theorem lmo_windingWitness_of_reachesLeftmost (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K a).IsCycle)
    (hreach : lmo_OrbitReachesLeftmost K a m) :
    wei_WindingWitness K a :=
  shw_windingWitness_of_minLeft K a hcyc
    (lmo_minVertStepLeft_of_reachesLeftmost K a m hm hreach)









theorem lmo_unitCell_minColumn : ∀ w ∈ unitCell, (0 : ℤ) ≤ w 0 := by
  intro w hw
  rw [unitCell, Set.mem_singleton_iff] at hw
  rw [hw]; simp




theorem lmo_unitCell_reachesLeftmost :
    lmo_OrbitReachesLeftmost unitCell ucBase 0 := by
  refine ⟨2, ?_, ?_, ?_⟩
  · rw [unitCell_orbitPeriod_eq_four]; norm_num
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2,
        mpl_dartFace_iterate_ucDart3]; rfl
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2]
    change (-1 : ℤ) ≤ (0 : ℤ) - 1; norm_num






theorem lmo_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  have hcyc : (mpl_orbitLoop unitCell ucBase).IsCycle :=
    mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
      shw_unitCell_faceInj
  exact lmo_windingWitness_of_reachesLeftmost unitCell ucBase 0 lmo_unitCell_minColumn hcyc
    lmo_unitCell_reachesLeftmost


















theorem lmo_face_col_left {e : Dart} (hd : e.dir = ![-1, 0]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_left e hd]; simp


theorem lmo_face_col_up {e : Dart} (hd : e.dir = ![0, 1]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_up e hd]; simp



theorem lmo_face_col_right {e : Dart} (hd : e.dir = ![1, 0]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_right e hd]; simp



theorem lmo_face_col_down {e : Dart} (hd : e.dir = ![0, -1]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_down e hd]; simp







theorem lmo_reachesLeftmost_of_left_tail (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ)
    {k : ℕ} (hk : k < dartOrbitPeriod K a)
    (htail : ((dartNext K)^[k] a.1).tail 0 = m)
    (hd : ((dartNext K)^[k] a.1).dir = ![-1, 0]) :
    lmo_OrbitReachesLeftmost K a m := by
  refine ⟨k, hk, ?_, ?_⟩
  · 
    rw [show (dartNext K)^[k + 1] a.1 = dartNext K ((dartNext K)^[k] a.1) from by
        rw [Function.iterate_succ_apply']]
    exact shw_vertStep_left K _ hd
  · rw [lmo_face_col_left hd, htail]

end Lattice

end StatMech
