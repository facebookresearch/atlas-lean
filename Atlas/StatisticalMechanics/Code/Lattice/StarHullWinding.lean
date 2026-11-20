/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.OrbitEncloses
import Code.Lattice.JordanSingleCycle
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.NoPinchDual
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.WindingEarInduction

open Set SimpleGraph Function

namespace StatMech

namespace Lattice










theorem shw_vertStep_right (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![1, 0]) :
    (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
  rw [dartFace_of_dir_right e hd, dartFace_next_of_dir_right K e hd]; simp


theorem shw_vertStep_left (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![-1, 0]) :
    (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
  rw [dartFace_of_dir_left e hd, dartFace_next_of_dir_left K e hd]; simp




theorem shw_vertStep_dir (K : Set (Site 2)) (e : Dart)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exfalso
    rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega
  · exfalso
    rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega














theorem shw_extremeCell_eq_tail_of_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) = e.tail :=
  (dartFace_tail_of_dir_left e hd).symm




theorem shw_extremeCell_mem_of_left {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
  rw [shw_extremeCell_eq_tail_of_left e hd]; exact he.tail_mem







theorem shw_extremeCell_notMem_of_right {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K := by
  have h := (npd_corners_right he hd).2
  unfold npd_P10 at h
  exact h










theorem shw_mpl_edges_form (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]




theorem shw_exists_vertStep (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) :
    ∃ k < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
  obtain ⟨i, hi, hvert⟩ := eaw_exists_vertEdge (mpl_orbitLoop K a) hcyc
  have hmem : s((mpl_orbitLoop K a).getVert i, (mpl_orbitLoop K a).getVert (i + 1)) ∈
      (mpl_orbitLoop K a).edges := eaw_getVert_edge_mem (mpl_orbitLoop K a) hi
  rw [shw_mpl_edges_form] at hmem
  rw [List.mem_map] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  rw [List.mem_range] at hk
  refine ⟨k, hk, ?_⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hvert
  · rw [h1, h2]; exact hvert.symm




theorem shw_minCol_le_of_vertEdge (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : ℤ)
    (hmin : ∀ k < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 →
        c ≤ (dartFace ((dartNext K)^[k] a.1)) 0)
    {x y : Site 2} (hxy : s(x, y) ∈ (mpl_orbitLoop K a).edges) (hcol : x 0 = y 0) : c ≤ x 0 := by
  rw [shw_mpl_edges_form] at hxy
  rw [List.mem_map] at hxy
  obtain ⟨k, hk, heq⟩ := hxy
  rw [List.mem_range] at hk
  rw [Sym2.eq_iff] at heq
  
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · 
    have hv : (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
      rw [h1, h2]; exact hcol
    have := hmin k hk hv
    rw [← h1]; exact this
  · 
    have hv : (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
      rw [h1, h2]; exact hcol.symm
    have hle := hmin k hk hv
    
    rw [← h2, ← hv]; exact hle





theorem shw_minVertStep_exists (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) :
    ∃ k < dartOrbitPeriod K a,
      ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
      (∀ j < dartOrbitPeriod K a,
        (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
          (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0) := by
  classical
  obtain ⟨k0, hk0, hv0⟩ := shw_exists_vertStep K a hcyc
  set p := dartOrbitPeriod K a with hp
  set S := (Finset.range p).filter
    (fun k => (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0)
    with hS
  have hSne : S.Nonempty := ⟨k0, by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩⟩
  obtain ⟨k, hkS, hkmin⟩ := S.exists_min_image (fun k => (dartFace ((dartNext K)^[k] a.1)) 0) hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hkS
  refine ⟨k, hkS.1, hkS.2, ?_⟩
  intro j hj hvj
  have hjS : j ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hvj⟩
  exact hkmin j hjS




















def shw_MinVertStepLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ k < dartOrbitPeriod K a,
    ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
    (∀ j < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
        (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0) ∧
    ((dartNext K)^[k] a.1).dir = ![-1, 0]

















theorem shw_windingWitness_of_minLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) (hres : shw_MinVertStepLeft K a) :
    wei_WindingWitness K a := by
  classical
  obtain ⟨k, hk, hvk, hkmin, hdir⟩ := hres
  set e := (dartNext K)^[k] a.1 with he_def
  have hbe : IsBoundaryDart K e := iterate_isBoundaryDart K a.1 a.2 k
  
  set c : ℤ := dartFace e 0 with hc
  set r : ℤ := dartFace e 1 with hr
  
  have hlow : dartFace e = (![c, r] : Site 2) := by
    funext i; fin_cases i <;> rfl
  
  have hc' : c = e.tail 0 - 1 := by rw [hc, dartFace_of_dir_left e hdir]; simp
  have hr' : r = e.tail 1 - 1 := by rw [hr, dartFace_of_dir_left e hdir]; simp
  have hup : dartFace (dartNext K e) = (![c, r + 1] : Site 2) := by
    rw [dartFace_next_of_dir_left K e hdir]
    funext i; fin_cases i
    · change e.tail 0 - 1 = c; omega
    · change e.tail 1 = r + 1; omega
  
  have hsucc : (dartNext K)^[k + 1] a.1 = dartNext K e := by
    rw [he_def, Function.iterate_succ_apply']
  
  have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ (mpl_orbitLoop K a).edges := by
    rw [shw_mpl_edges_form, List.mem_map]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [show (dartNext K)^[k] a.1 = e from rfl, ← hlow, hsucc, hup]
  
  have hmin : ∀ x y : Site 2, s(x, y) ∈ (mpl_orbitLoop K a).edges → x 0 = y 0 → c ≤ x 0 := by
    intro x y hxy hcol
    apply shw_minCol_le_of_vertEdge K a c ?_ hxy hcol
    intro j hj hvj
    exact hkmin j hj hvj
  
  have hnodup : (mpl_orbitLoop K a).edges.Nodup := hcyc.edges_nodup
  have hone : jec_rayCount (![c + 1, r + 1] : Site 2) (mpl_orbitLoop K a) = 1 :=
    eaw_rayCount_extreme (mpl_orbitLoop K a) c r hmin he0 hnodup
  
  have hzmem : (![c + 1, r + 1] : Site 2) ∈ K := by
    have := shw_extremeCell_mem_of_left hbe hdir
    rwa [← hc, ← hr] at this
  exact ⟨![c + 1, r + 1], hzmem, by rw [hone]; decide⟩










theorem shw_starHull_mpl_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    (mpl_orbitLoop (ndt_StarHull K) a).IsCycle :=
  mpl_orbitLoop_isCycle (ndt_StarHull K) a hp
    (orbitFace_injOn_of_noPinch (ndt_StarHull K) a (ndt_orbitFaceNoPinch K a))







theorem shw_starHull_windingWitness_of_minLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
    wei_WindingWitness (ndt_StarHull K) a :=
  shw_windingWitness_of_minLeft (ndt_StarHull K) a (shw_starHull_mpl_isCycle K a hp) hres










theorem shw_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn





theorem shw_unitCell_minVertStepLeft : shw_MinVertStepLeft unitCell ucBase := by
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · rw [unitCell_orbitPeriod_eq_four]; norm_num
  · 
    rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2,
        mpl_dartFace_iterate_ucDart3]
    rfl
  · 
    intro j hj hvj
    rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2]
    change (-1 : ℤ) ≤ (dartFace ((dartNext unitCell)^[j] ucDart0)) 0
    rw [unitCell_orbitPeriod_eq_four] at hj
    interval_cases j
    · rw [mpl_dartFace_iterate_ucDart0]; norm_num
    · rw [mpl_dartFace_iterate_ucDart1]; norm_num
    · rw [mpl_dartFace_iterate_ucDart2]; norm_num
    · rw [mpl_dartFace_iterate_ucDart3]; norm_num
  · 
    rw [show ucBase.1 = ucDart0 from rfl, iterate_ucDart_2, ucDart2_dir]






theorem shw_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  have hcyc : (mpl_orbitLoop unitCell ucBase).IsCycle :=
    mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
      shw_unitCell_faceInj
  exact shw_windingWitness_of_minLeft unitCell ucBase hcyc shw_unitCell_minVertStepLeft
























theorem shw_kingSat_excludes_diagSubcase {K : Set (Site 2)} (hK : npd_NoDiagTouch K)
    {e : Dart} (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) (c r : ℤ)
    (hc : c = dartFace e 0) (hr : r + 1 = dartFace e 1) :
    ¬ ((![c + 1, r] : Site 2) ∈ K ∧ (![c, r] : Site 2) ∉ K) := by
  rintro ⟨hP10, hP00⟩
  obtain ⟨hcP00, hcP10⟩ := npd_corners_right he hd
  
  
  
  apply hK (![c, r] : Site 2)
  right
  refine ⟨?_, ?_, hP00, ?_⟩
  · 
    change (npd_P10 (![c, r] : Site 2)) ∈ K
    have : (npd_P10 (![c, r] : Site 2)) = ![c + 1, r] := by
      unfold npd_P10; funext i; fin_cases i <;> simp
    rw [this]; exact hP10
  · 
    change (![c, r + 1] : Site 2) ∈ K
    have : (npd_P00 (dartFace e) : Site 2) = ![c, r + 1] := by
      unfold npd_P00; funext i; fin_cases i
      · change dartFace e 0 = c; omega
      · change dartFace e 1 = r + 1; omega
    rwa [this] at hcP00
  · 
    change (![c + 1, r + 1] : Site 2) ∉ K
    have : (npd_P10 (dartFace e) : Site 2) = ![c + 1, r + 1] := by
      unfold npd_P10; funext i; fin_cases i
      · change dartFace e 0 + 1 = c + 1; omega
      · change dartFace e 1 = r + 1; omega
    rwa [this] at hcP10

end Lattice

end StatMech
