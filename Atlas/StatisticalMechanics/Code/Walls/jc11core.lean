/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.TurningNumber
import Code.Lattice.ContourLinksExits
import Code.Lattice.EarExistence
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitEncloses
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Walls.jc10core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice









theorem jc11_dartFace_extremeBase (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    dartFace (extremeBase K c hc).1 = ![c 0 - 1, c 1 - 1] := by
  show dartFace (leftDart c) = ![c 0 - 1, c 1 - 1]
  rw [dartFace_of_dir_left _ (leftDart_dir c)]
  simp [leftDart_tail]




theorem jc11_dartNext_extremeBase (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    dartNext K (leftDart c) = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) := by
  have hfront : (leftDart c).head + (-rot90Fun (leftDart c).dir) ∉ K :=
    extremeCell_front_nmem K c hc
  have hside : (leftDart c).tail + (-rot90Fun (leftDart c).dir) ∉ K :=
    extremeCell_side_nmem K c hc
  rw [dartNext_of_corner K (leftDart c) hfront hside]
  have htravel : -rot90Fun (leftDart c).dir = (![0, 1] : Site 2) := leftDart_travel c
  apply Lattice.Dart.ext
  · simp [leftDart_tail]
  · rw [mkDart_head, mkDart_head, htravel, leftDart_tail]


theorem jc11_dartNext_dir (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (dartNext K (leftDart c)).dir = ![0, 1] := by
  rw [jc11_dartNext_extremeBase K c hc, mkDart_dir]


theorem jc11_dartNext_tail (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (dartNext K (leftDart c)).tail = c := by
  rw [jc11_dartNext_extremeBase K c hc, mkDart_tail]



theorem jc11_dartFace_dartNext (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    dartFace (dartNext K (leftDart c)) = ![c 0 - 1, c 1] := by
  rw [dartFace_of_dir_up _ (jc11_dartNext_dir K c hc), jc11_dartNext_tail K c hc]


theorem jc11_dartNext_travel (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    -rot90Fun (dartNext K (leftDart c)).dir = (![1, 0] : Site 2) := by
  rw [jc11_dartNext_dir K c hc, rot90Fun_apply]; funext i; fin_cases i <;> simp


theorem jc11_dartNext_front_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (dartNext K (leftDart c)).head + (-rot90Fun (dartNext K (leftDart c)).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [jc11_dartNext_travel K c hc, dart_head_eq, jc11_dartNext_dir K c hc, jc11_dartNext_tail K c hc]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega





theorem jc11_dartFace_dartNext2 (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    dartFace (dartNext K (dartNext K (leftDart c))) = ![c 0, c 1] := by
  set e := dartNext K (leftDart c) with he
  have hfront : e.head + (-rot90Fun e.dir) ∉ K := jc11_dartNext_front_nmem K c hc
  have htravel : -rot90Fun e.dir = (![1, 0] : Site 2) := jc11_dartNext_travel K c hc
  have htail : e.tail = c := jc11_dartNext_tail K c hc
  have hdir : e.dir = (![0, 1] : Site 2) := jc11_dartNext_dir K c hc
  by_cases hside : e.tail + (-rot90Fun e.dir) ∈ K
  · 
    rw [dartNext_of_side_mem K e hfront hside]
    have hd : (mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e)).dir = (![0, 1] : Site 2) := by
      rw [mkDart_dir]; exact hdir
    rw [dartFace_of_dir_up _ hd, mkDart_tail, htravel, htail]
    funext i; fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply] <;>
      ring_nf
  · 
    rw [dartNext_of_corner K e hfront hside]
    have hd : (mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e)).dir
        = (![1, 0] : Site 2) := by rw [mkDart_dir]; exact htravel
    rw [dartFace_of_dir_right _ hd, mkDart_tail, htail]












theorem jc11_dartFace_eq_aboveLeft_unique (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c)
    (e : Dart) (he : IsBoundaryDart K e) (hf : dartFace e = ![c 0 - 1, c 1]) :
    e = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) := by
  have hf0 : dartFace e 0 = c 0 - 1 := by rw [hf]; simp
  have hf1 : dartFace e 1 = c 1 := by rw [hf]; simp
  rcases dartDir_cases e with hd | hd | hd | hd
  · 
    rw [dartFace_of_dir_right e hd] at hf0 hf1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hf0 hf1
    exfalso
    have hmem := he.tail_mem
    exact extremeCell_not_mem_of_left K c e.tail hc hf1 (by omega) hmem
  · 
    rw [dartFace_of_dir_left e hd] at hf1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hf1
    exfalso
    have hmem := he.tail_mem
    exact extremeCell_not_mem_of_higher K c e.tail hc (by omega) hmem
  · 
    rw [dartFace_of_dir_up e hd] at hf0 hf1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hf0 hf1
    have htail0 : e.tail 0 = c 0 := by omega
    have htail : e.tail = c := by
      funext i
      fin_cases i
      · exact htail0
      · exact hf1
    apply Lattice.Dart.ext
    · rw [htail, mkDart_tail]
    · rw [dart_head_eq, hd, mkDart_head, htail]
  · 
    rw [dartFace_of_dir_down e hd] at hf1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hf1
    exfalso
    have hmem := he.tail_mem
    exact extremeCell_not_mem_of_higher K c e.tail hc (by omega) hmem










theorem jc11_orbit_face_one (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    dartFace ((dartNext K)^[1] (extremeBase K c hc).1) = ![c 0 - 1, c 1] := by
  rw [Function.iterate_one]
  show dartFace (dartNext K (leftDart c)) = ![c 0 - 1, c 1]
  exact jc11_dartFace_dartNext K c hc





theorem jc11_face_aboveLeft_index_eq_one (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) (m : ℕ) (hm1 : 1 ≤ m) (hmp : m ≤ dartOrbitPeriod K (extremeBase K c hc))
    (hf : dartFace ((dartNext K)^[m] (extremeBase K c hc).1) = ![c 0 - 1, c 1]) :
    m = 1 := by
  set a := extremeBase K c hc with ha
  
  have hbd : IsBoundaryDart K ((dartNext K)^[m] a.1) := iterate_isBoundaryDart K a.1 a.2 m
  have hdart_m : (dartNext K)^[m] a.1 = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) :=
    jc11_dartFace_eq_aboveLeft_unique K c hc _ hbd hf
  
  have hdart_1 : (dartNext K)^[1] a.1 = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) := by
    rw [Function.iterate_one]
    show dartNext K (leftDart c) = _
    exact jc11_dartNext_extremeBase K c hc
  
  have hpos : 0 < Function.minimalPeriod (dartNextSub K) a := dartOrbitPeriod_pos K hK a
  have hpe : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  have hval_m : ((dartNextSub K)^[m] a).1 = (dartNext K)^[m] a.1 := dartNextSub_iterate_val K a m
  have hval_1 : ((dartNextSub K)^[1] a).1 = (dartNext K)^[1] a.1 := dartNextSub_iterate_val K a 1
  have hsub_eq : (dartNextSub K)^[m] a = (dartNextSub K)^[1] a := by
    apply Subtype.ext
    rw [hval_m, hval_1, hdart_m, hdart_1]
  exact iterate_inj_on_Icc_minimalPeriod (dartNextSub K) a hpos hm1 (by rwa [← hpe]) (by omega)
    (by rw [← hpe]; exact dartOrbitPeriod_pos K hK a) hsub_eq










theorem jc11_orbitLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy,
    orbitFaceWalk_edges]


theorem jc11_face_eq_aboveLeft (f : Site 2) (c : Site 2) (h0 : f 0 = c 0 - 1) (h1 : f 1 = c 1) :
    f = (![c 0 - 1, c 1] : Site 2) := by
  funext i; fin_cases i
  · exact h0
  · exact h1







theorem jc11_topWall_iff_index_one (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) (k : ℕ) (hk : k < dartOrbitPeriod K (extremeBase K c hc)) :
    jc10core_topWallEdge c
        s(dartFace ((dartNext K)^[k] (extremeBase K c hc).1),
          dartFace ((dartNext K)^[k + 1] (extremeBase K c hc).1)) ↔ k = 1 := by
  constructor
  · intro htw
    rw [jc10core_topWallEdge_mk] at htw
    obtain ⟨⟨hrow_eq, hrow_c⟩, hcols⟩ := htw
    rcases hcols with ⟨hxc, hyc⟩ | ⟨hyc, hxc⟩
    · 
      have hfk_eq : dartFace ((dartNext K)^[k] (extremeBase K c hc).1) = (![c 0 - 1, c 1] : Site 2) :=
        jc11_face_eq_aboveLeft _ c hxc hrow_c
      
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exfalso
          rw [h0, Function.iterate_zero_apply, jc11_dartFace_extremeBase K c hc] at hfk_eq
          have hc1 : (![c 0 - 1, c 1 - 1] : Site 2) 1 = (![c 0 - 1, c 1] : Site 2) 1 := by
            rw [hfk_eq]
          simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc1
          omega
        · exact h0
      exact jc11_face_aboveLeft_index_eq_one K hK c hc k hk1 (le_of_lt hk) hfk_eq
    · 
      exfalso
      have hfk1_eq :
          dartFace ((dartNext K)^[k + 1] (extremeBase K c hc).1) = (![c 0 - 1, c 1] : Site 2) :=
        jc11_face_eq_aboveLeft _ c hyc (by rw [← hrow_eq]; exact hrow_c)
      have hk1z : k + 1 = 1 :=
        jc11_face_aboveLeft_index_eq_one K hK c hc (k + 1) (by omega) (by omega) hfk1_eq
      have hk0 : k = 0 := by omega
      
      rw [hk0, Function.iterate_zero_apply, jc11_dartFace_extremeBase K c hc] at hrow_c
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hrow_c
      omega
  · intro hk1
    subst hk1
    rw [jc10core_topWallEdge_mk]
    have hf1 : dartFace ((dartNext K)^[1] (extremeBase K c hc).1) = (![c 0 - 1, c 1] : Site 2) :=
      jc11_orbit_face_one K c hc
    have hf2 : dartFace ((dartNext K)^[1 + 1] (extremeBase K c hc).1) = (![c 0, c 1] : Site 2) := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
      show dartFace (dartNext K (dartNext K (leftDart c))) = _
      exact jc11_dartFace_dartNext2 K c hc
    rw [hf1, hf2]
    refine ⟨⟨rfl, by simp⟩, Or.inl ⟨by simp, by simp⟩⟩





theorem jc11_two_le_period (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 2 ≤ dartOrbitPeriod K a := by
  have hpos : 0 < dartOrbitPeriod K a := dartOrbitPeriod_pos K hK a
  have hne1 : dartOrbitPeriod K a ≠ 1 := by
    show Function.minimalPeriod (dartNextSub K) a ≠ 1
    intro hh
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at hh
    exact dartNextSub_ne_self K a hh
  omega


theorem jc11_range_countP_eq_one (p : ℕ) (hp : 1 < p) :
    (List.range p).countP (fun k => decide (k = 1)) = 1 := by
  have h1 : (List.range p).countP (fun k => decide (k = 1)) = (List.range p).count 1 := by
    rw [List.count]; congr 1
  rw [h1, List.count_eq_one_of_mem (List.nodup_range) (List.mem_range.mpr hp)]





theorem jc11_topWallCount_eq_one (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) :
    jc10core_topWallCount c (mpl_orbitLoop K (extremeBase K c hc)) = 1 := by
  classical
  rw [jc10core_topWallCount, jc11_orbitLoop_edges, List.countP_map]
  
  have hcongr : ∀ k ∈ List.range (dartOrbitPeriod K (extremeBase K c hc)),
      (((fun e => decide (jc10core_topWallEdge c e)) ∘ fun k =>
          s(dartFace ((dartNext K)^[k] (extremeBase K c hc).1),
            dartFace ((dartNext K)^[k + 1] (extremeBase K c hc).1))) k = true
        ↔ (fun k => decide (k = 1)) k = true) := by
    intro k hk
    rw [List.mem_range] at hk
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact jc11_topWall_iff_index_one K hK c hc k hk
  rw [List.countP_congr hcongr]
  exact jc11_range_countP_eq_one _ (by have := jc11_two_le_period K hK (extremeBase K c hc); omega)










theorem jc11_TopWallOdd (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : IsExtremeCell K c) :
    jc10core_TopWallOdd K (extremeBase K c hc) c := by
  unfold jc10core_TopWallOdd
  rw [jc11_topWallCount_eq_one K hK c hc]
  decide




theorem jc11_cornerCellOdd (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : IsExtremeCell K c) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) :=
  jc10core_cornerCellOdd_of_topWallOdd K (extremeBase K c hc) c hc (jc11_TopWallOdd K hK c hc)



theorem jc11_exists_windingWitness (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c : Site 2, ∃ hc : IsExtremeCell K c,
      c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, hc, hc.mem, jc11_cornerCellOdd K hK c hc⟩

end Walls

end StatMech
