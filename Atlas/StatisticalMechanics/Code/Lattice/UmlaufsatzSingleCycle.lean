/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.ContourLinksExits
import Code.Lattice.OrbitEncloses
import Code.Lattice.JordanSingleCycle
import Code.Lattice.Umlaufsatz

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}










noncomputable def usc_fourDirs : Finset (Site 2) :=
  {![1, 0], ![-1, 0], ![0, 1], ![0, -1]}


theorem usc_dir_mem_fourDirs (e : Dart) : e.dir ∈ usc_fourDirs := by
  unfold usc_fourDirs
  rcases dartDir_cases e with h | h | h | h <;> rw [h] <;> simp


theorem usc_fourDirs_card : usc_fourDirs.card = 4 := by
  unfold usc_fourDirs
  decide





theorem usc_dir_injOn_of_face_eq (f : Site 2) (T : Set Dart) (hT : ∀ e ∈ T, dartFace e = f) :
    Set.InjOn (fun e : Dart => e.dir) T := by
  intro e₁ he₁ e₂ he₂ hdir
  simp only at hdir
  exact dartFace_eq_of_dir_eq hdir (by rw [hT e₁ he₁, hT e₂ he₂])




noncomputable def usc_visitSet (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) : Finset ℕ := by
  classical
  exact (Finset.range (dartOrbitPeriod K a)).filter
    (fun i => dartFace ((dartNext K)^[i] a.1) = f)






theorem usc_dir_injOn_visitSet (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) :
    Set.InjOn (fun i => ((dartNext K)^[i] a.1).dir) (usc_visitSet K a f) := by
  classical
  intro i hi j hj hdir
  simp only [usc_visitSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hj
  simp only at hdir
  have hface : dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) := by
    rw [hi.2, hj.2]
  have hdart : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    dartFace_eq_of_dir_eq hdir hface
  exact orbitDart_injOn K a (Set.mem_Iio.mpr hi.1) (Set.mem_Iio.mpr hj.1) hdart







theorem usc_orbitFace_multiplicity_le_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2) :
    (usc_visitSet K a f).card ≤ 4 := by
  classical
  calc (usc_visitSet K a f).card
      ≤ ((usc_visitSet K a f).image (fun i => ((dartNext K)^[i] a.1).dir)).card := by
        rw [Finset.card_image_of_injOn (usc_dir_injOn_visitSet K a f)]
    _ ≤ usc_fourDirs.card := by
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨i, _, rfl⟩ := hd
        exact usc_dir_mem_fourDirs _
    _ = 4 := usc_fourDirs_card














theorem usc_faceInjOn_iff_visit_le_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔
      ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
  classical
  constructor
  · 
    intro hinj f
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at hi hj
    exact hinj (Set.mem_Iio.mpr hi.1) (Set.mem_Iio.mpr hj.1) (by simp only; rw [hi.2, hj.2])
  · 
    intro hcard i hi j hj hface
    simp only [Set.mem_Iio] at hi hj
    simp only at hface
    
    set f := dartFace ((dartNext K)^[i] a.1) with hf
    have hi' : i ∈ usc_visitSet K a f := by
      simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, rfl⟩
    have hj' : j ∈ usc_visitSet K a f := by
      simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hface.symm⟩
    exact Finset.card_le_one.mp (hcard f) i hi' j hj'







theorem usc_noPinch_iff_singleVisit (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    OrbitFaceNoPinch K a ↔ ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
  rw [← orbitFace_injOn_iff_dir_collision K a]
  exact usc_faceInjOn_iff_visit_le_one K a







def usc_FaceMultiplicityOne (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ f : Site 2, 1 ≤ (usc_visitSet K a f).card → (usc_visitSet K a f).card = 1





theorem usc_faceMultiplicityOne_iff_noPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    usc_FaceMultiplicityOne K a ↔ OrbitFaceNoPinch K a := by
  rw [usc_noPinch_iff_singleVisit]
  constructor
  · intro h f
    rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
    · omega
    · rw [h f hpos]
  · intro h f _
    have := h f
    omega















noncomputable def usc_localTurn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) : ℤ :=
  ∑ i ∈ usc_visitSet K a f, turnZ K ((dartNext K)^[i] a.1)


noncomputable def usc_orbitFaces (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Finset (Site 2) := by
  classical
  exact (Finset.range (dartOrbitPeriod K a)).image (fun i => dartFace ((dartNext K)^[i] a.1))










theorem usc_totalTurnZ_eq_sum_localTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a)
      = ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f := by
  classical
  unfold totalTurnZ usc_localTurn usc_visitSet usc_orbitFaces
  rw [Finset.sum_image']
  intro i _
  rfl





theorem usc_singleVisit_local_turn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) (i : ℕ) (h : usc_visitSet K a f = {i}) :
    usc_localTurn K a f = turnZ K ((dartNext K)^[i] a.1) := by
  unfold usc_localTurn
  rw [h, Finset.sum_singleton]







theorem usc_abs_localTurn_le_four (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) : |usc_localTurn K a f| ≤ 4 := by
  classical
  unfold usc_localTurn
  calc |∑ i ∈ usc_visitSet K a f, turnZ K ((dartNext K)^[i] a.1)|
      ≤ ∑ i ∈ usc_visitSet K a f, |turnZ K ((dartNext K)^[i] a.1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ usc_visitSet K a f, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => abs_turnZ_le_one K _)
    _ = (usc_visitSet K a f).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 4 := by exact_mod_cast usc_orbitFace_multiplicity_le_four K a f



















theorem usc_orbit_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a) :
    ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl
      (by rw [orbit_iterate_period_eq K a])).IsCycle :=
  orbitFaceWalk_isCycle K a.1 a.2 (dartOrbitPeriod K a) hp (orbit_iterate_period_eq K a)
    (orbitFace_injOn_of_noPinch K a hnp)







theorem usc_orbitFaceSimple_of_noPinch (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    OrbitFaceSimple ω hfin :=
  ⟨hp, orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp⟩






theorem usc_exitMinFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    (exitMinFaceLoop (ω := ω) hfin).IsCycle :=
  exitMinFaceLoop_isCycle (ω := ω) hfin (usc_orbitFaceSimple_of_noPinch (ω := ω) hfin hp hnp)











theorem usc_pc_lt_one_of_noPinch
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
        OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
        ExitDartsSameOrbit ω hfin) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  apply pc_lt_one_of_orbitFaceSimple
  intro ω hfin
  obtain ⟨hp, hnp, hsame⟩ := h ω hfin
  exact ⟨usc_orbitFaceSimple_of_noPinch (ω := ω) hfin hp hnp, hsame⟩















theorem usc_unitCell_noPinch : OrbitFaceNoPinch unitCell ucBase := by
  apply orbitFace_noPinch_of_injOn unitCell ucBase
  rw [unitCell_orbitPeriod_eq_four]
  exact unitCell_orbitFace_injOn





theorem usc_unitCell_faceMultiplicityOne : usc_FaceMultiplicityOne unitCell ucBase :=
  (usc_faceMultiplicityOne_iff_noPinch unitCell ucBase).mpr usc_unitCell_noPinch






theorem usc_unitCell_isCycle :
    ((dartOrbitFaceWalk unitCell ucBase.1 ucBase.2 (dartOrbitPeriod unitCell ucBase)).copy rfl
      (by rw [orbit_iterate_period_eq unitCell ucBase])).IsCycle :=
  usc_orbit_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    usc_unitCell_noPinch





theorem usc_domino_noPinch : OrbitFaceNoPinch domino dmBase := by
  apply orbitFace_noPinch_of_injOn domino dmBase
  rw [domino_orbitPeriod_eq_six]
  exact domino_orbitFace_injOn




theorem usc_domino_faceMultiplicityOne : usc_FaceMultiplicityOne domino dmBase :=
  (usc_faceMultiplicityOne_iff_noPinch domino dmBase).mpr usc_domino_noPinch





theorem usc_domino_isCycle :
    ((dartOrbitFaceWalk domino dmBase.1 dmBase.2 (dartOrbitPeriod domino dmBase)).copy rfl
      (by rw [orbit_iterate_period_eq domino dmBase])).IsCycle :=
  usc_orbit_isCycle domino dmBase (by rw [domino_orbitPeriod_eq_six]; norm_num) usc_domino_noPinch

end Lattice

end StatMech
