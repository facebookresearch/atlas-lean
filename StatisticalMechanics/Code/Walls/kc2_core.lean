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
import Code.Lattice.ContourLinksExits
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.ExteriorConnected
import Code.Walls.kc2_supportisface
import Code.Walls.kc2_dartdircases
import Code.Walls.kc2_rightfaceinK
import Code.Walls.kc2_downfaceoutK
import Code.Walls.kc2_leftupfacecell

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice










theorem kc2_supportOdd_right {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) :
    dartFace e ∈ K :=
  kc2_rightDart_face_mem_K K e he hd












def kc2_SupportOddNonRight (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z ∈ (mpl_orbitLoop K a).support, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) →
    ∀ e : Dart, IsBoundaryDart K e → z = dartFace e →
      (e.dir = ![0, -1] ∨ e.dir = ![0, 1] ∨ e.dir = ![-1, 0]) → z ∈ K












theorem kc2_supportOddNonRight_of_core {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (h : exc_SupportOddInK K a) : kc2_SupportOddNonRight K a :=
  fun z hz hodd _e _he _hzf _hdir => h z hz hodd









theorem kc2_supportOddInK_of_nonRight {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (h : kc2_SupportOddNonRight K a) : exc_SupportOddInK K a := by
  intro z hz hodd
  obtain ⟨i, hzf, hbd⟩ := kc2_support_is_face_exists K a hz
  
  set e : Dart := (dartNext K)^[i] a.1 with he_def
  rcases kc2_dart_dir_cases e with hdir | hdir | hdir | hdir
  · 
    rw [hzf]; exact kc2_supportOdd_right hbd hdir
  · 
    exact h z hz hodd e hbd hzf (Or.inr (Or.inr hdir))
  · 
    exact h z hz hodd e hbd hzf (Or.inr (Or.inl hdir))
  · 
    exact h z hz hodd e hbd hzf (Or.inl hdir)





theorem kc2_supportOddInK_iff_nonRight {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔ kc2_SupportOddNonRight K a :=
  ⟨kc2_supportOddNonRight_of_core, kc2_supportOddInK_of_nonRight⟩















theorem kc2_down_residue_is_evenRay {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    {e : Dart} (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    (¬ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) → dartFace e ∈ K) ↔
      Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
  constructor
  · intro himp
    by_contra hodd
    exact kc2_dartFace_down_notMem he hd (himp hodd)
  · intro heven hodd
    exact absurd heven hodd



















def kc2_DownFaceEven (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ e : Dart, IsBoundaryDart K e → e.dir = ![0, -1] →
    dartFace e ∈ (mpl_orbitLoop K a).support →
    Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a))



def kc2_UpFaceInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ e : Dart, IsBoundaryDart K e → e.dir = ![0, 1] →
    dartFace e ∈ (mpl_orbitLoop K a).support →
    ¬ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) → dartFace e ∈ K



def kc2_LeftFaceInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ e : Dart, IsBoundaryDart K e → e.dir = ![-1, 0] →
    dartFace e ∈ (mpl_orbitLoop K a).support →
    ¬ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) → dartFace e ∈ K








theorem kc2_supportOddNonRight_iff_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    kc2_SupportOddNonRight K a ↔
      kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · 
      intro e he hd hsupp
      rw [← kc2_down_residue_is_evenRay (a := a) he hd]
      intro hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inl hd)
    · 
      intro e he hd hsupp hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inr (Or.inl hd))
    · 
      intro e he hd hsupp hodd
      exact h (dartFace e) hsupp hodd e he rfl (Or.inr (Or.inr hd))
  · rintro ⟨hdown, hup, hleft⟩ z hz hodd e he hzf hdir
    subst hzf
    rcases hdir with hd | hd | hd
    · 
      exact absurd (hdown e he hd hz) hodd
    · exact hup e he hd hz hodd
    · exact hleft e he hd hz hodd





theorem kc2_supportOddInK_of_three {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (hdown : kc2_DownFaceEven K a) (hup : kc2_UpFaceInK K a) (hleft : kc2_LeftFaceInK K a) :
    exc_SupportOddInK K a :=
  kc2_supportOddInK_of_nonRight (kc2_supportOddNonRight_iff_three.mpr ⟨hdown, hup, hleft⟩)











theorem kc2_unitCell_core : exc_SupportOddInK unitCell ucBase :=
  exc_unitCell_supportOddInK






theorem kc2_unitCell_supportOddNonRight : kc2_SupportOddNonRight unitCell ucBase :=
  kc2_supportOddNonRight_of_core exc_unitCell_supportOddInK








theorem kc2_unitCell_three :
    kc2_DownFaceEven unitCell ucBase ∧ kc2_UpFaceInK unitCell ucBase ∧
      kc2_LeftFaceInK unitCell ucBase :=
  kc2_supportOddNonRight_iff_three.mp kc2_unitCell_supportOddNonRight


















theorem kc2_core_iff_three {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔
      (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) :=
  kc2_supportOddInK_iff_nonRight.trans kc2_supportOddNonRight_iff_three

end Walls

end StatMech
