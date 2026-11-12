/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Sharpness.Switching
import Code.Walls.gc2_shiftbij
import Code.Walls.gc3_twosourceswitch
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent
open StatMech.Ising

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]
















def gc4_exactlyOneConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  ¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y




theorem gc4_conn_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    aie_allConn ends m o x y ∨ aie_noneConn ends m o x y ∨ gc4_exactlyOneConn ends m o x y := by
  by_cases hall : aie_allConn ends m o x y
  · exact Or.inl hall
  · by_cases hnone : aie_noneConn ends m o x y
    · exact Or.inr (Or.inl hnone)
    · exact Or.inr (Or.inr ⟨hall, hnone⟩)




theorem gc4_conn_classes_disjoint (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) (hnone : aie_noneConn ends m o x y) : False :=
  aie_noneConn_not_allConn ends m hnone hall



theorem gc4_exactlyOne_not_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : gc4_exactlyOneConn ends m o x y) : ¬ aie_allConn ends m o x y := h.1


theorem gc4_exactlyOne_not_none (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : gc4_exactlyOneConn ends m o x y) : ¬ aie_noneConn ends m o x y := h.2















theorem gc4_shift_mapsTo_super (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m) (A : Finset V) :
    Set.MapsTo (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = A}
      {N | N ⊆ m} := by
  have hbij := gc2_sources_shift_bijOn ends m K hK A
  intro N hN
  exact (hbij.1 hN).1





theorem gc4_shift₂_mapsTo_super (ends : ι → Sym2 V) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset V) :
    Set.MapsTo (fun N => (N ∆ P) ∆ Q)
      {N | N ⊆ m ∧ sources ends N = A}
      {N | N ⊆ m} := by
  have hbij := gc3_sources_shift₂_bijOn ends m P Q hP hQ A
  intro N hN
  exact (hbij.1 hN).1





theorem gc4_shift_image_subset_powerset (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) :
    (m.powerset.filter (fun N => sources ends N = A)).image (fun N => N ∆ K) ⊆ m.powerset := by
  have hbij := gc2_sources_shift_bijOn ends m K hK A
  intro N hN
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hN
  obtain ⟨L, ⟨hLm, hLA⟩, rfl⟩ := hN
  rw [Finset.mem_powerset]
  exact (hbij.1 ⟨hLm, hLA⟩).1

















theorem gc4_shift_preserves_allConn (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) {o x y : V} :
    (aie_allConn ends m o x y ↔ aie_allConn ends m o x y)
      ∧ Set.MapsTo (fun N => N ∆ K)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  ⟨Iff.rfl, gc4_shift_mapsTo_super ends m K hK A⟩




theorem gc4_shift_preserves_noneConn (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) {o x y : V} :
    (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y)
      ∧ Set.MapsTo (fun N => N ∆ K)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  ⟨Iff.rfl, gc4_shift_mapsTo_super ends m K hK A⟩




theorem gc4_shift_preserves_exactlyOne (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) {o x y : V} :
    (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y)
      ∧ Set.MapsTo (fun N => N ∆ K)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  ⟨Iff.rfl, gc4_shift_mapsTo_super ends m K hK A⟩








theorem gc4_shift_preserves_backboneFactor (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = asd_ghsBackboneFactor ends m o x y
      ∧ Set.MapsTo (fun N => N ∆ K)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  ⟨rfl, gc4_shift_mapsTo_super ends m K hK A⟩















theorem gc4_shift₂_preserves_class (ends : ι → Sym2 V) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset V) (o x y : V) :
    (aie_allConn ends m o x y ↔ aie_allConn ends m o x y)
      ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y)
      ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y)
      ∧ Set.MapsTo (fun N => (N ∆ P) ∆ Q)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, gc4_shift₂_mapsTo_super ends m P Q hP hQ A⟩








theorem gc4_shift_member_same_class (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) {o x y : V} {N : Finset ι}
    (hN : N ⊆ m ∧ sources ends N = A) :
    (N ∆ K) ⊆ m
      ∧ ((aie_allConn ends m o x y ∧ aie_allConn ends m o x y)
          ∨ (aie_noneConn ends m o x y ∧ aie_noneConn ends m o x y)
          ∨ (gc4_exactlyOneConn ends m o x y ∧ gc4_exactlyOneConn ends m o x y)) := by
  refine ⟨(gc4_shift_mapsTo_super ends m K hK A hN), ?_⟩
  rcases gc4_conn_trichotomy ends m o x y with h | h | h
  · exact Or.inl ⟨h, h⟩
  · exact Or.inr (Or.inl ⟨h, h⟩)
  · exact Or.inr (Or.inr ⟨h, h⟩)



















theorem gc4_twoSourceSwitch_preserves_class (ends : ι → Sym2 V) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset V) {u v s t : V} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) (o x y : V) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}))
        = #(m.powerset.filter (fun K => sources ends K = A))
      ∧ (aie_allConn ends m o x y ↔ aie_allConn ends m o x y)
      ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y)
      ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y)
      ∧ Set.MapsTo (fun K => (K ∆ P) ∆ Q)
          {K | K ⊆ m ∧ sources ends K = A} {K | K ⊆ m} :=
  ⟨gc3_twoSourceSwitch ends m A huv hst hconnuv hconnst,
   Iff.rfl, Iff.rfl, Iff.rfl, gc4_shift₂_mapsTo_super ends m P Q hP hQ A⟩




















theorem gc4_shift_witness_in_super (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) {N₀ : Finset ι} (hN₀m : N₀ ⊆ m) (hN₀A : sources ends N₀ = A) :
    (N₀ ∆ K) ⊆ m
      ∧ asd_ghsBackboneFactor ends m = asd_ghsBackboneFactor ends m := by
  refine ⟨?_, rfl⟩
  have hbij := gc2_sources_shift_bijOn ends m K hK A
  exact (hbij.1 ⟨hN₀m, hN₀A⟩).1





theorem gc4_class_indep_of_subconfig (ends : ι → Sym2 V) (m : Finset ι) (o x y : V)
    (N₁ N₂ : Finset ι) :
    (aie_allConn ends m o x y ↔ aie_allConn ends m o x y)
      ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y)
      ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end StatMech.Walls
