/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.MultiReplica
import Code.Ising.AizenmanSignDominance
import Code.Ising.AizenmanInclusionExclusion
import Code.Ising.AizenmanHdom

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent



local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]









theorem ght_backbone_removed_subset (m P : Finset ι) (hP : P ⊆ m) : m ∆ P ⊆ m := by
  intro a ha
  rw [Finset.mem_symmDiff] at ha
  rcases ha with ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · exact hP h






theorem ght_backbone_removed_sources (ends : ι → Sym2 V) (m P : Finset ι) (A : Finset V)
    (hm : srcK ends m = A) {x y : V} (hPsrc : srcK ends P = {x, y}) :
    srcK ends (m ∆ P) = A ∆ {x, y} := by
  rw [sources_symmDiff, hm, hPsrc]





theorem ght_backbone_exists_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) (hxy : x ≠ y) :
    ∃ P ⊆ m, srcK ends P = {x, y} :=
  StatMech.Sharpness.RandomCurrent.exists_conn_set ends m hall.1 hxy




theorem ght_backbone_removed_nd (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) :
    ∀ i ∈ m ∆ P, ¬ (ends i).IsDiag :=
  fun i hi => hnd i (ght_backbone_removed_subset m P hP hi)
























theorem ght_backbone_per_switching (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {x y : V} (hPsrc : srcK ends P = {x, y}) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K) :
    aie_mass ends (m ∆ P) φ A
      = (if connK ends (m ∆ P) x y then 1 else 0) *
          aie_mass ends (m ∆ P) φ (A ∆ {x, y}) := by
  have hndP : ∀ i ∈ m ∆ P, ¬ (ends i).IsDiag :=
    ght_backbone_removed_nd ends m P hP hnd
  have hmP : srcK ends (m ∆ P) = A ∆ {x, y} :=
    ght_backbone_removed_sources ends m P A hm hPsrc
  have key := asd_switching_weighted_indicator ends (m ∆ P) hndP (A ∆ {x, y}) hmP hxy φ hφ
  have hAA : (A ∆ {x, y}) ∆ {x, y} = A := by
    rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  rw [hAA] at key
  exact key











theorem ght_backbone_no_surplus_of_conn (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {x y : V} (hPsrc : srcK ends P = {x, y}) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K)
    (hconn : connK ends (m ∆ P) x y) :
    aie_mass ends (m ∆ P) φ (A ∆ {x, y}) = aie_mass ends (m ∆ P) φ A := by
  have key := ght_backbone_per_switching ends m P hP hnd A hm hPsrc hxy φ hφ
  rw [if_pos hconn, one_mul] at key
  exact key.symm











noncomputable def ght_backbones (ends : ι → Sym2 V) (m : Finset ι) (x y : V) : Finset (Finset ι) :=
  m.powerset.filter (fun P => srcK ends P = {x, y})





noncomputable def ght_resummedNoneMass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (A : Finset V) (o x y : V) : ℝ :=
  ∑ P ∈ (ght_backbones ends m x y).filter (fun P => aie_noneConn ends (m ∆ P) o x y),
    aie_mass ends (m ∆ P) φ (A ∆ {x, y})











def ght_backboneAvgDom (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (o x y : V) (Φ : Finset ι → Finset ι → ℝ) : Prop :=
  2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ ∑ m ∈ M.filter (fun m => aie_allConn ends m o x y),
        ght_resummedNoneMass ends m (Φ m) A o x y






theorem ght_backboneAvgDom_holds_of_no_allConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    ght_backboneAvgDom ends M A o x y Φ := by
  unfold ght_backboneAvgDom
  rw [hno, Finset.sum_empty, Finset.sum_empty, mul_zero]













theorem ght_tri_backbones :
    ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2
      = {{1}, {0, 2}} := by
  unfold ght_backbones
  decide





theorem ght_tri_removed_conn_1 :
    connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({1} : Finset (Fin 3))) 1 2 := by
  have h : (({0, 1, 2} : Finset (Fin 3)) ∆ ({1} : Finset (Fin 3))) = {0, 2} := by decide
  rw [h]
  refine Relation.ReflTransGen.head (b := 0) ?_
    (Relation.ReflTransGen.single (a := 0) (b := 2) ?_)
  · exact ⟨0, by decide, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide, by decide⟩




theorem ght_tri_removed_conn_2 :
    connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({0, 2} : Finset (Fin 3))) 1 2 := by
  have h : (({0, 1, 2} : Finset (Fin 3)) ∆ ({0, 2} : Finset (Fin 3))) = {1} := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩






theorem ght_tri_resummed_filter_empty :
    (ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2).filter
      (fun P => aie_noneConn ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ P) 0 1 2) = ∅ := by
  rw [ght_tri_backbones, Finset.filter_eq_empty_iff]
  intro P hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · rintro ⟨h1, _, _⟩; exact h1 ght_tri_removed_conn_1
  · rintro ⟨h1, _, _⟩; exact h1 ght_tri_removed_conn_2





theorem ght_tri_resummedNoneMass_zero :
    ght_resummedNoneMass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1)
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 = 0 := by
  unfold ght_resummedNoneMass
  rw [ght_tri_resummed_filter_empty, Finset.sum_empty]




















theorem ght_backboneAvgDom_refutable :
    ¬ ght_backboneAvgDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
  unfold ght_backboneAvgDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := srcK ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton, Finset.sum_singleton] at hdom
  
  rw [ght_tri_resummedNoneMass_zero] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising

end StatMech
