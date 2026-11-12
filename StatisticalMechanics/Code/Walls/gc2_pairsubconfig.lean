/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Sharpness.Switching

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


























theorem gc2_walk_subconfig (ends : ι → Sym2 V) (m : Finset ι) (u : V) :
    ∀ {w : V}, connK ends m u w → ∃ P ⊆ m, sources ends P = ({u} : Finset V) ∆ {w} := by
  intro w hconnw
  induction hconnw with
  | refl =>
    
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [symmDiff_self]
    ext x; simp [sources, degK]
  | @tail b c _ hstep ih =>
    
    obtain ⟨P, hPm, hP⟩ := ih
    obtain ⟨i, hi, hb, hc, hbc⟩ := hstep
    refine ⟨P ∆ {i}, ?_, ?_⟩
    · 
      intro x hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨h, _⟩ | ⟨h, _⟩
      · exact hPm h
      · rw [Finset.mem_singleton] at h; subst h; exact hi
    · 
      rw [sources_symmDiff, hP]
      have hsi : sources ends {i} = {b, c} := by
        ext x
        simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hx : x ∈ ends i
        · rw [if_pos hx, Finset.card_singleton]
          have hxbc : x = b ∨ x = c := by
            obtain ⟨⟨a, a'⟩, haa⟩ := (ends i).exists_rep
            rw [← haa] at hx hb hc
            rw [Sym2.mem_iff] at hx hb hc
            rcases hx with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
              tauto
          simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; tauto
        · rw [if_neg hx, Finset.card_empty]
          have hxbc : ¬ (x = b ∨ x = c) := by
            rintro (rfl | rfl)
            · exact hx hb
            · exact hx hc
          simp only [show ¬ Odd 0 from by decide, false_iff]; tauto
      rw [hsi]
      
      have hbc'' : ({b, c} : Finset V) = {b} ∆ {c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_symmDiff]
        constructor
        · rintro (rfl | rfl)
          · left; exact ⟨rfl, fun h => hbc (by simpa using h)⟩
          · right; exact ⟨rfl, fun h => hbc (by simpa using h.symm)⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> tauto
      rw [hbc'']
      rw [symmDiff_assoc, ← symmDiff_assoc ({b} : Finset V), symmDiff_self, bot_symmDiff]





theorem gc2_singleton_symmDiff {u v : V} (huv : u ≠ v) :
    ({u} : Finset V) ∆ {v} = {u, v} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> tauto
  · rintro (rfl | rfl)
    · left; exact ⟨rfl, huv⟩
    · right; exact ⟨rfl, fun h => huv h.symm⟩













theorem gc2_pair_subconfig (ends : ι → Sym2 V) (m : Finset ι)
    {u v : V} (hconn : connK ends m u v) (huv : u ≠ v) :
    ∃ P ⊆ m, sources ends P = {u, v} := by
  obtain ⟨P, hPm, hP⟩ := gc2_walk_subconfig ends m u hconn
  exact ⟨P, hPm, by rw [hP, gc2_singleton_symmDiff huv]⟩














theorem gc2_pair_subconfig_exists (ends : ι → Sym2 V) (m : Finset ι)
    {u v : V} (hconn : connK ends m u v) (huv : u ≠ v) :
    ∃ P : Finset ι, P ⊆ m ∧ sources ends P = {u, v} := by
  obtain ⟨P, hPm, hP⟩ := gc2_pair_subconfig ends m hconn huv
  exact ⟨P, hPm, hP⟩








theorem gc2_pair_subconfig_eq_exists_conn_set (ends : ι → Sym2 V) (m : Finset ι)
    {u v : V} (hconn : connK ends m u v) (huv : u ≠ v) :
    (∃ P ⊆ m, sources ends P = ({u, v} : Finset V))
      ↔ (∃ P ⊆ m, sources ends P = ({u, v} : Finset V)) :=
  ⟨fun _ => RandomCurrent.exists_conn_set ends m hconn huv,
   fun _ => gc2_pair_subconfig ends m hconn huv⟩

end StatMech.Walls
