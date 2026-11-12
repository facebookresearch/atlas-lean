/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Ising.KramersWannierClose
import Code.Ising.KramersWannierDuality

open scoped BigOperators
open Finset

namespace StatMech

namespace Walls

open StatMech.Ising

section FlipFiber

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj]




def flipConfig (s : ConfigSpace V) : ConfigSpace V := fun v => ! s v

omit [Fintype V] [DecidableEq V] in
@[simp] theorem flipConfig_apply (s : ConfigSpace V) (v : V) :
    flipConfig s v = ! s v := rfl

omit [Fintype V] [DecidableEq V] in

theorem flipConfig_flipConfig (s : ConfigSpace V) :
    flipConfig (flipConfig s) = s := by
  funext v; simp [flipConfig]

omit [DecidableEq V] in



theorem cutEdges_flipConfig (s : ConfigSpace V) :
    cutEdges Gp (flipConfig s) = cutEdges Gp s :=
  cutEdges_flip Gp s

omit [Fintype V] [DecidableEq V] in




theorem flipConfig_ne [Nonempty V] (s : ConfigSpace V) :
    flipConfig s ≠ s := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  intro hcontra
  have hv := congrFun hcontra v₀
  cases h : s v₀ <;> rw [flipConfig_apply, h] at hv <;> simp at hv












theorem cutMap_fiber_eq_flip_orbit [Nonempty V] (hG : Gp.Preconnected)
    (s : ConfigSpace V) :
    (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = cutEdges Gp s))
      = {s, flipConfig s} := by
  ext s'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · 
    intro hs'
    have hcut : cutEdges Gp s = cutEdges Gp s' := hs'.symm
    rcases eq_or_flip_of_cutEdges_eq Gp hG hcut with h | h
    · exact Or.inl h
    · exact Or.inr h
  · 
    rintro (rfl | rfl)
    · rfl
    · exact cutEdges_flipConfig Gp s



theorem cutMap_fiber_card_eq_two [Nonempty V] (hG : Gp.Preconnected)
    (s : ConfigSpace V) :
    (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = cutEdges Gp s)).card
      = 2 := by
  rw [cutMap_fiber_eq_flip_orbit Gp hG s, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  exact (flipConfig_ne s).symm





theorem cutMap_fiber_eq_flip_orbit_of_mem [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} {s : ConfigSpace V} (hs : cutEdges Gp s = δ) :
    (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = δ))
      = {s, flipConfig s} := by
  rw [← hs]; exact cutMap_fiber_eq_flip_orbit Gp hG s

end FlipFiber

end Walls

end StatMech
