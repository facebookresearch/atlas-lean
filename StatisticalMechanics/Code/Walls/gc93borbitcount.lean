/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc88brereroutehall
import Code.Walls.gc89bmetricinjection
import Code.Walls.gc90bperfiberinject
import Code.Walls.gc91bglobalinjection
import Code.Walls.gc92borbitobstruction

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]





theorem gc93b_pairAction_involutive (τ : Equiv.Perm ι) (hτ2 : ∀ i, τ (τ i) = i) :
    Function.Involutive (gc92b_pairAction (ι := ι) τ) := by
  intro s
  unfold gc92b_pairAction
  have key : ∀ K : Finset ι, (K.image τ).image τ = K := by
    intro K
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := K)]
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply, id_eq, hτ2]
  ext
  · simp only [key]
  · simp only [key]












theorem gc93b_even_card_ff_involution {α : Type*} [DecidableEq α] (φ : α → α)
    (hinv : Function.Involutive φ) :
    ∀ t : Finset α, (∀ a ∈ t, φ a ∈ t) → (∀ a ∈ t, φ a ≠ a) → Even t.card := by
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro hmap hff
    rcases t.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · 
      have hφa : φ a ∈ t := hmap a ha
      have hne : φ a ≠ a := hff a ha
      set t' := t.erase a |>.erase (φ a) with ht'
      have hsub : t' ⊂ t := by
        rw [ht']
        refine Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) ?_
        exact Finset.erase_ssubset ha
      have hmap' : ∀ b ∈ t', φ b ∈ t' := by
        intro b hb
        rw [ht', Finset.mem_erase, Finset.mem_erase] at hb ⊢
        obtain ⟨hbφa, hba, hbt⟩ := hb
        refine ⟨?_, ?_, hmap b hbt⟩
        · 
          intro h; exact hba (by have := congrArg φ h; rwa [hinv, hinv] at this)
        · 
          intro h; apply hbφa; have := congrArg φ h; rwa [hinv] at this
      have hff' : ∀ b ∈ t', φ b ≠ b := by
        intro b hb
        rw [ht', Finset.mem_erase, Finset.mem_erase] at hb
        exact hff b hb.2.2
      have hcard' : t'.card = t.card - 2 := by
        rw [ht', Finset.card_erase_of_mem, Finset.card_erase_of_mem ha]
        · omega
        · rw [Finset.mem_erase]; exact ⟨hne, hφa⟩
      have heven' : Even t'.card := ih t' hsub hmap' hff'
      
      have h2 : 2 ≤ t.card := by
        have hsubtwo : ({a, φ a} : Finset α) ⊆ t := by
          intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl; exacts [ha, hφa]
        have := Finset.card_le_card hsubtwo
        rwa [Finset.card_insert_of_notMem (by simp [Ne.symm hne]), Finset.card_singleton] at this
      rw [hcard'] at heven'
      have hrw : t.card = (t.card - 2) + 2 := by omega
      rw [hrw]
      exact heven'.add (by decide)




theorem gc93b_even_nonfixed {α : Type*} [DecidableEq α] (φ : α → α)
    (hinv : Function.Involutive φ) (s : Finset α) (hmap : ∀ a ∈ s, φ a ∈ s) :
    Even (#(s.filter (fun a => φ a ≠ a))) := by
  set t := s.filter (fun a => φ a ≠ a) with ht
  have hmapt : ∀ a ∈ t, φ a ∈ t := by
    intro a ha
    rw [ht, Finset.mem_filter] at ha ⊢
    refine ⟨hmap a ha.1, ?_⟩
    intro h
    apply ha.2
    have := hinv a
    rw [h] at this
    exact this
  have hff : ∀ a ∈ t, φ a ≠ a := by
    intro a ha
    rw [ht, Finset.mem_filter] at ha
    exact ha.2
  exact gc93b_even_card_ff_involution φ hinv t hmapt hff





theorem gc93b_card_eq_fixed_add_even {α : Type*} [DecidableEq α] (φ : α → α)
    (hinv : Function.Involutive φ) (s : Finset α) (hmap : ∀ a ∈ s, φ a ∈ s) :
    #s = #(s.filter (fun a => φ a = a)) + #(s.filter (fun a => φ a ≠ a))
      ∧ Even (#(s.filter (fun a => φ a ≠ a))) := by
  refine ⟨?_, gc93b_even_nonfixed φ hinv s hmap⟩
  exact (Finset.card_filter_add_card_filter_not (s := s) (fun a => φ a = a)).symm





theorem gc93b_two_mul_orbits {α : Type*} [DecidableEq α] (φ : α → α)
    (hinv : Function.Involutive φ) (s : Finset α) (hmap : ∀ a ∈ s, φ a ∈ s) :
    2 * (#(s.filter (fun a => φ a = a)) + #(s.filter (fun a => φ a ≠ a)) / 2)
      = #s + #(s.filter (fun a => φ a = a)) := by
  obtain ⟨hcard, ⟨k, hk⟩⟩ := gc93b_card_eq_fixed_add_even φ hinv s hmap
  rw [hcard, hk]
  omega











theorem gc93b_pairAction_fixed_iff (τ : Equiv.Perm ι) (K₁ K₂ : Finset ι) :
    gc92b_pairAction τ (K₁, K₂) = (K₁, K₂) ↔ K₁.image τ = K₁ ∧ K₂.image τ = K₂ := by
  unfold gc92b_pairAction
  simp only [Prod.mk.injEq]





theorem gc93b_cogxg_fixed_eq_invariant_pairs (ends : ι → Sym2 W) (m : Finset ι) (o x g : W)
    (τ : Equiv.Perm ι) :
    #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s))
      = #((gc91b_cogxgPairs ends m o x g).filter
          (fun s => s.1.image τ = s.1 ∧ s.2.image τ = s.2)) := by
  apply Finset.card_bij (fun s _ => s)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hmem, hfix⟩ := hs
    exact ⟨hmem, (gc93b_pairAction_fixed_iff τ s.1 s.2).1 (by rw [← Prod.mk.eta (p := s)] at hfix ⊢; exact hfix)⟩
  · intro a _ b _ h; exact h
  · intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hmem, hfix⟩ := hs
    refine ⟨s, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨hmem, by rw [← Prod.mk.eta (p := s)]; exact (gc93b_pairAction_fixed_iff τ s.1 s.2).2 hfix⟩




theorem gc93b_T3_fixed_eq_invariant_pairs (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (τ : Equiv.Perm ι) :
    #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s))
      = #((gc91b_T3Pairs ends m o x y g).filter
          (fun s => s.1.image τ = s.1 ∧ s.2.image τ = s.2)) := by
  apply Finset.card_bij (fun s _ => s)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hmem, hfix⟩ := hs
    exact ⟨hmem, (gc93b_pairAction_fixed_iff τ s.1 s.2).1 (by rw [← Prod.mk.eta (p := s)] at hfix ⊢; exact hfix)⟩
  · intro a _ b _ h; exact h
  · intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hmem, hfix⟩ := hs
    refine ⟨s, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨hmem, by rw [← Prod.mk.eta (p := s)]; exact (gc93b_pairAction_fixed_iff τ s.1 s.2).2 hfix⟩


















theorem gc93b_orbitcount_iff (ends : ι → Sym2 W) (m : Finset ι) {o x y g : W}
    (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i) (hτ2 : ∀ i, τ (τ i) = i)
    (hm : m.image τ = m) :
    let cog := #(gc91b_cogxgPairs ends m o x g)
    let t3 := #(gc91b_T3Pairs ends m o x y g)
    let Fc := #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s))
    let Ft := #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s))
    let ncog := Fc + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2
    let nt3 := Ft + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2
    2 * ncog = cog + Fc ∧ 2 * nt3 = t3 + Ft ∧ (ncog ≤ nt3 ↔ cog + Fc ≤ t3 + Ft) := by
  intro cog t3 Fc Ft ncog nt3
  
  have hinvol := gc93b_pairAction_involutive τ hτ2
  have hmapcog : ∀ s ∈ gc91b_cogxgPairs ends m o x g, gc92b_pairAction τ s ∈ gc91b_cogxgPairs ends m o x g := by
    intro s hs
    have := (gc92b_perm_mem_cogxgSet_iff ends τ hτ m hm o x g s.1 s.2).2 (by rwa [Prod.mk.eta] )
    simpa [gc92b_pairAction] using this
  have hmapt3 : ∀ s ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ s ∈ gc91b_T3Pairs ends m o x y g := by
    intro s hs
    have := (gc92b_perm_mem_T3Set_iff ends τ hτ m hm o x y g s.1 s.2).2 (by rwa [Prod.mk.eta] )
    simpa [gc92b_pairAction] using this
  have hcog := gc93b_two_mul_orbits (gc92b_pairAction τ) hinvol (gc91b_cogxgPairs ends m o x g) hmapcog
  have ht3 := gc93b_two_mul_orbits (gc92b_pairAction τ) hinvol (gc91b_T3Pairs ends m o x y g) hmapt3
  refine ⟨hcog, ht3, ?_⟩
  constructor
  · intro h; omega
  · intro h; omega












theorem gc93b_wred_swap_involutive : ∀ i : Fin 4, (Equiv.swap (1 : Fin 4) 2) ((Equiv.swap (1 : Fin 4) 2) i) = i := by
  decide








theorem gc93b_wred_orbit_data :
    
    (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ≠ (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
        (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
        (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ≠ (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    
    ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
        ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
    ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
        ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) := by
  refine ⟨gc92b_wred_cogxg_swapped.1, gc92b_wred_cogxg_swapped.2, ?_,
    gc92b_wred_swap_fixes_T3.1, gc92b_wred_swap_fixes_T3.2⟩
  rw [gc92b_wred_cogxg_swapped.2]; exact fun h => gc92b_wred_cogxg_swapped.1 h.symm


















theorem gc93b_burnside_status (ends : ι → Sym2 W) (m : Finset ι) {o x y g : W}
    (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i) (hτ2 : ∀ i, τ (τ i) = i)
    (hm : m.image τ = m) :
    
    Function.Involutive (gc92b_pairAction (ι := ι) τ)
    
    ∧ (#(gc91b_cogxgPairs ends m o x g)
        = #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s))
          + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s))
        ∧ Even (#((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s))))
    
    ∧ (#((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s))
          + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2
        ≤ #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s))
          + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s ≠ s)) / 2
      ↔ #(gc91b_cogxgPairs ends m o x g)
          + #((gc91b_cogxgPairs ends m o x g).filter (fun s => gc92b_pairAction τ s = s))
        ≤ #(gc91b_T3Pairs ends m o x y g)
          + #((gc91b_T3Pairs ends m o x y g).filter (fun s => gc92b_pairAction τ s = s))) := by
  have hinvol := gc93b_pairAction_involutive τ hτ2
  have hmapcog : ∀ s ∈ gc91b_cogxgPairs ends m o x g, gc92b_pairAction τ s ∈ gc91b_cogxgPairs ends m o x g := by
    intro s hs
    have := (gc92b_perm_mem_cogxgSet_iff ends τ hτ m hm o x g s.1 s.2).2 (by rwa [Prod.mk.eta])
    simpa [gc92b_pairAction] using this
  refine ⟨hinvol, gc93b_card_eq_fixed_add_even (gc92b_pairAction τ) hinvol _ hmapcog, ?_⟩
  exact (gc93b_orbitcount_iff ends m τ hτ hτ2 hm).2.2



















theorem gc93b_machine_findings : True := trivial

end StatMech.Walls
