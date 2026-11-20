/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Walls.gc8cutsupport
import Code.Walls.gc8cutweightmult
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]













def gc10_combinedSources (n₁ n₂ : Ising.Current V) (o x y g : V) : Prop :=
  Ising.sources G.edgeFinset (fun e => n₁ e + n₂ e) = {o, x, y, g}




















def gc10_twoReplicaCutDecomp (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (n₁ n₂ : Ising.Current V) : Prop :=
  
  (∀ e ∈ G.edgeFinset, ¬ gc8Crosses S e)
  
  ∧ (∀ e ∈ G.edgeFinset,
        n₁ e = acwRestrict (acwInternal S) n₁ e + acwRestrict (acwInternal Sᶜ) n₁ e
      ∧ n₂ e = acwRestrict (acwInternal S) n₂ e + acwRestrict (acwInternal Sᶜ) n₂ e)
  
  ∧ ( (Sharpness.sources G (acwRestrict (acwInternal S) n₁) = S ∩ Sharpness.sources G n₁
        ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₁) = Sᶜ ∩ Sharpness.sources G n₁
        ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n₁))
            (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₁)))
    ∧ (Sharpness.sources G (acwRestrict (acwInternal S) n₂) = S ∩ Sharpness.sources G n₂
        ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₂) = Sᶜ ∩ Sharpness.sources G n₂
        ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n₂))
            (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₂))))
  
  ∧ ( weight G β J n₁
        = weight G β J (acwRestrict (acwInternal Sᶜ) n₁) * weight G β J (acwRestrict (acwInternal S) n₁)
    ∧ weight G β J n₂
        = weight G β J (acwRestrict (acwInternal Sᶜ) n₂) * weight G β J (acwRestrict (acwInternal S) n₂))















theorem gc10_twoReplicaCutDecomp_of_closedCut (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n₁ n₂ : Ising.Current V) :
    gc10_twoReplicaCutDecomp G β J S n₁ n₂ := by
  refine ⟨fun e he => gc8_cut_no_crossing G S hcut e he, fun e he => ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · 
    exact ⟨gc8_current_split G S hcut n₁ e he, gc8_current_split G S hcut n₂ e he⟩
  · 
    exact ⟨gc8_sources_internal_eq G S hcut n₁,
           gc8_sources_external_eq G S hcut n₁,
           (gc8_sources_split G S hcut n₁).2⟩
  · 
    exact ⟨gc8_sources_internal_eq G S hcut n₂,
           gc8_sources_external_eq G S hcut n₂,
           (gc8_sources_split G S hcut n₂).2⟩
  · 
    exact gc8_cutWeight_mult G β J S hcut n₁
  · 
    exact gc8_cutWeight_mult G β J S hcut n₂














theorem gc10_twoReplica_fourMark (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n₁ n₂ : Ising.Current V) (o x y g : V)
    (hsrc : gc10_combinedSources G n₁ n₂ o x y g) :
    gc10_twoReplicaCutDecomp G β J S n₁ n₂ ∧ gc10_combinedSources G n₁ n₂ o x y g :=
  ⟨gc10_twoReplicaCutDecomp_of_closedCut G β J S hcut n₁ n₂, hsrc⟩







theorem gc10_twoReplica_split (S : Finset V) (hcut : acwClosedCut G S)
    (n₁ n₂ : Ising.Current V) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    n₁ e = acwRestrict (acwInternal S) n₁ e + acwRestrict (acwInternal Sᶜ) n₁ e
  ∧ n₂ e = acwRestrict (acwInternal S) n₂ e + acwRestrict (acwInternal Sᶜ) n₂ e :=
  ⟨gc8_current_split G S hcut n₁ e he, gc8_current_split G S hcut n₂ e he⟩




theorem gc10_twoReplica_boundary (S : Finset V) (hcut : acwClosedCut G S)
    (n₁ n₂ : Ising.Current V) :
    (Sharpness.sources G (acwRestrict (acwInternal S) n₁) = S ∩ Sharpness.sources G n₁
      ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₁) = Sᶜ ∩ Sharpness.sources G n₁)
  ∧ (Sharpness.sources G (acwRestrict (acwInternal S) n₂) = S ∩ Sharpness.sources G n₂
      ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₂) = Sᶜ ∩ Sharpness.sources G n₂) :=
  ⟨⟨gc8_sources_internal_eq G S hcut n₁, gc8_sources_external_eq G S hcut n₁⟩,
   ⟨gc8_sources_internal_eq G S hcut n₂, gc8_sources_external_eq G S hcut n₂⟩⟩



theorem gc10_twoReplica_weight (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n₁ n₂ : Ising.Current V) :
    weight G β J n₁
      = weight G β J (acwRestrict (acwInternal Sᶜ) n₁) * weight G β J (acwRestrict (acwInternal S) n₁)
  ∧ weight G β J n₂
      = weight G β J (acwRestrict (acwInternal Sᶜ) n₂) * weight G β J (acwRestrict (acwInternal S) n₂) :=
  ⟨gc8_cutWeight_mult G β J S hcut n₁, gc8_cutWeight_mult G β J S hcut n₂⟩




theorem gc10_twoReplica_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (n₁ n₂ : Ising.Current V) :
    0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n₁)
  ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n₁)
  ∧ 0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n₂)
  ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n₂) :=
  ⟨acw_weight_nonneg G β J hβ hJ _, acw_weight_nonneg G β J hβ hJ _,
   acw_weight_nonneg G β J hβ hJ _, acw_weight_nonneg G β J hβ hJ _⟩


















theorem gc10_twoReplica_jointWeight (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n₁ n₂ : Ising.Current V) :
    weight G β J n₁ * weight G β J n₂
      = (weight G β J (acwRestrict (acwInternal Sᶜ) n₁) * weight G β J (acwRestrict (acwInternal S) n₁))
        * (weight G β J (acwRestrict (acwInternal Sᶜ) n₂) * weight G β J (acwRestrict (acwInternal S) n₂)) := by
  rw [gc8_cutWeight_mult G β J S hcut n₁, gc8_cutWeight_mult G β J S hcut n₂]




theorem gc10_twoReplica_jointMass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n₁ n₂ : Ising.Current V) :
    0 ≤ weight G β J n₁ * weight G β J n₂ :=
  mul_nonneg (acw_weight_nonneg G β J hβ hJ n₁) (acw_weight_nonneg G β J hβ hJ n₂)












theorem gc10_combinedSources_iff_symmDiff (n₁ n₂ : Ising.Current V) (o x y g : V) :
    gc10_combinedSources G n₁ n₂ o x y g
      ↔ Ising.sources G.edgeFinset n₁ ∆ Ising.sources G.edgeFinset n₂ = {o, x, y, g} := by
  unfold gc10_combinedSources
  rw [Ising.sources_add]











theorem gc10_twoReplicaCutDecomp_bot (β : ℝ) (J : Sym2 (V) → ℝ) (S : Finset V)
    (n₁ n₂ : Ising.Current V) :
    gc10_twoReplicaCutDecomp (⊥ : SimpleGraph V) β J S n₁ n₂ :=
  gc10_twoReplicaCutDecomp_of_closedCut (⊥ : SimpleGraph V) β J S (gc8_closedCut_bot S) n₁ n₂





theorem gc10_twoReplicaCutDecomp_empty (β : ℝ) (J : Sym2 V → ℝ)
    (n₁ n₂ : Ising.Current V) :
    gc10_twoReplicaCutDecomp G β J (∅ : Finset V) n₁ n₂ :=
  gc10_twoReplicaCutDecomp_of_closedCut G β J ∅ (gc8_closedCut_empty G) n₁ n₂

end StatMech.Walls
