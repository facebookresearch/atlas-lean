/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











theorem gc8_not_internal_both_cwm (S : Finset V) (e : Sym2 V) :
    ¬ (acwInternal S e ∧ acwInternal Sᶜ e) := by
  rintro ⟨hS, hSc⟩
  obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
  have ha : a ∈ e := hab ▸ Sym2.mem_mk_left a b
  exact (Finset.mem_compl.1 (hSc a ha)) (hS a ha)











theorem gc8_notInternalS_iff_internalCompl (S : Finset V) (hcut : acwClosedCut G S)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    ¬ acwInternal S e ↔ acwInternal Sᶜ e := by
  constructor
  · intro hns
    rcases hcut e he with h | h
    · exact absurd h hns
    · exact h
  · intro hsc hns
    exact gc8_not_internal_both_cwm S e ⟨hns, hsc⟩





















theorem gc8_cut_decomp (S : Finset V) (hcut : acwClosedCut G S) (n : Sharpness.Current V)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e := by
  unfold acwRestrict
  by_cases h : acwInternal S e
  · have hnsc : ¬ acwInternal Sᶜ e := fun hsc => gc8_not_internal_both_cwm S e ⟨h, hsc⟩
    rw [if_pos h, if_neg hnsc, add_zero]
  · have hsc : acwInternal Sᶜ e := (gc8_notInternalS_iff_internalCompl G S hcut he).1 h
    rw [if_neg h, if_pos hsc, zero_add]



















theorem gc8_notInternalS_weight_eq_internalCompl (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n : Sharpness.Current V) :
    weight G β J (acwRestrict (fun e => ¬ acwInternal S e) n)
      = weight G β J (acwRestrict (acwInternal Sᶜ) n) := by
  unfold weight acwRestrict
  refine Finset.prod_congr rfl (fun e he => ?_)
  have hiff := gc8_notInternalS_iff_internalCompl G S hcut he
  by_cases h : acwInternal S e
  · rw [if_neg (by simp [h]), if_neg (fun hc => (hiff.2 hc) h)]
  · rw [if_pos h, if_pos (hiff.1 h)]


























theorem gc8_cutWeight_mult (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (hcut : acwClosedCut G S)
    (n : Sharpness.Current V) :
    weight G β J n
      = weight G β J (acwRestrict (acwInternal Sᶜ) n)
        * weight G β J (acwRestrict (acwInternal S) n) := by
  rw [acw_weight_factor_cut G β J S n, mul_comm]
  congr 1
  exact gc8_notInternalS_weight_eq_internalCompl G β J S hcut n







theorem gc8_cutWeight_mult_innerFirst (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (hcut : acwClosedCut G S) (n : Sharpness.Current V) :
    weight G β J n
      = weight G β J (acwRestrict (acwInternal S) n)
        * weight G β J (acwRestrict (acwInternal Sᶜ) n) := by
  rw [gc8_cutWeight_mult G β J S hcut n, mul_comm]



















theorem gc8_cut_support (S : Finset V) (hcut : acwClosedCut G S) (n : Sharpness.Current V) :
    Sharpness.sources G (acwRestrict (acwInternal S) n) = (Sharpness.sources G n) ∩ S :=
  acw_sources_internal_eq G S hcut n




theorem gc8_cut_support_external (S : Finset V) (hcut : acwClosedCut G S) (n : Sharpness.Current V) :
    Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = (Sharpness.sources G n) ∩ Sᶜ :=
  acw_sources_external_eq G S hcut n

















theorem gc8_weight_factor_pred (β : ℝ) (J : Sym2 V → ℝ) (p : Sym2 V → Prop) [DecidablePred p]
    (n : Sharpness.Current V) :
    weight G β J n
      = weight G β J (acwRestrict p n) * weight G β J (acwRestrict (fun e => ¬ p e) n) :=
  acw_weight_factor G β J p n












theorem gc8_cutWeight_mult_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (n : Sharpness.Current V) :
    0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n)
      ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n) :=
  ⟨acw_weight_nonneg G β J hβ hJ _, acw_weight_nonneg G β J hβ hJ _⟩












theorem gc8_closedCut_empty : acwClosedCut G (∅ : Finset V) := by
  intro e he
  right
  intro z hz
  simp





theorem gc8_cutWeight_mult_nonvacuous (n : Sharpness.Current (Fin 3)) :
    weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) n
      = weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
            (acwRestrict (acwInternal (∅ : Finset (Fin 3))ᶜ) n)
        * weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
            (acwRestrict (acwInternal (∅ : Finset (Fin 3))) n) :=
  gc8_cutWeight_mult (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ∅
    (gc8_closedCut_empty (⊤ : SimpleGraph (Fin 3))) n

end StatMech.Walls
