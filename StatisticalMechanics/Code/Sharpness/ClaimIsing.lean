/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Sharpness.CurrentRep
import Code.Sharpness.RandomCurrent

open Finset SimpleGraph
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





def edgeInside (S : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∈ S

instance (S : Finset V) (e : Sym2 V) : Decidable (edgeInside S e) := by
  unfold edgeInside; infer_instance




theorem not_edgeInside_compl_of_edgeInside (S : Finset V) (e : Sym2 V)
    (h : edgeInside S e) : ¬ edgeInside Sᶜ e := by
  intro hc
  obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
  have ha : a ∈ e := hab ▸ Sym2.mem_mk_left a b
  exact (Finset.mem_compl.mp (hc a ha)) (h a ha)





def NoCrossing (n : Current V) (S : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, 1 ≤ n e → edgeInside S e ∨ edgeInside Sᶜ e






noncomputable def restrictTo (n : Current V) (S : Finset V) : Current V :=
  fun e => if edgeInside S e then n e else 0

@[simp]
theorem restrictTo_apply (n : Current V) (S : Finset V) (e : Sym2 V) :
    restrictTo n S e = if edgeInside S e then n e else 0 := rfl



@[simp]
theorem restrictTo_idem (n : Current V) (S : Finset V) :
    restrictTo (restrictTo n S) S = restrictTo n S := by
  funext e; unfold restrictTo; by_cases h : edgeInside S e <;> simp [h]




theorem restrictTo_add_compl (n : Current V) (S : Finset V) (hn : NoCrossing G n S)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    n e = restrictTo n S e + restrictTo n Sᶜ e := by
  unfold restrictTo
  by_cases hS : edgeInside S e
  · rw [if_pos hS, if_neg (not_edgeInside_compl_of_edgeInside S e hS), add_zero]
  · by_cases hSc : edgeInside Sᶜ e
    · rw [if_neg hS, if_pos hSc, zero_add]
    · rw [if_neg hS, if_neg hSc, add_zero]
      by_contra hne
      rcases hn e he (Nat.one_le_iff_ne_zero.mpr hne) with h | h
      · exact hS h
      · exact hSc h



theorem restrictTo_left_inv (n : Current V) (S : Finset V) (hn : NoCrossing G n S) :
    ∀ e ∈ G.edgeFinset, restrictTo n S e + restrictTo n Sᶜ e = n e :=
  fun e he => (restrictTo_add_compl G n S hn e he).symm









theorem weight_restrictTo_mul_compl (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) (S : Finset V)
    (hn : NoCrossing G n S) :
    weight G β J n = weight G β J (restrictTo n S) * weight G β J (restrictTo n Sᶜ) := by
  unfold weight restrictTo
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e he => ?_)
  by_cases hS : edgeInside S e
  · rw [if_pos hS, if_neg (not_edgeInside_compl_of_edgeInside S e hS)]; simp
  · by_cases hSc : edgeInside Sᶜ e
    · rw [if_neg hS, if_pos hSc]; simp
    · rw [if_neg hS, if_neg hSc]
      have hzero : n e = 0 := by
        by_contra hne
        rcases hn e he (Nat.one_le_iff_ne_zero.mpr hne) with h | h
        · exact hS h
        · exact hSc h
      rw [hzero]; simp




theorem incidentFlux_add (n m : Current V) (x : V) :
    incidentFlux G (fun e => n e + m e) x = incidentFlux G n x + incidentFlux G m x := by
  unfold incidentFlux
  rw [← Finset.sum_add_distrib]




theorem sources_add (n m : Current V) :
    sources G (fun e => n e + m e) = sources G n ∆ sources G m := by
  ext x
  simp only [mem_sources, incidentFlux_add, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd]
  push_cast
  generalize (incidentFlux G n x : ZMod 2) = a
  generalize (incidentFlux G m x : ZMod 2) = b
  revert a b; decide



theorem incidentFlux_split (n : Current V) (S : Finset V) (hn : NoCrossing G n S) (x : V) :
    incidentFlux G n x
      = incidentFlux G (restrictTo n S) x + incidentFlux G (restrictTo n Sᶜ) x := by
  unfold incidentFlux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  exact restrictTo_add_compl G n S hn e he.1



theorem incidentFlux_restrictTo_eq_zero_of_notMem (n : Current V) (S : Finset V) {x : V}
    (hx : x ∉ S) : incidentFlux G (restrictTo n S) x = 0 := by
  unfold incidentFlux restrictTo
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  by_cases h : edgeInside S e
  · exact absurd (h x he.2) hx
  · rw [if_neg h]



theorem sources_restrictTo_subset (n : Current V) (S : Finset V) :
    sources G (restrictTo n S) ⊆ S := by
  intro x hx
  rw [mem_sources] at hx
  by_contra hxS
  rw [incidentFlux_restrictTo_eq_zero_of_notMem G n S hxS] at hx
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hx



theorem sources_restrictTo_compl_subset (n : Current V) (S : Finset V) :
    sources G (restrictTo n Sᶜ) ⊆ Sᶜ :=
  sources_restrictTo_subset G n Sᶜ









theorem sources_restrictTo_eq_inter (n : Current V) (S : Finset V) (hn : NoCrossing G n S) :
    sources G (restrictTo n S) = sources G n ∩ S
      ∧ sources G (restrictTo n Sᶜ) = sources G n ∩ Sᶜ := by
  refine ⟨Finset.ext (fun x => ?_), Finset.ext (fun x => ?_)⟩
  · 
    rw [Finset.mem_inter, mem_sources, mem_sources]
    constructor
    · intro hx
      have hxS : x ∈ S := sources_restrictTo_subset G n S (by rw [mem_sources]; exact hx)
      refine ⟨?_, hxS⟩
      rw [incidentFlux_split G n S hn x,
        incidentFlux_restrictTo_eq_zero_of_notMem G n Sᶜ
          (by rw [Finset.mem_compl]; exact not_not.mpr hxS), add_zero]
      exact hx
    · rintro ⟨hxn, hxS⟩
      rw [incidentFlux_split G n S hn x,
        incidentFlux_restrictTo_eq_zero_of_notMem G n Sᶜ
          (by rw [Finset.mem_compl]; exact not_not.mpr hxS), add_zero] at hxn
      exact hxn
  · 
    rw [Finset.mem_inter, mem_sources, mem_sources]
    constructor
    · intro hx
      have hxSc : x ∈ Sᶜ := sources_restrictTo_subset G n Sᶜ (by rw [mem_sources]; exact hx)
      refine ⟨?_, hxSc⟩
      rw [incidentFlux_split G n S hn x,
        incidentFlux_restrictTo_eq_zero_of_notMem G n S
          (by rw [Finset.mem_compl] at hxSc; exact hxSc), zero_add]
      exact hx
    · rintro ⟨hxn, hxSc⟩
      rw [incidentFlux_split G n S hn x,
        incidentFlux_restrictTo_eq_zero_of_notMem G n S
          (by rw [Finset.mem_compl] at hxSc; exact hxSc), zero_add] at hxn
      exact hxn



theorem sources_parts_disjoint (n : Current V) (S : Finset V) :
    Disjoint (sources G (restrictTo n S)) (sources G (restrictTo n Sᶜ)) := by
  refine Finset.disjoint_left.mpr (fun x hxS hxSc => ?_)
  have h1 : x ∈ S := sources_restrictTo_subset G n S hxS
  have h2 : x ∈ Sᶜ := sources_restrictTo_compl_subset G n S hxSc
  exact (Finset.mem_compl.mp h2) h1
















theorem current_split (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) (S : Finset V)
    (hn : NoCrossing G n S) :
    (∀ e ∈ G.edgeFinset, restrictTo n S e + restrictTo n Sᶜ e = n e)
      ∧ weight G β J n = weight G β J (restrictTo n S) * weight G β J (restrictTo n Sᶜ)
      ∧ sources G n = sources G (restrictTo n S) ∪ sources G (restrictTo n Sᶜ)
      ∧ sources G (restrictTo n S) = sources G n ∩ S
      ∧ sources G (restrictTo n Sᶜ) = sources G n ∩ Sᶜ := by
  obtain ⟨hS, hSc⟩ := sources_restrictTo_eq_inter G n S hn
  refine ⟨restrictTo_left_inv G n S hn, weight_restrictTo_mul_compl G β J n S hn, ?_, hS, hSc⟩
  
  rw [hS, hSc, ← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]

end Sharpness

end StatMech
