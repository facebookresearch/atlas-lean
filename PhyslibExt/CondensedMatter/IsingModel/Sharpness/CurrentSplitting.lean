/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent
public import Mathlib.Data.ZMod.Basic

/-!
# Splitting currents along a set

Currents with no edge crossing the boundary of a set `S` split into a part inside `S` and a part
inside `Sᶜ`, with multiplicative weights and disjoint source sets.

## i. Overview

An edge is inside `S` if both endpoints lie in `S`. A current `n` has no crossing for `S` if every
edge it uses lies inside `S` or inside `Sᶜ`. Then `n = n|_S + n|_{Sᶜ}`, the weight factorizes as
`w(n) = w(n|_S) w(n|_{Sᶜ})`, and the sources of the two parts are `∂n ∩ S` and `∂n ∩ Sᶜ`.

## ii. Key results

- `NoCrossing` : currents using no edge between `S` and `Sᶜ`
- `restrictTo` : restriction of a current to the edges inside `S`
- `sources_restrictTo_eq_inter` : sources of the restricted parts
- `current_split` : the additive and multiplicative splitting

## iii. Table of contents

- A. Edges inside a set and restriction
- B. Weights and incidence fluxes
- C. Sources of the parts

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48

-/

@[expose] public section

open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Edges inside a set and restriction -/

/-- An unordered pair `e` is inside `S` if both of its endpoints lie in `S`. -/
def edgeInside (S : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∈ S

/-- Decidability of `edgeInside`. -/
instance (S : Finset V) (e : Sym2 V) : Decidable (edgeInside S e) := by
  unfold edgeInside; infer_instance

lemma not_edgeInside_compl_of_edgeInside (S : Finset V) (e : Sym2 V)
    (h : edgeInside S e) : ¬ edgeInside Sᶜ e := by
  intro hc
  obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
  have ha : a ∈ e := hab ▸ Sym2.mem_mk_left a b
  exact (Finset.mem_compl.mp (hc a ha)) (h a ha)

/-- The current `n` uses no edge joining `S` to `Sᶜ`: every edge with `n e ≥ 1` is inside `S` or
inside `Sᶜ`. -/
def NoCrossing (n : Current V) (S : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, 1 ≤ n e → edgeInside S e ∨ edgeInside Sᶜ e

/-- The restriction `n|_S` of a current to the edges inside `S`, zero elsewhere. -/
noncomputable def restrictTo (n : Current V) (S : Finset V) : Current V :=
  fun e => if edgeInside S e then n e else 0

@[simp]
lemma restrictTo_apply (n : Current V) (S : Finset V) (e : Sym2 V) :
    restrictTo n S e = if edgeInside S e then n e else 0 := rfl

@[simp]
lemma restrictTo_idem (n : Current V) (S : Finset V) :
    restrictTo (restrictTo n S) S = restrictTo n S := by
  funext e; unfold restrictTo; by_cases h : edgeInside S e <;> simp [h]

lemma restrictTo_add_compl (n : Current V) (S : Finset V) (hn : NoCrossing G n S)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    n e = restrictTo n S e + restrictTo n Sᶜ e := by
  unfold restrictTo
  by_cases hS : edgeInside S e
  · rw [ite_eq_left hS, ite_eq_right (not_edgeInside_compl_of_edgeInside S e hS), add_zero]
  · by_cases hSc : edgeInside Sᶜ e
    · rw [ite_eq_right hS, ite_eq_left hSc, zero_add]
    · rw [ite_eq_right hS, ite_eq_right hSc, add_zero]
      by_contra hne
      rcases hn e he (Nat.one_le_iff_ne_zero.mpr hne) with h | h
      · exact hS h
      · exact hSc h

lemma restrictTo_left_inv (n : Current V) (S : Finset V) (hn : NoCrossing G n S) :
    ∀ e ∈ G.edgeFinset, restrictTo n S e + restrictTo n Sᶜ e = n e :=
  fun e he => (restrictTo_add_compl G n S hn e he).symm

/-! ## B. Weights and incidence fluxes -/

lemma weight_restrictTo_mul_compl (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) (S : Finset V)
    (hn : NoCrossing G n S) :
    weight G β J n = weight G β J (restrictTo n S) * weight G β J (restrictTo n Sᶜ) := by
  unfold weight restrictTo
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e he => ?_)
  by_cases hS : edgeInside S e
  · rw [ite_eq_left hS, ite_eq_right (not_edgeInside_compl_of_edgeInside S e hS)]; simp
  · by_cases hSc : edgeInside Sᶜ e
    · rw [ite_eq_right hS, ite_eq_left hSc]; simp
    · rw [ite_eq_right hS, ite_eq_right hSc]
      have hzero : n e = 0 := by
        by_contra hne
        rcases hn e he (Nat.one_le_iff_ne_zero.mpr hne) with h | h
        · exact hS h
        · exact hSc h
      rw [hzero]; simp

lemma incidentFlux_add (n m : Current V) (x : V) :
    incidentFlux G (fun e => n e + m e) x = incidentFlux G n x + incidentFlux G m x := by
  unfold incidentFlux
  rw [← Finset.sum_add_distrib]

lemma sources_add (n m : Current V) :
    sources G (fun e => n e + m e) = sources G n ∆ sources G m := by
  ext x
  simp only [mem_sources, incidentFlux_add, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd]
  push_cast
  generalize (incidentFlux G n x : ZMod 2) = a
  generalize (incidentFlux G m x : ZMod 2) = b
  revert a b; decide

lemma incidentFlux_split (n : Current V) (S : Finset V) (hn : NoCrossing G n S) (x : V) :
    incidentFlux G n x
      = incidentFlux G (restrictTo n S) x + incidentFlux G (restrictTo n Sᶜ) x := by
  unfold incidentFlux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  exact restrictTo_add_compl G n S hn e he.1

lemma incidentFlux_restrictTo_eq_zero_of_notMem (n : Current V) (S : Finset V) {x : V}
    (hx : x ∉ S) : incidentFlux G (restrictTo n S) x = 0 := by
  unfold incidentFlux restrictTo
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  by_cases h : edgeInside S e
  · exact absurd (h x he.2) hx
  · rw [ite_eq_right h]

/-! ## C. Sources of the parts -/

lemma sources_restrictTo_subset (n : Current V) (S : Finset V) :
    sources G (restrictTo n S) ⊆ S := by
  intro x hx
  rw [mem_sources] at hx
  by_contra hxS
  rw [incidentFlux_restrictTo_eq_zero_of_notMem G n S hxS] at hx
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hx

lemma sources_restrictTo_compl_subset (n : Current V) (S : Finset V) :
    sources G (restrictTo n Sᶜ) ⊆ Sᶜ :=
  sources_restrictTo_subset G n Sᶜ

lemma sources_restrictTo_eq_inter (n : Current V) (S : Finset V) (hn : NoCrossing G n S) :
    sources G (restrictTo n S) = sources G n ∩ S
      ∧ sources G (restrictTo n Sᶜ) = sources G n ∩ Sᶜ := by
  refine ⟨Finset.ext (fun x => ?_), Finset.ext (fun x => ?_)⟩
  · rw [Finset.mem_inter, mem_sources, mem_sources]
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
  · rw [Finset.mem_inter, mem_sources, mem_sources]
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

lemma sources_parts_disjoint (n : Current V) (S : Finset V) :
    Disjoint (sources G (restrictTo n S)) (sources G (restrictTo n Sᶜ)) := by
  refine Finset.disjoint_left.mpr (fun x hxS hxSc => ?_)
  have h1 : x ∈ S := sources_restrictTo_subset G n S hxS
  have h2 : x ∈ Sᶜ := sources_restrictTo_compl_subset G n S hxSc
  exact (Finset.mem_compl.mp h2) h1

lemma current_split (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) (S : Finset V)
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
