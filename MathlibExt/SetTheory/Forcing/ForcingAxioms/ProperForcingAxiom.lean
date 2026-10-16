/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 49
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal

-- Logic 49: Proper Forcing Axiom
def ProperForcingAxiom : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsProperForcing P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ aleph 1 →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

theorem isPFilter_principal {P : Type*} [PartialOrder P] (p : P) :
    Order.IsPFilter {x : P | p ≤ x} :=
  Order.IsPFilter.of_def ⟨p, le_refl p⟩ (fun _ hx _ hy => ⟨p, le_refl p, hx, hy⟩)
    (fun hxy hx => le_trans hx hxy)

theorem exists_pFilter_of_empty {P : Type*} [PartialOrder P] (p : P) :
    ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ (∅ : Set (Set P)), (G ∩ S).Nonempty :=
  ⟨{x : P | p ≤ x}, isPFilter_principal p, le_refl p, fun S hS => absurd hS (Set.notMem_empty S)⟩

theorem not_pfa_conclusion_without_isCoinitial {P : Type*} [PartialOrder P] [Nonempty P] :
    ¬ ∀ D : Set (Set P), Cardinal.mk D ≤ aleph 1 →
        ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty := by
  intro h
  obtain ⟨G, -, -, hG⟩ :=
    h {∅} (by rw [Cardinal.mk_singleton]; exact one_le_aleph0.trans (aleph0_le_aleph 1))
      (Classical.arbitrary P)
  obtain ⟨x, -, hx⟩ := hG ∅ rfl
  exact hx

end
