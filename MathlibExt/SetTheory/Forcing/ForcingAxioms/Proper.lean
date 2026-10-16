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

public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 43, Logic 44, Logic 45, Logic 46, Logic 47, Logic 48
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 43: Conditions belonging to a model
def modelConds {P : Type*} (M : Set (P ⊕ Set P)) : Set P := Sum.inl ⁻¹' M


theorem modelConds_insert_inr {P : Type*} (M : Set (P ⊕ Set P)) (D : Set P) :
    modelConds (insert (Sum.inr D) M) = modelConds M := by
  ext p
  simp [modelConds]


theorem countable_modelConds {P : Type*} {M : Set (P ⊕ Set P)} (hM : M.Countable) :
    (modelConds M).Countable :=
  hM.preimage Sum.inl_injective

-- Logic 44: Subsets belonding to a model

def modelSets {P : Type*} (M : Set (P ⊕ Set P)) : Set (Set P) := Sum.inr ⁻¹' M


theorem modelSets_insert_inl {P : Type*} (M : Set (P ⊕ Set P)) (p : P) :
    modelSets (insert (Sum.inl p) M) = modelSets M := by
  ext D
  simp [modelSets]


theorem countable_modelSets {P : Type*} {M : Set (P ⊕ Set P)} (hM : M.Countable) :
    (modelSets M).Countable :=
  hM.preimage Sum.inr_injective

-- Logic 45: Compatibility

def IsCompatible {P : Type*} [PartialOrder P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q


theorem IsCompatible.symm {P : Type*} [PartialOrder P] {p q : P} (h : IsCompatible p q) :
    IsCompatible q p :=
  let ⟨r, hp, hq⟩ := h; ⟨r, hq, hp⟩


theorem isCompatible_of_linearOrder {P : Type*} [LinearOrder P] (p q : P) : IsCompatible p q :=
  ⟨min p q, min_le_left p q, min_le_right p q⟩

-- Logic 46: Predense below

def IsPredenseBelow {P : Type*} [PartialOrder P] (A : Set P) (q : P) : Prop :=
  ∀ r ≤ q, ∃ a ∈ A, IsCompatible r a


theorem not_isPredenseBelow_empty {P : Type*} [PartialOrder P] (q : P) :
    ¬ IsPredenseBelow (∅ : Set P) q := by
  intro h
  obtain ⟨a, ha, -⟩ := h q le_rfl
  exact ha


theorem IsPredenseBelow.of_le {P : Type*} [PartialOrder P] {A : Set P} {q q' : P}
    (h : IsPredenseBelow A q) (hq : q' ≤ q) : IsPredenseBelow A q' :=
  fun r hr => h r (hr.trans hq)

-- Logic 47: $(M,P)$-generic condition

def IsGenericFor {P : Type*} [PartialOrder P] (M : Set (P ⊕ Set P)) (q : P) : Prop :=
  ∀ D ∈ modelSets M, IsCoinitial D → IsPredenseBelow (D ∩ modelConds M) q


theorem isGenericFor_of_modelSets_eq_empty {P : Type*} [PartialOrder P]
    {M : Set (P ⊕ Set P)} (hM : modelSets M = ∅) (q : P) : IsGenericFor M q := by
  intro D hD
  rw [hM] at hD
  exact absurd hD (Set.notMem_empty D)


theorem IsGenericFor.nonempty_inter {P : Type*} [PartialOrder P] {M : Set (P ⊕ Set P)} {q : P}
    (h : IsGenericFor M q) {D : Set P} (hD : D ∈ modelSets M) (hcoi : IsCoinitial D) :
    (D ∩ modelConds M).Nonempty := by
  obtain ⟨a, ha, -⟩ := h D hD hcoi q le_rfl
  exact ⟨a, ha⟩

-- Logic 48: Proper Forcings

def IsProperForcing (P : Type*) [PartialOrder P] : Prop :=
  ∃ C : Set (Set (P ⊕ Set P)), IsClubOmega C ∧
    ∀ M ∈ C, ∀ p ∈ modelConds M, ∃ q ≤ p, IsGenericFor M q


theorem exists_model_containing {P : Type*} (C : Set (Set (P ⊕ Set P))) (hC : IsClubOmega C)
    (p : P) (D : Set P) : ∃ M ∈ C, Sum.inl p ∈ M ∧ Sum.inr D ∈ M := by
  obtain ⟨y, hy, hsub⟩ :=
    hC.cofinal {Sum.inl p, Sum.inr D} ((Set.finite_singleton _).insert _).countable
  exact ⟨y, hy, hsub (by simp), hsub (by simp)⟩


theorem isClubOmega_mem {α : Type*} (a : α) : IsClubOmega {x : Set α | x.Countable ∧ a ∈ x} where
  mem_countable _ hx := hx.1
  cofinal x hx := ⟨insert a x, ⟨hx.insert a, Set.mem_insert a x⟩, Set.subset_insert a x⟩
  closed _f hf _ := ⟨Set.countable_iUnion fun n => (hf n).1, Set.mem_iUnion.2 ⟨0, (hf 0).2⟩⟩

end
