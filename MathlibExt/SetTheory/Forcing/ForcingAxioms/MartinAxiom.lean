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
public import Mathlib.SetTheory.Cardinal.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 10, Logic 9, Logic 13, Logic 14
-- Proposed path (advisory metadata only, not a review instruction).

open Set

-- Logic 10: Countable chain condition in a partial order
def IsCCC (P : Type*) [PartialOrder P] : Prop :=
    ∀ A : Set P, IsAntichain (fun p q : P => ∃ r, r ≤ p ∧ r ≤ q) A → A.Countable

  def MartinAxiom (κ : Cardinal) : Prop :=
    ∀ (P : Type*) [PartialOrder P], IsCCC P →
      ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
      ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty


theorem martinAxiom_zero : MartinAxiom 0 := by
  intro P _ _ D _ hcard p
  refine ⟨Set.Ici p, ?_, Set.self_mem_Ici, ?_⟩
  · exact Order.IsPFilter.of_def ⟨p, Set.self_mem_Ici⟩
      (fun x hx y hy => ⟨p, Set.self_mem_Ici, hx, hy⟩) fun hxy hx => le_trans hx hxy
  · 
    intro S hS
    have : Nonempty D := ⟨⟨S, hS⟩⟩
    exact absurd (le_antisymm hcard zero_le) (Cardinal.mk_ne_zero _)


theorem MartinAxiom.mono {κ μ : Cardinal} (h : MartinAxiom κ) (hμ : μ ≤ κ) :
    MartinAxiom μ := by
  intro P _ hccc D hD hcard p
  exact h P hccc D hD (hcard.trans hμ) p

-- Logic 13: $\sigma$-centered posets

  def IsSigmaCentered (P : Type*) [PartialOrder P] : Prop :=
    ∃ c : P → ℕ, ∀ (n : ℕ) (s : Finset P), (∀ p ∈ s, c p = n) → ∃ r : P, ∀ p ∈ s, r ≤ p


theorem IsSigmaCentered.nonempty {P : Type*} [PartialOrder P] (h : IsSigmaCentered P) :
    Nonempty P := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨r, -⟩ := hc 0 ∅ (by simp)
  exact ⟨r⟩


theorem IsSigmaCentered.isCCC {P : Type*} [PartialOrder P] (h : IsSigmaCentered P) :
    IsCCC P := by
  classical
  obtain ⟨c, hc⟩ := h
  intro A hA
  rw [Set.countable_iff_exists_injOn]
  refine ⟨c, fun p hp q hq hpq => ?_⟩
  by_contra hne
  obtain ⟨r, hr⟩ := hc (c p) {p, q} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · exact hpq.symm)
  exact hA hp hq hne ⟨r, hr p (by simp), hr q (by simp)⟩


theorem isSigmaCentered_of_countable {P : Type*} [PartialOrder P] [Countable P] [Nonempty P] :
    IsSigmaCentered P := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat P
  refine ⟨f, fun n s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨Classical.arbitrary P, by simp⟩
  · refine ⟨p₀, fun p hp => ?_⟩
    have hfp : f p = f p₀ := by rw [hs p hp, hs p₀ hp₀]
    exact le_of_eq (hf hfp).symm

 def MartinAxiomSigmaCentered (κ : Cardinal) : Prop :=
    ∀ (P : Type*) [PartialOrder P], IsSigmaCentered P →
      ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
      ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty


theorem isPFilter_Ici {P : Type*} [PartialOrder P] (p : P) : Order.IsPFilter (Set.Ici p) :=
  Order.IsPFilter.of_def ⟨p, Set.self_mem_Ici⟩
    (fun _ hx _ hy => ⟨p, Set.self_mem_Ici, hx, hy⟩) fun hxy hx => le_trans hx hxy


theorem martinAxiomSigmaCentered_one : MartinAxiomSigmaCentered 1 := by
  intro P _ _ D hD hcard p
  rcases Set.eq_empty_or_nonempty D with rfl | ⟨S, hS⟩
  · exact ⟨Set.Ici p, isPFilter_Ici p, Set.self_mem_Ici, by simp⟩
  · obtain ⟨q, hqS, hqp⟩ := hD S hS p
    refine ⟨Set.Ici q, isPFilter_Ici q, Set.mem_Ici.2 hqp, fun T hT => ?_⟩
    have hTS : T = S := Cardinal.mk_le_one_iff_set_subsingleton.1 hcard hT hS
    exact ⟨q, Set.self_mem_Ici, by rw [hTS]; exact hqS⟩


theorem MartinAxiomSigmaCentered.mono {κ μ : Cardinal} (h : MartinAxiomSigmaCentered κ)
    (hμ : μ ≤ κ) : MartinAxiomSigmaCentered μ := by
  intro P _ hσ D hD hcard p
  exact h P hσ D hD (hcard.trans hμ) p


theorem martinAxiomSigmaCentered_zero : MartinAxiomSigmaCentered 0 :=
  martinAxiomSigmaCentered_one.mono zero_le


theorem MartinAxiom.sigmaCentered {κ : Cardinal} (h : MartinAxiom κ) :
    MartinAxiomSigmaCentered κ := by
  intro P _ hσ D hD hcard p
  exact h P hσ.isCCC D hD hcard p

end
