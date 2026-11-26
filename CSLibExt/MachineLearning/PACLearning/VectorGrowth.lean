/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.GrowthFunction
public import CSLibExt.MachineLearning.PACLearning.Natarajan
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Vector-valued growth functions

The growth function of a class of functions into a finite label type `β`:
the supremum, over `m`-element samples, of the number of distinct labelings
the class realizes on the sample. At `β = Bool` this is the growth function
of `CSLibExt.MachineLearning.PACLearning.GrowthFunction`.

The product and composition bounds are Exercises 20.3 and 20.4 of
Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory
to Algorithms*, Chapter 20; they are the counting steps of Theorem 20.6.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

variable {α β β₁ β₂ γ : Type*} [Fintype β]

open scoped Classical in
/-- The distinct labelings `s → β` realized by `C` on the finite sample `s`. -/
noncomputable def traceSetVec (C : ConceptClass α β) (s : Finset α) :
    Finset (s → β) :=
  Finset.univ.filter fun t => ∃ c ∈ C, ∀ x : s, t x = c x

/-- The vector-valued growth function: supremum of trace counts over
`m`-subsets of the domain. `0` when no `m`-subset exists. Per-sample
counts use `tracesCard`. -/
noncomputable def growthFunctionVec (C : ConceptClass α β) (m : ℕ) : ℕ :=
  sSup { tracesCard C s | (s : Finset α) (_ : s.card = m) }

/-- A labeling is a trace iff some concept in `C` realizes it. -/
@[simp] theorem mem_traceSetVec {C : ConceptClass α β} {s : Finset α}
    {t : s → β} :
    t ∈ traceSetVec C s ↔ ∃ c ∈ C, ∀ x : s, t x = c x := by
  classical
  simp [traceSetVec]

/-- Trace counts agree with `tracesCard`. -/
theorem traceSetVec_card_eq_tracesCard (C : ConceptClass α β) (s : Finset α) :
    (traceSetVec C s).card = tracesCard C s := by
  classical
  unfold traceSetVec tracesCard
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x => (h x).symm⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x => (h x).symm⟩

/-- Trace counts are bounded by the number of all labelings. -/
theorem traceSetVec_card_le (C : ConceptClass α β) (s : Finset α) :
    (traceSetVec C s).card ≤ (Fintype.card β) ^ s.card := by
  classical
  calc (traceSetVec C s).card ≤ Fintype.card (s → β) := Finset.card_le_univ _
    _ = (Fintype.card β) ^ s.card := by
        rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ,
          Fintype.card_coe]

/-- The trace count on any sample is bounded by the growth function. -/
theorem traceSetVec_card_le_growthFunctionVec (C : ConceptClass α β)
    (s : Finset α) :
    (traceSetVec C s).card ≤ growthFunctionVec C s.card := by
  rw [traceSetVec_card_eq_tracesCard]
  unfold growthFunctionVec
  refine le_csSup ?_ ⟨s, rfl, rfl⟩
  refine ⟨(Fintype.card β) ^ s.card, ?_⟩
  rintro k ⟨t, ht, rfl⟩
  rw [← ht, ← traceSetVec_card_eq_tracesCard]
  exact traceSetVec_card_le C t

/-- The growth function is bounded by `(card β) ^ m`. -/
theorem growthFunctionVec_le_pow (C : ConceptClass α β) (m : ℕ) :
    growthFunctionVec C m ≤ (Fintype.card β) ^ m := by
  unfold growthFunctionVec
  apply csSup_le'
  rintro k ⟨t, ht, rfl⟩
  rw [← ht, ← traceSetVec_card_eq_tracesCard]
  exact traceSetVec_card_le C t

/-- When an `m`-subset exists, the supremum is attained on one. -/
theorem exists_traceSetVec_card_eq_growthFunctionVec (C : ConceptClass α β)
    (m : ℕ) (hex : ∃ s0 : Finset α, s0.card = m) :
    ∃ s, s.card = m ∧ (traceSetVec C s).card = growthFunctionVec C m := by
  obtain ⟨s0, hs0⟩ := hex
  have hne : { tracesCard C t | (t : Finset α) (_ : t.card = m) }.Nonempty :=
    ⟨tracesCard C s0, s0, hs0, rfl⟩
  have hbdd : BddAbove { tracesCard C t | (t : Finset α) (_ : t.card = m) } := by
    refine ⟨(Fintype.card β) ^ m, ?_⟩
    rintro k ⟨t, ht, rfl⟩
    rw [← ht, ← traceSetVec_card_eq_tracesCard]
    exact traceSetVec_card_le C t
  have hmem := Nat.sSup_mem hne hbdd
  obtain ⟨s, hs, hcard⟩ := hmem
  refine ⟨s, hs, ?_⟩
  rw [traceSetVec_card_eq_tracesCard]
  exact hcard

/-- Larger samples realize at least as many traces. -/
theorem traceSetVec_card_mono {C : ConceptClass α β} {s t : Finset α}
    (hst : s ⊆ t) : (traceSetVec C s).card ≤ (traceSetVec C t).card := by
  classical
  have hmem : ∀ g : t → β, g ∈ traceSetVec C t →
      (fun x : s => g ⟨x.val, hst x.2⟩) ∈ traceSetVec C s := by
    intro g hg
    rw [mem_traceSetVec] at hg ⊢
    obtain ⟨c, hc, hgc⟩ := hg
    exact ⟨c, hc, fun x => hgc ⟨x.val, hst x.2⟩⟩
  have hsurj : Function.Surjective
      (fun g : ↥(traceSetVec C t) =>
        (⟨fun x : s => g.val ⟨x.val, hst x.2⟩, hmem g.val g.property⟩ :
          ↥(traceSetVec C s))) := by
    rintro ⟨u, hu⟩
    rw [mem_traceSetVec] at hu
    obtain ⟨c, hc, hcu⟩ := hu
    refine ⟨⟨fun y : t => c y.val,
      mem_traceSetVec.mpr ⟨c, hc, fun _ => rfl⟩⟩, ?_⟩
    refine Subtype.ext ?_
    change (fun x : s => c x.val) = u
    funext x
    exact (hcu x).symm
  have hcard := Fintype.card_le_of_surjective _ hsurj
  rwa [Fintype.card_coe, Fintype.card_coe] at hcard

/-- A `k`-set extends to an `m`-set when an `m`-set exists. -/
private theorem exists_superset_card_eq {α : Type*} (t s0 : Finset α)
    {k m : ℕ} (ht : t.card = k) (hs0 : s0.card = m) (hkm : k ≤ m) :
    ∃ s, t ⊆ s ∧ s.card = m := by
  classical
  have hdisj : Disjoint (s0 \ t) (s0 ∩ t) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter] at hx2
    exact hx1.2 hx2.2
  have hunion : s0 \ t ∪ s0 ∩ t = s0 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hpart : (s0 \ t).card + (s0 ∩ t).card = m := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, hs0] at h
    exact h.symm
  have hinter : (s0 ∩ t).card ≤ k := by
    rw [← ht]
    exact Finset.card_le_card (fun x hx => (Finset.mem_inter.mp hx).2)
  have hge : m - k ≤ (s0 \ t).card := by omega
  obtain ⟨v, hvu, hvcard⟩ := Finset.exists_subset_card_eq hge
  have hd : Disjoint t v := by
    rw [Finset.disjoint_left]
    rintro x hxt hxv
    have hx := hvu hxv
    rw [Finset.mem_sdiff] at hx
    exact hx.2 hxt
  refine ⟨t ∪ v, fun x hx => Finset.mem_union.mpr (Or.inl hx), ?_⟩
  have hcard := Finset.card_union_of_disjoint hd
  rw [ht, hvcard] at hcard
  rw [hcard]
  exact Nat.add_sub_cancel' hkm

/-- The growth function is monotone in `m` wherever `m`-samples exist. -/
theorem growthFunctionVec_mono {C : ConceptClass α β} {k m : ℕ}
    (hkm : k ≤ m) (hex : ∃ s0 : Finset α, s0.card = m) :
    growthFunctionVec C k ≤ growthFunctionVec C m := by
  obtain ⟨s0, hs0⟩ := hex
  unfold growthFunctionVec
  apply csSup_le'
  rintro j ⟨t, ht, rfl⟩
  obtain ⟨s, hts, hs⟩ := exists_superset_card_eq t s0 ht hs0 hkm
  have hmono : (traceSetVec C t).card ≤ (traceSetVec C s).card :=
    traceSetVec_card_mono hts
  rw [traceSetVec_card_eq_tracesCard, traceSetVec_card_eq_tracesCard] at hmono
  refine hmono.trans ?_
  refine le_csSup ?_ ⟨s, hs, rfl⟩
  refine ⟨(Fintype.card β) ^ m, ?_⟩
  rintro k' ⟨u, hu, rfl⟩
  rw [← hu, ← traceSetVec_card_eq_tracesCard]
  exact traceSetVec_card_le C u

/-- At `β = Bool` this is the merged `growthFunction`. -/
theorem growthFunctionVec_bool_eq (C : ConceptClass α Bool) (m : ℕ) :
    growthFunctionVec C m = growthFunction C m := by
  classical
  have key : ∀ s : Finset α,
      (traceSetVec C s).card = (traceFamily C s).card := by
    intro s
    have hfwd : ∀ t : s → Bool, t ∈ traceSetVec C s →
        Finset.univ.filter (fun x : s => t x = true) ∈ traceFamily C s := by
      intro t ht
      rw [mem_traceSetVec] at ht
      obtain ⟨c, hc, hcu⟩ := ht
      rw [mem_traceFamily]
      exact ⟨c, hc, fun x => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcu x]⟩
    have hbwd : ∀ u : Finset s, u ∈ traceFamily C s →
        (fun x : s => decide (x ∈ u)) ∈ traceSetVec C s := by
      intro u hu
      rw [mem_traceFamily] at hu
      obtain ⟨c, hc, hcu⟩ := hu
      rw [mem_traceSetVec]
      exact ⟨c, hc, fun x => by
        by_cases hx : x ∈ u
        · have hcx : c x.val = true := (hcu x).mp hx
          simp [hx, hcx]
        · cases hcx : c x.val
          · simp [hx]
          · exact absurd hcx (fun h => hx ((hcu x).mpr h))⟩
    have hcard : Fintype.card ↥(traceSetVec C s) =
        Fintype.card ↥(traceFamily C s) := by
      refine Fintype.card_congr
        { toFun := fun a =>
            ⟨Finset.univ.filter (fun x : s => a.val x = true),
              hfwd a.val a.property⟩
          invFun := fun b =>
            ⟨fun x : s => decide (x ∈ b.val), hbwd b.val b.property⟩
          left_inv := by
            rintro ⟨t, ht⟩
            refine Subtype.ext ?_
            change (fun x : s => decide
              (x ∈ Finset.univ.filter (fun x : s => t x = true))) = t
            funext x
            by_cases h : t x = true
            · simp [h]
            · cases hx : t x
              · simp [hx]
              · exact absurd hx h
          right_inv := by
            rintro ⟨u, hu⟩
            refine Subtype.ext ?_
            change Finset.univ.filter
              (fun x : s => decide (x ∈ u) = true) = u
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              decide_eq_true_eq] }
    rwa [Fintype.card_coe, Fintype.card_coe] at hcard
  have key' : ∀ s : Finset α, tracesCard C s = (traceFamily C s).card := by
    intro s
    rw [← traceSetVec_card_eq_tracesCard]
    exact key s
  have hset :
      { tracesCard C s | (s : Finset α) (_ : s.card = m) } =
        { (traceFamily C s).card | (s : Finset α) (_ : s.card = m) } := by
    ext k
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, (key' s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, key' s⟩
  unfold growthFunctionVec growthFunction
  rw [hset]

/-- The Cartesian product class (SSBD Exercise 20.3). -/
def prodClass (C₁ : ConceptClass α β₁) (C₂ : ConceptClass α β₂) :
    ConceptClass α (β₁ × β₂) :=
  {c | ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, ∀ x, c x = (c₁ x, c₂ x)}

/-- The composition class (SSBD Exercise 20.4). -/
def compClass (C₁ : ConceptClass α γ) (C₂ : ConceptClass γ β) :
    ConceptClass α β :=
  {c | ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, ∀ x, c x = c₂ (c₁ x)}

/-- Growth function of a product (SSBD Exercise 20.3). -/
theorem growthFunctionVec_prod_le [Fintype β₁] [Fintype β₂]
    (C₁ : ConceptClass α β₁) (C₂ : ConceptClass α β₂) (m : ℕ) :
    growthFunctionVec (prodClass C₁ C₂) m ≤
      growthFunctionVec C₁ m * growthFunctionVec C₂ m := by
  classical
  have hcard : ∀ s : Finset α, (traceSetVec (prodClass C₁ C₂) s).card ≤
      (traceSetVec C₁ s).card * (traceSetVec C₂ s).card := by
    intro s
    have hmem₁ : ∀ t : s → β₁ × β₂, t ∈ traceSetVec (prodClass C₁ C₂) s →
        (fun x : s => (t x).1) ∈ traceSetVec C₁ s := by
      intro t ht
      rw [mem_traceSetVec] at ht ⊢
      obtain ⟨c, hc, hcu⟩ := ht
      obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := hc
      exact ⟨c₁, hc₁, fun x => by rw [hcu x, hcc x.val]⟩
    have hmem₂ : ∀ t : s → β₁ × β₂, t ∈ traceSetVec (prodClass C₁ C₂) s →
        (fun x : s => (t x).2) ∈ traceSetVec C₂ s := by
      intro t ht
      rw [mem_traceSetVec] at ht ⊢
      obtain ⟨c, hc, hcu⟩ := ht
      obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := hc
      exact ⟨c₂, hc₂, fun x => by rw [hcu x, hcc x.val]⟩
    have hinj : Function.Injective (fun t : ↥(traceSetVec (prodClass C₁ C₂) s) =>
        ((⟨fun x : s => (t.val x).1, hmem₁ t.val t.property⟩ :
          ↥(traceSetVec C₁ s)),
        (⟨fun x : s => (t.val x).2, hmem₂ t.val t.property⟩ :
          ↥(traceSetVec C₂ s)))) := by
      rintro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      refine Subtype.ext ?_
      funext x
      exact Prod.ext (congrFun h1 x) (congrFun h2 x)
    have hle := Fintype.card_le_of_injective _ hinj
    rwa [Fintype.card_coe, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_coe] at hle
  unfold growthFunctionVec
  apply csSup_le'
  rintro k ⟨t, ht, rfl⟩
  have hcard' := hcard t
  rw [traceSetVec_card_eq_tracesCard, traceSetVec_card_eq_tracesCard,
    traceSetVec_card_eq_tracesCard] at hcard'
  refine hcard'.trans ?_
  have h1 := traceSetVec_card_le_growthFunctionVec C₁ t
  have h2 := traceSetVec_card_le_growthFunctionVec C₂ t
  rw [ht] at h1 h2
  rw [traceSetVec_card_eq_tracesCard] at h1
  rw [traceSetVec_card_eq_tracesCard] at h2
  exact Nat.mul_le_mul h1 h2

/-- Growth function of a composition (SSBD Exercise 20.4). The
intermediate type needs an `m`-sample: without one its growth value
is the supremum of the empty set of naturals, and the bound fails. -/
theorem growthFunctionVec_comp_le [Fintype γ]
    (C₁ : ConceptClass α γ) (C₂ : ConceptClass γ β) (m : ℕ)
    (hex : ∃ s0 : Finset γ, s0.card = m) :
    growthFunctionVec (compClass C₁ C₂) m ≤
      growthFunctionVec C₂ m * growthFunctionVec C₁ m := by
  classical
  have hcard : ∀ s : Finset α, s.card = m →
      (traceSetVec (compClass C₁ C₂) s).card ≤
        growthFunctionVec C₂ m * growthFunctionVec C₁ m := by
    intro s hs
    have hwit : ∀ t : ↥(traceSetVec (compClass C₁ C₂) s),
        ∃ c₁ : α → γ, c₁ ∈ C₁ ∧ ∃ c₂ : γ → β,
          c₂ ∈ C₂ ∧ ∀ x : s, t.val x = c₂ (c₁ x.val) := by
      intro t
      obtain ⟨c, hc, hcu⟩ := mem_traceSetVec.mp t.property
      obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := hc
      exact ⟨c₁, hc₁, c₂, hc₂, fun x => by rw [hcu x, hcc x.val]⟩
    choose c₁ hc₁ using hwit
    have hwit₂ : ∀ t : ↥(traceSetVec (compClass C₁ C₂) s),
        ∃ c₂ : γ → β, c₂ ∈ C₂ ∧ ∀ x : s, t.val x = c₂ (c₁ t x.val) :=
      fun t => (hc₁ t).2
    choose c₂ hc₂ using hwit₂
    have hc₁mem : ∀ t, c₁ t ∈ C₁ := fun t => (hc₁ t).1
    have hc₂mem : ∀ t, c₂ t ∈ C₂ := fun t => (hc₂ t).1
    have hcu : ∀ t, ∀ x : s, t.val x = c₂ t (c₁ t x.val) :=
      fun t => (hc₂ t).2
    have hmemU : ∀ t : ↥(traceSetVec (compClass C₁ C₂) s),
        (fun x : s => c₁ t x.val) ∈ traceSetVec C₁ s :=
      fun t => mem_traceSetVec.mpr ⟨c₁ t, hc₁mem t, fun _ => rfl⟩
    have hmemV : ∀ t : ↥(traceSetVec (compClass C₁ C₂) s),
        (fun y : ↥(Finset.univ.image (fun x : s => c₁ t x.val)) =>
          c₂ t y.val) ∈
          traceSetVec C₂ (Finset.univ.image (fun x : s => c₁ t x.val)) :=
      fun t => mem_traceSetVec.mpr ⟨c₂ t, hc₂mem t, fun _ => rfl⟩
    have hdec : ∀ t : ↥(traceSetVec (compClass C₁ C₂) s),
        ∀ w : Σ u : ↥(traceSetVec C₁ s),
          ↥(traceSetVec C₂ (Finset.univ.image fun x : s => u.val x)),
        w = (⟨⟨fun x : s => c₁ t x.val, hmemU t⟩,
          ⟨fun y : ↥(Finset.univ.image (fun x : s => c₁ t x.val)) =>
            c₂ t y.val, hmemV t⟩⟩ :
          Σ u : ↥(traceSetVec C₁ s),
            ↥(traceSetVec C₂ (Finset.univ.image fun x : s => u.val x))) →
        (fun x : s => w.2.val ⟨w.1.val x,
          Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩) = t.val := by
      intro t w hw
      subst hw
      funext x
      exact (hcu t x).symm
    have hinj : Function.Injective
        (fun t : ↥(traceSetVec (compClass C₁ C₂) s) =>
          (⟨⟨fun x : s => c₁ t x.val, hmemU t⟩,
            ⟨fun y : ↥(Finset.univ.image (fun x : s => c₁ t x.val)) =>
              c₂ t y.val, hmemV t⟩⟩ :
            Σ u : ↥(traceSetVec C₁ s),
              ↥(traceSetVec C₂
                (Finset.univ.image fun x : s => u.val x)))) := by
      rintro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h
      have e1 := hdec ⟨t₁, ht₁⟩ _ rfl
      have e2 := hdec ⟨t₂, ht₂⟩ _ h
      exact Subtype.ext (e1.symm.trans e2)
    have hkm : ∀ u : ↥(traceSetVec C₁ s),
        Fintype.card ↥(traceSetVec C₂
          (Finset.univ.image fun x : s => u.val x)) ≤
          growthFunctionVec C₂ m := by
      intro u
      rw [Fintype.card_coe]
      refine (traceSetVec_card_le_growthFunctionVec C₂ _).trans ?_
      refine growthFunctionVec_mono ?_ hex
      calc (Finset.univ.image (fun x : s => u.val x)).card
          ≤ Finset.univ.card := Finset.card_image_le
        _ = s.card := by rw [Finset.card_univ, Fintype.card_coe]
        _ = m := hs
    have hinj₂ : Function.Injective
        (fun w : Σ u : ↥(traceSetVec C₁ s),
          ↥(traceSetVec C₂ (Finset.univ.image fun x : s => u.val x)) =>
          (Fin.castLE (hkm w.1) ((Fintype.equivFin _) w.2), w.1)) := by
      rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨houter, h1⟩ := h
      subst h1
      have h3 := Fin.castLE_injective (hkm u₁) houter
      have hv := (Fintype.equivFin _).injective h3
      subst hv
      rfl
    have hle := Fintype.card_le_of_injective _ (hinj₂.comp hinj)
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] at hle
    have h1 := traceSetVec_card_le_growthFunctionVec C₁ s
    rw [hs] at h1
    exact hle.trans (Nat.mul_le_mul le_rfl h1)
  unfold growthFunctionVec
  apply csSup_le'
  rintro k ⟨t, ht, rfl⟩
  rw [← traceSetVec_card_eq_tracesCard]
  exact hcard t ht

end Cslib.MachineLearning.PACLearning
