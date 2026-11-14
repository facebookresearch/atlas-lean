/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

variable {S : Type*} [Fintype S] [DecidableEq S]

@[expose] public section

open Finset
/-- One naive partition-refinement step for strong
bisimilarity on a finite labeled transition system with
transition relation `step : S → S → Prop` (labels suppressed;
the labeled version is the same construction per label):
two states stay together iff they agree on which blocks of
the current partition they can reach. -/
def refineStep (step : S → S → Prop)
    (R : S → S → Prop) : S → S → Prop :=
  fun a b => R a b ∧
    (∀ a', step a a' → ∃ b', step b b' ∧ R a' b') ∧
    (∀ b', step b b' → ∃ a', step a a' ∧ R a' b')

/-- The `k`-th naive refinement iterate, starting from the
total relation. -/
def refineIter (step : S → S → Prop) :
    ℕ → S → S → Prop
  | 0 => fun _ _ => True
  | k + 1 => refineStep step (refineIter step k)

/-- A relation is a strong bisimulation if related states can
match each other's moves staying in the relation. -/
def IsBisim (step : S → S → Prop) (R : S → S → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ a', step a a' → ∃ b', step b b' ∧ R a' b') ∧
    (∀ b', step b b' → ∃ a', step a a' ∧ R a' b')

/-- Strong bisimilarity: being related by some strong
bisimulation. -/
def Bisim (step : S → S → Prop) (a b : S) : Prop :=
  ∃ R, IsBisim step R ∧ R a b

/-- Each refinement iterate is an equivalence relation. -/
private theorem refineIter_equiv (step : S → S → Prop) (k : ℕ) :
    Equivalence (refineIter step k) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> exact True.intro
  | succ k ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro a
        refine ⟨ih.refl a, ?_, ?_⟩
        · intro a' ha'
          exact ⟨a', ha', ih.refl a'⟩
        · intro b' hb'
          exact ⟨b', hb', ih.refl b'⟩
      · intro a b h
        obtain ⟨hr, h1, h2⟩ := h
        refine ⟨ih.symm hr, ?_, ?_⟩
        · intro a' ha'
          obtain ⟨b', hb', hr'⟩ := h2 a' ha'
          exact ⟨b', hb', ih.symm hr'⟩
        · intro b' hb'
          obtain ⟨a', ha', hr'⟩ := h1 b' hb'
          exact ⟨a', ha', ih.symm hr'⟩
      · intro a b c hab hbc
        obtain ⟨habr, hab1, hab2⟩ := hab
        obtain ⟨hbcr, hbc1, hbc2⟩ := hbc
        refine ⟨ih.trans habr hbcr, ?_, ?_⟩
        · intro a' ha'
          obtain ⟨b', hb', hr1⟩ := hab1 a' ha'
          obtain ⟨c', hc', hr2⟩ := hbc1 b' hb'
          exact ⟨c', hc', ih.trans hr1 hr2⟩
        · intro c' hc'
          obtain ⟨b', hb', hr2⟩ := hbc2 c' hc'
          obtain ⟨a', ha', hr1⟩ := hab2 b' hb'
          exact ⟨a', ha', ih.trans hr1 hr2⟩

/-- Refinement steps respect pointwise equivalence of relations. -/
private theorem refineStep_congr (step : S → S → Prop) {R Q : S → S → Prop}
    (h : ∀ x y, R x y ↔ Q x y) (x y : S) :
    refineStep step R x y ↔ refineStep step Q x y := by
  constructor <;> intro hR
  · obtain ⟨hr, h1, h2⟩ := hR
    refine ⟨(h x y).mp hr, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', r⟩ := h1 a' ha'
      exact ⟨b', hb', (h a' b').mp r⟩
    · intro b' hb'
      obtain ⟨a', ha', r⟩ := h2 b' hb'
      exact ⟨a', ha', (h a' b').mp r⟩
  · obtain ⟨hr, h1, h2⟩ := hR
    refine ⟨(h x y).mpr hr, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', r⟩ := h1 a' ha'
      exact ⟨b', hb', (h a' b').mpr r⟩
    · intro b' hb'
      obtain ⟨a', ha', r⟩ := h2 b' hb'
      exact ⟨a', ha', (h a' b').mpr r⟩

/-- Once two consecutive iterates agree, all later ones agree. -/
private theorem refineIter_forward_stable (step : S → S → Prop) (k : ℕ)
    (Heq : ∀ x y, refineIter step (k + 1) x y ↔ refineIter step k x y)
    (i : ℕ) (hki : k ≤ i) :
    ∀ x y, refineIter step (i + 1) x y ↔ refineIter step i x y := by
  induction i, hki using Nat.le_induction with
  | base => exact Heq
  | succ n hkn ih =>
      intro x y
      exact refineStep_congr step (fun x y => ih x y) x y

/-- Equivalence class of `a` under `R`, as a finset. -/
private noncomputable def eclass (R : S → S → Prop) (a : S) : Finset S := by
  classical
  exact Finset.univ.filter (fun b => R a b)

private theorem mem_eclass (R : S → S → Prop) (c d : S) :
    d ∈ eclass R c ↔ R c d := by
  simp [eclass, Finset.mem_filter]

private theorem eclass_eq_of_equiv {R : S → S → Prop} (hR : Equivalence R)
    (a c : S) :
    eclass R a = eclass R c ↔ R a c := by
  constructor
  · intro h
    have ha : a ∈ eclass R a := (mem_eclass R a a).mpr (hR.refl a)
    rw [h] at ha
    have hca : R c a := (mem_eclass R c a).mp ha
    exact hR.symm hca
  · intro hac
    ext d
    simp only [mem_eclass]
    exact ⟨fun had => hR.trans (hR.symm hac) had, fun hcd => hR.trans hac hcd⟩

/-- The partition at stage `k`, as the finset of equivalence classes. -/
private noncomputable def classes (step : S → S → Prop) (k : ℕ) :
    Finset (Finset S) :=
  Finset.univ.image (fun a => eclass (refineIter step k) a)

private theorem mem_classes (step : S → S → Prop) (k : ℕ) (X : Finset S) :
    X ∈ classes step k ↔ ∃ c, eclass (refineIter step k) c = X := by
  unfold classes
  simp [Finset.mem_image]

private theorem classes_card_le (step : S → S → Prop) (k : ℕ) :
    (classes step k).card ≤ Fintype.card S := by
  have h1 : (classes step k).card ≤ (Finset.univ : Finset S).card := by
    unfold classes
    exact Finset.card_image_le
  rw [Finset.card_univ] at h1
  exact h1

private theorem eclass_zero_total (step : S → S → Prop) (c : S) :
    eclass (refineIter step 0) c = Finset.univ := by
  ext d
  rw [mem_eclass]
  exact ⟨fun _ => Finset.mem_univ d, fun _ => True.intro⟩

/-- Each stage-`k+1` class determines a stage-`k` class: the map
sending a set to the stage-`k` neighborhood of its elements. -/
private noncomputable def classMap (step : S → S → Prop) (k : ℕ)
    (Y : Finset S) : Finset S := by
  classical
  exact Finset.univ.filter (fun d => ∃ c ∈ Y, refineIter step k c d)

private theorem classMap_eclass (step : S → S → Prop) (k : ℕ) (c : S) :
    classMap step k (eclass (refineIter step (k + 1)) c) =
      eclass (refineIter step k) c := by
  ext d
  simp only [classMap, Finset.mem_filter, Finset.mem_univ, true_and, mem_eclass]
  constructor
  · intro ⟨e, heq, hed⟩
    have hec : refineIter step k c e := heq.1
    exact (refineIter_equiv step k).trans hec hed
  · intro hcd
    exact ⟨c, (refineIter_equiv step (k + 1)).refl c, hcd⟩

/-- A surjective, non-injective map between finsets
forces the target to be smaller. -/
private theorem card_lt_of_surjOn_not_injOn {A B : Finset (Finset S)}
    {f : Finset S → Finset S}
    (hmap : ∀ Y ∈ B, f Y ∈ A)
    (hsurj : ∀ X ∈ A, ∃ Y ∈ B, f Y = X)
    (hne : ∃ Y₁ ∈ B, ∃ Y₂ ∈ B, Y₁ ≠ Y₂ ∧ f Y₁ = f Y₂) :
    A.card < B.card := by
  let g : ↥B → ↥A := fun y => ⟨f y.1, hmap y.1 y.2⟩
  have hgsurj : Function.Surjective g := by
    intro x
    obtain ⟨Y, hYB, hfY⟩ := hsurj x.1 x.2
    exact ⟨⟨Y, hYB⟩, Subtype.ext hfY⟩
  have hgninj : ¬ Function.Injective g := by
    intro hinj
    obtain ⟨Y₁, hY₁, Y₂, hY₂, hne', heq'⟩ := hne
    have h : g ⟨Y₁, hY₁⟩ = g ⟨Y₂, hY₂⟩ := Subtype.ext heq'
    have h2 := hinj h
    exact hne' (congrArg Subtype.val h2)
  have hlt := Fintype.card_lt_of_surjective_not_injective g hgsurj hgninj
  rw [Fintype.card_coe, Fintype.card_coe] at hlt
  exact hlt

/-- A strict refinement round strictly increases the class count. -/
private theorem classes_card_lt_of_strict (step : S → S → Prop) (k : ℕ)
    (x y : S)
    (hxy : refineIter step k x y) (hneq : ¬ refineIter step (k + 1) x y) :
    (classes step k).card < (classes step (k + 1)).card := by
  refine card_lt_of_surjOn_not_injOn (f := classMap step k) ?_ ?_ ?_
  · intro Y hY
    rw [mem_classes] at hY
    obtain ⟨c, hc⟩ := hY
    rw [mem_classes]
    exact ⟨c, by rw [← hc, classMap_eclass]⟩
  · intro X hX
    rw [mem_classes] at hX
    obtain ⟨c, hc⟩ := hX
    exact ⟨eclass (refineIter step (k + 1)) c,
      (mem_classes step (k + 1) _).mpr ⟨c, rfl⟩,
      by rw [classMap_eclass, hc]⟩
  · refine ⟨eclass (refineIter step (k + 1)) x,
        (mem_classes step (k + 1) _).mpr ⟨x, rfl⟩,
        eclass (refineIter step (k + 1)) y,
        (mem_classes step (k + 1) _).mpr ⟨y, rfl⟩, ?_, ?_⟩
    · intro heq
      exact hneq ((eclass_eq_of_equiv (refineIter_equiv step (k + 1)) x y).mp heq)
    · rw [classMap_eclass, classMap_eclass]
      exact (eclass_eq_of_equiv (refineIter_equiv step k) x y).mpr hxy

/-- Every refinement iterate is an equivalence relation
containing bisimilarity, and the iterates decrease. -/
theorem refineIter_antitone (step : S → S → Prop)
    (k : ℕ) (a b : S) :
    refineIter step (k + 1) a b → refineIter step k a b := by
  intro h
  exact h.1

/-- Bisimilar states survive every refinement round. -/
theorem bisim_refineIter (step : S → S → Prop)
    (k : ℕ) {a b : S} (h : Bisim step a b) :
    refineIter step k a b := by
  suffices H : ∀ (a b : S), Bisim step a b → refineIter step k a b from H a b h
  induction k with
  | zero =>
      intro a b h
      exact True.intro
  | succ k ih =>
      intro a b h
      obtain ⟨R, hR, hab⟩ := h
      refine ⟨ih a b ⟨R, hR, hab⟩, ?_, ?_⟩
      · intro a' ha'
        obtain ⟨b', hb', hr'⟩ := (hR a b hab).1 a' ha'
        exact ⟨b', hb', ih a' b' ⟨R, hR, hr'⟩⟩
      · intro b' hb'
        obtain ⟨a', ha', hr'⟩ := (hR a b hab).2 b' hb'
        exact ⟨a', ha', ih a' b' ⟨R, hR, hr'⟩⟩

/-- At `Fintype.card S` rounds the refinement stabilizes:
the next iterate equals it. -/
theorem refineIter_stabilizes (step : S → S → Prop)
    (a b : S) :
    refineIter step (Fintype.card S + 1) a b ↔
      refineIter step (Fintype.card S) a b := by
  classical
  suffices H : ∀ x y : S, refineIter step (Fintype.card S + 1) x y ↔
      refineIter step (Fintype.card S) x y from H a b
  by_cases hS : Nonempty S
  · by_contra Hcon
    have Hwit : ∃ x y, ¬ (refineIter step (Fintype.card S + 1) x y ↔
        refineIter step (Fintype.card S) x y) := by
      by_contra Hall
      push Not at Hall
      exact Hcon Hall
    have hstrict : ∀ k : ℕ, k ≤ Fintype.card S →
        ∃ x y, refineIter step k x y ∧ ¬ refineIter step (k + 1) x y := by
      intro k hk
      by_contra Hk
      have Hk' : ∀ x y, refineIter step k x y → refineIter step (k + 1) x y := by
        intro x y hxy
        by_contra hnxy
        exact Hk ⟨x, y, hxy, hnxy⟩
      have Heq : ∀ x y, refineIter step (k + 1) x y ↔ refineIter step k x y :=
        fun x y => ⟨refineIter_antitone step k x y, Hk' x y⟩
      have Hstab := refineIter_forward_stable step k Heq (Fintype.card S) hk
      obtain ⟨x, y, hxy⟩ := Hwit
      exact hxy (Hstab x y)
    have hlt : ∀ k : ℕ, k ≤ Fintype.card S →
        (classes step k).card < (classes step (k + 1)).card := by
      intro k hk
      obtain ⟨x, y, hxy, hneq⟩ := hstrict k hk
      exact classes_card_lt_of_strict step k x y hxy hneq
    have h0 : (classes step 0).card = 1 := by
      have heq : classes step 0 = {Finset.univ} := by
        ext X
        simp only [mem_classes, Finset.mem_singleton]
        constructor
        · intro ⟨c, hc⟩
          have htot := eclass_zero_total step c
          rw [← hc, htot]
        · intro hX
          obtain ⟨a0⟩ := hS
          refine ⟨a0, ?_⟩
          have htot := eclass_zero_total step a0
          rw [htot, hX]
      rw [heq]
      exact Finset.card_singleton _
    have hchain : ∀ m : ℕ, m ≤ Fintype.card S + 1 →
        (classes step 0).card + m ≤ (classes step m).card := by
      intro m
      induction m with
      | zero =>
          intro _
          omega
      | succ m ih =>
          intro hm
          have h1 := ih (by omega : m ≤ Fintype.card S + 1)
          have h2 := hlt m (by omega : m ≤ Fintype.card S)
          omega
    have hfinal := hchain (Fintype.card S + 1) (Nat.le_refl _)
    have hle := classes_card_le step (Fintype.card S + 1)
    omega
  · intro x y
    exact (hS ⟨x⟩).elim

/-- The stabilized refinement is a bisimulation. -/
theorem refineIter_isBisim (step : S → S → Prop) :
    IsBisim step (refineIter step (Fintype.card S)) := by
  intro a b hab
  have h := (refineIter_stabilizes step a b).mpr hab
  exact h.2

/-- Decision procedure correctness: the `card S`-th
refinement equals strong bisimilarity. -/
theorem refineIter_eq_bisim (step : S → S → Prop)
    (a b : S) :
    refineIter step (Fintype.card S) a b ↔ Bisim step a b := by
  constructor
  · intro h
    exact ⟨refineIter step (Fintype.card S), refineIter_isBisim step, h⟩
  · intro h
    exact bisim_refineIter step (Fintype.card S) h
