/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Naive partition refinement computes strong bisimilarity

One naive partition-refinement round on a labelled transition system
`lts : Cslib.LTS State Label` keeps two states related exactly when they are
related now and, for every label, each transition of either state is matched by
a transition of the other under the same label into related states. Starting
from the total relation, the iterates are equivalence relations, they decrease,
and every iterate contains strong bisimilarity. On a finite state space every
iterate from round `Fintype.card State` on is exactly strong bisimilarity.

Bisimulation and bisimilarity are the upstream `Cslib.LTS.IsHomBisimulation`
and `Cslib.LTS.HomBisimilarity`. An unlabelled transition relation is the
special case of an LTS with `Unit` labels.

## Main results

* `Cslib.LTS.refineStep`, `Cslib.LTS.refineIter`: one refinement round, and its
  iterates from the total relation.
* `Cslib.LTS.refineIter_equivalence`: every iterate is an equivalence relation.
* `Cslib.LTS.refineIter_antitone`: each iterate is contained in the previous
  one.
* `Cslib.LTS.refineIter_of_homBisimilarity`: bisimilar states stay related in
  every round.
* `Cslib.LTS.refineIter_stabilizes`: the iterates at rounds
  `Fintype.card State` and `Fintype.card State + 1` agree.
* `Cslib.LTS.refineIter_card_iff_homBisimilarity`,
  `Cslib.LTS.refineIter_iff_homBisimilarity_of_card_le`: the iterate at round
  `Fintype.card State`, and at every later round, is strong bisimilarity.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- One naive partition-refinement round for strong bisimilarity: `a` and `b`
stay related iff `R` relates them and, for every label `μ`, each `μ`-transition
of either state is matched by a `μ`-transition of the other into `R`-related
states. -/
def refineStep (lts : LTS State Label) (R : State → State → Prop) :
    State → State → Prop :=
  fun a b => R a b ∧ ∀ μ,
    (∀ a', lts.Tr a μ a' → ∃ b', lts.Tr b μ b' ∧ R a' b') ∧
    (∀ b', lts.Tr b μ b' → ∃ a', lts.Tr a μ a' ∧ R a' b')

/-- The `k`-th naive refinement iterate, starting from the total relation. -/
def refineIter (lts : LTS State Label) : ℕ → State → State → Prop
  | 0 => fun _ _ => True
  | k + 1 => lts.refineStep (lts.refineIter k)

variable (lts : LTS State Label)

/-- Every refinement iterate is an equivalence relation. -/
theorem refineIter_equivalence (k : ℕ) : Equivalence (lts.refineIter k) := by
  induction k with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | succ k ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro a
        exact ⟨ih.refl a, fun μ => ⟨fun a' ha' => ⟨a', ha', ih.refl a'⟩,
          fun b' hb' => ⟨b', hb', ih.refl b'⟩⟩⟩
      · rintro a b ⟨hr, h⟩
        refine ⟨ih.symm hr, fun μ => ⟨?_, ?_⟩⟩
        · intro b' hb'
          obtain ⟨a', ha', hr'⟩ := (h μ).2 b' hb'
          exact ⟨a', ha', ih.symm hr'⟩
        · intro a' ha'
          obtain ⟨b', hb', hr'⟩ := (h μ).1 a' ha'
          exact ⟨b', hb', ih.symm hr'⟩
      · rintro a b c ⟨habr, hab⟩ ⟨hbcr, hbc⟩
        refine ⟨ih.trans habr hbcr, fun μ => ⟨?_, ?_⟩⟩
        · intro a' ha'
          obtain ⟨b', hb', hr1⟩ := (hab μ).1 a' ha'
          obtain ⟨c', hc', hr2⟩ := (hbc μ).1 b' hb'
          exact ⟨c', hc', ih.trans hr1 hr2⟩
        · intro c' hc'
          obtain ⟨b', hb', hr2⟩ := (hbc μ).2 c' hc'
          obtain ⟨a', ha', hr1⟩ := (hab μ).2 b' hb'
          exact ⟨a', ha', ih.trans hr1 hr2⟩

/-- Each refinement iterate is contained in the previous one. -/
theorem refineIter_antitone (k : ℕ) (a b : State) :
    lts.refineIter (k + 1) a b → lts.refineIter k a b :=
  fun h => h.1

/-- Bisimilar states stay related in every refinement round. -/
theorem refineIter_of_homBisimilarity (k : ℕ) {a b : State}
    (h : lts.HomBisimilarity a b) : lts.refineIter k a b := by
  obtain ⟨R, hab, hR⟩ := h
  suffices H : ∀ x y, R x y → lts.refineIter k x y from H a b hab
  induction k with
  | zero => exact fun _ _ _ => trivial
  | succ k ih =>
      intro x y hxy
      refine ⟨ih x y hxy, fun μ => ⟨?_, ?_⟩⟩
      · intro x' hx'
        obtain ⟨y', hy', hr⟩ := (hR hxy μ).1 x' hx'
        exact ⟨y', hy', ih x' y' hr⟩
      · intro y' hy'
        obtain ⟨x', hx', hr⟩ := (hR hxy μ).2 y' hy'
        exact ⟨x', hx', ih x' y' hr⟩

/-- Once two consecutive iterates agree, all later ones agree. -/
private theorem refineIter_forward_stable (k : ℕ)
    (Heq : ∀ x y, lts.refineIter (k + 1) x y ↔ lts.refineIter k x y)
    (i : ℕ) (hki : k ≤ i) :
    ∀ x y, lts.refineIter (i + 1) x y ↔ lts.refineIter i x y := by
  induction i, hki using Nat.le_induction with
  | base => exact Heq
  | succ n hkn ih =>
      have e : lts.refineIter (n + 1) = lts.refineIter n :=
        funext fun x => funext fun y => propext (ih x y)
      intro x y
      change lts.refineStep (lts.refineIter (n + 1)) x y ↔
        lts.refineStep (lts.refineIter n) x y
      rw [e]

/-- A surjective, non-injective map between finsets forces the target to be
smaller. -/
private theorem card_lt_of_surjOn_not_injOn {A B : Finset (Finset State)}
    {f : Finset State → Finset State}
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

section Finite

variable [Fintype State]

/-- Equivalence class of `a` under `R`, as a finset. -/
private noncomputable def eclass (R : State → State → Prop) (a : State) :
    Finset State := by
  classical
  exact Finset.univ.filter (fun b => R a b)

private theorem mem_eclass (R : State → State → Prop) (c d : State) :
    d ∈ eclass R c ↔ R c d := by
  simp [eclass, Finset.mem_filter]

private theorem eclass_eq_of_equiv {R : State → State → Prop} (hR : Equivalence R)
    (a c : State) :
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

/-- The partition at round `k`, as the finset of equivalence classes. -/
private noncomputable def classes (k : ℕ) : Finset (Finset State) := by
  classical
  exact Finset.univ.image (fun a => eclass (lts.refineIter k) a)

private theorem mem_classes (k : ℕ) (X : Finset State) :
    X ∈ classes lts k ↔ ∃ c, eclass (lts.refineIter k) c = X := by
  unfold classes
  simp [Finset.mem_image]

private theorem classes_card_le (k : ℕ) :
    (classes lts k).card ≤ Fintype.card State := by
  classical
  have h1 : (classes lts k).card ≤ (Finset.univ : Finset State).card := by
    unfold classes
    exact Finset.card_image_le
  rw [Finset.card_univ] at h1
  exact h1

private theorem eclass_zero_total (c : State) :
    eclass (lts.refineIter 0) c = Finset.univ := by
  ext d
  rw [mem_eclass]
  exact ⟨fun _ => Finset.mem_univ d, fun _ => True.intro⟩

/-- Each round-`k+1` class determines a round-`k` class: the map sending a set
to the round-`k` neighborhood of its elements. -/
private noncomputable def classMap (k : ℕ) (Y : Finset State) : Finset State := by
  classical
  exact Finset.univ.filter (fun d => ∃ c ∈ Y, lts.refineIter k c d)

private theorem classMap_eclass (k : ℕ) (c : State) :
    classMap lts k (eclass (lts.refineIter (k + 1)) c) =
      eclass (lts.refineIter k) c := by
  ext d
  simp only [classMap, Finset.mem_filter, Finset.mem_univ, true_and, mem_eclass]
  constructor
  · intro ⟨e, heq, hed⟩
    have hec : lts.refineIter k c e := heq.1
    exact (lts.refineIter_equivalence k).trans hec hed
  · intro hcd
    exact ⟨c, (lts.refineIter_equivalence (k + 1)).refl c, hcd⟩

/-- A strict refinement round strictly increases the number of classes. -/
private theorem classes_card_lt_of_strict (k : ℕ) (x y : State)
    (hxy : lts.refineIter k x y) (hneq : ¬ lts.refineIter (k + 1) x y) :
    (classes lts k).card < (classes lts (k + 1)).card := by
  refine card_lt_of_surjOn_not_injOn (f := classMap lts k) ?_ ?_ ?_
  · intro Y hY
    rw [mem_classes] at hY
    obtain ⟨c, hc⟩ := hY
    rw [mem_classes]
    exact ⟨c, by rw [← hc, classMap_eclass]⟩
  · intro X hX
    rw [mem_classes] at hX
    obtain ⟨c, hc⟩ := hX
    exact ⟨eclass (lts.refineIter (k + 1)) c,
      (mem_classes lts (k + 1) _).mpr ⟨c, rfl⟩,
      by rw [classMap_eclass, hc]⟩
  · refine ⟨eclass (lts.refineIter (k + 1)) x,
        (mem_classes lts (k + 1) _).mpr ⟨x, rfl⟩,
        eclass (lts.refineIter (k + 1)) y,
        (mem_classes lts (k + 1) _).mpr ⟨y, rfl⟩, ?_, ?_⟩
    · intro heq
      exact hneq ((eclass_eq_of_equiv (lts.refineIter_equivalence (k + 1)) x y).mp heq)
    · rw [classMap_eclass, classMap_eclass]
      exact (eclass_eq_of_equiv (lts.refineIter_equivalence k) x y).mpr hxy

/-- The refinement is stable at round `Fintype.card State`: the next iterate
agrees with it. -/
theorem refineIter_stabilizes (a b : State) :
    lts.refineIter (Fintype.card State + 1) a b ↔
      lts.refineIter (Fintype.card State) a b := by
  classical
  suffices H : ∀ x y : State, lts.refineIter (Fintype.card State + 1) x y ↔
      lts.refineIter (Fintype.card State) x y from H a b
  by_cases hS : Nonempty State
  · by_contra Hcon
    have Hwit : ∃ x y, ¬ (lts.refineIter (Fintype.card State + 1) x y ↔
        lts.refineIter (Fintype.card State) x y) := by
      by_contra Hall
      push Not at Hall
      exact Hcon Hall
    have hstrict : ∀ k : ℕ, k ≤ Fintype.card State →
        ∃ x y, lts.refineIter k x y ∧ ¬ lts.refineIter (k + 1) x y := by
      intro k hk
      by_contra Hk
      have Hk' : ∀ x y, lts.refineIter k x y → lts.refineIter (k + 1) x y := by
        intro x y hxy
        by_contra hnxy
        exact Hk ⟨x, y, hxy, hnxy⟩
      have Heq : ∀ x y, lts.refineIter (k + 1) x y ↔ lts.refineIter k x y :=
        fun x y => ⟨lts.refineIter_antitone k x y, Hk' x y⟩
      have Hstab := refineIter_forward_stable lts k Heq (Fintype.card State) hk
      obtain ⟨x, y, hxy⟩ := Hwit
      exact hxy (Hstab x y)
    have hlt : ∀ k : ℕ, k ≤ Fintype.card State →
        (classes lts k).card < (classes lts (k + 1)).card := by
      intro k hk
      obtain ⟨x, y, hxy, hneq⟩ := hstrict k hk
      exact classes_card_lt_of_strict lts k x y hxy hneq
    have h0 : (classes lts 0).card = 1 := by
      have heq : classes lts 0 = {Finset.univ} := by
        ext X
        simp only [mem_classes, Finset.mem_singleton]
        constructor
        · intro ⟨c, hc⟩
          have htot := eclass_zero_total lts c
          rw [← hc, htot]
        · intro hX
          obtain ⟨a0⟩ := hS
          refine ⟨a0, ?_⟩
          have htot := eclass_zero_total lts a0
          rw [htot, hX]
      rw [heq]
      exact Finset.card_singleton _
    have hchain : ∀ m : ℕ, m ≤ Fintype.card State + 1 →
        (classes lts 0).card + m ≤ (classes lts m).card := by
      intro m
      induction m with
      | zero =>
          intro _
          omega
      | succ m ih =>
          intro hm
          have h1 := ih (by omega : m ≤ Fintype.card State + 1)
          have h2 := hlt m (by omega : m ≤ Fintype.card State)
          omega
    have hfinal := hchain (Fintype.card State + 1) (Nat.le_refl _)
    have hle := classes_card_le lts (Fintype.card State + 1)
    omega
  · intro x y
    exact (hS ⟨x⟩).elim

/-- The iterate at round `Fintype.card State` is a bisimulation. -/
theorem refineIter_isHomBisimulation :
    lts.IsHomBisimulation (lts.refineIter (Fintype.card State)) := by
  intro a b hab μ
  exact ((lts.refineIter_stabilizes a b).mpr hab).2 μ

/-- Correctness of naive partition refinement: the iterate at round
`Fintype.card State` is strong bisimilarity. -/
theorem refineIter_card_iff_homBisimilarity (a b : State) :
    lts.refineIter (Fintype.card State) a b ↔ lts.HomBisimilarity a b :=
  ⟨fun h => ⟨_, h, lts.refineIter_isHomBisimulation⟩,
    lts.refineIter_of_homBisimilarity _⟩

/-- Every iterate from round `Fintype.card State` on is strong bisimilarity. -/
theorem refineIter_iff_homBisimilarity_of_card_le {i : ℕ} (hi : Fintype.card State ≤ i)
    (a b : State) : lts.refineIter i a b ↔ lts.HomBisimilarity a b := by
  refine ⟨fun h => ?_, lts.refineIter_of_homBisimilarity i⟩
  have hdown : ∀ j, Fintype.card State ≤ j →
      lts.refineIter j a b → lts.refineIter (Fintype.card State) a b := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact id
    | succ n _ ih => exact fun hn => ih (lts.refineIter_antitone n a b hn)
  exact (lts.refineIter_card_iff_homBisimilarity a b).mp (hdown i hi h)

end Finite

end Cslib.LTS
