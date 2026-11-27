/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.EquivFin

/-! # Natarajan dimension and the Natarajan lemma

This file defines N-shattering and the Natarajan dimension for concept classes
over an arbitrary label type, and proves the Natarajan lemma: over a finite
label type of cardinality `k`, a class of Natarajan dimension at most `d`
induces at most `m ^ d * k ^ (2 * d)` distinct restrictions on any nonempty
sample of `m` points.

The public interface is set-based, over `ConceptClass α β`: the class
itself may be infinite; only the sample is finite. Shattering and dimension
need no finiteness on `β`; counting needs `[Fintype β]`. The proof goes
through a private finite-class core (`FinCore`) over `Fin k`: for each
realized labeling, one witness concept is chosen from the class, and the
finite witness class inherits both the trace count and the dimension bound.
The general finite-label case is transported along `β ≃ Fin (Fintype.card β)`.

## Main definitions

- `NShatters C s`: the class `C` N-shatters the sample `s`.
- `NDimLE C d`: the class `C` has Natarajan dimension at most `d`.
- `tracesCard C s`: the number of distinct restrictions of `C` to `s`.

## Main statements

- `nShatters_subset`: N-shattering is hereditary to subsets.
- `nDimLE_mono`: the dimension bound is monotone in `d`.
- `natarajan_lemma`: the Natarajan lemma growth bound.
- `nDimLE_zero`: under a zero-dimensional bound, all concepts agree everywhere.
- `tracesCard_coe_finset`: trace-count bridge for coerced finite classes.
- `natarajan_lemma_finset`: the lemma for executable finite classes.

## References

* B. K. Natarajan, *On learning sets and functions*, Machine Learning 4 (1989), 67-97,
  doi:10.1007/BF00114804.
* S. Shalev-Shwartz and S. Ben-David,
  *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press,
  2014, Chapter 29 (Multiclass Learnability), Definition 29.1 and the Natarajan lemma.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- A concept class `C` over an arbitrary label type *N-shatters* a finite
sample `s` if there are two labelings `f₀ f₁` of the domain, disagreeing at
every point of `s`, such that every subset `t` of `s` is realized by some
concept agreeing with `f₁` on `t` and with `f₀` on the rest of `s`. The class
itself may be infinite. -/
def NShatters {α β : Type*} (C : ConceptClass α β)
    (s : Finset α) : Prop :=
  ∃ f₀ f₁ : α → β, (∀ x ∈ s, f₀ x ≠ f₁ x) ∧
    ∀ t : Finset α, t ⊆ s → ∃ h ∈ C,
      (∀ x ∈ t, h x = f₁ x) ∧ ∀ x ∈ s, x ∉ t → h x = f₀ x

/-- A concept class has *Natarajan dimension at most `d`* if no set of `d + 1`
points is N-shattered by it. Stated in `≤`-form to avoid supremum conventions
for the dimension itself. -/
def NDimLE {α β : Type*} (C : ConceptClass α β) (d : ℕ) : Prop :=
  ∀ s : Finset α, s.card = d + 1 → ¬ NShatters C s

open scoped Classical in
/-- The number of distinct restrictions of the concepts in `C` to the sample
`s`: the labelings of `s` realized by some concept in `C`. The class itself
may be infinite; only the sample is finite. Needs a finite label type. -/
noncomputable def tracesCard {α β : Type*} [Fintype β]
    (C : ConceptClass α β) (s : Finset α) : ℕ :=
  (Finset.univ.filter fun g : s → β =>
    ∃ c ∈ C, ∀ x : s, c x.val = g x).card

/-- N-shattering is hereditary: if `C` N-shatters `s`, it N-shatters every
subset of `s`. -/
theorem nShatters_subset {α β : Type*} (C : ConceptClass α β)
    (s t : Finset α) (h : NShatters C s) (hsub : t ⊆ s) :
    NShatters C t := by
  obtain ⟨f₀, f₁, hne, hwit⟩ := h
  refine ⟨f₀, f₁, fun x hx => hne x (hsub hx), fun u hu => ?_⟩
  obtain ⟨h, mh, h1, h0⟩ := hwit u (hu.trans hsub)
  exact ⟨h, mh, h1, fun x hx hxu => h0 x (hsub hx) hxu⟩

/-- The `NDimLE` bound is monotone in `d`: a `(d' + 1)`-set contains a
`(d + 1)`-subset, to which shattering descends. -/
theorem nDimLE_mono {α β : Type*} (C : ConceptClass α β)
    (d d' : ℕ) (hle : d ≤ d') (hd : NDimLE C d) : NDimLE C d' := by
  intro s hs hsh
  have hle' : d + 1 ≤ s.card := by omega
  obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hle'
  exact hd t hcard (nShatters_subset C s t hsh hts)

namespace FinCore

/-- A finite hypothesis class `H` of `Fin k`-valued functions *N-shatters* a
finite sample `s` if there are two labelings `f₀ f₁` of the domain, disagreeing
at every point of `s`, such that every subset `t` of `s` is realized by some
hypothesis agreeing with `f₁` on `t` and with `f₀` on the rest of `s`. -/
private def NShatters {α : Type*} {k : ℕ} (H : Finset (α → Fin k))
    (s : Finset α) : Prop :=
  ∃ f₀ f₁ : α → Fin k, (∀ x ∈ s, f₀ x ≠ f₁ x) ∧
    ∀ t : Finset α, t ⊆ s → ∃ h ∈ H,
      (∀ x ∈ t, h x = f₁ x) ∧ ∀ x ∈ s, x ∉ t → h x = f₀ x

/-- A finite hypothesis class has *Natarajan dimension at most `d`* if no set of
`d + 1` points is N-shattered by it. Stated in `≤`-form to avoid supremum
conventions for the dimension itself. -/
private def NDimLE {α : Type*} {k : ℕ} (H : Finset (α → Fin k)) (d : ℕ) : Prop :=
  ∀ s : Finset α, s.card = d + 1 → ¬ NShatters H s

/-- The number of distinct restrictions of the hypotheses in `H` to the sample
`s`, i.e. the cardinality of the image of `H` under evaluation on `s`. -/
private noncomputable def tracesCard {α : Type*} [DecidableEq α] {k : ℕ}
    (H : Finset (α → Fin k)) (s : Finset α) : ℕ :=
  (H.image fun h (x : s) => h x.val).card

/-- Relativized dimension bound: no `(d + 1)`-subset of `s` is N-shattered.
The growth induction carries this form so the dimension-drop step applies to
subsets of the erased sample. -/
private def NDimLERel {α : Type*} {k : ℕ} (H : Finset (α → Fin k))
    (s : Finset α) (d : ℕ) : Prop :=
  ∀ T : Finset α, T ⊆ s → T.card = d + 1 → ¬ NShatters H T

/-- Under a relativized zero-dimensional bound, any two hypotheses in `H`
agree at every point of `s`: a disagreement at `y` would N-shatter `{y}`. -/
private theorem agree_of_relDim_zero {α : Type*} {k : ℕ}
    {H : Finset (α → Fin k)} {s : Finset α} (hrel : NDimLERel H s 0)
    {h₁ h₂ : α → Fin k} (m₁ : h₁ ∈ H) (m₂ : h₂ ∈ H) {y : α}
    (hy : y ∈ s) : h₁ y = h₂ y := by
  by_contra hne
  simp only [NDimLERel] at hrel
  apply hrel {y} (Finset.singleton_subset_iff.mpr hy)
    (Finset.card_singleton y)
  refine ⟨h₁, h₂, ?_, ?_⟩
  · intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact hne
  · intro t ht
    obtain rfl | rfl := Finset.subset_singleton_iff.mp ht
    · exact ⟨h₁, m₁, fun z hz => absurd hz (Finset.notMem_empty z),
        fun z _ _ => rfl⟩
    · exact ⟨h₂, m₂, fun z _ => rfl,
        fun z hz1 hz2 => absurd hz1 hz2⟩

/-- Restriction of a trace on `s` to the erased sample `s.erase x`. -/
private def restrictErase {α : Type*} [DecidableEq α] {k : ℕ} (s : Finset α)
    (x : α) (g : s → Fin k) : s.erase x → Fin k :=
  fun y => g ⟨y.val, Finset.mem_of_mem_erase y.property⟩

/-- Application rule for `restrictErase`. -/
private theorem restrictErase_apply {α : Type*} [DecidableEq α] {k : ℕ}
    (s : Finset α) (x : α) (g : s → Fin k) (y : s.erase x) :
    restrictErase s x g y =
      g ⟨y.val, Finset.mem_of_mem_erase y.property⟩ := rfl

/-- Restricting the trace of `h` on `s` gives the trace of `h` on `s.erase x`. -/
private theorem restrictErase_image {α : Type*} [DecidableEq α] {k : ℕ}
    (s : Finset α) (x : α) (h : α → Fin k) :
    restrictErase s x (fun y : s => h y.val) =
      fun y : s.erase x => h y.val := by
  funext y
  rfl

/-- Equal restrictions agree pointwise on the erased sample. -/
private theorem restrictErase_inj_on_erase {α : Type*} [DecidableEq α] {k : ℕ}
    (s : Finset α) (x : α) {g₁ g₂ : s → Fin k}
    (heq : restrictErase s x g₁ = restrictErase s x g₂) (y : s.erase x) :
    g₁ ⟨y.val, Finset.mem_of_mem_erase y.property⟩ =
      g₂ ⟨y.val, Finset.mem_of_mem_erase y.property⟩ := by
  have h1 := congrFun heq y
  simp only [restrictErase_apply] at h1
  exact h1

/-- Two hypotheses equal at `x` and on `s.erase x` have equal traces on `s`. -/
private theorem restreq_of_agree {α : Type*} [DecidableEq α] {k : ℕ}
    {s : Finset α} {x : α} (hx : x ∈ s) {h₁ h₂ : α → Fin k}
    (hxeq : h₁ x = h₂ x) (hag : ∀ y ∈ s.erase x, h₁ y = h₂ y) :
    (fun y : s => h₁ y.val) = fun y : s => h₂ y.val := by
  funext y
  by_cases hyx : y.val = x
  · have hy : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [hy]
    exact hxeq
  · exact hag y.val (Finset.mem_erase.mpr ⟨hyx, y.property⟩)

/-- The subclass of `H` of hypotheses taking value `a` at `x` that admit a
partner in `H` taking value `b` at `x` and agreeing with them on `s'`. -/
private noncomputable def branchClass {α : Type*} {k : ℕ}
    (H : Finset (α → Fin k)) (s' : Finset α) (x : α) (a b : Fin k) :
    Finset (α → Fin k) :=
  H.filter fun h => h x = a ∧ ∃ h₂ ∈ H, (∀ y ∈ s', h₂ y = h y) ∧ h₂ x = b

/-- The subclass of `H` of hypotheses whose restriction to `s'` extends
uniquely to `s`, i.e. every hypothesis agreeing with them on `s'` takes the
same value at `x`. -/
private noncomputable def uniqueClass {α : Type*} {k : ℕ}
    (H : Finset (α → Fin k)) (s' : Finset α) (x : α) :
    Finset (α → Fin k) :=
  H.filter fun h => ∀ h' ∈ H, (∀ y ∈ s', h' y = h y) → h' x = h x

/-- Ordered pairs of distinct labels, indexing the branch classes. -/
private def labelPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p => p.1 ≠ p.2

/-- Membership in `labelPairs` is inequality of the components. -/
private theorem mem_labelPairs {k : ℕ} {p : Fin k × Fin k} :
    p ∈ labelPairs k ↔ p.1 ≠ p.2 := by
  simp [labelPairs]

/-- Dimension drop: if no `(d + 2)`-subset of `s` is N-shattered by `H`, then
no `(d + 1)`-subset of `s.erase x` is N-shattered by a branch class. A
shattering of `T` transfers to a shattering of `insert x T` by `H`, using the
branch value `a` off `x` and the partner value `b` on it. -/
private theorem relDim_drop {α : Type*} [DecidableEq α] {k : ℕ}
    {H : Finset (α → Fin k)} {d : ℕ} {s : Finset α} {x : α} (hx : x ∈ s)
    (hrel : NDimLERel H s (d + 1)) {a b : Fin k} (hab : a ≠ b) :
    NDimLERel (branchClass H (s.erase x) x a b) (s.erase x) d := by
  simp only [NDimLERel] at hrel ⊢
  intro T hTs' hcard hsh
  obtain ⟨f₀, f₁, hne, hwit⟩ := hsh
  have hxT : x ∉ T := fun h => (Finset.mem_erase.mp (hTs' h)).1 rfl
  have hsub : insert x T ⊆ s := by
    intro y hy
    rw [Finset.mem_insert] at hy
    obtain rfl | hy := hy
    · exact hx
    · exact Finset.mem_of_mem_erase (hTs' hy)
  have hcard' : (insert x T).card = d + 1 + 1 := by
    rw [Finset.card_insert_of_notMem hxT, hcard]
  apply hrel (insert x T) hsub hcard'
  refine ⟨Function.update f₀ x a, Function.update f₁ x b, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_insert] at hy
    obtain rfl | hy := hy
    · rw [Function.update_self, Function.update_self]
      exact hab
    · have hyx : y ≠ x := by
        rintro rfl
        exact hxT hy
      rw [Function.update_of_ne hyx _ _, Function.update_of_ne hyx _ _]
      exact hne y hy
  · intro U hU
    have hV : U.erase x ⊆ T := by
      intro y hy
      obtain ⟨hyx, hyU⟩ := Finset.mem_erase.mp hy
      have hyI := hU hyU
      rw [Finset.mem_insert] at hyI
      obtain rfl | hyT := hyI
      · exact absurd rfl hyx
      · exact hyT
    obtain ⟨h₁, m₁, hp₁, hp₀⟩ := hwit (U.erase x) hV
    simp only [branchClass, Finset.mem_filter] at m₁
    obtain ⟨m₁H, hxa, h₂, m₂H, hagree, hxb⟩ := m₁
    by_cases hxU : x ∈ U
    · refine ⟨h₂, m₂H, fun y hyU => ?_, fun y hyI hyU' => ?_⟩
      · have hyI := hU hyU
        rw [Finset.mem_insert] at hyI
        obtain rfl | hyT := hyI
        · rw [Function.update_self]
          exact hxb
        · have hyx : y ≠ x := by
            rintro rfl
            exact hxT hyT
          have hyV : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hyx, hyU⟩
          have hyS : y ∈ s.erase x := hTs' hyT
          rw [Function.update_of_ne hyx _ _, ← hp₁ y hyV, hagree y hyS]
      · rw [Finset.mem_insert] at hyI
        obtain rfl | hyT := hyI
        · exact absurd hxU hyU'
        · have hyx : y ≠ x := by
            rintro rfl
            exact hxT hyT
          have hyVn : y ∉ U.erase x :=
            fun h => hyU' (Finset.mem_of_mem_erase h)
          have hyS : y ∈ s.erase x := hTs' hyT
          rw [Function.update_of_ne hyx _ _, ← hp₀ y hyT hyVn, hagree y hyS]
    · refine ⟨h₁, m₁H, fun y hyU => ?_, fun y hyI hyU' => ?_⟩
      · have hyI := hU hyU
        rw [Finset.mem_insert] at hyI
        obtain rfl | hyT := hyI
        · exact absurd hyU hxU
        · have hyx : y ≠ x := by
            rintro rfl
            exact hxT hyT
          have hyV : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hyx, hyU⟩
          rw [Function.update_of_ne hyx _ _]
          exact hp₁ y hyV
      · rw [Finset.mem_insert] at hyI
        obtain rfl | hyT := hyI
        · rw [Function.update_self]
          exact hxa
        · have hyx : y ≠ x := by
            rintro rfl
            exact hxT hyT
          have hyVn : y ∉ U.erase x :=
            fun h => hyU' (Finset.mem_of_mem_erase h)
          rw [Function.update_of_ne hyx _ _]
          exact hp₀ y hyT hyVn

open Classical in
/-- Fiber recursion: traces on `s` are bounded by traces on `s.erase x` plus,
over all label pairs, the traces of the branch classes there. Every hypothesis
either extends uniquely or carries a partner witnessing a label pair. -/
private theorem tracesCard_erase_le {α : Type*} [DecidableEq α] {k : ℕ}
    (H : Finset (α → Fin k)) (s : Finset α) (x : α) (hx : x ∈ s) :
    tracesCard H s ≤ tracesCard H (s.erase x) +
      ∑ p ∈ labelPairs k,
        tracesCard (branchClass H (s.erase x) x p.1 p.2) (s.erase x) := by
  simp only [tracesCard]
  have hsub : H ⊆ uniqueClass H (s.erase x) x ∪
      (labelPairs k).biUnion
        (fun p => branchClass H (s.erase x) x p.1 p.2) := by
    intro h mh
    rw [Finset.mem_union]
    by_cases huniq : ∀ h' ∈ H, (∀ y ∈ s.erase x, h' y = h y) → h' x = h x
    · left
      simp only [uniqueClass, Finset.mem_filter]
      exact ⟨mh, huniq⟩
    · right
      have hwit : ∃ h' ∈ H, (∀ y ∈ s.erase x, h' y = h y) ∧ h' x ≠ h x := by
        by_contra hall
        apply huniq
        intro h' mh' hag
        by_contra hne
        exact hall ⟨h', mh', hag, hne⟩
      obtain ⟨h', mh', hag, hne⟩ := hwit
      rw [Finset.mem_biUnion]
      refine ⟨(h x, h' x), ?_, ?_⟩
      · rw [mem_labelPairs]
        exact Ne.symm hne
      · unfold branchClass
        rw [Finset.mem_filter]
        exact ⟨mh, rfl, h', mh', hag, rfl⟩
  have himg : H.image (fun h (y : s) => h y.val) ⊆
      (uniqueClass H (s.erase x) x).image (fun h (y : s) => h y.val) ∪
        (labelPairs k).biUnion (fun p =>
          (branchClass H (s.erase x) x p.1 p.2).image
            (fun h (y : s) => h y.val)) := by
    intro g hg
    obtain ⟨h, mh, rfl⟩ := Finset.mem_image.mp hg
    have hmem := hsub mh
    rw [Finset.mem_union] at hmem
    obtain hmem | hmem := hmem
    · apply Finset.mem_union.mpr; left
      apply Finset.mem_image.mpr
      exact ⟨h, hmem, rfl⟩
    · apply Finset.mem_union.mpr; right
      have hmem' := Finset.mem_biUnion.mp hmem
      obtain ⟨p, mp, mhp⟩ := hmem'
      apply Finset.mem_biUnion.mpr
      refine ⟨p, mp, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨h, mhp, rfl⟩
  have step4 : ((uniqueClass H (s.erase x) x).image
      (fun h (y : s) => h y.val)).card ≤
      (H.image (fun h (y : s.erase x) => h y.val)).card := by
    apply Finset.card_le_card_of_injOn (restrictErase s x)
    · intro g hg
      rw [Finset.mem_coe] at hg
      obtain ⟨h, mh, rfl⟩ := Finset.mem_image.mp hg
      have mhH : h ∈ H := (Finset.mem_filter.mp mh).1
      apply Finset.mem_coe.mpr
      apply Finset.mem_image.mpr
      exact ⟨h, mhH, (restrictErase_image s x h).symm⟩
    · intro g₁ hg₁ g₂ hg₂ heq
      rw [Finset.mem_coe] at hg₁ hg₂
      obtain ⟨h₁, mh₁, hgeq₁⟩ := Finset.mem_image.mp hg₁
      obtain ⟨h₂, mh₂, hgeq₂⟩ := Finset.mem_image.mp hg₂
      have mh₁' := Finset.mem_filter.mp mh₁
      have mh₂H : h₂ ∈ H := (Finset.mem_filter.mp mh₂).1
      have hgeq₁' : ∀ v : s, h₁ v.val = g₁ v := fun v => congrFun hgeq₁ v
      have hgeq₂' : ∀ v : s, h₂ v.val = g₂ v := fun v => congrFun hgeq₂ v
      have hag : ∀ y ∈ s.erase x, h₁ y = h₂ y := by
        intro y hy
        have e := restrictErase_inj_on_erase s x heq ⟨y, hy⟩
        rw [← hgeq₁', ← hgeq₂'] at e
        exact e
      have hag' : ∀ y ∈ s.erase x, h₂ y = h₁ y :=
        fun y hy => (hag y hy).symm
      have hxeq : h₁ x = h₂ x := (mh₁'.2 h₂ mh₂H hag').symm
      rw [← hgeq₁, ← hgeq₂]
      exact restreq_of_agree hx hxeq hag
  have step5 : ∀ p ∈ labelPairs k,
      ((branchClass H (s.erase x) x p.1 p.2).image
        (fun h (y : s) => h y.val)).card ≤
      ((branchClass H (s.erase x) x p.1 p.2).image
        (fun h (y : s.erase x) => h y.val)).card := by
    intro p _
    apply Finset.card_le_card_of_injOn (restrictErase s x)
    · intro g hg
      rw [Finset.mem_coe] at hg
      obtain ⟨h, mh, rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_coe.mpr
      apply Finset.mem_image.mpr
      exact ⟨h, mh, (restrictErase_image s x h).symm⟩
    · intro g₁ hg₁ g₂ hg₂ heq
      rw [Finset.mem_coe] at hg₁ hg₂
      obtain ⟨h₁, mh₁, hgeq₁⟩ := Finset.mem_image.mp hg₁
      obtain ⟨h₂, mh₂, hgeq₂⟩ := Finset.mem_image.mp hg₂
      have hgeq₁' : ∀ v : s, h₁ v.val = g₁ v := fun v => congrFun hgeq₁ v
      have hgeq₂' : ∀ v : s, h₂ v.val = g₂ v := fun v => congrFun hgeq₂ v
      have hag : ∀ y ∈ s.erase x, h₁ y = h₂ y := by
        intro y hy
        have e := restrictErase_inj_on_erase s x heq ⟨y, hy⟩
        rw [← hgeq₁', ← hgeq₂'] at e
        exact e
      have e1 : h₁ x = p.1 := (Finset.mem_filter.mp mh₁).2.1
      have e2 : h₂ x = p.1 := (Finset.mem_filter.mp mh₂).2.1
      have hxeq : h₁ x = h₂ x := by rw [e1, e2]
      rw [← hgeq₁, ← hgeq₂]
      exact restreq_of_agree hx hxeq hag
  calc (H.image (fun h (y : s) => h y.val)).card
      ≤ ((uniqueClass H (s.erase x) x).image (fun h (y : s) => h y.val) ∪
          (labelPairs k).biUnion (fun p =>
            (branchClass H (s.erase x) x p.1 p.2).image
              (fun h (y : s) => h y.val))).card :=
        Finset.card_le_card himg
    _ ≤ ((uniqueClass H (s.erase x) x).image
          (fun h (y : s) => h y.val)).card +
          (((labelPairs k).biUnion (fun p =>
            (branchClass H (s.erase x) x p.1 p.2).image
              (fun h (y : s) => h y.val))).card) :=
        Finset.card_union_le _ _
    _ ≤ (H.image (fun h (y : s.erase x) => h y.val)).card +
          ∑ p ∈ labelPairs k, ((branchClass H (s.erase x) x p.1 p.2).image
            (fun h (y : s.erase x) => h y.val)).card := by
        apply add_le_add step4
        calc (((labelPairs k).biUnion (fun p =>
                (branchClass H (s.erase x) x p.1 p.2).image
                  (fun h (y : s) => h y.val))).card)
            ≤ ∑ p ∈ labelPairs k, ((branchClass H (s.erase x) x p.1 p.2).image
                (fun h (y : s) => h y.val)).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ p ∈ labelPairs k, ((branchClass H (s.erase x) x p.1 p.2).image
                (fun h (y : s.erase x) => h y.val)).card :=
              Finset.sum_le_sum (fun p hp => step5 p hp)

/-- Growth induction for the Natarajan lemma, by induction on a bound `n` for
the sample size. At `d = 0` all traces agree; at `d + 1` the fiber recursion
over an erased point combines the induction hypotheses. -/
private theorem natarajan_aux {α : Type*} [DecidableEq α] {k : ℕ} :
    ∀ (n d : ℕ) (H : Finset (α → Fin k)) (s : Finset α), s.card ≤ n →
      NDimLERel H s d → s.Nonempty →
      tracesCard H s ≤ s.card ^ d * k ^ (2 * d) := by
  intro n
  induction n with
  | zero =>
    intro d H s hle _ hsne
    rw [Nat.le_zero, Finset.card_eq_zero] at hle
    rw [hle] at hsne
    exact absurd hsne Finset.not_nonempty_empty
  | succ n IH =>
    intro d H s hle hrel hsne
    by_cases hk0 : k = 0
    · subst hk0
      have hHe : H = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro h _
        obtain ⟨x, _⟩ := hsne
        exact (h x).elim0
      rw [hHe]
      simp only [tracesCard, Finset.image_empty, Finset.card_empty]
      exact Nat.zero_le _
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      cases d with
      | zero =>
        have h1 : tracesCard H s ≤ 1 := by
          simp only [tracesCard, Finset.card_le_one]
          intro g₁ hg₁ g₂ hg₂
          obtain ⟨h₁, m₁, rfl⟩ := Finset.mem_image.mp hg₁
          obtain ⟨h₂, m₂, rfl⟩ := Finset.mem_image.mp hg₂
          funext y
          exact agree_of_relDim_zero hrel m₁ m₂ y.property
        have hrhs : s.card ^ 0 * k ^ (2 * 0) = 1 := by simp
        rw [hrhs]
        exact h1
      | succ d =>
        have hne : s.Nonempty := hsne
        obtain ⟨x, hx⟩ := hne
        by_cases hs' : s.erase x = ∅
        · have hcard1 : s.card = 1 := by
            have h := Finset.card_erase_of_mem hx
            rw [hs', Finset.card_empty] at h
            have hpos : 0 < s.card := Finset.card_pos.mpr hsne
            omega
          obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard1
          have hxa : a = x := (Finset.mem_singleton.mp hx).symm
          subst hxa
          rw [Finset.card_singleton, one_pow, one_mul]
          have hle_k : tracesCard H {a} ≤ k := by
            simp only [tracesCard]
            have huniv : (Finset.univ : Finset (Fin k)).card = k := by
              rw [Finset.card_univ, Fintype.card_fin]
            conv => rhs; rw [← huniv]
            apply Finset.card_le_card_of_injOn
              (fun g : ↥({a} : Finset α) → Fin k =>
                g ⟨a, Finset.mem_singleton_self a⟩)
            · intro g _
              rw [Finset.mem_coe]
              exact Finset.mem_univ _
            · intro g₁ _ g₂ _ heq
              funext y
              have hy : y = ⟨a, Finset.mem_singleton_self a⟩ :=
                Subtype.ext (Finset.mem_singleton.mp y.property)
              rw [hy]
              exact heq
          calc tracesCard H {a} ≤ k := hle_k
            _ = k ^ 1 := (pow_one k).symm
            _ ≤ k ^ (2 * (d + 1)) :=
                Nat.pow_le_pow_right hk1 (by omega)
        · have hs'ne : (s.erase x).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hs'
          have hcard' : (s.erase x).card ≤ n := by
            have h := Finset.card_erase_of_mem hx
            omega
          have hrel' : NDimLERel H (s.erase x) (d + 1) := by
            simp only [NDimLERel] at hrel ⊢
            intro T hT hcard
            exact hrel T (hT.trans (Finset.erase_subset _ _)) hcard
          have IH1 : tracesCard H (s.erase x) ≤
              (s.erase x).card ^ (d + 1) * k ^ (2 * (d + 1)) :=
            IH (d + 1) H (s.erase x) hcard' hrel' hs'ne
          have IH2 : ∀ p ∈ labelPairs k,
              tracesCard (branchClass H (s.erase x) x p.1 p.2)
                (s.erase x) ≤ (s.erase x).card ^ d * k ^ (2 * d) := by
            intro p hp
            have hab : p.1 ≠ p.2 := mem_labelPairs.mp hp
            have hrelp : NDimLERel (branchClass H (s.erase x) x p.1 p.2)
                (s.erase x) d :=
              relDim_drop hx hrel hab
            exact IH d _ _ hcard' hrelp hs'ne
          have hpairs : (labelPairs k).card ≤ k ^ 2 := by
            have hsub : labelPairs k ⊆ Finset.univ ×ˢ Finset.univ :=
              Finset.filter_subset _ _
            have hle := Finset.card_le_card hsub
            rw [Finset.card_product, Finset.card_univ,
              Fintype.card_fin] at hle
            rw [pow_two]; exact hle
          have hsum : ∑ p ∈ labelPairs k,
                tracesCard (branchClass H (s.erase x) x p.1 p.2)
                  (s.erase x) ≤
              k ^ 2 * ((s.erase x).card ^ d * k ^ (2 * d)) := by
            have h := Finset.sum_le_card_nsmul (labelPairs k) _ _
              (fun p hp => IH2 p hp)
            rw [nsmul_eq_mul] at h
            refine le_trans h ?_
            exact Nat.mul_le_mul_right _ hpairs
          have hpos : 0 < s.card := Finset.card_pos.mpr hsne
          obtain ⟨t, ht⟩ : ∃ t, s.card = t + 1 := ⟨s.card - 1, by omega⟩
          have hst : (s.erase x).card = t := by
            rw [Finset.card_erase_of_mem hx, ht, Nat.add_sub_cancel]
          rw [ht] at ⊢
          rw [hst] at IH1 hsum
          have hE : k ^ 2 * k ^ (2 * d) = k ^ (2 * (d + 1)) := by
            rw [← pow_add]
            congr 1
            ring
          have hfact : t ^ (d + 1) + t ^ d ≤ (t + 1) ^ (d + 1) := by
            have h1 : t ^ (d + 1) = t ^ d * t := pow_succ t d
            have h2 : (t + 1) ^ (d + 1) = (t + 1) ^ d * (t + 1) :=
              pow_succ (t + 1) d
            have h3 : t ^ d ≤ (t + 1) ^ d :=
              Nat.pow_le_pow_left (Nat.le_succ t) d
            calc t ^ (d + 1) + t ^ d = t ^ d * t + t ^ d := by rw [h1]
              _ = t ^ d * (t + 1) := by ring
              _ ≤ (t + 1) ^ d * (t + 1) := by
                  exact Nat.mul_le_mul_right _ h3
              _ = (t + 1) ^ (d + 1) := by rw [h2]
          calc tracesCard H s
              ≤ tracesCard H (s.erase x) + ∑ p ∈ labelPairs k,
                  tracesCard (branchClass H (s.erase x) x p.1 p.2)
                    (s.erase x) :=
                tracesCard_erase_le H s x hx
            _ ≤ t ^ (d + 1) * k ^ (2 * (d + 1)) +
                  k ^ 2 * (t ^ d * k ^ (2 * d)) :=
                add_le_add IH1 hsum
            _ = (t ^ (d + 1) + t ^ d) * k ^ (2 * (d + 1)) := by
                rw [← hE]
                ring
            _ ≤ (t + 1) ^ (d + 1) * k ^ (2 * (d + 1)) :=
                Nat.mul_le_mul_right _ hfact

/-- Finite-class core of the Natarajan lemma: if `H` has Natarajan dimension
at most `d`, the number of distinct restrictions of `H` to any nonempty
sample `s` is at most `s.card ^ d * k ^ (2 * d)`.

Corners: the empty sample is excluded by `hs` (a single empty restriction
would exceed `0 ^ d * k ^ (2 * d) = 0` for `d ≥ 1`); the empty class gives
zero restrictions; `k = 0` forces the class empty on a nonempty sample; at
`k = 1` no nonempty set is N-shattered and the bound holds trivially. -/
private theorem natarajan_lemma {α : Type*} [DecidableEq α] {k : ℕ}
    (H : Finset (α → Fin k)) (d : ℕ) (hd : NDimLE H d) (s : Finset α)
    (hs : s.Nonempty) :
    tracesCard H s ≤ s.card ^ d * k ^ (2 * d) := by
  have hrel : NDimLERel H s d := fun T _ hcard => hd T hcard
  exact natarajan_aux _ _ H s le_rfl hrel hs

end FinCore

/-- Under `NDimLE C 0`, any two concepts in `C` agree at every point: a
disagreement at `x` would N-shatter the singleton `{x}`. -/
theorem nDimLE_zero {α β : Type*} (C : ConceptClass α β)
    (hd : NDimLE C 0) (c₁ c₂ : α → β) (m₁ : c₁ ∈ C) (m₂ : c₂ ∈ C)
    (x : α) : c₁ x = c₂ x := by
  by_contra hne
  apply hd {x} (Finset.card_singleton x)
  refine ⟨c₁, c₂, ?_, ?_⟩
  · intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact hne
  · intro t ht
    obtain rfl | rfl := Finset.subset_singleton_iff.mp ht
    · exact ⟨c₁, m₁, fun z hz => absurd hz (Finset.notMem_empty z),
        fun z _ _ => rfl⟩
    · exact ⟨c₂, m₂, fun z _ => rfl,
        fun z hz1 hz2 => absurd hz1 hz2⟩

/-- Private `Fin k` set-based lemma, retained as the transport target for
the general finite-label case. If `C` has Natarajan dimension at most `d`,
the number of distinct restrictions of `C` to any nonempty sample `s` is at
most `s.card ^ d * k ^ (2 * d)`. -/
private theorem natarajan_lemma_fin {α : Type*} {k : ℕ}
    (C : ConceptClass α (Fin k)) (d : ℕ) (hd : NDimLE C d) (s : Finset α)
    (hs : s.Nonempty) :
    tracesCard C s ≤ s.card ^ d * k ^ (2 * d) := by
  classical
  -- Explicit pointwise choice: one witness concept per realized labeling.
  have hmem : ∀ t : { g : s → Fin k // ∃ c ∈ C, ∀ x : s, c x.val = g x },
      ∃ c ∈ C, ∀ x : s, c x.val = t.val x :=
    fun t => t.property
  -- The finite witness class, via its finite range of witnesses.
  have hfin : (Set.range fun t : { g : s → Fin k //
      ∃ c ∈ C, ∀ x : s, c x.val = g x } =>
      Classical.choose (hmem t)).Finite :=
    Set.finite_range _
  obtain ⟨W, hW⟩ := hfin.exists_finset_coe
  -- Every witness lies in `C`.
  have hWsub : (↑W : Set (α → Fin k)) ⊆ C := by
    intro w hw
    rw [hW] at hw
    obtain ⟨t, ht⟩ := Set.mem_range.mp hw
    rw [← ht]
    exact (Classical.choose_spec (hmem t)).1
  -- The witness class realizes exactly the same traces.
  have htraces : FinCore.tracesCard W s = tracesCard C s := by
    unfold FinCore.tracesCard tracesCard
    congr 1
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hWsub (Finset.mem_coe.mpr hw), fun x => rfl⟩
    · rintro ⟨c, hc, hcg⟩
      refine ⟨Classical.choose (hmem ⟨g, c, hc, hcg⟩), ?_, ?_⟩
      · rw [← Finset.mem_coe, hW]
        exact ⟨_, rfl⟩
      · have hspec := (Classical.choose_spec (hmem ⟨g, c, hc, hcg⟩)).2
        exact funext fun x => hspec x
  -- The dimension bound transfers to the finite witness subclass.
  have hWdim : FinCore.NDimLE W d := by
    intro s' hcard' hsh
    apply hd s' hcard'
    obtain ⟨f₀, f₁, hne, hwit⟩ := hsh
    refine ⟨f₀, f₁, hne, fun t ht => ?_⟩
    obtain ⟨h, mh, h1, h0⟩ := hwit t ht
    exact ⟨h, hWsub (Finset.mem_coe.mpr mh), h1, h0⟩
  rw [← htraces]
  exact FinCore.natarajan_lemma W d hWdim s hs

/-- The Natarajan lemma: if `C` over a finite label type has Natarajan
dimension at most `d`, the number of distinct restrictions of `C` to any
nonempty sample `s` is at most `s.card ^ d * (Fintype.card β) ^ (2 * d)`.
The class may be infinite: the `Fin` case chooses one witness concept in
`C` per realized labeling and applies the finite-class core; the general
case is transported along `β ≃ Fin (Fintype.card β)`.

Corners: the empty sample is excluded by `hs` (a single empty restriction
would exceed `0 ^ d * k ^ (2 * d) = 0` for `d ≥ 1` with `k` the label
cardinality); the empty class gives zero restrictions; `Fintype.card β = 0`
forces no realized labeling on a nonempty sample; at `Fintype.card β = 1`
no nonempty set is N-shattered and the bound holds trivially. -/
theorem natarajan_lemma {α β : Type*} [Fintype β]
    (C : ConceptClass α β) (d : ℕ) (hd : NDimLE C d) (s : Finset α)
    (hs : s.Nonempty) :
    tracesCard C s ≤ s.card ^ d * (Fintype.card β) ^ (2 * d) := by
  classical
  set k := Fintype.card β with hk
  set e := Fintype.equivFin β with he
  set C' : ConceptClass α (Fin k) :=
    { h' | ∃ c ∈ C, ∀ x, e (c x) = h' x } with hC'
  have hC'mem : ∀ h' : α → Fin k,
      h' ∈ C' ↔ ∃ c ∈ C, ∀ x, e (c x) = h' x := by
    intro h'
    rw [hC']
    rfl
  have hd' : NDimLE C' d := by
    intro s' hcard' hsh'
    apply hd s' hcard'
    obtain ⟨f₀', f₁', hne', hwit'⟩ := hsh'
    refine ⟨fun x => e.symm (f₀' x), fun x => e.symm (f₁' x), ?_, ?_⟩
    · intro x hx hcon
      exact hne' x hx (e.symm.injective hcon)
    · intro t ht
      obtain ⟨h', mh', h1', h0'⟩ := hwit' t ht
      obtain ⟨c, mc, hceq⟩ := (hC'mem _).mp mh'
      refine ⟨c, mc, fun x hxt => ?_, fun x hxs hxt => ?_⟩
      · have h1x := h1' x hxt
        have heq : e (c x) = f₁' x := (hceq x).trans h1x
        have hcon := congrArg e.symm heq
        rw [e.symm_apply_apply] at hcon
        exact hcon
      · have h0x := h0' x hxs hxt
        have heq : e (c x) = f₀' x := (hceq x).trans h0x
        have hcon := congrArg e.symm heq
        rw [e.symm_apply_apply] at hcon
        exact hcon
  have htraces : tracesCard C s = tracesCard C' s := by
    unfold tracesCard
    apply Finset.card_bij' (fun g _ => fun x : s => e (g x))
      (fun g' _ => fun x : s => e.symm (g' x))
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      obtain ⟨c, mc, hcg⟩ := hg
      refine ⟨fun x => e (c x), (hC'mem _).mpr ⟨c, mc, ?_⟩, ?_⟩
      · intro x
        rfl
      · intro x
        change e (c x.val) = e (g x)
        rw [hcg x]
    · intro g' hg'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg' ⊢
      obtain ⟨c', mc', hcg'⟩ := hg'
      obtain ⟨c, mc, hceq⟩ := (hC'mem _).mp mc'
      refine ⟨c, mc, fun x => ?_⟩
      have h1 : e (c x.val) = c' x.val := hceq x.val
      have heq : e (c x.val) = g' x := h1.trans (hcg' x)
      have hcon := congrArg e.symm heq
      rw [e.symm_apply_apply] at hcon
      exact hcon
    · intro g hg
      funext x
      simp only [e.symm_apply_apply]
    · intro g' hg'
      funext x
      simp only [e.apply_symm_apply]
  have hbound := natarajan_lemma_fin C' d hd' s hs
  rw [htraces]
  exact hbound

/-- The set-based trace count on a coerced finite class agrees with the
image-of-finite-class count. -/
theorem tracesCard_coe_finset {α β : Type*} [Fintype β] [DecidableEq β]
    (H : Finset (α → β)) (s : Finset α) :
    tracesCard (↑H : ConceptClass α β) s =
      (H.image fun h (x : s) => h x.val).card := by
  unfold tracesCard
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_coe]
  constructor
  · rintro ⟨c, hc, hcg⟩
    exact ⟨c, hc, funext hcg⟩
  · rintro ⟨h, mh, rfl⟩
    exact ⟨h, mh, fun x => rfl⟩

/-- Finite-class corollary of the Natarajan lemma, stated with a `Finset`
throughout: the dimension hypothesis takes the coerced class and the
conclusion counts the image of the finite class. -/
theorem natarajan_lemma_finset {α β : Type*} [Fintype β] [DecidableEq β]
    (H : Finset (α → β)) (d : ℕ)
    (hd : NDimLE (↑H : ConceptClass α β) d) (s : Finset α)
    (hs : s.Nonempty) :
    (H.image fun h (x : s) => h x.val).card ≤
      s.card ^ d * (Fintype.card β) ^ (2 * d) := by
  rw [← tracesCard_coe_finset]
  exact natarajan_lemma _ d hd s hs

end Cslib.MachineLearning.PACLearning
