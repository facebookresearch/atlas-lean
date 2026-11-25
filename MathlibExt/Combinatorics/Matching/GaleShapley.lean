/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import MathlibExt.Order.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- **Strict preference order.** A strict total order on a type $\alpha$ is a binary relation
$<$ on $\alpha$ that is irreflexive ($a < a$ holds for no $a$), transitive ($a < b$ and $b < c$
imply $a < c$) and total on distinct elements ($a \ne b$ implies $a < b$ or $b < a$). In the
Gale–Shapley development it models strict preference. -/
abbrev StrictTotalOrder := MathlibExt.Order.StrictTotalOrder

namespace StrictTotalOrder

/-- **Building a strict total order from a relation.** A binary relation $<$ on a set $\alpha$
that is irreflexive ($a \not< a$ for all $a$), transitive ($a < b$ and $b < c$ imply $a < c$) and
total on distinct elements ($a \ne b$ implies $a < b$ or $b < a$) defines a strict total order on
$\alpha$ whose relation is $<$. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- **Relation of a strict total order.** The relation of a strict total order $T$ on a set
$\alpha$ is its underlying binary relation $<_T$ on $\alpha$, which is irreflexive, transitive,
and relates any two distinct elements in one direction or the other. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- **Irreflexivity of a strict total order.** Let $T$ be a strict total order on a set $\alpha$,
with relation $<_T$. Then $a <_T a$ fails for every $a \in \alpha$. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- **Transitivity of a strict total order.** Let $<$ be the relation of a strict total order on a
type $\alpha$. If $a, b, c \in \alpha$ satisfy $a < b$ and $b < c$, then $a < c$. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- **Strict total orders are total on distinct elements.** Let $<$ be the relation of a strict
total order on a type $\alpha$. If $a, b \in \alpha$ and $a \ne b$, then $a < b$ or $b < a$. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

/-- **Strict total orders are determined by their relation.** Let $T$ and $T'$ be strict total
orders on a set $\alpha$, with relations $<_T$ and $<_{T'}$. If $x <_T y \iff x <_{T'} y$ for all
$x, y \in \alpha$, then $T = T'$. -/
@[ext]
theorem ext {α : Type*} {T T' : StrictTotalOrder α} (h : T.lt = T'.lt) :
    T = T' :=
  MathlibExt.Order.StrictTotalOrder.ext h

/-- Compatibility instance for the former `GaleShapley` order instance.

For new code, use `MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder` directly. -/
instance isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt :=
  MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder T

end StrictTotalOrder

/-- **Men's preferences.** For sets $M$ (men) and $W$ (women), a preference profile of the men
assigns to each $m \in M$ a strict total order on $W$, the preferences of $m$. -/
abbrev MPrefs (M W : Type*) := M → StrictTotalOrder W

/-- **Women's preference profile.** For types $M$ and $W$, a preference profile of $W$ over $M$
assigns to each $w \in W$ a strict total order on $M$, read as the strict preference of $w$
among the elements of $M$. -/
abbrev WPrefs (M W : Type*) := W → StrictTotalOrder M

/-- **Perfect matching.** A perfect matching between sets $M$ and $W$ is a bijection
$\mu \colon M \to W$, which matches each $m \in M$ with $\mu(m) \in W$. -/
abbrev PerfectMatching (M W : Type*) := M ≃ W

/-- **Blocking pair.** Let $M$ and $W$ be sets. Suppose that each $m \in M$ has a strict total
order $<_m$ of preference on $W$ and each $w \in W$ has a strict total order $<_w$ of preference
on $M$, where $x <_m y$ means that $m$ prefers $x$ to $y$, and likewise for $<_w$. For a perfect
matching $\mu$ between $M$ and $W$, a pair $(m, w) \in M \times W$ is a blocking pair when
$w <_m \mu(m)$ and $m <_w \mu^{-1}(w)$, that is, when $m$ prefers $w$ to $\mu(m)$ and $w$ prefers
$m$ to $\mu^{-1}(w)$. -/
def IsBlockingPair {M W : Type*}
    (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) (m : M) (w : W) : Prop :=
  (mp m).lt w (μ m) ∧ (wp w).lt m (μ.symm w)

/-- **Stable perfect matching.** Let $M$ and $W$ be sets. Suppose that each $m \in M$ has a strict
total order of preference on $W$ and each $w \in W$ has a strict total order of preference on
$M$. A perfect matching $\mu$ between $M$ and $W$ is stable for these preferences when no pair
$(m, w) \in M \times W$ is a blocking pair for $\mu$. -/
def IsStable {M W : Type*} (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair mp wp μ m w

theorem isBlockingPair_iff {M W : Type*} (mp : MPrefs M W) (wp : WPrefs M W)
    (μ : PerfectMatching M W) (m : M) (w : W) :
    IsBlockingPair mp wp μ m w ↔ (mp m).lt w (μ m) ∧ (wp w).lt m (μ.symm w) :=
  Iff.rfl

theorem isStable_iff {M W : Type*} (mp : MPrefs M W) (wp : WPrefs M W)
    (μ : PerfectMatching M W) : IsStable mp wp μ ↔ ∀ m w, ¬ IsBlockingPair mp wp μ m w :=
  Iff.rfl


/-! ## Proof of Gale–Shapley via the men-proposing deferred-acceptance algorithm.

State: each man records the women he proposed to (`prop`); each woman holds her best
proposer so far (`hold`). A free man who has not proposed everywhere proposes to his
favourite remaining woman; she keeps the better of her old holder and the new proposer.
The number of proposals strictly grows each step and is bounded by `|M| * |W|`, so after
`K = |M| * |W| + 1` steps no man can propose; that state yields a stable matching. -/

/-- A nonempty finset has a strictly-least element under a strict total order. -/
private lemma sto_exists_minimal {α : Type*} (T : StrictTotalOrder α) :
    ∀ (s : Finset α), s.Nonempty → ∃ x ∈ s, ∀ y ∈ s, x ≠ y → T.lt x y := by
  classical
  intro s
  induction s using Finset.induction
  case empty =>
    intro h
    exact (Finset.not_nonempty_empty h).elim
  case insert a s _ha ih =>
    intro h
    by_cases hs : s.Nonempty
    · obtain ⟨x, hxs, hmin⟩ := ih hs
      by_cases hax : a = x
      · refine ⟨x, Finset.mem_insert_of_mem hxs, fun y hy hne => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact absurd hax.symm hne
        · exact hmin y hys hne
      · rcases T.total hax with hlt | hlt
        · refine ⟨a, Finset.mem_insert_self a s, fun y hy hne => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hys
          · exact absurd rfl hne
          · by_cases hyx : y = x
            · subst hyx
              exact hlt
            · exact T.trans hlt (hmin y hys (Ne.symm hyx))
        · refine ⟨x, Finset.mem_insert_of_mem hxs, fun y hy hne => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hys
          · exact hlt
          · exact hmin y hys hne
    · have hsempty : s = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hs ⟨x, hx⟩)
      refine ⟨a, Finset.mem_insert_self a s, fun y hy hne => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact absurd rfl hne
      · rw [hsempty] at hys
        exact (Finset.notMem_empty y hys).elim

/-- Deferred-acceptance state. -/
private structure DAState (M W : Type*) where
  prop : M → Finset W
  hold : W → Option M

/-- A man is free if no woman holds him. -/
private def DAState.Free {M W : Type*} (s : DAState M W) (m : M) : Prop :=
  ∀ w, s.hold w ≠ some m

/-- A man can propose if he is free and has not proposed to every woman. -/
private def DAState.CanPropose {M W : Type*} (s : DAState M W) (m : M) : Prop :=
  s.Free m ∧ ∃ w, w ∉ s.prop m

/-- No man can propose. -/
private def DAState.Done {M W : Type*} (s : DAState M W) : Prop :=
  ∀ m, ¬ s.CanPropose m

/-- A woman picks between her old holder `o` and a new proposer `m`. -/
private lemma womanChoice_exists {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) :
    ∃ mstar : M, (o = none ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 = m ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m m1 ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m1 m ∧ mstar = m1) := by
  cases o with
  | none => exact ⟨m, Or.inl ⟨rfl, rfl⟩⟩
  | some m' =>
    by_cases h1 : m' = m
    · subst m'
      exact ⟨m, Or.inr (Or.inl ⟨m, rfl, rfl, rfl⟩)⟩
    · by_cases h2 : T.lt m m'
      · exact ⟨m, Or.inr (Or.inr (Or.inl ⟨m', rfl, h1, h2, rfl⟩))⟩
      · have h3 : T.lt m' m := by
          rcases T.total h1 with h | h
          · exact h
          · exact absurd h h2
        exact ⟨m', Or.inr (Or.inr (Or.inr ⟨m', rfl, h1, h3, rfl⟩))⟩

private noncomputable def womanChoice {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) : M :=
  Classical.choose (womanChoice_exists T o m)

/-- Case analysis on the woman's choice. -/
private lemma womanChoice_spec {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) :
    (o = none ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 = m ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m m1 ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m1 m ∧ womanChoice T o m = m1) := by
  unfold womanChoice
  exact Classical.choose_spec (womanChoice_exists T o m)

/-- One proposal step: free man `m0` proposes to `w0`, who keeps the better candidate. -/
private noncomputable def dostep {M W : Type*} [DecidableEq M] [DecidableEq W]
    (_mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W) :
    DAState M W :=
  { prop := fun m' => if m' = m0 then insert w0 (s.prop m0) else s.prop m',
    hold := fun w' =>
      if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w' }

private lemma dostep_prop {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
    (m' : M) :
    (dostep mp wp s m0 w0).prop m' =
      (if m' = m0 then insert w0 (s.prop m0) else s.prop m') := rfl

private lemma dostep_hold {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
    (w' : W) :
    (dostep mp wp s m0 w0).hold w' =
      (if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w') :=
  rfl

/-- Algorithm invariants: holders exist for proposed-to women; holders were proposed to;
holders are best among proposers; holders are unique; proposals go in preference order. -/
private def DAInv {M W : Type*}
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) : Prop :=
  (∀ w m', w ∈ s.prop m' → ∃ m, s.hold w = some m) ∧
  (∀ w m, s.hold w = some m → w ∈ s.prop m) ∧
  (∀ w m, s.hold w = some m → ∀ m', w ∈ s.prop m' → m' = m ∨ (wp w).lt m m') ∧
  (∀ m w₁ w₂, s.hold w₁ = some m → s.hold w₂ = some m → w₁ = w₂) ∧
  (∀ m w w', w ∈ s.prop m → w' ∉ s.prop m → w ≠ w' → (mp m).lt w w')

/-- A proposal step preserves the invariants. -/
private lemma dostep_preserves {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
    (hfree : s.Free m0) (_hnew : w0 ∉ s.prop m0)
    (hfav : ∀ y, y ∉ s.prop m0 → w0 ≠ y → (mp m0).lt w0 y)
    (hinv : DAInv mp wp s) : DAInv mp wp (dostep mp wp s m0 w0) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hinv
  have hp : ∀ m', (dostep mp wp s m0 w0).prop m' =
      (if m' = m0 then insert w0 (s.prop m0) else s.prop m') :=
    fun m' => dostep_prop mp wp s m0 w0 m'
  have hh : ∀ w', (dostep mp wp s m0 w0).hold w' =
      (if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w') :=
    fun w' => dostep_hold mp wp s m0 w0 w'
  have inv0 : (∀ w m', w ∈ (dostep mp wp s m0 w0).prop m' →
      ∃ m, (dostep mp wp s m0 w0).hold w = some m) := by
    intro w m' hm'
    rw [hp] at hm'
    by_cases he : m' = m0
    · rw [ite_eq_left he] at hm'
      by_cases hww : w = w0
      · rw [hww]
        refine ⟨womanChoice (wp w0) (s.hold w0) m0, ?_⟩
        rw [hh, ite_eq_left rfl]
      · rw [Finset.mem_insert] at hm'
        rcases hm' with hcontra | hmold
        · exact absurd hcontra hww
        · obtain ⟨m, hm⟩ := h0 w m0 hmold
          exact ⟨m, by rw [hh, ite_eq_right hww]; exact hm⟩
    · rw [ite_eq_right he] at hm'
      obtain ⟨m, hm⟩ := h0 w m' hm'
      by_cases hww : w = w0
      · rw [hww]
        refine ⟨womanChoice (wp w0) (s.hold w0) m0, ?_⟩
        rw [hh, ite_eq_left rfl]
      · exact ⟨m, by rw [hh, ite_eq_right hww]; exact hm⟩
  have inv4 : (∀ m w w', w ∈ (dostep mp wp s m0 w0).prop m →
      w' ∉ (dostep mp wp s m0 w0).prop m → w ≠ w' → (mp m).lt w w') := by
    intro m w w' hw hw' hne
    rw [hp] at hw
    rw [hp] at hw'
    by_cases he : m = m0
    · rw [ite_eq_left he] at hw
      rw [ite_eq_left he] at hw'
      rw [Finset.mem_insert] at hw
      rw [Finset.mem_insert, not_or] at hw'
      obtain ⟨hne0, hout⟩ := hw'
      rcases hw with hweq | hmold
      · rw [hweq, he]
        exact hfav w' hout (Ne.symm hne0)
      · rw [he]
        exact h4 m0 w w' hmold hout hne
    · rw [ite_eq_right he] at hw
      rw [ite_eq_right he] at hw'
      exact h4 m w w' hw hw' hne
  have inv1 : (∀ w m, (dostep mp wp s m0 w0).hold w = some m →
      w ∈ (dostep mp wp s m0 w0).prop m) := by
    intro w m hm
    rw [hh] at hm
    by_cases hww : w = w0
    · rw [hww] at hm ⊢
      rw [ite_eq_left rfl] at hm
      have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
        (Option.some_injective _ hm).symm
      subst hmw
      rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
        ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, hne, _, hw⟩
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_right hne]
        exact h1 w0 m1 ho
    · rw [ite_eq_right hww] at hm
      have hmem := h1 w m hm
      rw [hp]
      by_cases he : m = m0
      · rw [ite_eq_left he]
        rw [he] at hmem
        exact Finset.mem_insert_of_mem hmem
      · rw [ite_eq_right he]
        exact hmem
  have inv2 : (∀ w m, (dostep mp wp s m0 w0).hold w = some m → ∀ m',
      w ∈ (dostep mp wp s m0 w0).prop m' → m' = m ∨ (wp w).lt m m') := by
    intro w m hm m' hm'
    rw [hh] at hm
    rw [hp] at hm'
    by_cases hww : w = w0
    · rw [hww] at hm hm' ⊢
      rw [ite_eq_left rfl] at hm
      have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
        (Option.some_injective _ hm).symm
      subst hmw
      by_cases he : m' = m0
      · rw [ite_eq_left he] at hm'
        subst m'
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, hne, hlt, hw⟩
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inr hlt
      · rw [ite_eq_right he] at hm'
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨ho, _⟩ | ⟨m1, ho, hmeq, hw⟩ | ⟨m1, ho, _, hlt, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · obtain ⟨mx, hmold⟩ := h0 w0 m' hm'
          rw [ho] at hmold
          cases hmold
        · subst m1
          rw [hw]
          exact h2 w0 m0 ho m' hm'
        · rw [hw]
          rcases h2 w0 m1 ho m' hm' with hme | hlt'
          · rw [hme]
            exact Or.inr hlt
          · exact Or.inr ((wp w0).trans hlt hlt')
        · rw [hw]
          exact h2 w0 m1 ho m' hm'
    · rw [ite_eq_right hww] at hm
      by_cases he : m' = m0
      · rw [ite_eq_left he] at hm'
        rw [Finset.mem_insert] at hm'
        rcases hm' with hweq | hmold
        · exact (hww hweq).elim
        · rw [he]
          exact h2 w m hm m0 hmold
      · rw [ite_eq_right he] at hm'
        exact h2 w m hm m' hm'
  have inv3 : (∀ m w₁ w₂, (dostep mp wp s m0 w0).hold w₁ = some m →
      (dostep mp wp s m0 w0).hold w₂ = some m → w₁ = w₂) := by
    intro m w₁ w₂ h₁ h₂
    rw [hh] at h₁
    rw [hh] at h₂
    by_cases hww1 : w₁ = w0
    · by_cases hww2 : w₂ = w0
      · exact hww1.trans hww2.symm
      · rw [hww1] at h₁ ⊢
        rw [ite_eq_left rfl] at h₁
        rw [ite_eq_right hww2] at h₂
        have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
          (Option.some_injective _ h₁).symm
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm1 : m = m1 := hmw.trans hw
          rw [hm1] at h₂
          exact h3 m1 w0 w₂ ho h₂
    · by_cases hww2 : w₂ = w0
      · rw [hww2] at h₂ ⊢
        rw [ite_eq_right hww1] at h₁
        rw [ite_eq_left rfl] at h₂
        have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
          (Option.some_injective _ h₂).symm
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm1 : m = m1 := hmw.trans hw
          rw [hm1] at h₁
          exact h3 m1 w₁ w0 h₁ ho
      · rw [ite_eq_right hww1] at h₁
        rw [ite_eq_right hww2] at h₂
        exact h3 m w₁ w₂ h₁ h₂
  exact ⟨inv0, inv1, inv2, inv3, inv4⟩

/-- Total number of proposals made so far. -/
private def DAMeasure {M W : Type*} [Fintype M] (s : DAState M W) : ℕ :=
  ∑ m ∈ Finset.univ, (s.prop m).card

/-- Each proposal step adds exactly one proposal. -/
private lemma dostep_measure {M W : Type*} [Fintype M] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
    (hnew : w0 ∉ s.prop m0) :
    DAMeasure (dostep mp wp s m0 w0) = DAMeasure s + 1 := by
  change (∑ m ∈ Finset.univ, ((dostep mp wp s m0 w0).prop m).card) =
    (∑ m ∈ Finset.univ, (s.prop m).card) + 1
  have hp : ∀ m', (dostep mp wp s m0 w0).prop m' =
      (if m' = m0 then insert w0 (s.prop m0) else s.prop m') :=
    fun m' => dostep_prop mp wp s m0 w0 m'
  have e1 : ((dostep mp wp s m0 w0).prop m0).card +
      ∑ x ∈ Finset.univ.erase m0, ((dostep mp wp s m0 w0).prop x).card =
      ∑ x ∈ Finset.univ, ((dostep mp wp s m0 w0).prop x).card :=
    Finset.add_sum_erase Finset.univ
      (fun x => ((dostep mp wp s m0 w0).prop x).card) (Finset.mem_univ m0)
  have e2 : (s.prop m0).card + ∑ x ∈ Finset.univ.erase m0, (s.prop x).card =
      ∑ x ∈ Finset.univ, (s.prop x).card :=
    Finset.add_sum_erase Finset.univ
      (fun x => (s.prop x).card) (Finset.mem_univ m0)
  have e3 : (∑ x ∈ Finset.univ.erase m0, ((dostep mp wp s m0 w0).prop x).card) =
      ∑ x ∈ Finset.univ.erase m0, (s.prop x).card := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp, ite_eq_right (Finset.ne_of_mem_erase hx)]
  have e4 : ((dostep mp wp s m0 w0).prop m0).card = (s.prop m0).card + 1 := by
    rw [hp, ite_eq_left rfl, Finset.card_insert_of_notMem hnew]
  omega

/-- The measure is bounded by `|M| * |W|`. -/
private lemma DAMeasure_le {M W : Type*} [Fintype M] [Fintype W]
    (s : DAState M W) : DAMeasure s ≤ Fintype.card M * Fintype.card W := by
  unfold DAMeasure
  calc ∑ m ∈ Finset.univ, (s.prop m).card
      ≤ Finset.univ.card • Fintype.card W :=
        Finset.sum_le_card_nsmul _ _ _ (fun m _ => Finset.card_le_univ _)
    _ = Fintype.card M * Fintype.card W := by
        rw [Finset.card_univ, smul_eq_mul]

/-- The remaining-proposal set of the chosen man is nonempty. -/
private lemma dastepNe {M W : Type*} [Fintype W] [DecidableEq W]
    (_mp : MPrefs M W) (s : DAState M W) (h : ∃ m, s.CanPropose m) :
    (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h))).Nonempty := by
  obtain ⟨_hmfree, w, hw⟩ := Classical.choose_spec h
  exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩

/-- One algorithm step: the chosen free man proposes to his favourite remaining woman. -/
private noncomputable def dastep {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) : DAState M W :=
  dostep mp wp s (Classical.choose h)
    (Classical.choose (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h)))

/-- Characterisation of the algorithm step. -/
private lemma dastep_spec {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) :
    ∃ m0 w0, s.Free m0 ∧ w0 ∉ s.prop m0 ∧
      (∀ y, y ∉ s.prop m0 → w0 ≠ y → (mp m0).lt w0 y) ∧
      dastep mp wp s h = dostep mp wp s m0 w0 := by
  refine ⟨Classical.choose h,
    Classical.choose (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h)), (Classical.choose_spec h).1, ?_, ?_, rfl⟩
  · exact (Finset.mem_filter.mp
      (Classical.choose_spec (sto_exists_minimal (mp (Classical.choose h))
        (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
        (dastepNe mp s h))).1).2
  · intro y hy hne
    exact (Classical.choose_spec (sto_exists_minimal (mp (Classical.choose h))
      (Finset.univ.filter (fun w => w ∉ s.prop (Classical.choose h)))
      (dastepNe mp s h))).2 y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩) hne

private lemma dastep_preserves {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) (hinv : DAInv mp wp s) :
    DAInv mp wp (dastep mp wp s h) := by
  obtain ⟨m0, w0, hfree, hnew, hfav, heq⟩ := dastep_spec mp wp s h
  rw [heq]
  exact dostep_preserves mp wp s m0 w0 hfree hnew hfav hinv

private lemma dastep_measure {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W)
    (h : ∃ m, s.CanPropose m) :
    DAMeasure (dastep mp wp s h) = DAMeasure s + 1 := by
  obtain ⟨m0, w0, hfree, hnew, hfav, heq⟩ := dastep_spec mp wp s h
  rw [heq]
  exact dostep_measure mp wp s m0 w0 hnew

/-- Initial state: no proposals, no holders. -/
private def dainit {M W : Type*} : DAState M W :=
  { prop := fun _ => ∅, hold := fun _ => none }

private lemma dainit_inv {M W : Type*}
    (mp : MPrefs M W) (wp : WPrefs M W) : DAInv mp wp dainit := by
  refine ⟨fun w m' hw => ?_, fun w m hw => ?_, fun w m hw => ?_,
    fun m w₁ w₂ h₁ h₂ => ?_, fun m w w' hw => ?_⟩
  · simp [dainit] at hw
  · simp [dainit] at hw
  · simp [dainit] at hw
  · simp [dainit] at h₁
  · simp [dainit] at hw

private lemma dainit_measure {M W : Type*} [Fintype M] :
    DAMeasure (dainit : DAState M W) = 0 := by
  simp [DAMeasure, dainit]

/-- Run the algorithm for `n` steps (stopping early once done). -/
private noncomputable def darun {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M]
    [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) : ℕ → DAState M W → DAState M W
  | 0, s => s
  | n + 1, s =>
    @dite _ _ (Classical.propDecidable _) (fun h : ∃ m, s.CanPropose m =>
      darun mp wp n (dastep mp wp s h)) (fun _ => s)

private lemma darun_inv {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (n : ℕ) (s : DAState M W)
    (hinv : DAInv mp wp s) : DAInv mp wp (darun mp wp n s) := by
  induction n generalizing s with
  | zero => simpa [darun] using hinv
  | succ n ih =>
    by_cases h : ∃ m, s.CanPropose m
    · have e : darun mp wp (n + 1) s = darun mp wp n (dastep mp wp s h) := by
        simp only [darun, dite_eq_left h]
      rw [e]
      exact ih _ (dastep_preserves mp wp s h hinv)
    · have e : darun mp wp (n + 1) s = s := by simp only [darun, dite_eq_right h]
      rw [e]
      exact hinv

private lemma darun_grows {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (n : ℕ) (s : DAState M W)
    (hinv : DAInv mp wp s) :
    (darun mp wp n s).Done ∨ DAMeasure (darun mp wp n s) ≥ DAMeasure s + n := by
  induction n generalizing s with
  | zero => exact Or.inr (by simp [darun])
  | succ n ih =>
    by_cases h : ∃ m, s.CanPropose m
    · have e : darun mp wp (n + 1) s = darun mp wp n (dastep mp wp s h) := by
        simp only [darun, dite_eq_left h]
      rw [e]
      have hinv' := dastep_preserves mp wp s h hinv
      have hmeas := dastep_measure mp wp s h
      rcases ih _ hinv' with hd | hg
      · exact Or.inl hd
      · exact Or.inr (by omega)
    · have e : darun mp wp (n + 1) s = s := by simp only [darun, dite_eq_right h]
      rw [e]
      exact Or.inl (fun m hm => h ⟨m, hm⟩)

/-- **Existence of stable perfect matchings.** Let $M$ and $W$ be finite sets with the same
number of elements. Suppose that each $m \in M$ has a strict total order of preference on $W$ and
each $w \in W$ has a strict total order of preference on $M$. Then some perfect matching between
$M$ and $W$ is stable for these preferences.

This is the Gale–Shapley theorem, stated without decidability assumptions on $M$ and $W$. -/
theorem gale_shapley_exists_stable_matching_general
    {M W : Type*} [Fintype M] [Fintype W]
    (hCard : Fintype.card M = Fintype.card W)
    (mp : MPrefs M W) (wp : WPrefs M W) :
    ∃ μ : PerfectMatching M W, IsStable mp wp μ := by
  classical
  rcases isEmpty_or_nonempty M with hE | hNE
  · have hW0 : Fintype.card W = 0 := by
      rw [← hCard]
      exact @Fintype.card_eq_zero M _ hE
    have hW : IsEmpty W := Fintype.card_eq_zero_iff.mp hW0
    refine ⟨@Equiv.equivOfIsEmpty M W hE hW, fun m w => ?_⟩
    exact (@IsEmpty.false M hE m).elim
  · have m₀ : M := Classical.choice hNE
    have hposM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨m₀⟩
    have hposW : 0 < Fintype.card W := by omega
    set K := Fintype.card M * Fintype.card W + 1 with hK
    set s := darun mp wp K dainit with hs
    have hinv : DAInv mp wp s := darun_inv mp wp K dainit (dainit_inv mp wp)
    have hdone : s.Done := by
      rcases darun_grows mp wp K dainit (dainit_inv mp wp) with hd | hg
      · exact hd
      · exfalso
        have hle := DAMeasure_le (darun mp wp K dainit)
        rw [dainit_measure] at hg
        omega
    obtain ⟨h0, h1, h2, h3, h4⟩ := hinv
    have hall : ∀ m, ∃ w, s.hold w = some m := by
      intro m
      by_contra hc
      have hfree : s.Free m := fun w hw => hc ⟨w, hw⟩
      have hfull : ∀ w, w ∈ s.prop m := by
        intro w
        by_contra hw
        exact hdone m ⟨hfree, w, hw⟩
      choose f hf using fun w => h0 w m (hfull w)
      have hmaps : Set.MapsTo f (↑(Finset.univ : Finset W)) (↑(Finset.univ.image f)) :=
        fun w _ => Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_univ w))
      have hcard : (Finset.univ.image f).card ≤ Fintype.card M - 1 := by
        have hsub : Finset.univ.image f ⊆ Finset.univ.erase m := by
          intro x hx
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
          have h2w := hf w
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hcon
          rw [hcon] at h2w
          exact hfree w h2w
        calc (Finset.univ.image f).card ≤ (Finset.univ.erase m).card :=
              Finset.card_le_card hsub
          _ = Fintype.card M - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]
      obtain ⟨w₁, _, w₂, _, hne, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := (Finset.univ : Finset W))
          (t := Finset.univ.image f) (f := f) (by
            have hWc : (Finset.univ : Finset W).card = Fintype.card W :=
              Finset.card_univ
            omega) hmaps
      have e1 : s.hold w₁ = some (f w₂) := by
        rw [← heq]
        exact hf w₁
      exact hne (h3 (f w₂) w₁ w₂ e1 (hf w₂))
    choose h hh using hall
    have hinj : Function.Injective h := by
      intro m₁ m₂ heq
      have e1 := hh m₁
      rw [heq] at e1
      have e2 := hh m₂
      rw [e1] at e2
      exact (Option.some_injective _) e2
    have himg : (Finset.univ.image h).card = Fintype.card M := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have huniv : Finset.univ.image h = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [himg]; exact hCard)
    have hwall : ∀ w, ∃ m, s.hold w = some m := by
      intro w
      have hw : w ∈ Finset.univ.image h := by
        rw [huniv]
        exact Finset.mem_univ w
      obtain ⟨m, _, heq⟩ := Finset.mem_image.mp hw
      exact ⟨m, by rw [← heq]; exact hh m⟩
    choose f hf using hwall
    have hleft : ∀ m, f (h m) = m := by
      intro m
      have e1 := hh m
      have e2 := hf (h m)
      rw [e1] at e2
      exact ((Option.some_injective _) e2).symm
    have hright : ∀ w, h (f w) = w := by
      intro w
      exact (h3 (f w) w (h (f w)) (hf w) (hh (f w))).symm
    refine ⟨⟨h, f, hleft, hright⟩, fun m w hb => ?_⟩
    rw [show IsBlockingPair mp wp ⟨h, f, hleft, hright⟩ m w ↔
      (mp m).lt w (h m) ∧ (wp w).lt m (f w) from Iff.rfl] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hmem : w ∈ s.prop m := by
      by_contra hw
      have hwin : h m ∈ s.prop m := h1 (h m) m (hh m)
      have hne : h m ≠ w := by
        intro heq
        rw [heq] at hb1
        exact (mp m).irrefl w hb1
      exact (mp m).irrefl (h m) ((mp m).trans (h4 m (h m) w hwin hw hne) hb1)
    have hne2 : m ≠ f w := by
      intro heq
      rw [heq] at hb2
      exact (wp w).irrefl (f w) hb2
    rcases h2 w (f w) (hf w) m hmem with heq | hlt
    · exact hne2 heq
    · exact (wp w).irrefl (f w) ((wp w).trans hlt hb2)


set_option linter.unusedDecidableInType false in
/--
**Gale–Shapley theorem.** Let $M$ and $W$ be finite sets with the same number of elements.
Suppose that each $m \in M$ has a strict total order of preference on $W$ and each $w \in W$ has
a strict total order of preference on $M$. Then some perfect matching between $M$ and $W$ is
stable for these preferences.

Source: D. Gale and L. S. Shapley, "College Admissions and the Stability of Marriage", American
Mathematical Monthly 69 (1962), 9–15, DOI 10.2307/2312726.
It follows from `gale_shapley_exists_stable_matching_general`; the instances `[DecidableEq M]` and
`[DecidableEq W]` are unused and keep the source's shape.
Proves `Wanted` entry `gale_shapley_exists_stable_matching`.
-/
@[nolint unusedArguments]
theorem gale_shapley_exists_stable_matching
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hCard : Fintype.card M = Fintype.card W)
    (mp : MPrefs M W) (wp : WPrefs M W) :
    ∃ μ : PerfectMatching M W, IsStable mp wp μ :=
  gale_shapley_exists_stable_matching_general hCard mp wp

end MathlibExt.Combinatorics.Matching.GaleShapley
