/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Primitive recursive list helpers
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.RE
public import Mathlib.Data.Finset.Card

/-!
# Primitive recursive list helpers for decision procedures

Small list utilities shared by the decision procedures for encoded automata
(`Decidability/Regular.lean`) and encoded grammars (`Decidability/ContextFree.lean`), with their
primitive recursiveness.

* `Cslib.Decidability.memB`, `Cslib.Decidability.dedupB`: membership test and duplicate removal
  for lists of numbers.
* `Cslib.Decidability.iterate_closed`: a monotone round on lists of numbers whose results stay
  inside a fixed list `B` is closed after `B.length` rounds from `[]`.
* `Cslib.Decidability.primrec_memB`, `primrec_dedupB`, `primrec_list_all`, `primrec_list_any`,
  `primrec_list_filter`: primitive recursiveness, with tests depending on a parameter.
* `Cslib.Decidability.computablePred_of_primrec_bool`: a correct primitive recursive `Bool` test
  gives a `ComputablePred`.
-/

@[expose] public section

namespace Cslib.Decidability

/-- **Boolean membership test for lists of natural numbers.** For a list $G$ of natural numbers
and a natural number $j$, the Boolean value that is true exactly when $j$ is an entry of $G$. -/
def memB (G : List ℕ) (j : ℕ) : Bool :=
  G.foldr (fun a b => decide (a = j) || b) false

theorem memB_iff {G : List ℕ} {j : ℕ} : memB G j = true ↔ j ∈ G := by
  induction G with
  | nil => simp [memB]
  | cons a G ih =>
      simp only [memB, List.foldr_cons, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons] at ih ⊢
      rw [ih, eq_comm]

/-- **Duplicate removal for lists of natural numbers.** For a list $l$ of natural numbers, the list
obtained from $l$ by deleting every entry that occurs again later in $l$: each element of $l$ is
kept once, at its last occurrence, and the kept entries stay in their order in $l$. -/
def dedupB (l : List ℕ) : List ℕ :=
  l.foldr (fun x acc => cond (memB acc x) acc (x :: acc)) []

theorem mem_dedupB {l : List ℕ} {x : ℕ} : x ∈ dedupB l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupB]
  | cons y l ih =>
      change x ∈ cond (memB (dedupB l) y) (dedupB l) (y :: dedupB l) ↔ x ∈ y :: l
      cases h : memB (dedupB l) y
      · simp only [Bool.cond_false, List.mem_cons, ih]
      · simp only [Bool.cond_true, List.mem_cons, ← ih]
        rw [memB_iff] at h
        constructor
        · exact Or.inr
        · rintro (rfl | hx)
          · exact h
          · exact hx

/-- **Bounded monotone rounds on lists close off.** Let $f$ map lists of natural numbers to lists
of natural numbers and be monotone for list inclusion: $f(G) \subseteq f(G')$ whenever
$G \subseteq G'$, where $G \subseteq G'$ means that every entry of $G$ is an entry of $G'$. If $B$
is a list with $f(G) \subseteq B$ for every list $G$, and $n$ is the length of $B$, then
$f(f^n([\,])) \subseteq f^n([\,])$, where $f^n$ is the $n$-fold iterate of $f$ and $[\,]$ is the
empty list. -/
theorem iterate_closed {f : List ℕ → List ℕ} (hmono : ∀ G G', G ⊆ G' → f G ⊆ f G')
    (B : List ℕ) (hB : ∀ G, f G ⊆ B) : f (f^[B.length] []) ⊆ f^[B.length] [] := by
  classical
  set a : ℕ → List ℕ := fun k => f^[k] [] with ha
  have hsucc : ∀ k, a (k + 1) = f (a k) := fun k => Function.iterate_succ_apply' f k []
  have hchain : ∀ k, a k ⊆ a (k + 1) := by
    intro k
    induction k with
    | zero => exact List.nil_subset _
    | succ k ih =>
        have h := hmono _ _ ih
        rwa [← hsucc k, ← hsucc (k + 1)] at h
  have hstable : ∀ k, a (k + 1) ⊆ a k → ∀ m, k ≤ m → a (m + 1) ⊆ a m := by
    intro k hk m hm
    induction m, hm using Nat.le_induction with
    | base => exact hk
    | succ m _ ih =>
        have h := hmono _ _ ih
        rwa [← hsucc m, ← hsucc (m + 1)] at h
  suffices ∃ k ≤ B.length, a (k + 1) ⊆ a k by
    obtain ⟨k, hk, h⟩ := this
    have := hstable k h B.length hk
    rwa [hsucc] at this
  by_contra hno
  push Not at hno
  have hcard : ∀ k ≤ B.length + 1, k ≤ (a k).toFinset.card := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have hlt : (a k).toFinset ⊂ (a (k + 1)).toFinset := by
          refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun heq => hno k (by omega) ?_⟩
          · simp only [List.mem_toFinset] at hx ⊢
            exact hchain k hx
          · intro x hx
            have : x ∈ (a (k + 1)).toFinset := List.mem_toFinset.2 hx
            rw [← heq] at this
            exact List.mem_toFinset.1 this
        have := Finset.card_lt_card hlt
        have := ih (by omega)
        omega
  have h1 := hcard (B.length + 1) le_rfl
  have h2 : (a (B.length + 1)).toFinset ⊆ B.toFinset := by
    intro x hx
    rw [hsucc] at hx
    exact List.mem_toFinset.2 (hB _ (List.mem_toFinset.1 hx))
  have h3 := Finset.card_le_card h2
  have h4 := List.toFinset_card_le B
  omega

theorem primrec_memB : Primrec₂ memB :=
  Primrec.list_foldr Primrec.fst (Primrec.const false)
    (Primrec.or.comp₂ (Primrec.eq.decide.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)) (Primrec.snd.comp₂ Primrec₂.right))

theorem primrec_dedupB : Primrec dedupB :=
  (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.cond (primrec_memB.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun _ => rfl


theorem primrec_list_all {β γ : Type*} [Primcodable β] [Primcodable γ] {p : β → γ → Bool}
    {l : β → List γ} (hp : Primrec₂ p) (hl : Primrec l) :
    Primrec fun b => (l b).all (p b) :=
  (Primrec.list_foldr hl (Primrec.const true)
    (Primrec.and.comp₂ (hp.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun b => by
    generalize l b = L
    induction L with
    | nil => rfl
    | cons x L ih => simp only [List.foldr_cons, List.all_cons, ih]

theorem primrec_list_any {β γ : Type*} [Primcodable β] [Primcodable γ] {p : β → γ → Bool}
    {l : β → List γ} (hp : Primrec₂ p) (hl : Primrec l) :
    Primrec fun b => (l b).any (p b) :=
  (Primrec.list_foldr hl (Primrec.const false)
    (Primrec.or.comp₂ (hp.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun b => by
    generalize l b = L
    induction L with
    | nil => rfl
    | cons x L ih => simp only [List.foldr_cons, List.any_cons, ih]

theorem primrec_list_filter {β γ : Type*} [Primcodable β] [Primcodable γ] {p : β → γ → Bool}
    {l : β → List γ} (hp : Primrec₂ p) (hl : Primrec l) :
    Primrec fun b => (l b).filter (p b) :=
  (Primrec.listFilterMap hl
    (Primrec.cond hp (Primrec.option_some.comp₂ Primrec₂.right)
      (Primrec.const none |>.comp₂ Primrec₂.left)).to₂).of_eq fun b => by
    generalize l b = L
    induction L with
    | nil => rfl
    | cons x L ih =>
        rw [List.filterMap_cons, List.filter_cons]
        cases h : p b x
        · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
          exact ih
        · simp only [Bool.cond_true, ↓reduceIte]
          exact congrArg _ ih

/-- **Predicates with a primitive recursive decision procedure are computable.** Let $\beta$ be a
primcodable type, $p$ a predicate on $\beta$, and $f : \beta \to \mathrm{Bool}$ a primitive
recursive function such that $f(b) = \mathrm{true}$ exactly when $p(b)$ holds, for every
$b \in \beta$. Then $p$ is a computable predicate. -/
theorem computablePred_of_primrec_bool {β : Type*} [Primcodable β] {p : β → Prop}
    {f : β → Bool} (hf : Primrec f) (h : ∀ b, f b = true ↔ p b) : ComputablePred p := by
  let _ : DecidablePred p := fun b => decidable_of_iff _ (h b)
  refine Computable.computablePred (hf.to_comp.of_eq fun b => ?_)
  cases hb : f b
  · exact (decide_eq_false fun hp => by simp [(h b).2 hp] at hb).symm
  · exact (decide_eq_true ((h b).1 hb)).symm


end Cslib.Decidability
