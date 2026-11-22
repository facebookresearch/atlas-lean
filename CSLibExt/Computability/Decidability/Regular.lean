/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decision procedures for DFAs
-/
module

public import Mathlib.Computability.DFA
public import MathlibExt.Order.FixedPoints.Finset
public import CSLibExt.Computability.Automata.DA.EncodedDFA
public import CSLibExt.Computability.Decidability.Basic
public import CSLibExt.Computability.Decidability.PrimrecList
public import Mathlib.Data.FinEnum

/-!
# Decision procedures for DFAs: emptiness, universality, equivalence

Executable `Bool` procedures for Mathlib's `DFA` over finite alphabets and finite state
types, with correctness theorems (Sipser, *Introduction to the Theory of Computation*,
Theorems 4.4 and 4.5, for E_DFA and EQ_DFA).

* `DFA.reachable`: the states reachable from the start state, computed as a least fixed point
  by finite iteration (`Finset.lfpFin`); `DFA.mem_reachable_iff`: a state is reachable exactly
  when some word leads to it.
* `DFA.reachableWithin`: the same search stopping as soon as a round adds nothing, equal to
  `DFA.reachable` for any bound on the rounds of at least the number of states
  (`DFA.reachableWithin_eq_reachable`); `DFA.accessiblePartWithin`: the DFA restricted to the
  reachable states it finds.
* `DFA.isEmptyB`: no reachable state accepts; `DFA.isEmptyB_iff`: it returns `true` exactly
  when the DFA accepts no word.
* `DFA.isUnivB` with `DFA.isUnivB_iff`: universality, through the complement DFA.
* `DFA.symmDiff`: the product DFA accepting the words on which two DFAs disagree;
  `DFA.equivB` with `DFA.equivB_iff`: two DFAs accept the same language exactly when their
  symmetric difference is empty.

For DFAs as data (`Cslib.Automata.EncodedDFA`, natural-number states and a transition list),
the same problems are decided by primitive recursive functions, which gives Sipser's theorems
for multi-stack machines (`Cslib.Decidability.TM2Decidable`):

* `EncodedDFA.acceptsB_iff` and `EncodedDFA.tm2Decidable_mem_language`: A_DFA (Theorem 4.1).
* `EncodedDFA.reachN`, `EncodedDFA.mem_reachN_iff`: a list-based reachability search, bounded by
  the number of listed states; `EncodedDFA.mem_reachable_iff`.
* `EncodedDFA.isEmptyB_iff` and `EncodedDFA.tm2Decidable_language_eq_zero`: E_DFA (Theorem 4.4).
* `EncodedDFA.mem_pairReachable_iff`, `EncodedDFA.equivB_iff` and
  `EncodedDFA.tm2Decidable_language_eq`: EQ_DFA (Theorem 4.5), through the reachable pairs of
  states of the two automata reading the same word.
* `EncodedDFA.isUnivB_iff` and `EncodedDFA.tm2Decidable_language_eq_top`: ALL_DFA, every
  reachable state accepts.
* `EncodedDFA.infiniteB_iff` and `EncodedDFA.tm2Decidable_language_infinite`: INFINITE_DFA over a
  finite alphabet (`FinEnum`): the language is infinite exactly when it contains a word whose
  length is between the number `N` of listed states and `2N` (Mathlib's pumping lemma, applied to
  the encoded DFA restricted to its listed states, `EncodedDFA.toFinDFA`).
-/

@[expose] public section

namespace DFA

section Product

variable {α σ σ' : Type*} (M : DFA α σ) (N : DFA α σ')

/-- The product DFA accepting the words on which `M` and `N` disagree. -/
def symmDiff : DFA α (σ × σ') where
  step p a := (M.step p.1 a, N.step p.2 a)
  start := (M.start, N.start)
  accept := {p | ¬ (p.1 ∈ M.accept ↔ p.2 ∈ N.accept)}

theorem eval_symmDiff (w : List α) : (M.symmDiff N).eval w = (M.eval w, N.eval w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [eval_append_singleton, ih, eval_append_singleton, eval_append_singleton]
      rfl

end Product

variable {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ] (M : DFA α σ)

/-- One round of the reachability search: the start state, the states found so far, and their
successors. -/
def reachStep (S : Finset σ) : Finset σ :=
  {M.start} ∪ S.biUnion fun s => Finset.univ.image (M.step s)

omit [Fintype σ] in
theorem reachStep_mono : Monotone M.reachStep := fun _ _ h =>
  Finset.union_subset_union le_rfl (Finset.biUnion_subset_biUnion_of_subset_left _ h)

/-- The states reachable from the start state. -/
def reachable : Finset σ :=
  Finset.lfpFin M.reachStep

/-- **A state is reachable exactly when some word leads to it.** -/
theorem mem_reachable_iff {s : σ} : s ∈ M.reachable ↔ ∃ w, M.eval w = s := by
  classical
  constructor
  · intro hs
    have hle : M.reachable ⊆ Finset.univ.filter fun s => ∃ w, M.eval w = s := by
      refine Finset.lfpFin_le M.reachStep_mono fun t ht => ?_
      simp only [reachStep, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at ht ⊢
      rcases ht with rfl | ⟨u, hu, a, rfl⟩
      · exact ⟨[], rfl⟩
      · obtain ⟨w, rfl⟩ := hu
        exact ⟨w ++ [a], M.eval_append_singleton w a⟩
    simpa using hle hs
  · rintro ⟨w, rfl⟩
    have hfix := Finset.lfpFin_fixed M.reachStep_mono
    induction w using List.reverseRecOn with
    | nil =>
        rw [reachable, ← hfix]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    | append_singleton w a ih =>
        rw [M.eval_append_singleton, reachable, ← hfix]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, ih, Finset.mem_image_of_mem _
          (Finset.mem_univ a)⟩)

/-- The start state is reachable. -/
theorem start_mem_reachable : M.start ∈ M.reachable :=
  M.mem_reachable_iff.2 ⟨[], rfl⟩

/-- The reachable states are closed under transitions. -/
theorem step_mem_reachable {s : σ} (hs : s ∈ M.reachable) (a : α) :
    M.step s a ∈ M.reachable := by
  obtain ⟨w, rfl⟩ := M.mem_reachable_iff.1 hs
  exact M.mem_reachable_iff.2 ⟨w ++ [a], M.eval_append_singleton w a⟩

/-- The reachability search from `S` with at most `n` rounds, stopping as soon as a round adds
nothing. -/
def reachableWithin : ℕ → Finset σ → Finset σ
  | 0, S => S
  | n + 1, S => if M.reachStep S = S then S else reachableWithin n (M.reachStep S)

omit [Fintype σ] in
theorem reachableWithin_eq_iterate :
    ∀ (n : ℕ) (S : Finset σ), M.reachableWithin n S = M.reachStep^[n] S
  | 0, _ => rfl
  | n + 1, S => by
      rw [reachableWithin, Function.iterate_succ_apply]
      split_ifs with h
      · rw [h, Function.iterate_fixed h]
      · exact reachableWithin_eq_iterate n _

/-- With at least `Fintype.card σ` rounds the early-stopping search finds every reachable state;
since it stops once nothing changes, a generous bound costs nothing. -/
theorem reachableWithin_eq_reachable {n : ℕ} (hn : Fintype.card σ ≤ n) :
    M.reachableWithin n ∅ = M.reachable := by
  rw [reachableWithin_eq_iterate, reachable, Finset.lfpFin, ← Nat.sub_add_cancel hn,
    Function.iterate_add_apply]
  exact Function.iterate_fixed (Finset.lfpFin_fixed M.reachStep_mono) _

theorem mem_reachableWithin_iff {n : ℕ} (hn : Fintype.card σ ≤ n) {s : σ} :
    s ∈ M.reachableWithin n ∅ ↔ ∃ w, M.eval w = s := by
  rw [M.reachableWithin_eq_reachable hn, mem_reachable_iff]

/-- `M` restricted to its reachable states, found by the early-stopping search with `n` rounds,
for any bound `n ≥ Fintype.card σ`. -/
def accessiblePartWithin (n : ℕ) (hn : Fintype.card σ ≤ n) :
    DFA α {s // s ∈ M.reachableWithin n ∅} where
  step p a := ⟨M.step p.1 a, (M.mem_reachableWithin_iff hn).2 <| by
    obtain ⟨w, hw⟩ := (M.mem_reachableWithin_iff hn).1 p.2
    exact ⟨w ++ [a], by rw [eval_append_singleton, hw]⟩⟩
  start := ⟨M.start, (M.mem_reachableWithin_iff hn).2 ⟨[], rfl⟩⟩
  accept := {p | p.1 ∈ M.accept}

/-- `M` restricted to its reachable states. -/
abbrev accessiblePart : DFA α {s // s ∈ M.reachableWithin (Fintype.card σ) ∅} :=
  M.accessiblePartWithin (Fintype.card σ) le_rfl

instance decidableMemAccessiblePartWithinAccept [DecidablePred (· ∈ M.accept)] {n : ℕ}
    (hn : Fintype.card σ ≤ n) : DecidablePred (· ∈ (M.accessiblePartWithin n hn).accept) :=
  fun p => inferInstanceAs (Decidable (p.1 ∈ M.accept))

section AccessiblePart

variable {n : ℕ} (hn : Fintype.card σ ≤ n)

theorem accessiblePartWithin_eval (w : List α) :
    ((M.accessiblePartWithin n hn).eval w).1 = M.eval w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [eval_append_singleton, eval_append_singleton, ← ih]
      rfl

theorem accessiblePartWithin_accepts : (M.accessiblePartWithin n hn).accepts = M.accepts := by
  ext w
  rw [mem_accepts, mem_accepts, ← M.accessiblePartWithin_eval hn w]
  rfl

/-- Every state of the accessible part is reached. -/
theorem accessiblePartWithin_surjective (p : {s // s ∈ M.reachableWithin n ∅}) :
    ∃ w, (M.accessiblePartWithin n hn).eval w = p := by
  obtain ⟨w, hw⟩ := (M.mem_reachableWithin_iff hn).1 p.2
  exact ⟨w, Subtype.ext ((M.accessiblePartWithin_eval hn w).trans hw)⟩

theorem accessiblePartWithin_eval_eq_iff {w w' : List α} :
    (M.accessiblePartWithin n hn).eval w = (M.accessiblePartWithin n hn).eval w' ↔
      M.eval w = M.eval w' := by
  rw [Subtype.ext_iff, accessiblePartWithin_eval, accessiblePartWithin_eval]

end AccessiblePart

variable [DecidablePred (· ∈ M.accept)]

/-- Emptiness test: no reachable state accepts. -/
def isEmptyB : Bool :=
  decide (∀ s ∈ M.reachable, s ∉ M.accept)

/-- **Emptiness of DFAs is decided by `isEmptyB`.** -/
theorem isEmptyB_iff : M.isEmptyB = true ↔ M.accepts = 0 := by
  rw [isEmptyB, decide_eq_true_iff]
  constructor
  · intro h
    ext w
    simp only [Language.notMem_zero, iff_false]
    exact h _ (M.mem_reachable_iff.2 ⟨w, rfl⟩)
  · intro h s hs hacc
    obtain ⟨w, rfl⟩ := M.mem_reachable_iff.1 hs
    have : w ∈ M.accepts := hacc
    rw [h] at this
    exact Language.notMem_zero w this

instance decidableMemComplAccept : DecidablePred (· ∈ Mᶜ.accept) :=
  inferInstanceAs (DecidablePred fun s => s ∉ M.accept)

/-- Universality test: the complement DFA is empty. -/
def isUnivB : Bool :=
  Mᶜ.isEmptyB

/-- **Universality of DFAs is decided by `isUnivB`.** -/
theorem isUnivB_iff : M.isUnivB = true ↔ M.accepts = ⊤ := by
  rw [isUnivB, isEmptyB_iff, accepts_compl]
  constructor
  · intro h
    rw [← compl_compl M.accepts, h]
    exact compl_bot
  · intro h
    rw [h]
    exact compl_top

variable {σ' : Type*} [Fintype σ'] [DecidableEq σ'] (N : DFA α σ') [DecidablePred (· ∈ N.accept)]


instance decidableMemSymmDiffAccept : DecidablePred (· ∈ (M.symmDiff N).accept) :=
  inferInstanceAs (DecidablePred fun p : σ × σ' => ¬ (p.1 ∈ M.accept ↔ p.2 ∈ N.accept))

/-- Equivalence test: the symmetric difference is empty. -/
def equivB : Bool :=
  (M.symmDiff N).isEmptyB

/-- **Equivalence of DFAs is decided by `equivB`.** -/
theorem equivB_iff : M.equivB N = true ↔ M.accepts = N.accepts := by
  rw [equivB, isEmptyB_iff]
  constructor
  · intro h
    ext w
    by_contra hne
    have : w ∈ (M.symmDiff N).accepts := by
      rw [mem_accepts, eval_symmDiff]
      exact hne
    rw [h] at this
    exact Language.notMem_zero w this
  · intro h
    ext w
    simp only [Language.notMem_zero, iff_false]
    intro hw
    rw [mem_accepts, eval_symmDiff] at hw
    exact hw (by rw [← mem_accepts, ← mem_accepts, h])

end DFA

/-! ## Encoded DFAs: Sipser's decidable DFA problems -/

namespace Cslib.Automata.EncodedDFA

open Cslib.Decidability

variable {α : Type*} [DecidableEq α]

/-! ### Acceptance -/

/-- Acceptance test: run the encoded DFA and check the final state. -/
def acceptsB (D : EncodedDFA α) (w : List α) : Bool :=
  memB D.accept (D.toDFA.eval w)

theorem acceptsB_iff {D : EncodedDFA α} {w : List α} : D.acceptsB w = true ↔ w ∈ D.language :=
  memB_iff

/-! ### Reachability -/

/-- One round of the search from `s₀` with successors `next`, kept inside `B`: `s₀`, the states
found so far and their successors. -/
def reachRound (s₀ : ℕ) (next : ℕ → List ℕ) (B R : List ℕ) : List ℕ :=
  dedupB ((s₀ :: R.flatMap fun s => s :: next s).filterMap fun t =>
    cond (memB B t) (some t) none)

theorem mem_reachRound {s₀ : ℕ} {next : ℕ → List ℕ} {B R : List ℕ} {t : ℕ} :
    t ∈ reachRound s₀ next B R ↔ t ∈ B ∧ (t = s₀ ∨ ∃ s ∈ R, t = s ∨ t ∈ next s) := by
  simp only [reachRound, mem_dedupB, List.mem_filterMap, List.mem_cons, List.mem_flatMap]
  constructor
  · rintro ⟨u, hu, h⟩
    cases hB : memB B u
    · simp [hB] at h
    · simp only [hB, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact ⟨memB_iff.1 hB, hu⟩
  · rintro ⟨hB, hu⟩
    exact ⟨t, hu, by simp [memB_iff.2 hB]⟩

/-- The states reachable from `s₀` through `next`, by `B.length` rounds. -/
def reachN (s₀ : ℕ) (next : ℕ → List ℕ) (B : List ℕ) : List ℕ :=
  (reachRound s₀ next B)^[B.length] []

/-- **Correctness of the search**: when `B` contains `s₀` and is closed under `next`, the search
finds exactly the states reachable from `s₀`. -/
theorem mem_reachN_iff {s₀ : ℕ} {next : ℕ → List ℕ} {B : List ℕ} (hs₀ : s₀ ∈ B)
    (hB : ∀ s ∈ B, ∀ t ∈ next s, t ∈ B) {t : ℕ} :
    t ∈ reachN s₀ next B ↔ Relation.ReflTransGen (fun s t => t ∈ next s) s₀ t := by
  have hmono : ∀ R R', R ⊆ R' → reachRound s₀ next B R ⊆ reachRound s₀ next B R' := by
    intro R R' h u hu
    rw [mem_reachRound] at hu ⊢
    obtain ⟨huB, hu | ⟨s, hs, hsu⟩⟩ := hu
    · exact ⟨huB, Or.inl hu⟩
    · exact ⟨huB, Or.inr ⟨s, h hs, hsu⟩⟩
  have hsub : ∀ R, reachRound s₀ next B R ⊆ B := fun R u hu => (mem_reachRound.1 hu).1
  have hclosed : reachRound s₀ next B (reachN s₀ next B) ⊆ reachN s₀ next B :=
    iterate_closed hmono B hsub
  have hreachB : reachN s₀ next B ⊆ B := by
    unfold reachN
    cases B.length with
    | zero => exact List.nil_subset _
    | succ n =>
        rw [Function.iterate_succ_apply']
        exact hsub _
  constructor
  · intro h
    suffices ∀ k u, u ∈ (reachRound s₀ next B)^[k] [] →
        Relation.ReflTransGen (fun s t => t ∈ next s) s₀ u from this _ t h
    intro k
    induction k with
    | zero => intro u hu; simp at hu
    | succ k ih =>
        intro u hu
        rw [Function.iterate_succ_apply', mem_reachRound] at hu
        obtain ⟨-, hu | ⟨s, hs, hus | hsu⟩⟩ := hu
        · exact hu ▸ .refl
        · rw [hus]
          exact ih s hs
        · exact (ih s hs).tail hsu
  · intro h
    induction h with
    | refl => exact hclosed (mem_reachRound.2 ⟨hs₀, Or.inl rfl⟩)
    | tail _ hst ih =>
        exact hclosed (mem_reachRound.2 ⟨hB _ (hreachB ih) _ hst, Or.inr ⟨_, ih, Or.inr hst⟩⟩)

/-- The reachable states of an encoded DFA. -/
def reachable (D : EncodedDFA α) : List ℕ :=
  reachN D.start (fun s => D.letters.map (D.step s)) D.states

theorem mem_reachable_iff {D : EncodedDFA α} {t : ℕ} :
    t ∈ D.reachable ↔ ∃ w, D.toDFA.eval w = t := by
  have hs₀ : D.start ∈ D.states := List.mem_cons_self
  rw [reachable, mem_reachN_iff hs₀ fun s hs u hu => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hu
    exact step_mem_states hs a]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hst ih =>
        obtain ⟨w, rfl⟩ := ih
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hst
        exact ⟨w ++ [a], DFA.eval_append_singleton _ _ _⟩
  · rintro ⟨w, rfl⟩
    induction w using List.reverseRecOn with
    | nil => exact .refl
    | append_singleton w a ih =>
        rw [DFA.eval_append_singleton]
        by_cases ha : a ∈ D.letters
        · exact ih.tail (List.mem_map.2 ⟨a, ha, rfl⟩)
        · change Relation.ReflTransGen _ _ (D.step _ a)
          rw [step_of_not_mem_letters ha]
          exact ih

/-! ### Emptiness -/

/-- Emptiness test: no reachable state accepts. -/
def isEmptyB (D : EncodedDFA α) : Bool :=
  D.reachable.all fun s => !memB D.accept s

theorem isEmptyB_iff {D : EncodedDFA α} : D.isEmptyB = true ↔ D.language = 0 := by
  rw [isEmptyB, List.all_eq_true]
  constructor
  · intro h
    ext w
    simp only [Language.notMem_zero, iff_false]
    intro hw
    have h' := h _ (mem_reachable_iff.2 ⟨w, rfl⟩)
    have hm : memB D.accept (D.toDFA.eval w) = true := memB_iff.2 hw
    rw [hm] at h'
    exact Bool.false_ne_true h'
  · intro h s hs
    obtain ⟨w, rfl⟩ := mem_reachable_iff.1 hs
    cases hm : memB D.accept (D.toDFA.eval w)
    · rfl
    · have hw : w ∈ D.language := memB_iff.1 hm
      rw [h] at hw
      exact absurd hw (Language.notMem_zero w)

/-! ### Equivalence -/

/-- Pairs of listed states, coded by `Nat.pair`. -/
def pairStates (D E : EncodedDFA α) : List ℕ :=
  D.states.flatMap fun s => E.states.map fun t => Nat.pair s t

/-- Successors of a coded pair of states: both automata read the same letter. -/
def pairNext (D E : EncodedDFA α) (p : ℕ) : List ℕ :=
  (D.letters ++ E.letters).map fun a => Nat.pair (D.step p.unpair.1 a) (E.step p.unpair.2 a)

/-- The reachable pairs of states of two encoded DFAs reading the same word. -/
def pairReachable (D E : EncodedDFA α) : List ℕ :=
  reachN (Nat.pair D.start E.start) (pairNext D E) (pairStates D E)

omit [DecidableEq α] in
theorem mem_pairStates {D E : EncodedDFA α} {s t : ℕ} (hs : s ∈ D.states) (ht : t ∈ E.states) :
    Nat.pair s t ∈ pairStates D E :=
  List.mem_flatMap.2 ⟨s, hs, List.mem_map.2 ⟨t, ht, rfl⟩⟩

theorem mem_pairReachable_iff {D E : EncodedDFA α} {p : ℕ} :
    p ∈ pairReachable D E ↔ ∃ w, p = Nat.pair (D.toDFA.eval w) (E.toDFA.eval w) := by
  have hB : ∀ q ∈ pairStates D E, ∀ r ∈ pairNext D E q, r ∈ pairStates D E := by
    intro q hq r hr
    obtain ⟨s, hs, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr
    rw [Nat.unpair_pair]
    exact mem_pairStates (step_mem_states hs a) (step_mem_states ht a)
  rw [pairReachable, mem_reachN_iff (mem_pairStates List.mem_cons_self List.mem_cons_self) hB]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hst ih =>
        obtain ⟨w, rfl⟩ := ih
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hst
        refine ⟨w ++ [a], ?_⟩
        rw [Nat.unpair_pair, DFA.eval_append_singleton, DFA.eval_append_singleton]
        rfl
  · rintro ⟨w, rfl⟩
    induction w using List.reverseRecOn with
    | nil => exact .refl
    | append_singleton w a ih =>
        rw [DFA.eval_append_singleton, DFA.eval_append_singleton]
        by_cases ha : a ∈ D.letters ++ E.letters
        · refine ih.tail (List.mem_map.2 ⟨a, ha, ?_⟩)
          rw [Nat.unpair_pair]
          rfl
        · rw [List.mem_append, not_or] at ha
          change Relation.ReflTransGen _ _ (Nat.pair (D.step _ a) (E.step _ a))
          rw [step_of_not_mem_letters ha.1, step_of_not_mem_letters ha.2]
          exact ih

/-- Equivalence test: every reachable pair of states agrees on acceptance. -/
def equivB (D E : EncodedDFA α) : Bool :=
  (pairReachable D E).all fun p => memB D.accept p.unpair.1 == memB E.accept p.unpair.2

theorem equivB_iff {D E : EncodedDFA α} : D.equivB E = true ↔ D.language = E.language := by
  rw [equivB, List.all_eq_true]
  constructor
  · intro h
    ext w
    have h' := h _ (mem_pairReachable_iff.2 ⟨w, rfl⟩)
    rw [Nat.unpair_pair, beq_iff_eq] at h'
    rw [← acceptsB_iff, ← acceptsB_iff]
    exact Bool.eq_iff_iff.1 h'
  · intro h p hp
    obtain ⟨w, rfl⟩ := mem_pairReachable_iff.1 hp
    rw [Nat.unpair_pair, beq_iff_eq]
    have h1 : D.acceptsB w = E.acceptsB w :=
      Bool.eq_iff_iff.2 (by rw [acceptsB_iff, acceptsB_iff, h])
    exact h1

/-! ### Universality -/

/-- Universality test: every reachable state accepts. -/
def isUnivB (D : EncodedDFA α) : Bool :=
  D.reachable.all fun s => memB D.accept s

theorem isUnivB_iff {D : EncodedDFA α} : D.isUnivB = true ↔ D.language = ⊤ := by
  rw [isUnivB, List.all_eq_true]
  constructor
  · intro h
    ext w
    exact iff_of_true (memB_iff.1 (h _ (mem_reachable_iff.2 ⟨w, rfl⟩))) trivial
  · intro h s hs
    obtain ⟨w, rfl⟩ := mem_reachable_iff.1 hs
    have hw : w ∈ D.language := by rw [h]; trivial
    exact memB_iff.2 hw

/-! ### Infiniteness -/

/-- The encoded DFA on its listed states, a finite type. -/
def toFinDFA (D : EncodedDFA α) : DFA α {s // s ∈ D.states.toFinset} where
  step s a := ⟨D.step s.1 a, List.mem_toFinset.2 (step_mem_states (List.mem_toFinset.1 s.2) a)⟩
  start := ⟨D.start, List.mem_toFinset.2 List.mem_cons_self⟩
  accept := {s | s.1 ∈ D.accept}

theorem toFinDFA_eval (D : EncodedDFA α) (w : List α) :
    (D.toFinDFA.eval w).1 = D.toDFA.eval w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [DFA.eval_append_singleton, DFA.eval_append_singleton, ← ih]
      rfl

theorem accepts_toFinDFA (D : EncodedDFA α) : D.toFinDFA.accepts = D.language := by
  ext w
  rw [DFA.mem_accepts, mem_language_iff, ← toFinDFA_eval]
  rfl

omit [DecidableEq α] in
theorem card_toFinDFA_le (D : EncodedDFA α) :
    Fintype.card {s // s ∈ D.states.toFinset} ≤ D.states.length := by
  rw [Fintype.card_coe]
  exact List.toFinset_card_le _

/-- A long accepted word pumps: the language is infinite. -/
theorem infinite_of_mem_of_le {D : EncodedDFA α} {w : List α} (hw : w ∈ D.language)
    (hlen : D.states.length ≤ w.length) : D.language.Infinite := by
  rw [← accepts_toFinDFA] at hw ⊢
  obtain ⟨a, b, c, -, -, hb, hsub⟩ :=
    D.toFinDFA.pumping_lemma hw ((card_toFinDFA_le D).trans hlen)
  have hmem : ∀ k : ℕ, a ++ (List.replicate k b).flatten ++ c ∈ D.toFinDFA.accepts := by
    intro k
    refine hsub (Language.mem_mul.2 ⟨a ++ (List.replicate k b).flatten,
      Language.mem_mul.2 ⟨a, rfl, _, Language.mem_kstar.2 ⟨List.replicate k b, rfl, ?_⟩, rfl⟩,
      c, rfl, rfl⟩)
    intro y hy
    rw [(List.mem_replicate.1 hy).2]
    rfl
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => a ++ (List.replicate k b).flatten
    ++ c) (fun k l hkl => ?_) hmem
  have hlen := congrArg List.length hkl
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul] at hlen
  have hbpos : 0 < b.length := List.length_pos_iff.2 hb
  have : k * b.length = l * b.length := by omega
  exact Nat.eq_of_mul_eq_mul_right hbpos this

/-- An accepted word of length at least the number of listed states can be shortened, keeping
it accepted and at least that long, until it is shorter than twice that number. -/
theorem exists_mem_le_lt {D : EncodedDFA α} :
    ∀ (n : ℕ) (w : List α), w.length = n → w ∈ D.language → D.states.length ≤ w.length →
      ∃ v ∈ D.language, D.states.length ≤ v.length ∧ v.length < 2 * D.states.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw hlen
    by_cases hlt : w.length < 2 * D.states.length
    · exact ⟨w, hw, hlen, hlt⟩
    · rw [← accepts_toFinDFA] at hw
      obtain ⟨a, b, c, rfl, hab, hb, hsub⟩ :=
        D.toFinDFA.pumping_lemma hw ((card_toFinDFA_le D).trans hlen)
      have hac : a ++ c ∈ D.language := by
        rw [← accepts_toFinDFA]
        exact hsub (Language.mem_mul.2 ⟨a, Language.mem_mul.2 ⟨a, rfl, [],
          Language.nil_mem_kstar _, by simp⟩, c, rfl, rfl⟩)
      have hcard := card_toFinDFA_le D
      have hbpos : 0 < b.length := List.length_pos_iff.2 hb
      simp only [List.length_append] at hn hlen hlt
      refine ih (a ++ c).length (by simp only [List.length_append]; omega) (a ++ c) rfl hac ?_
      simp only [List.length_append]
      omega

section Infinite

variable [FinEnum α]

/-- The words of length `n` over the alphabet. -/
def wordsOfLength (n : ℕ) : List (List α) :=
  (fun W => W.flatMap fun w => (FinEnum.toList α).map fun a => a :: w)^[n] [[]]

omit [DecidableEq α] in
theorem mem_wordsOfLength {n : ℕ} {w : List α} : w ∈ wordsOfLength n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsOfLength, List.length_eq_zero_iff]
  | succ n ih =>
      rw [wordsOfLength, Function.iterate_succ_apply', ← wordsOfLength]
      simp only [List.mem_flatMap, List.mem_map, ih]
      constructor
      · rintro ⟨v, hv, a, -, rfl⟩
        simp [hv]
      · intro h
        obtain ⟨a, v, rfl⟩ : ∃ a v, w = a :: v := by
          cases w with
          | nil => simp at h
          | cons a v => exact ⟨a, v, rfl⟩
        exact ⟨v, by simpa using h, a, FinEnum.mem_toList a, rfl⟩

/-- Infiniteness test: some word with length between the number `N` of listed states and `2N`
is accepted. -/
def infiniteB (D : EncodedDFA α) : Bool :=
  (List.range D.states.length).any fun i =>
    (wordsOfLength (D.states.length + i)).any fun w => D.acceptsB w

/-- **Infiniteness of DFA languages is decided by `infiniteB`.** -/
theorem infiniteB_iff {D : EncodedDFA α} : D.infiniteB = true ↔ D.language.Infinite := by
  rw [infiniteB, List.any_eq_true]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨w, hw, hacc⟩ := List.any_eq_true.1 hi
    rw [mem_wordsOfLength] at hw
    exact infinite_of_mem_of_le (acceptsB_iff.1 hacc) (by omega)
  · intro hinf
    have hfin : {w : List α | w.length < D.states.length}.Finite := by
      refine ((List.range D.states.length).flatMap wordsOfLength).finite_toSet.subset ?_
      intro w hw
      exact List.mem_flatMap.2 ⟨w.length, List.mem_range.2 hw, mem_wordsOfLength.2 rfl⟩
    obtain ⟨w, hw, hlong⟩ := (hinf.sdiff hfin).nonempty
    simp only [Set.mem_ofPred_eq, not_lt] at hlong
    obtain ⟨v, hv, hle, hlt⟩ := exists_mem_le_lt _ w rfl hw hlong
    refine ⟨v.length - D.states.length, List.mem_range.2 (by omega), List.any_eq_true.2
      ⟨v, mem_wordsOfLength.2 (by omega), acceptsB_iff.2 hv⟩⟩

end Infinite

/-! ### Computability: Sipser's Theorems 4.1, 4.4 and 4.5 -/

section Computability

variable [Primcodable α]

theorem primrec_acceptsB : Primrec₂ (acceptsB (α := α)) :=
  primrec_memB.comp (primrec_accept.comp Primrec.fst) primrec₂_eval

theorem primrec_reachRound {β : Type*} [Primcodable β] {s₀ : β → ℕ} {next : β → ℕ → List ℕ}
    {B : β → List ℕ} (hs₀ : Primrec s₀) (hnext : Primrec₂ next) (hB : Primrec B) :
    Primrec₂ fun b R => reachRound (s₀ b) (next b) (B b) R :=
  primrec_dedupB.comp (Primrec.listFilterMap
    (Primrec.list_cons.comp (hs₀.comp Primrec.fst) (Primrec.list_flatMap Primrec.snd
      (Primrec.list_cons.comp₂ Primrec₂.right
        (hnext.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))))
    (Primrec.cond (primrec_memB.comp₂ (hB.comp₂ (Primrec.fst.comp₂ Primrec₂.left)) Primrec₂.right)
      (Primrec.option_some.comp₂ Primrec₂.right) (Primrec.const none |>.comp₂ Primrec₂.left)))

theorem primrec_reachN {β : Type*} [Primcodable β] {s₀ : β → ℕ} {next : β → ℕ → List ℕ}
    {B : β → List ℕ} (hs₀ : Primrec s₀) (hnext : Primrec₂ next) (hB : Primrec B) :
    Primrec fun b => reachN (s₀ b) (next b) (B b) :=
  Primrec.nat_iterate (Primrec.list_length.comp hB) (Primrec.const [])
    (primrec_reachRound hs₀ hnext hB)

omit [DecidableEq α] in
theorem primrec_letters : Primrec (letters (α := α)) :=
  Primrec.list_map primrec_trans (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).to₂

omit [DecidableEq α] in
theorem primrec_states : Primrec (states (α := α)) :=
  Primrec.list_cons.comp primrec_start
    (Primrec.list_map primrec_trans (Primrec.snd.comp Primrec.snd).to₂)

omit [DecidableEq α] in
theorem primrec_compl : Primrec (compl (α := α)) := by
  have hf : Primrec fun D : EncodedDFA α => D.states.filter fun s => decide (s ∉ D.accept) :=
    (primrec_list_filter
      (Primrec.not.comp₂ (primrec_memB.comp₂ (primrec_accept.comp₂ Primrec₂.left)
        Primrec₂.right))
      primrec_states).of_eq fun D => List.filter_congr fun s _ => by
        cases h : memB D.accept s
        · have : s ∉ D.accept := fun hs => by simp [memB_iff.2 hs] at h
          simp [this]
        · simp [memB_iff.1 h]
  exact primrec_mk.comp (Primrec.pair primrec_start (Primrec.pair hf primrec_trans))

theorem primrec_reachable : Primrec (reachable (α := α)) :=
  primrec_reachN primrec_start
    (Primrec.list_map (primrec_letters.comp Primrec.fst)
      (primrec_step.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂)
    primrec_states

theorem primrec_isEmptyB : Primrec (isEmptyB (α := α)) :=
  primrec_list_all (Primrec.not.comp₂ (primrec_memB.comp₂ (primrec_accept.comp₂ Primrec₂.left)
    Primrec₂.right)) primrec_reachable

omit [DecidableEq α] in
theorem primrec_pairStates : Primrec₂ (pairStates (α := α)) :=
  Primrec.list_flatMap (primrec_states.comp Primrec.fst)
    (Primrec.list_map (primrec_states.comp (Primrec.snd.comp Primrec.fst))
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem primrec_pairNext :
    Primrec fun x : (EncodedDFA α × EncodedDFA α) × ℕ => pairNext x.1.1 x.1.2 x.2 :=
  Primrec.list_map
    (Primrec.list_append.comp (primrec_letters.comp (Primrec.fst.comp Primrec.fst))
      (primrec_letters.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec₂.natPair.comp
      (primrec_step.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)))
      (primrec_step.comp (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)))).to₂

theorem primrec_pairReachable : Primrec₂ (pairReachable (α := α)) :=
  primrec_reachN (Primrec₂.natPair.comp (primrec_start.comp Primrec.fst)
      (primrec_start.comp Primrec.snd))
    primrec_pairNext.to₂ primrec_pairStates

theorem primrec_equivB : Primrec₂ (equivB (α := α)) :=
  primrec_list_all
    (Primrec.beq.comp₂
      (primrec_memB.comp₂ (primrec_accept.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        (Primrec.fst.comp₂ (Primrec.unpair.comp₂ Primrec₂.right)))
      (primrec_memB.comp₂ (primrec_accept.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
        (Primrec.snd.comp₂ (Primrec.unpair.comp₂ Primrec₂.right))))
    primrec_pairReachable

/-- **Sipser, Theorem 4.1**: acceptance for DFAs (A_DFA) is decidable by a multi-stack
machine. -/
theorem tm2Decidable_mem_language :
    TM2Decidable fun p : EncodedDFA α × List α => p.2 ∈ p.1.language :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_acceptsB fun _ => acceptsB_iff)

/-- **Sipser, Theorem 4.4**: emptiness for DFAs (E_DFA) is decidable by a multi-stack
machine. -/
theorem tm2Decidable_language_eq_zero : TM2Decidable fun D : EncodedDFA α => D.language = 0 :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_isEmptyB fun _ => isEmptyB_iff)

/-- **Sipser, Theorem 4.5**: equivalence of DFAs (EQ_DFA) is decidable by a multi-stack
machine. -/
theorem tm2Decidable_language_eq :
    TM2Decidable fun p : EncodedDFA α × EncodedDFA α => p.1.language = p.2.language :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_equivB fun _ => equivB_iff)

theorem primrec_isUnivB : Primrec (isUnivB (α := α)) :=
  primrec_list_all (primrec_memB.comp₂ (primrec_accept.comp₂ Primrec₂.left) Primrec₂.right)
    primrec_reachable

/-- **Universality for DFAs (ALL_DFA) is decidable** by a multi-stack machine. -/
theorem tm2Decidable_language_eq_top : TM2Decidable fun D : EncodedDFA α => D.language = ⊤ :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_isUnivB fun _ => isUnivB_iff)

section Infinite

variable [FinEnum α]

omit [DecidableEq α] in
theorem primrec_wordsOfLength : Primrec (wordsOfLength (α := α)) :=
  (Primrec.nat_iterate Primrec.id (Primrec.const [[]])
    (Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.const (FinEnum.toList α))
        (Primrec.list_cons.comp₂ Primrec₂.right (Primrec.snd.comp₂ Primrec₂.left))).to₂).to₂).of_eq
    fun _ => rfl

theorem primrec_infiniteB : Primrec (infiniteB (α := α)) :=
  primrec_list_any
    (primrec_list_any (primrec_acceptsB.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (primrec_wordsOfLength.comp (Primrec.nat_add.comp
        (Primrec.list_length.comp (primrec_states.comp Primrec.fst)) Primrec.snd))).to₂
    (Primrec.list_range.comp (Primrec.list_length.comp primrec_states))

/-- **Infiniteness for DFAs (INFINITE_DFA) is decidable** by a multi-stack machine, over a
finite alphabet. -/
theorem tm2Decidable_language_infinite :
    TM2Decidable fun D : EncodedDFA α => D.language.Infinite :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_infiniteB fun _ => infiniteB_iff)

end Infinite

end Computability

end Cslib.Automata.EncodedDFA
