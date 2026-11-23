/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# The Earley recognizer

An Earley item is a production with a dot marking how much of its
right-hand side has been recognized, together with the input already
consumed before the item's origin (`pre`) and the input consumed by the
recognized prefix (`consumed`). The chart is the least set of items
closed under prediction (a nonterminal after the dot starts a new item
at the current position), scanning (a terminal after the dot consumes
the next input letter), and completion (a completed item advances every
item waiting on its nonterminal). Positions are carried as input words
rather than indices, so no slice arithmetic is needed: the chart
invariant is `w = pre ++ consumed ++ rest` for some `rest`.

## Main definitions

* `Cslib.Language.EarleyItem`: an Earley item: production, dot, `pre`, `consumed`.
* `Cslib.Language.EarleyChart`: the chart, as an inductive closure.
* `Cslib.Language.EarleyChartItem`: the chart as a predicate on `EarleyItem`s.
* `Cslib.Language.earleyAccepts`: acceptance by a completed item for a
  production of the initial nonterminal consuming the whole input.

## Main results

* `Cslib.Language.yields_take_of_earleyChart`: soundness: an item's
  recognized prefix yields its consumed input.
* `Cslib.Language.earleyChart_complete_of_yields`: completeness: a
  yield of the unrecognized suffix completes any chart item waiting
  on it, provided the yield fits in the remaining input.
* `Cslib.Language.earleyAccepts_iff`: the Earley recognizer accepts
  exactly the grammar's language.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {g : ContextFreeGrammar T}

/-- An Earley item: a production with a dot after `dot` symbols of its
output, recognizing input that starts at the end of `pre` and whose
recognized prefix is `consumed`. The full input is `pre ++ consumed
++ rest` for some `rest`. -/
structure EarleyItem (T : Type*) (N : Type*) where
  /-- The production whose right-hand side is being recognized. -/
  rule : ContextFreeRule T N
  /-- How many symbols of `rule.output` have been recognized so far. -/
  dot : ℕ
  /-- The input consumed before the origin of this item. -/
  pre : List T
  /-- The input consumed by the recognized prefix `rule.output.take dot`. -/
  consumed : List T

/-- The Earley chart for input `w`: the least set of items closed
under initialization, prediction, scanning, and completion.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
inductive EarleyChart (g : ContextFreeGrammar T) (w : List T) :
    ContextFreeRule T g.NT → ℕ → List T → List T → Prop
  | init {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
      (hinit : r.input = g.initial) :
      EarleyChart g w r 0 [] []
  | predict {r : ContextFreeRule T g.NT} {k : ℕ} {pre consumed : List T}
      (h : EarleyChart g w r k pre consumed) {A : g.NT}
      (hnext : r.output[k]? = some (Symbol.nonterminal A))
      {r' : ContextFreeRule T g.NT} (hr' : r' ∈ g.rules)
      (hinput : r'.input = A) :
      EarleyChart g w r' 0 (pre ++ consumed) []
  | scan {r : ContextFreeRule T g.NT} {k : ℕ} {pre consumed : List T}
      (h : EarleyChart g w r k pre consumed) {a : T}
      (hnext : r.output[k]? = some (Symbol.terminal a)) {rest : List T}
      (hw : w = pre ++ consumed ++ a :: rest) :
      EarleyChart g w r (k + 1) pre (consumed ++ [a])
  | complete {r : ContextFreeRule T g.NT} {k : ℕ} {pre consumed : List T}
      (h : EarleyChart g w r k pre consumed) {A : g.NT}
      (hnext : r.output[k]? = some (Symbol.nonterminal A))
      {r' : ContextFreeRule T g.NT} {consumed' : List T}
      (hr' : r' ∈ g.rules) (hinput : r'.input = A)
      (hcomp : EarleyChart g w r' r'.output.length (pre ++ consumed)
        consumed') :
      EarleyChart g w r (k + 1) pre (consumed ++ consumed')

/-- The chart as a predicate on `EarleyItem`s.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
def EarleyChartItem (g : ContextFreeGrammar T) (w : List T)
    (item : EarleyItem T g.NT) : Prop :=
  EarleyChart g w item.rule item.dot item.pre item.consumed

/-- Acceptance by the Earley recognizer: some completed item for a
production of the initial nonterminal consumes the whole input.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
def earleyAccepts (g : ContextFreeGrammar T) (w : List T) : Prop :=
  ∃ (r : ContextFreeRule T g.NT), r ∈ g.rules ∧ r.input = g.initial ∧
    EarleyChartItem g w ⟨r, r.output.length, [], w⟩

/-- A defined list entry bounds its index by the length.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
private theorem lt_length_of_getElem?_eq_some {α : Type*} {l : List α}
    {k : ℕ} {s : α} (h : l[k]? = some s) : k < l.length := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons b l => simp
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons b l => exact Nat.succ_lt_succ (ih h)

/-- The symbol after a dropped prefix is the symbol at that index.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
private theorem getElem?_of_drop_eq_cons {α : Type*} {l : List α}
    {k : ℕ} {s : α} {rest : List α} (h : l.drop k = s :: rest) :
    l[k]? = some s := by
  induction k generalizing l with
  | zero =>
    simp only [List.drop_zero] at h
    subst h
    rfl
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons b l => exact ih h

/-- Dropping one more symbol after a dropped prefix drops its head.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
private theorem drop_succ_eq_of_drop_eq_cons {α : Type*} {l : List α}
    {k : ℕ} {s : α} {rest : List α} (h : l.drop k = s :: rest) :
    l.drop (k + 1) = rest := by
  induction k generalizing l with
  | zero =>
    simp only [List.drop_zero] at h
    subst h
    rfl
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons b l => exact ih h

/-- Taking one more symbol appends the symbol at that index.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
private theorem take_succ_eq_of_getElem? {α : Type*} {l : List α}
    {k : ℕ} {s : α} (h : l[k]? = some s) :
    l.take (k + 1) = l.take k ++ [s] := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons b l =>
      have h' : b = s := Option.some.inj h
      subst h'
      rfl
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons b l =>
      change b :: l.take (k + 1) = (b :: l.take k) ++ [s]
      rw [ih h, List.cons_append]

/-- The dot of a chart item never passes the end of its production.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
theorem dot_le_of_earleyChart {w : List T} {r : ContextFreeRule T g.NT}
    {k : ℕ} {pre consumed : List T}
    (h : EarleyChart g w r k pre consumed) : k ≤ r.output.length := by
  induction h with
  | init hr hinit => exact Nat.zero_le _
  | predict h hnext hr' hinput ih => exact Nat.zero_le _
  | scan h hnext hw ih =>
    exact Nat.succ_le_of_lt (lt_length_of_getElem?_eq_some hnext)
  | complete h hnext hr' hinput hcomp ih ihcomp =>
    exact Nat.succ_le_of_lt (lt_length_of_getElem?_eq_some hnext)

/-- Soundness: the recognized prefix of a chart item yields the input
it consumed.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
theorem yields_take_of_earleyChart {w : List T} {r : ContextFreeRule T g.NT}
    {k : ℕ} {pre consumed : List T}
    (h : EarleyChart g w r k pre consumed) :
    Yields g (r.output.take k) consumed := by
  induction h with
  | init hr hinit => exact Yields.nil
  | predict h hnext hr' hinput ih => exact Yields.nil
  | scan h hnext hw ih =>
    rw [take_succ_eq_of_getElem? hnext]
    exact Yields.append ih (Yields.terminal _ Yields.nil)
  | complete h hnext hr' hinput hcomp ih ihcomp =>
    rw [List.take_length] at ihcomp
    rw [take_succ_eq_of_getElem? hnext]
    apply Yields.append ih
    have hy := yields_of_rule hr' ihcomp
    rwa [hinput] at hy

/-- Completeness: if a chart item waits on a sentential form and that
form yields a word fitting in the remaining input, the chart contains
the item completed by that word.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
theorem earleyChart_complete_of_yields {w : List T}
    {α : List (Symbol T g.NT)} {u : List T} (h : Yields g α u) :
    ∀ {ρ : ContextFreeRule T g.NT} {k : ℕ} {pre consumed : List T}
      {rest : List T},
      EarleyChart g w ρ k pre consumed → ρ.output.drop k = α →
      w = pre ++ consumed ++ u ++ rest →
      EarleyChart g w ρ ρ.output.length pre (consumed ++ u) := by
  induction h with
  | nil =>
    intro ρ k pre consumed rest hchart hdrop hw
    have hkeq : k = ρ.output.length := by
      have hle := dot_le_of_earleyChart hchart
      have hlen : (ρ.output.drop k).length = 0 := by
        rw [hdrop]
        rfl
      rw [List.length_drop] at hlen
      have hge : ρ.output.length ≤ k := by omega
      exact le_antisymm hle hge
    rw [← hkeq]
    simpa using hchart
  | terminal a htail ih =>
    rename_i α' u'
    intro ρ k pre consumed rest hchart hdrop hw
    have hnext : ρ.output[k]? = some (Symbol.terminal a) :=
      getElem?_of_drop_eq_cons hdrop
    have hdrop' : ρ.output.drop (k + 1) = α' :=
      drop_succ_eq_of_drop_eq_cons hdrop
    have hscan : EarleyChart g w ρ (k + 1) pre (consumed ++ [a]) :=
      EarleyChart.scan (rest := u' ++ rest) hchart hnext
        (by rw [hw]; simp [List.append_assoc])
    have hcomp := ih (rest := rest) hscan hdrop'
      (by rw [hw]; simp [List.append_assoc])
    simpa [List.append_assoc] using hcomp
  | nonterminal hr hout hrest ihout ihrest =>
    rename_i r α' w₁ w₂
    intro ρ k pre consumed rest hchart hdrop hw
    have hnext : ρ.output[k]? = some (Symbol.nonterminal r.input) :=
      getElem?_of_drop_eq_cons hdrop
    have hdrop' : ρ.output.drop (k + 1) = α' :=
      drop_succ_eq_of_drop_eq_cons hdrop
    have hpred := EarleyChart.predict hchart hnext hr rfl
    have hcomp := ihout (rest := w₂ ++ rest) hpred List.drop_zero
      (by rw [hw]; simp [List.append_assoc])
    have hcomplete := EarleyChart.complete hchart hnext hr rfl hcomp
    have hdone := ihrest (rest := rest) hcomplete hdrop'
      (by rw [hw]; simp [List.append_assoc])
    simpa [List.append_assoc] using hdone

/-- Inversion of a yield from a single nonterminal: it begins with
one production of that nonterminal.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
theorem exists_rule_of_yields_singleton {A : g.NT} {w : List T}
    (h : Yields g [Symbol.nonterminal A] w) :
    ∃ (r : ContextFreeRule T g.NT), r ∈ g.rules ∧ r.input = A ∧
      Yields g r.output w := by
  cases h with
  | nonterminal hr hout hrest =>
    cases hrest with
    | nil => exact ⟨_, hr, rfl, by simpa using hout⟩

/-- The Earley recognizer accepts exactly the grammar's language.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
theorem earleyAccepts_iff {w : List T} :
    earleyAccepts g w ↔ w ∈ g.language := by
  constructor
  · rintro ⟨r, hr, hinit, hchart⟩
    have hchart' : EarleyChart g w r r.output.length [] w := hchart
    have hy := yields_take_of_earleyChart hchart'
    rw [List.take_length] at hy
    have hy2 : Yields g [Symbol.nonterminal g.initial] w := by
      rw [← hinit]
      exact yields_of_rule hr hy
    exact mem_language_iff_yields.mpr hy2
  · intro hw
    have hy : Yields g [Symbol.nonterminal g.initial] w :=
      mem_language_iff_yields.mp hw
    obtain ⟨r, hr, hinit, hout⟩ := exists_rule_of_yields_singleton hy
    refine ⟨r, hr, hinit, ?_⟩
    change EarleyChart g w r r.output.length [] w
    have hchart : EarleyChart g w r 0 [] [] := EarleyChart.init hr hinit
    have hcomp := earleyChart_complete_of_yields (rest := []) hout hchart
      List.drop_zero (by simp)
    simpa using hcomp

end Cslib.Language
