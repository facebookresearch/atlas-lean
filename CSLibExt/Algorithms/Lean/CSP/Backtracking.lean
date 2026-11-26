/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.AC3
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card

/-!
# Backtracking search with forward checking: soundness and completeness

Backtracking search with forward checking (Haralick and Elliott, *Increasing tree search
efficiency for constraint satisfaction problems*, Artificial Intelligence 14 (1980); Russell and
Norvig, *Artificial Intelligence: A Modern Approach*, fourth edition, Section 6.3) solves a
binary constraint satisfaction problem (`BinaryCSP X D`, from AC-3) within domains
`dom : X → Finset D`. It picks an unassigned variable `x`, tries the values of its current domain
one at a time and, for `x = a`, *forward checks*: it shrinks the current domain of every other
variable `y` joined to `x` by an arc to the values `b` with `x = a, y = b` allowed by every arc
between `x` and `y` (`forwardCheck`); a variable with no arc to `x` keeps its domain unchanged.
A value whose forward check empties the domain of an unassigned variable is
skipped (a *wipeout*); otherwise the search recurses and backtracks to the next value on failure.

The variable and value orders are parameters (`SearchOrder`): any rule that picks an unassigned
variable from the current domains, and any list enumerating exactly the current domain of the
picked variable. `SearchOrder.ofLinearOrder` picks the least variable and tries values in
increasing order; `SearchOrder.mrv` picks a variable with the fewest remaining values
(*minimum remaining values*, Russell and Norvig, Section 6.3.1).

Main results, for every search order:

* `backtrackFC_sound`: a returned assignment is a solution within the domains (`IsSolution`).
* `backtrackFC_complete`: if a solution exists, the search returns an assignment.
* `backtrackFC_isSome_iff`, `backtrackFC_eq_none_iff`: the search succeeds iff a solution exists.

## Scope

This file states correctness only. `backtrackFC` returns an `Option` and charges no cost, and no
bound on the number of search nodes is claimed. Self-loop arcs `(x, x)` are unary constraints:
`x = a` is tried only when every such arc allows `(a, a)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CSPBacktracking

open Cslib.Algorithms.Lean.ArcConsistency

variable {X D : Type*} [DecidableEq X] (P : BinaryCSP X D)

/-- The arcs between `x` and `y`, in either orientation, filtered from the whole arc list. Only
these arcs constrain `x` and `y`; unrelated arcs are still inspected when locating them. -/
def incidentArcs (x y : X) : List (X × X) :=
  P.arcs.filter fun e => e = (x, y) ∨ e = (y, x)

theorem mem_incidentArcs {x y : X} {e : X × X} :
    e ∈ incidentArcs P x y ↔ e ∈ P.arcs ∧ (e = (x, y) ∨ e = (y, x)) := by
  simp [incidentArcs]

/-- `compat P x a y b`: every arc between `x` and `y` allows `x = a` together with `y = b`, in
both orientations. -/
def compat (x : X) (a : D) (y : X) (b : D) : Bool :=
  P.arcs.all fun e =>
    decide ((e = (x, y) → P.allowed x y a b = true) ∧ (e = (y, x) → P.allowed y x b a = true))

/-- Compatibility checked against a supplied list of arcs; forward checking applies it to
`incidentArcs`, so the full arc list is not rescanned for every candidate value. -/
def compatOn (arcs : List (X × X)) (x : X) (a : D) (y : X) (b : D) : Bool :=
  arcs.all fun e =>
    decide ((e = (x, y) → P.allowed x y a b = true) ∧ (e = (y, x) → P.allowed y x b a = true))

/-- Forward checking after `x = a`: `x` keeps only `a`; a variable joined to `x` by an arc
keeps the values compatible with `x = a`; any other variable keeps its domain unchanged. -/
def forwardCheck (dom : X → Finset D) (x : X) (a : D) : X → Finset D :=
  fun y => if y = x then {a}
    else
      let arcs := incidentArcs P x y
      if arcs.isEmpty then dom y
      else (dom y).filter fun b => compatOn P arcs x a y b

/-- A variable order and a value order: `pick` chooses an unassigned variable from the current
domains, and `vals dom x` lists exactly the current domain of `x`, in the order to try. -/
structure SearchOrder (X D : Type*) where
  /-- The next variable, chosen from the current domains among the unassigned ones `U`. -/
  pick : (X → Finset D) → (U : Finset X) → U.Nonempty → X
  pick_mem : ∀ dom U h, pick dom U h ∈ U
  /-- The values of `x` to try, in order. -/
  vals : (X → Finset D) → X → List D
  mem_vals : ∀ dom x a, a ∈ vals dom x ↔ a ∈ dom x

/-- The total assignment read off a partial one, if every variable is assigned. -/
def toTotal [Fintype X] (asg : X → Option D) : Option (X → D) :=
  if h : ∀ x, (asg x).isSome then some fun x => (asg x).get (h x) else none

/-- The search with fuel `n`, current domains `dom`, partial assignment `asg` and unassigned
variables `U`. -/
def search [Fintype X] (O : SearchOrder X D) :
    ℕ → (X → Finset D) → (X → Option D) → Finset X → Option (X → D)
  | 0, _, asg, _ => toTotal asg
  | n + 1, dom, asg, U =>
      if hU : U.Nonempty then
        (O.vals dom (O.pick dom U hU)).findSome? fun a =>
          if compat P (O.pick dom U hU) a (O.pick dom U hU) a = true ∧
              ∀ y ∈ U.erase (O.pick dom U hU),
                (forwardCheck P dom (O.pick dom U hU) a y).Nonempty then
            search O n (forwardCheck P dom (O.pick dom U hU) a)
              (Function.update asg (O.pick dom U hU) (some a)) (U.erase (O.pick dom U hU))
          else none
      else toTotal asg

/-- **Backtracking with forward checking** from the domains `dom`, all variables unassigned. -/
def backtrackFC [Fintype X] (O : SearchOrder X D) (dom : X → Finset D) : Option (X → D) :=
  search P O (Fintype.card X) dom (fun _ => none) Finset.univ

/-! ## Compatibility -/

theorem compat_eq_true {x : X} {a : D} {y : X} {b : D} :
    compat P x a y b = true ↔
      ∀ e ∈ P.arcs, (e = (x, y) → P.allowed x y a b = true) ∧
        (e = (y, x) → P.allowed y x b a = true) := by
  simp only [compat, List.all_eq_true, decide_eq_true_eq]

theorem compatOn_incidentArcs {x : X} {a : D} {y : X} {b : D} :
    compatOn P (incidentArcs P x y) x a y b = compat P x a y b := by
  rw [Bool.eq_iff_iff, compat_eq_true]
  simp only [compatOn, incidentArcs, List.all_eq_true, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · intro h e he
    by_cases hxy : e = (x, y) ∨ e = (y, x)
    · exact h e ⟨he, hxy⟩
    · rw [not_or] at hxy
      exact ⟨fun h => (hxy.1 h).elim, fun h => (hxy.2 h).elim⟩
  · intro h e he
    exact h e he.1

theorem compat_of_incidentArcs_eq_nil {x y : X} (h : incidentArcs P x y = [])
    (a : D) (b : D) : compat P x a y b = true := by
  rw [compat_eq_true]
  intro e he
  have hne : ¬(e = (x, y) ∨ e = (y, x)) := by
    intro hxy
    have hmem : e ∈ incidentArcs P x y := (mem_incidentArcs P).2 ⟨he, hxy⟩
    rw [h] at hmem
    simp at hmem
  rw [not_or] at hne
  exact ⟨fun hxy => (hne.1 hxy).elim, fun hyx => (hne.2 hyx).elim⟩

theorem compat_comm (x : X) (a : D) (y : X) (b : D) : compat P x a y b = compat P y b x a := by
  rw [Bool.eq_iff_iff, compat_eq_true, compat_eq_true]
  exact forall₂_congr fun _ _ => And.comm

theorem allowed_of_compat {u v : X} {a b : D} (h : compat P u a v b = true)
    (he : (u, v) ∈ P.arcs) : P.allowed u v a b = true :=
  ((compat_eq_true P).1 h _ he).1 rfl

theorem compat_of_isSolution {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    (x y : X) : compat P x (σ x) y (σ y) = true := by
  rw [compat_eq_true]
  intro e he
  exact ⟨fun h => by subst h; exact hσ.2 _ he, fun h => by subst h; exact hσ.2 _ he⟩

/-! ## Forward checking -/

theorem forwardCheck_subset {dom : X → Finset D} {x : X} {a : D} (ha : a ∈ dom x) (y : X) :
    forwardCheck P dom x a y ⊆ dom y := by
  simp only [forwardCheck]
  split_ifs with hy
  · subst hy; exact Finset.singleton_subset_iff.2 ha
  · exact subset_rfl
  · exact Finset.filter_subset (fun b => compatOn P (incidentArcs P x y) x a y b) (dom y)

/-- A variable `y ≠ x` with no arc to or from `x` keeps its domain under forward checking. -/
theorem forwardCheck_eq_of_isEmpty {dom : X → Finset D} {x : X} {a : D} {y : X}
    (hy : y ≠ x) (h : (incidentArcs P x y).isEmpty = true) :
    forwardCheck P dom x a y = dom y := by
  simp [forwardCheck, hy, h]

theorem compat_of_mem_forwardCheck {dom : X → Finset D} {x : X} {a : D}
    (hxx : compat P x a x a = true) {y : X} {b : D} (hb : b ∈ forwardCheck P dom x a y) :
    compat P x a y b = true := by
  simp only [forwardCheck] at hb
  split_ifs at hb with hy hinc
  · subst hy; rw [Finset.mem_singleton.1 hb]; exact hxx
  · have hnil : incidentArcs P x y = [] := by
      by_contra hne
      rw [List.isEmpty_iff] at hinc
      exact hne hinc
    exact compat_of_incidentArcs_eq_nil P hnil a b
  · rw [← compatOn_incidentArcs (P := P)]
    exact (Finset.mem_filter.1 hb).2

/-- Forward checking after `x = σ x` keeps a solution `σ` within the domains. -/
theorem isSolution_forwardCheck {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    (x : X) : IsSolution P (forwardCheck P dom x (σ x)) σ := by
  refine ⟨fun y => ?_, hσ.2⟩
  simp only [forwardCheck]
  split_ifs with hy hinc
  · subst hy; exact Finset.mem_singleton_self _
  · exact hσ.1 y
  · exact (Finset.mem_filter
      (p := fun b => compatOn P (incidentArcs P x y) x (σ x) y b)).2
      ⟨hσ.1 y, by
        rw [compatOn_incidentArcs (P := P)]
        exact compat_of_isSolution P hσ x y⟩

/-! ## Reading off the assignment -/

omit [DecidableEq X] in
theorem toTotal_eq_some [Fintype X] {asg : X → Option D} {σ : X → D}
    (h : toTotal asg = some σ) (x : X) : asg x = some (σ x) := by
  unfold toTotal at h
  split_ifs at h with hall
  cases h
  exact (Option.some_get (hall x)).symm

omit [DecidableEq X] in
theorem toTotal_isSome [Fintype X] {asg : X → Option D} (h : ∀ x, (asg x).isSome) :
    (toTotal asg).isSome := by
  simp [toTotal, h]

/-! ## Soundness -/

/-- The soundness invariant relative to the input domains `dom₀`: assigned values lie in `dom₀`
and are pairwise compatible (an assigned entry with itself included), the current domains only
hold values compatible with every assigned value, and the current domains lie within `dom₀`. -/
structure SoundInv (dom₀ dom : X → Finset D) (asg : X → Option D) : Prop where
  mem : ∀ x a, asg x = some a → a ∈ dom₀ x
  pair : ∀ x a y b, asg x = some a → asg y = some b → compat P x a y b = true
  prune : ∀ x a y b, asg x = some a → b ∈ dom y → compat P x a y b = true
  sub : ∀ y, dom y ⊆ dom₀ y

theorem soundInv_init (dom₀ : X → Finset D) : SoundInv P dom₀ dom₀ fun _ => none where
  mem := by simp
  pair := by simp
  prune := by simp
  sub := fun _ => subset_rfl

/-- Assigning `x = a` from its current domain, with `x = a` compatible with itself, followed by
forward checking, keeps the invariant. -/
theorem soundInv_step {dom₀ dom : X → Finset D} {asg : X → Option D}
    (hI : SoundInv P dom₀ dom asg) {x : X} {a : D} (ha : a ∈ dom x)
    (hxx : compat P x a x a = true) :
    SoundInv P dom₀ (forwardCheck P dom x a) (Function.update asg x (some a)) where
  mem u c h := by
    obtain rfl | hu := eq_or_ne u x
    · rw [Function.update_self] at h; cases h; exact hI.sub u ha
    · rw [Function.update_of_ne hu] at h; exact hI.mem u c h
  pair u c v d hu hv := by
    obtain rfl | hux := eq_or_ne u x
    · rw [Function.update_self] at hu; cases hu
      obtain rfl | hvx := eq_or_ne v u
      · rw [Function.update_self] at hv; cases hv; exact hxx
      · rw [Function.update_of_ne hvx] at hv
        rw [compat_comm]; exact hI.prune v d u a hv ha
    · rw [Function.update_of_ne hux] at hu
      obtain rfl | hvx := eq_or_ne v x
      · rw [Function.update_self] at hv; cases hv; exact hI.prune u c v a hu ha
      · rw [Function.update_of_ne hvx] at hv; exact hI.pair u c v d hu hv
  prune u c y b hu hb := by
    obtain rfl | hux := eq_or_ne u x
    · rw [Function.update_self] at hu; cases hu; exact compat_of_mem_forwardCheck P hxx hb
    · rw [Function.update_of_ne hux] at hu
      exact hI.prune u c y b hu (forwardCheck_subset P ha y hb)
  sub y := (forwardCheck_subset P ha y).trans (hI.sub y)

theorem search_sound [Fintype X] (O : SearchOrder X D) (dom₀ : X → Finset D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X) (σ : X → D),
      SoundInv P dom₀ dom asg → search P O n dom asg U = some σ → IsSolution P dom₀ σ := by
  have hdone : ∀ (dom : X → Finset D) (asg : X → Option D) (σ : X → D),
      SoundInv P dom₀ dom asg → toTotal asg = some σ → IsSolution P dom₀ σ := by
    intro dom asg σ hI h
    have hσ := toTotal_eq_some h
    refine ⟨fun x => hI.mem x _ (hσ x), fun e he => ?_⟩
    obtain ⟨u, v⟩ := e
    exact allowed_of_compat P (hI.pair u _ v _ (hσ u) (hσ v)) he
  intro n
  induction n with
  | zero => intro dom asg U σ hI h; exact hdone dom asg σ hI h
  | succ n ih =>
      intro dom asg U σ hI h
      simp only [search] at h
      split_ifs at h with hU
      · obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some h
        split_ifs at hfa with hc
        exact ih _ _ _ σ (soundInv_step P hI ((O.mem_vals _ _ _).1 ha) hc.1) hfa
      · exact hdone dom asg σ hI h

/-- **Soundness**: an assignment returned by backtracking with forward checking is a solution
within the domains, for every search order. -/
theorem backtrackFC_sound [Fintype X] (O : SearchOrder X D) {dom : X → Finset D} {σ : X → D}
    (h : backtrackFC P O dom = some σ) : IsSolution P dom σ :=
  search_sound P O dom _ _ _ _ σ (soundInv_init P dom) h

/-! ## Completeness -/

theorem search_complete [Fintype X] (O : SearchOrder X D) (τ : X → D) :
    ∀ (n : ℕ) (dom : X → Finset D) (asg : X → Option D) (U : Finset X),
      U.card ≤ n → IsSolution P dom τ → (∀ y ∉ U, asg y = some (τ y)) →
        (search P O n dom asg U).isSome := by
  have hdone : ∀ (asg : X → Option D) (U : Finset X), ¬U.Nonempty →
      (∀ y ∉ U, asg y = some (τ y)) → (toTotal asg).isSome := by
    intro asg U hU hasg
    rw [Finset.not_nonempty_iff_eq_empty] at hU
    subst hU
    exact toTotal_isSome fun x => by rw [hasg x (Finset.notMem_empty x)]; rfl
  intro n
  induction n with
  | zero =>
      intro dom asg U hcard _ hasg
      have h0 : U = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      exact hdone asg U (by rw [h0]; exact Finset.not_nonempty_empty) hasg
  | succ n ih =>
      intro dom asg U hcard hτ hasg
      simp only [search]
      split_ifs with hU
      · set x := O.pick dom U hU with hx
        have hxU : x ∈ U := O.pick_mem dom U hU
        rw [List.findSome?_isSome_iff]
        refine ⟨τ x, (O.mem_vals _ _ _).2 (hτ.1 x), ?_⟩
        have hfc := isSolution_forwardCheck P hτ x
        have hc : compat P x (τ x) x (τ x) = true ∧
            ∀ y ∈ U.erase x, (forwardCheck P dom x (τ x) y).Nonempty :=
          ⟨compat_of_isSolution P hτ x x, fun y _ => ⟨τ y, hfc.1 y⟩⟩
        split_ifs
        · refine ih _ _ _ ?_ hfc fun y hy => ?_
          · rw [Finset.card_erase_of_mem hxU]; omega
          · obtain rfl | hyx := eq_or_ne y x
            · rw [Function.update_self]
            · rw [Function.update_of_ne hyx]
              exact hasg y fun hyU => hy (Finset.mem_erase.2 ⟨hyx, hyU⟩)
      · exact hdone asg U hU hasg

/-- **Completeness**: if a solution within the domains exists, backtracking with forward checking
returns an assignment, for every search order. -/
theorem backtrackFC_complete [Fintype X] (O : SearchOrder X D) {dom : X → Finset D} {σ : X → D}
    (hσ : IsSolution P dom σ) : (backtrackFC P O dom).isSome :=
  search_complete P O σ _ dom _ _ (Finset.card_le_univ _) hσ fun y hy =>
    absurd (Finset.mem_univ y) hy

/-- Backtracking with forward checking succeeds iff a solution exists. -/
theorem backtrackFC_isSome_iff [Fintype X] (O : SearchOrder X D) (dom : X → Finset D) :
    (backtrackFC P O dom).isSome ↔ ∃ σ, IsSolution P dom σ := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 h
    exact ⟨σ, backtrackFC_sound P O hσ⟩
  · rintro ⟨σ, hσ⟩
    exact backtrackFC_complete P O hσ

/-- Backtracking with forward checking fails iff there is no solution. -/
theorem backtrackFC_eq_none_iff [Fintype X] (O : SearchOrder X D) (dom : X → Finset D) :
    backtrackFC P O dom = none ↔ ∀ σ, ¬IsSolution P dom σ := by
  rw [← Option.not_isSome_iff_eq_none, backtrackFC_isSome_iff, not_exists]

/-! ## Search orders -/

/-- The first `n` elements of `s` in increasing order, by repeatedly removing the minimum. Unlike
`Finset.sort`, it reduces in the kernel, so `decide` evaluates searches that use it. -/
def ascending {α : Type*} [LinearOrder α] : ℕ → Finset α → List α
  | 0, _ => []
  | n + 1, s => if h : s.Nonempty then s.min' h :: ascending n (s.erase (s.min' h)) else []

theorem mem_ascending {α : Type*} [LinearOrder α] :
    ∀ (n : ℕ) (s : Finset α), s.card ≤ n → ∀ a, a ∈ ascending n s ↔ a ∈ s := by
  intro n
  induction n with
  | zero =>
      intro s hs a
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hs)]
      simp [ascending]
  | succ n ih =>
      intro s hs a
      by_cases h : s.Nonempty
      · have hm := s.min'_mem h
        have hcard : (s.erase (s.min' h)).card ≤ n := by
          rw [Finset.card_erase_of_mem hm]; omega
        simp only [ascending, h, ↓reduceDIte, List.mem_cons, ih _ hcard, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨-, ha⟩)
          · exact hm
          · exact ha
        · intro ha
          by_cases hae : a = s.min' h
          · exact Or.inl hae
          · exact Or.inr ⟨hae, ha⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at h
        subst h
        simp [ascending]

/-- The least unassigned variable, values in increasing order. -/
def SearchOrder.ofLinearOrder [LinearOrder X] [LinearOrder D] : SearchOrder X D where
  pick _ U h := U.min' h
  pick_mem _ U h := U.min'_mem h
  vals dom x := ascending (dom x).card (dom x)
  mem_vals dom x a := mem_ascending _ (dom x) le_rfl a

/-- The unassigned variables with the fewest remaining values. -/
def mrvCandidates (dom : X → Finset D) (U : Finset X) : Finset X :=
  U.filter fun y => ∀ z ∈ U, (dom y).card ≤ (dom z).card

omit [DecidableEq X] in
theorem mrvCandidates_nonempty {dom : X → Finset D} {U : Finset X} (h : U.Nonempty) :
    (mrvCandidates dom U).Nonempty := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image U (fun y => (dom y).card) h
  exact ⟨y, Finset.mem_filter.2 ⟨hy, hmin⟩⟩

/-- **Minimum remaining values**: the least unassigned variable with the fewest remaining values,
values in increasing order. -/
def SearchOrder.mrv [LinearOrder X] [LinearOrder D] : SearchOrder X D where
  pick dom U h := (mrvCandidates dom U).min' (mrvCandidates_nonempty h)
  pick_mem _ _ h := (Finset.mem_filter.1 (Finset.min'_mem _ (mrvCandidates_nonempty h))).1
  vals dom x := ascending (dom x).card (dom x)
  mem_vals dom x a := mem_ascending _ (dom x) le_rfl a

omit [DecidableEq X] in
/-- The variable picked by `SearchOrder.mrv` has no more remaining values than any other
unassigned variable. -/
theorem SearchOrder.mrv_pick_card_le [LinearOrder X] [LinearOrder D] (dom : X → Finset D)
    (U : Finset X) (h : U.Nonempty) :
    ∀ z ∈ U, (dom ((SearchOrder.mrv : SearchOrder X D).pick dom U h)).card ≤ (dom z).card :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (mrvCandidates_nonempty h))).2

end Cslib.Algorithms.Lean.CSPBacktracking
