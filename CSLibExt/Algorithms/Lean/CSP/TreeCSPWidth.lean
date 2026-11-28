/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.ConstraintWidth
public import CSLibExt.Algorithms.Lean.CSP.TreeCSP
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn

/-!
# Tree CSPs on forest constraint graphs

`TreeCSP` states its results for a parent map `parent : X → Option X` with a root-first order;
`ConstraintWidth` defines the simple constraint graph of a binary CSP and the width of an
ordering of its variables. This file connects the two models.

For an ordering `d`, `P.orderParent d x` is the earliest neighbor of `x` in the constraint graph
that `d` places before `x`. Listing the variables by position is a root-first order for it
(`rootedOrder_orderParent`). When `d` has width at most one, the parent of `x` is its only earlier
neighbor (`orderParent_eq_some_iff`), and, if no arc joins a variable to itself, every arc joins
a variable and its parent (`isTreeArcs_orderParent`). A forest constraint graph has an ordering of
width at most one (`constraintWidth_le_one_of_isAcyclic`), hence such a parent map
(`exists_rootedOrder_of_isAcyclic`).

Main results, for symmetric constraints (`Symmetric`) and no self-arcs:

* `treeSolve_orderParent_ne_none_iff`: along an ordering of width at most one, the tree-CSP
  algorithm succeeds iff the CSP has a solution, and then returns one
  (`isSolution_of_treeSolve_eq_some`).
* `exists_treeSolve_ne_none_iff_of_isAcyclic` (**forests are backtrack-free**): the same for
  some root-first order whenever the constraint graph is acyclic.
* `treeSolveT_ret`, `treeSolveT_time_le`: with both phases charged, the algorithm returns what
  `treeSolve` returns and performs at most `n · d² + n · d` relation checks for `n` variables and
  domains of size at most `d`.

## Cost model

`treeSolveT` charges the DAC pass as `dac` does (`|dom p| · |dom x|` checks for each variable `x`
with parent `p`), then charges `|dom x|` checks for each variable `x` with a parent when greedy
assignment filters the candidates of `x` against the value of its parent. Roots, the selection
function and assignment updates are free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ArcConsistency

open Cslib.Algorithms.Lean

namespace BinaryCSP

variable {X D : Type*} [DecidableEq X] [Fintype X] (P : BinaryCSP X D)

/-- **Parent of a variable in an ordering.** For an ordering `d` of the variables of a binary CSP
`P`, the parent of `x` is the neighbor `y` of `x` in the simple constraint graph of `P` with the
least position `d y` among those with `d y < d x`, and there is none if `x` has no such
neighbor. -/
def orderParent (d : X ≃ Fin (Fintype.card X)) (x : X) : Option X :=
  ((List.finRange (Fintype.card X)).find?
    fun i => decide (i < d x ∧ P.constraintGraph.Adj x (d.symm i))).map d.symm

/-- A parent is an earlier neighbor. -/
theorem orderParent_spec {d : X ≃ Fin (Fintype.card X)} {x p : X}
    (h : P.orderParent d x = some p) : P.constraintGraph.Adj x p ∧ d p < d x := by
  rw [orderParent, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hpa := List.find?_some hi
  have hpi := of_decide_eq_true hpa
  refine ⟨hpi.2, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hpi.1

/-- **Parents under an ordering of width at most one.** If the ordering `d` has width at most
one, the parent of `x` is `p` exactly when `p` is a neighbor of `x` in the simple constraint
graph placed before `x`. -/
theorem orderParent_eq_some_iff {d : X ≃ Fin (Fintype.card X)} (hw : P.orderWidth d ≤ 1)
    {x p : X} : P.orderParent d x = some p ↔ P.constraintGraph.Adj x p ∧ d p < d x := by
  constructor
  · exact P.orderParent_spec
  · intro h
    have hpred : (fun i => decide (i < d x ∧ P.constraintGraph.Adj x (d.symm i))) (d p)
        = true := by
      change decide (d p < d x ∧ P.constraintGraph.Adj x (d.symm (d p))) = true
      rw [Equiv.symm_apply_apply]
      exact decide_eq_true ⟨h.2, h.1⟩
    cases hfind : (List.finRange (Fintype.card X)).find?
        (fun i => decide (i < d x ∧ P.constraintGraph.Adj x (d.symm i))) with
    | none =>
        rw [List.find?_eq_none] at hfind
        exact absurd hpred (hfind (d p) (List.mem_finRange (d p)))
    | some i =>
        have hpa := List.find?_some hfind
        have hpi := of_decide_eq_true hpa
        by_cases heq : i = d p
        · subst heq
          simp only [orderParent, hfind, Option.map_some, Equiv.symm_apply_apply]
        · exfalso
          have hmem1 : d.symm i ∈ Finset.univ.filter
              (fun y => P.constraintGraph.Adj x y ∧ d y < d x) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨hpi.2, ?_⟩
            rw [Equiv.apply_symm_apply]
            exact hpi.1
          have hmem2 : p ∈ Finset.univ.filter
              (fun y => P.constraintGraph.Adj x y ∧ d y < d x) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h
          have hne : d.symm i ≠ p := fun hcon =>
            heq (d.symm.injective (hcon.trans (d.symm_apply_apply p).symm))
          have hsub : ({d.symm i, p} : Finset X) ⊆ Finset.univ.filter
              (fun y => P.constraintGraph.Adj x y ∧ d y < d x) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hmem1
            · exact hmem2
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_pair hne] at hcard
          have hle : P.vertexWidth d x ≤ P.orderWidth d :=
            Finset.le_sup (Finset.mem_univ x)
          have hw' : Finset.univ.sup (P.vertexWidth d) ≤ 1 := hw
          simp only [vertexWidth, orderWidth] at hle
          omega

/-- **Listing by position is a root-first order.** For every ordering `d`, the list of the
variables by increasing position is a root-first order for the parent map `P.orderParent d`. -/
theorem rootedOrder_orderParent (d : X ≃ Fin (Fintype.card X)) :
    RootedOrder (P.orderParent d) (List.ofFn d.symm) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [List.mem_ofFn]
    exact ⟨d x, d.symm_apply_apply x⟩
  · rw [List.nodup_ofFn]
    exact d.symm.injective
  · intro x h
    have h2 := (P.orderParent_spec h).2
    have h3 : (d x).val < (d x).val := h2
    omega
  · rw [List.pairwise_ofFn]
    intro i j hij hcon
    have hspec := P.orderParent_spec hcon
    simp only [Equiv.apply_symm_apply] at hspec
    have h1 : i.val < j.val := hij
    have h2 : j.val < i.val := hspec.2
    omega

/-- **Arcs are parent edges under an ordering of width at most one.** If the ordering `d` has
width at most one and no arc of `P` joins a variable to itself, every arc of `P` joins a variable
and its parent for `P.orderParent d`, in one orientation or the other. -/
theorem isTreeArcs_orderParent {d : X ≃ Fin (Fintype.card X)} (hw : P.orderWidth d ≤ 1)
    (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) : IsTreeArcs P (P.orderParent d) := by
  intro e he
  have hne : e.1 ≠ e.2 := hdist e he
  have hadj : P.constraintGraph.Adj e.1 e.2 := ⟨hne, Or.inl he⟩
  have hdn : d e.1 ≠ d e.2 := fun hcon => hne (d.injective hcon)
  rcases lt_trichotomy (d e.1) (d e.2) with hlt | heq | hgt
  · left
    rw [P.orderParent_eq_some_iff hw]
    exact ⟨P.constraintGraph.symm.symm _ _ hadj, hlt⟩
  · exact absurd heq hdn
  · right
    rw [P.orderParent_eq_some_iff hw]
    exact ⟨hadj, hgt⟩

/-- **Forests have an ordering of width at most one.** If the simple constraint graph of `P` is
acyclic, some ordering of the variables has width at most one. -/
theorem exists_orderWidth_le_one_of_isAcyclic (h : P.constraintGraph.IsAcyclic) :
    ∃ d : X ≃ Fin (Fintype.card X), P.orderWidth d ≤ 1 := by
  obtain ⟨d, hd⟩ := P.exists_orderWidth_eq_constraintWidth
  refine ⟨d, ?_⟩
  rw [hd]
  exact P.constraintWidth_le_one_of_isAcyclic h

omit [DecidableEq X] [Fintype X] in
private theorem cw_aux_a_rootedOrder_of_isAcyclic_aux {X D : Type*} [Finite X]
    (P : BinaryCSP X D) (h : P.constraintGraph.IsAcyclic)
    (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) :
    ∃ (parent : X → Option X) (order : List X), RootedOrder parent order ∧
      IsTreeArcs P parent ∧ ∀ x p, parent x = some p → P.constraintGraph.Adj p x := by
  classical
  suffices h : ∀ [Fintype X], ∃ (parent : X → Option X) (order : List X),
      RootedOrder parent order ∧ IsTreeArcs P parent ∧
      ∀ x p, parent x = some p → P.constraintGraph.Adj p x from
    @h (Fintype.ofFinite X)
  intro inst
  obtain ⟨d, hd⟩ := P.exists_orderWidth_le_one_of_isAcyclic h
  refine ⟨P.orderParent d, List.ofFn d.symm, P.rootedOrder_orderParent d,
    P.isTreeArcs_orderParent hd hdist, ?_⟩
  intro x p hxp
  exact P.constraintGraph.symm.symm _ _ (P.orderParent_spec hxp).1

omit [DecidableEq X] [Fintype X] in
/-- **A forest constraint graph is the forest of a rooted parent map.** If the simple constraint
graph of `P` is acyclic and no arc joins a variable to itself, there are a parent map and a
root-first order for it such that every arc joins a variable and its parent and every variable is
adjacent to its parent in the constraint graph. -/
theorem exists_rootedOrder_of_isAcyclic [Finite X] (h : P.constraintGraph.IsAcyclic)
    (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) :
    ∃ (parent : X → Option X) (order : List X), RootedOrder parent order ∧
      IsTreeArcs P parent ∧ ∀ x p, parent x = some p → P.constraintGraph.Adj p x := by
  exact cw_aux_a_rootedOrder_of_isAcyclic_aux P h hdist

private def cw_aux_a_symArcs {X D : Type*} (P : BinaryCSP X D) : BinaryCSP X D :=
  ⟨P.arcs ++ P.arcs.map Prod.swap, P.allowed⟩

private theorem cw_aux_a_symArcs_allowed {X D : Type*} (P : BinaryCSP X D) :
    (cw_aux_a_symArcs P).allowed = P.allowed := rfl

private theorem cw_aux_a_symArcs_arcs {X D : Type*} (P : BinaryCSP X D) :
    (cw_aux_a_symArcs P).arcs = P.arcs ++ P.arcs.map Prod.swap := rfl

private theorem cw_aux_a_dacPass_eq {X D : Type*} [DecidableEq X]
    (P : BinaryCSP X D) (parent : X → Option X) (dom : X → Finset D) (xs : List X) :
    dacPass (cw_aux_a_symArcs P) parent dom xs = dacPass P parent dom xs := by
  induction xs generalizing dom with
  | nil => rfl
  | cons x xs ih =>
      have hstep : dacStep (cw_aux_a_symArcs P) parent dom x =
          dacStep P parent dom x := rfl
      simp only [dacPass, hstep, ih]

private theorem cw_aux_a_dac_eq {X D : Type*} [DecidableEq X]
    (P : BinaryCSP X D) (parent : X → Option X) (order : List X) (dom : X → Finset D) :
    dac (cw_aux_a_symArcs P) parent order dom = dac P parent order dom := by
  simp only [dac, cw_aux_a_dacPass_eq]

private theorem cw_aux_a_greedyFrom_eq {X D : Type*} [DecidableEq X]
    (P : BinaryCSP X D) (parent : X → Option X) (sel : Finset D → Option D)
    (dom : X → Finset D) (xs : List X) (σ : X → D) :
    greedyFrom (cw_aux_a_symArcs P) parent sel dom xs σ =
      greedyFrom P parent sel dom xs σ := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      have hcand : candidates (cw_aux_a_symArcs P) parent dom σ x =
          candidates P parent dom σ x := rfl
      simp only [greedyFrom, hcand, ih]

private theorem cw_aux_a_treeSolve_eq {X D : Type*} [DecidableEq X] [Inhabited D]
    (P : BinaryCSP X D) (parent : X → Option X) (order : List X)
    (sel : Finset D → Option D) (dom : X → Finset D) :
    treeSolve (cw_aux_a_symArcs P) parent order sel dom =
      treeSolve P parent order sel dom := by
  simp only [treeSolve, greedy, cw_aux_a_dac_eq, cw_aux_a_greedyFrom_eq]

private theorem cw_aux_a_symmetric {X D : Type*} (P : BinaryCSP X D) (hsym : Symmetric P) :
    Symmetric (cw_aux_a_symArcs P) := by
  intro x y a b
  simp only [cw_aux_a_symArcs_allowed]
  exact hsym x y a b

private theorem cw_aux_a_isTreeArcs {X D : Type*} (P : BinaryCSP X D) {parent : X → Option X}
    (htree : IsTreeArcs P parent) : IsTreeArcs (cw_aux_a_symArcs P) parent := by
  intro e he
  simp only [cw_aux_a_symArcs_arcs, List.mem_append, List.mem_map] at he
  rcases he with he | ⟨a, ha, rfl⟩
  · exact htree e he
  · obtain ⟨a1, a2⟩ := a
    change parent a1 = some a2 ∨ parent a2 = some a1
    rcases htree (a1, a2) ha with h | h
    · exact Or.inr h
    · exact Or.inl h

private theorem cw_aux_a_isSolution_iff {X D : Type*} (P : BinaryCSP X D) (hsym : Symmetric P)
    (dom : X → Finset D) (σ : X → D) :
    IsSolution (cw_aux_a_symArcs P) dom σ ↔ IsSolution P dom σ := by
  simp only [IsSolution, cw_aux_a_symArcs_arcs, cw_aux_a_symArcs_allowed, List.mem_append,
    List.mem_map]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro e he
    exact h.2 e (Or.inl he)
  · intro h
    refine ⟨h.1, ?_⟩
    intro e he
    rcases he with he | ⟨a, ha, rfl⟩
    · exact h.2 e he
    · obtain ⟨a1, a2⟩ := a
      have h1 := h.2 (a1, a2) ha
      change P.allowed a2 a1 (σ a2) (σ a1) = true
      have h2 : P.allowed a1 a2 (σ a1) (σ a2) = true := h1
      rw [← hsym a1 a2 (σ a1) (σ a2)]
      exact h2

/-- **Orderings of width at most one are backtrack-free.** Let `P` have symmetric constraints and
no arc joining a variable to itself, and let `d` be an ordering of width at most one. For all
domains, the tree-CSP algorithm along `d`, each variable's parent being its earlier neighbor,
succeeds exactly when `P` has a solution within the domains. -/
theorem treeSolve_orderParent_ne_none_iff [Inhabited D] {sel : Finset D → Option D}
    (hsel : IsSelector sel) (hsym : Symmetric P) (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2)
    {d : X ≃ Fin (Fintype.card X)} (hw : P.orderWidth d ≤ 1) (dom : X → Finset D) :
    treeSolve P (P.orderParent d) (List.ofFn d.symm) sel dom ≠ none ↔
      ∃ σ, IsSolution P dom σ := by
  have htreeP : IsTreeArcs P (P.orderParent d) := P.isTreeArcs_orderParent hw hdist
  have htreeQ : IsTreeArcs (cw_aux_a_symArcs P) (P.orderParent d) :=
    cw_aux_a_isTreeArcs P htreeP
  have hsymQ : Symmetric (cw_aux_a_symArcs P) := cw_aux_a_symmetric P hsym
  have hedgeQ : ∀ x p, P.orderParent d x = some p → (p, x) ∈ (cw_aux_a_symArcs P).arcs := by
    intro x p hxp
    have hspec := P.orderParent_spec hxp
    have hmem : (x, p) ∈ P.arcs ∨ (p, x) ∈ P.arcs := hspec.1.2
    simp only [cw_aux_a_symArcs_arcs, List.mem_append, List.mem_map]
    rcases hmem with hmem | hmem
    · exact Or.inr ⟨(x, p), hmem, rfl⟩
    · exact Or.inl hmem
  have hQ := treeSolve_ne_none_iff (P := cw_aux_a_symArcs P) (parent := P.orderParent d)
    (order := List.ofFn d.symm) hsel (P.rootedOrder_orderParent d) hsymQ htreeQ hedgeQ dom
  rw [cw_aux_a_treeSolve_eq] at hQ
  exact hQ.trans (exists_congr (cw_aux_a_isSolution_iff P hsym dom))

omit [Fintype X] in
private theorem cw_aux_a_treeSolve_ne_none_iff_aux {X D : Type*} [DecidableEq X] [Finite X]
    [Inhabited D] (P : BinaryCSP X D) (sel : Finset D → Option D)
    (hsel : IsSelector sel) (hsym : Symmetric P) (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2)
    (hacyc : P.constraintGraph.IsAcyclic) :
    ∃ (parent : X → Option X) (order : List X), RootedOrder parent order ∧
      IsTreeArcs P parent ∧
      ∀ dom, treeSolve P parent order sel dom ≠ none ↔ ∃ σ, IsSolution P dom σ := by
  suffices h : ∀ [Fintype X], ∃ (parent : X → Option X) (order : List X),
      RootedOrder parent order ∧ IsTreeArcs P parent ∧
      ∀ dom, treeSolve P parent order sel dom ≠ none ↔ ∃ σ, IsSolution P dom σ from
    @h (Fintype.ofFinite X)
  intro inst
  obtain ⟨d, hd⟩ := P.exists_orderWidth_le_one_of_isAcyclic hacyc
  refine ⟨P.orderParent d, List.ofFn d.symm, P.rootedOrder_orderParent d,
    P.isTreeArcs_orderParent hd hdist, ?_⟩
  intro dom
  exact treeSolve_orderParent_ne_none_iff P hsel hsym hdist hd dom

omit [Fintype X] in
/-- **Forests are backtrack-free.** Let `P` have symmetric constraints, no arc joining a variable
to itself, and an acyclic simple constraint graph. Then there are a parent map and a root-first
order for it such that every arc joins a variable and its parent and, for all domains, the
tree-CSP algorithm succeeds exactly when `P` has a solution within the domains. -/
theorem exists_treeSolve_ne_none_iff_of_isAcyclic [Finite X] [Inhabited D]
    {sel : Finset D → Option D} (hsel : IsSelector sel) (hsym : Symmetric P)
    (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) (hacyc : P.constraintGraph.IsAcyclic) :
    ∃ (parent : X → Option X) (order : List X), RootedOrder parent order ∧
      IsTreeArcs P parent ∧
      ∀ dom, treeSolve P parent order sel dom ≠ none ↔ ∃ σ, IsSolution P dom σ := by
  exact cw_aux_a_treeSolve_ne_none_iff_aux P sel hsel hsym hdist hacyc

end BinaryCSP

/-! ## Relation checks of the whole procedure -/

variable {X D : Type*} [DecidableEq X] (P : BinaryCSP X D)

/-- **Relation checks of a greedy step.** The greedy step at a variable `x` with a parent filters
the domain of `x` against the parent's value, `|dom x|` checks; a root costs nothing. -/
def greedyCost (parent : X → Option X) (dom : X → Finset D) (x : X) : ℕ :=
  match parent x with
  | none => 0
  | some _ => (dom x).card

/-- Greedy assignment of the listed variables, in list order, charging `greedyCost` at each
step. -/
def greedyFromT (parent : X → Option X) (sel : Finset D → Option D) (dom : X → Finset D) :
    List X → (X → D) → TimeM ℕ (Option (X → D))
  | [], σ => pure (some σ)
  | x :: xs, σ => do
      TimeM.tick (greedyCost parent dom x)
      match sel (candidates P parent dom σ x) with
      | none => pure none
      | some b => greedyFromT parent sel dom xs (Function.update σ x b)

/-- The tree-CSP algorithm with both phases charged: the DAC pass, then greedy assignment of all
variables in order. -/
def treeSolveT [Inhabited D] (parent : X → Option X) (order : List X)
    (sel : Finset D → Option D) (dom : X → Finset D) : TimeM ℕ (Option (X → D)) := do
  let dom' ← dac P parent order dom
  greedyFromT P parent sel dom' order fun _ => default

omit [DecidableEq X] in
private theorem cw_aux_b_order_length {X : Type*} [Fintype X]
    (parent : X → Option X) (order : List X) (hord : RootedOrder parent order) :
    order.length = Fintype.card X := by
  classical
  have hcard : order.toFinset.card = order.length :=
    List.toFinset_card_of_nodup hord.nodup
  have huniv : order.toFinset = Finset.univ := by
    ext x
    simp [List.mem_toFinset, hord.mem x]
  rw [huniv, Finset.card_univ] at hcard
  exact hcard.symm

/-- Charging the greedy steps does not change the result. -/
theorem greedyFromT_ret (parent : X → Option X) (sel : Finset D → Option D)
    (dom : X → Finset D) (xs : List X) (σ : X → D) :
    (greedyFromT P parent sel dom xs σ).ret = greedyFrom P parent sel dom xs σ := by
  induction xs generalizing σ with
  | nil => simp [greedyFromT, greedyFrom, TimeM.ret_pure]
  | cons x xs ih =>
    cases hsel : sel (candidates P parent dom σ x)
    case none =>
      simp only [greedyFromT, greedyFrom, TimeM.ret_bind, hsel, TimeM.ret_pure]
    case some =>
      simp only [greedyFromT, greedyFrom, TimeM.ret_bind, hsel, ih]

/-- For domains of size at most `d`, greedy assignment of `xs` performs at most `|xs| · d`
relation checks. -/
theorem greedyFromT_time_le (parent : X → Option X) (sel : Finset D → Option D)
    (dom : X → Finset D) (d : ℕ) (hd : ∀ v, (dom v).card ≤ d) (xs : List X) (σ : X → D) :
    (greedyFromT P parent sel dom xs σ).time ≤ xs.length * d := by
  induction xs generalizing σ with
  | nil => simp [greedyFromT, TimeM.time_pure]
  | cons x xs ih =>
    have hcost : greedyCost parent dom x ≤ d := by
      simp only [greedyCost]
      split
      · exact Nat.zero_le _
      · exact hd _
    cases hsel : sel (candidates P parent dom σ x)
    case none =>
      simp only [greedyFromT, TimeM.time_bind, TimeM.time_tick, hsel,
        TimeM.time_pure, add_zero, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      exact hcost.trans (Nat.le_add_left _ _)
    case some =>
      simp only [greedyFromT, TimeM.time_bind, TimeM.time_tick, hsel,
        List.length_cons]
      rw [Nat.add_mul, Nat.one_mul, add_comm (List.length xs * d) d]
      exact add_le_add hcost (ih _)

/-- `treeSolveT` returns what `treeSolve` returns. -/
theorem treeSolveT_ret [Inhabited D] (parent : X → Option X) (order : List X)
    (sel : Finset D → Option D) (dom : X → Finset D) :
    (treeSolveT P parent order sel dom).ret = treeSolve P parent order sel dom := by
  simp only [treeSolveT, TimeM.ret_bind, greedyFromT_ret, treeSolve, greedy]

/-- **Relation checks of the tree-CSP algorithm.** Under a root-first order, for `n` variables and
domains of size at most `d`, the DAC pass and greedy assignment together perform at most
`n · d² + n · d` relation checks. -/
theorem treeSolveT_time_le [Fintype X] [Inhabited D] {parent : X → Option X} {order : List X}
    (hord : RootedOrder parent order) (sel : Finset D → Option D) (d : ℕ)
    (dom : X → Finset D) (hd : ∀ v, (dom v).card ≤ d) :
    (treeSolveT P parent order sel dom).time ≤
      Fintype.card X * (d * d) + Fintype.card X * d := by
  have hlen : order.length = Fintype.card X :=
    cw_aux_b_order_length parent order hord
  have hdac : ∀ v, ((dac P parent order dom).ret v).card ≤ d := fun v =>
    (Finset.card_le_card (dac_subset dom v)).trans (hd v)
  have hgreedy : (greedyFromT P parent sel (dac P parent order dom).ret order
      fun _ => default).time ≤ order.length * d :=
    greedyFromT_time_le P parent sel _ d hdac order _
  rw [hlen] at hgreedy
  have hdacT : (dac P parent order dom).time ≤ Fintype.card X * (d * d) :=
    dac_time_le_card hord d dom hd
  have hsplit : (treeSolveT P parent order sel dom).time =
      (dac P parent order dom).time +
        (greedyFromT P parent sel (dac P parent order dom).ret order
          fun _ => default).time := by
    simp only [treeSolveT, TimeM.time_bind]
  rw [hsplit]
  exact add_le_add hdacT hgreedy

end Cslib.Algorithms.Lean.ArcConsistency
