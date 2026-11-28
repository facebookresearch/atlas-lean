/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The generic amortized framework

The `Amortized` locale of `Amortized_Framework.thy` as a structure:
an operation type with an arity, execution, invariant, cost,
potential `Phi`, and amortized bound `U`, over rose-tree operation
histories. Main results: `t_sum_a_sum` (actual cost = amortized
cost − final potential, i.e. Ch. 19's telescoping sum),
`t_sum_le_a_sum`, `a_le_U`, `a_sum_le_U_sum`, `t_sum_le_U_sum`,
and the `Amortized2` transfer locale (`AmortizedTransfer`,
`amortizedTransfer`, potential `Phi ∘ hom`). Isabelle's `fun`
equations for `exec` / `cost` / `U` in instantiations cover only
arity-matching argument lists; Lean totalises them with fallbacks,
never used on a `wf` history.

Ported from the Chapter 22 Lean conversion in
`converted_proofs/ch22/lean/Chapter22.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Skew_Heap` (`Skew_Heap.thy`) and
`Amortized_Complexity` (`Skew_Heap_Analysis.thy`,
`Amortized_Framework.thy`, `Priority_Queue_ops_merge.thy`), and
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, Chapter 22 (Skew Heaps, pp. 253-256) with Appendix
B.10. Isabelle-derived names are kept for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized

/- ## The generic amortized framework (`Amortized_Framework.thy`) -/

/-- The `Amortized` locale, as a structure: the fields are hypotheses,
not axioms — instantiating it requires proving them. -/
structure AmortizedData (Op State : Type u) where
  arity : Op → ℕ
  exec : Op → List State → State
  inv : State → Prop
  cost : Op → List State → ℕ
  Phi : State → ℝ
  U : Op → List State → ℝ
  inv_exec : ∀ {f ss}, (∀ s ∈ ss, inv s) → ss.length = arity f → inv (exec f ss)
  ppos : ∀ {s}, inv s → 0 ≤ Phi s
  U_bound : ∀ {f ss}, (∀ s ∈ ss, inv s) → ss.length = arity f →
    (cost f ss : ℝ) + Phi (exec f ss) - (ss.map Phi).sum ≤ U f ss

/-- Rose trees: operation histories. The constructor is named `T`,
as in Isabelle's `datatype 'a rose_tree = T 'a "'a rose_tree list"`. -/
inductive RoseTree (Op : Type u) where
  | T : Op → List (RoseTree Op) → RoseTree Op

variable {Op State : Type u} (A : AmortizedData Op State)

/-- `wf ot`: `ot` is a well-formed operation history. -/
def wf : RoseTree Op → Prop
  | .T f ts => ts.length = A.arity f ∧ ∀ t ∈ ts, wf t

theorem wf_mk (f : Op) (ts : List (RoseTree Op)) :
    wf A (.T f ts) ↔ ts.length = A.arity f ∧ ∀ t ∈ ts, wf A t := by simp [wf]

/-- `state ot`: the state after performing the history `ot`. -/
def state : RoseTree Op → State
  | .T f ts => A.exec f (ts.map state)

theorem state_mk (f : Op) (ts : List (RoseTree Op)) :
    state A (.T f ts) = A.exec f (ts.map (state A)) := by simp [state]

/-- Size of a rose tree, for well-founded induction. -/
def roseSize : RoseTree Op → ℕ
  | .T _ ts => 1 + (ts.map roseSize).sum

theorem roseSize_mk (f : Op) (ts : List (RoseTree Op)) :
    roseSize (.T f ts) = 1 + (ts.map roseSize).sum := by simp [roseSize]

theorem roseSize_mem_lt {ts : List (RoseTree Op)} {t : RoseTree Op} (ht : t ∈ ts)
    (f : Op) : roseSize t < roseSize (.T f ts) := by
  rw [roseSize_mk]
  have h2 : roseSize t ≤ (ts.map roseSize).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem ht)
  omega

/-- Custom induction principle for rose trees (Lean's `induction`
tactic does not support nested inductives). -/
theorem rose_induct {P : RoseTree Op → Prop}
    (h : ∀ f ts, (∀ t ∈ ts, P t) → P (.T f ts)) : ∀ ot, P ot := by
  intro ot
  have key : ∀ n, ∀ ot : RoseTree Op, roseSize ot = n → P ot := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ot hsize
      cases ot with
      | T f ts =>
        apply h f ts
        intro t ht
        apply ih (roseSize t) (by have := roseSize_mem_lt ht f; omega) t rfl
  exact key (roseSize ot) ot rfl

/-- `inv_state`: the state of a well-formed history satisfies `inv`. -/
theorem inv_state {ot : RoseTree Op} (h : wf A ot) : A.inv (state A ot) := by
  induction ot using rose_induct with
  | _ f ts ih =>
    rw [wf_mk] at h
    rw [state_mk]
    apply A.inv_exec
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact ih t ht (h.2 t ht)
    · rw [List.length_map]; exact h.1

/-- `acost f ss`: the amortized cost of one operation. -/
def acost (f : Op) (ss : List State) : ℝ :=
  (A.cost f ss : ℝ) + A.Phi (A.exec f ss) - (ss.map A.Phi).sum

/-- `acost_sum ot`: total amortized cost of the history `ot`. -/
def acost_sum : RoseTree Op → ℝ
  | .T f ts => acost A f (ts.map (state A)) + (ts.map acost_sum).sum

/-- `cost_sum ot`: total actual cost of the history `ot`. -/
def cost_sum : RoseTree Op → ℝ
  | .T f ts => (A.cost f (ts.map (state A)) : ℝ) + (ts.map cost_sum).sum

/-- `U_sum ot`: total amortized bound of the history `ot`. -/
def U_sum : RoseTree Op → ℝ
  | .T f ts => A.U f (ts.map (state A)) + (ts.map U_sum).sum

theorem acost_sum_mk (f : Op) (ts : List (RoseTree Op)) :
    acost_sum A (.T f ts) = acost A f (ts.map (state A)) + (ts.map (acost_sum A)).sum := by
  simp [acost_sum]

theorem cost_sum_mk (f : Op) (ts : List (RoseTree Op)) :
    cost_sum A (.T f ts) = (A.cost f (ts.map (state A)) : ℝ) + (ts.map (cost_sum A)).sum := by
  simp [cost_sum]

theorem U_sum_mk (f : Op) (ts : List (RoseTree Op)) :
    U_sum A (.T f ts) = A.U f (ts.map (state A)) + (ts.map (U_sum A)).sum := by
  simp [U_sum]

theorem sum_map_sub' (ts : List (RoseTree Op)) (g h : RoseTree Op → ℝ) :
    (ts.map (fun t => g t - h t)).sum = (ts.map g).sum - (ts.map h).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [List.map_cons, List.sum_cons, ih]; ring

/-- `t_sum_a_sum`: actual cost = amortized cost − final potential. -/
theorem t_sum_a_sum {ot : RoseTree Op} (hw : wf A ot) :
    cost_sum A ot = acost_sum A ot - A.Phi (state A ot) := by
  induction ot using rose_induct with
  | _ f ts ih =>
    rw [wf_mk] at hw
    rw [cost_sum_mk, acost_sum_mk, state_mk]
    have hIH : ∀ t ∈ ts, cost_sum A t = acost_sum A t - A.Phi (state A t) :=
      fun t ht => ih t ht (hw.2 t ht)
    have hsum : (ts.map (cost_sum A)).sum =
        (ts.map (acost_sum A)).sum - (ts.map (fun t => A.Phi (state A t))).sum := by
      have h1 : ts.map (cost_sum A) =
          ts.map (fun t => acost_sum A t - A.Phi (state A t)) := by
        apply List.map_congr_left; intro t ht; exact hIH t ht
      rw [h1, sum_map_sub' ts (acost_sum A) (fun t => A.Phi (state A t))]
    have hmap : (ts.map (state A)).map A.Phi = ts.map (fun t => A.Phi (state A t)) := by
      rw [List.map_map]; rfl
    have hacost : acost A f (ts.map (state A)) =
        (A.cost f (ts.map (state A)) : ℝ) + A.Phi (A.exec f (ts.map (state A))) -
          ((ts.map (state A)).map A.Phi).sum := rfl
    rw [hacost, hsum, hmap]
    ring

/-- `t_sum_le_a_sum`: actual cost ≤ amortized cost. -/
theorem t_sum_le_a_sum {ot : RoseTree Op} (hw : wf A ot) :
    cost_sum A ot ≤ acost_sum A ot := by
  have h1 := t_sum_a_sum A hw
  have h2 : 0 ≤ A.Phi (state A ot) := A.ppos (inv_state A hw)
  linarith

/-- `a_le_U`: one operation's amortized cost is bounded by `U`. -/
theorem a_le_U {f : Op} {ss : List State} (hall : ∀ s ∈ ss, A.inv s)
    (hlen : ss.length = A.arity f) : acost A f ss ≤ A.U f ss := by
  exact A.U_bound hall hlen

/-- `a_sum_le_U_sum`: total amortized cost ≤ total bound. -/
theorem a_sum_le_U_sum {ot : RoseTree Op} (hw : wf A ot) :
    acost_sum A ot ≤ U_sum A ot := by
  induction ot using rose_induct with
  | _ f ts ih =>
    rw [wf_mk] at hw
    rw [acost_sum_mk, U_sum_mk]
    have h1 : acost A f (ts.map (state A)) ≤ A.U f (ts.map (state A)) := by
      apply a_le_U A
      · intro s hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
        exact inv_state A (hw.2 t ht)
      · rw [List.length_map]; exact hw.1
    have h2 : (ts.map (acost_sum A)).sum ≤ (ts.map (U_sum A)).sum := by
      apply List.sum_le_sum; intro t ht; exact ih t ht (hw.2 t ht)
    linarith

/-- `t_sum_le_U_sum`: actual cost ≤ total bound. -/
theorem t_sum_le_U_sum {ot : RoseTree Op} (hw : wf A ot) :
    cost_sum A ot ≤ U_sum A ot :=
  le_trans (t_sum_le_a_sum A hw) (a_sum_le_U_sum A hw)

/- ## `Amortized2`: transfer of amortized analysis (`Amortized_Framework.thy`) -/

/-- The `Amortized2` locale: an implementation on type `T` with a
homomorphism `hom` to the analysed type `S`. -/
structure AmortizedTransfer (Op S T : Type u) (Base : AmortizedData Op S) where
  exec' : Op → List T → T
  inv' : T → Prop
  cost' : Op → List T → ℕ
  U' : Op → List T → ℝ
  hom : T → S
  exec'_hom : ∀ {f ts}, (∀ s ∈ ts, inv' s) → ts.length = Base.arity f →
    hom (exec' f ts) = Base.exec f (ts.map hom)
  inv_exec' : ∀ {f ss}, (∀ s ∈ ss, inv' s) → ss.length = Base.arity f →
    inv' (exec' f ss)
  inv_hom : ∀ {t}, inv' t → Base.inv (hom t)
  cost'_hom : ∀ {f ts}, (∀ s ∈ ts, inv' s) → ts.length = Base.arity f →
    cost' f ts = Base.cost f (ts.map hom)
  U'_hom : ∀ {f ts}, (∀ s ∈ ts, inv' s) → ts.length = Base.arity f →
    U' f ts = Base.U f (ts.map hom)

/-- The `sublocale` in `Amortized2`: the implementation is itself an
`AmortizedData`, with potential `Phi ∘ hom`. -/
def amortizedTransfer {Op S T : Type u} {Base : AmortizedData Op S}
    (Tr : AmortizedTransfer Op S T Base) : AmortizedData Op T where
  arity := Base.arity
  exec := Tr.exec'
  inv := Tr.inv'
  cost := Tr.cost'
  Phi := fun t => Base.Phi (Tr.hom t)
  U := Tr.U'
  inv_exec := Tr.inv_exec'
  ppos := by
    intro s hs
    exact Base.ppos (Tr.inv_hom hs)
  U_bound := by
    intro f ss hall hlen
    have hA := Base.U_bound (f := f) (ss := ss.map Tr.hom)
      (by intro s hs
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
          exact Tr.inv_hom (hall t ht))
      (by rw [List.length_map]; exact hlen)
    have hcost := Tr.cost'_hom hall hlen
    have hU := Tr.U'_hom hall hlen
    have hexec := Tr.exec'_hom hall hlen
    have hmap : (ss.map (fun t => Base.Phi (Tr.hom t))) =
        (ss.map Tr.hom).map Base.Phi := by rw [List.map_map]; rfl
    change (Tr.cost' f ss : ℝ) + Base.Phi (Tr.hom (Tr.exec' f ss)) -
        (ss.map (fun t => Base.Phi (Tr.hom t))).sum ≤ Tr.U' f ss
    rw [hcost, hU, hmap, hexec]
    exact hA


end Amortized

end Cslib.Algorithms.Lean
