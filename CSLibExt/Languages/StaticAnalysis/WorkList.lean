/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Rewriting.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Order.Hom.Basic
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic

/-!
# The simple work-list algorithm of monotone frameworks

A dataflow analysis in a monotone framework gives each node `i : ι` of a control-flow graph a
constraint variable `x i` in a partial order `L` and a constraint function `x ↦ f x i`; the
combined function `f : (ι → L) →o (ι → L)` is monotone, and the solutions of the equations
`x i = f x i` are its fixed points. The simple work-list algorithm starts from `x = ⊥` with every
node in the work-list `W`. While `W` is nonempty it removes some node `i` from `W`, and if
`f x i ≠ x i` it sets `x i := f x i` and adds to `W` the nodes `dep i` whose constraint functions
may read `x i`. `WorkList.Step f dep` is one iteration of its loop, for each choice of the node
removed.

## Main results

- `WorkList.sn_and_isLeast_fixedPoints`: if `L` has a least element and no infinite strictly
  ascending chain, and `dep i` contains every node whose constraint function depends on `x i`,
  then every run of the algorithm is finite, whatever order the nodes are removed in, and it ends
  with an empty work-list and the least fixed point of `f`.

## References

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University,
  version of October 15, 2026, Section 5.3.
-/

@[expose] public section

namespace Cslib.StaticAnalysis.WorkList

open Function Relation Cslib.Semantics.Rewriting

variable {ι L : Type*} [DecidableEq ι]

/-- **One iteration of the simple work-list algorithm.** Let `f : (ι → L) →o (ι → L)` be the
combined function of a monotone framework, whose component `x ↦ f x i` is the constraint
function of node `i`, and let `dep : ι → Finset ι` give the nodes to revisit when `x i` changes.
A step from the state `(x, W)`, with current values `x` and work-list `W`, removes some node
`i ∈ W` from `W`. If `f x i = x i`, nothing else changes; otherwise `x i` becomes `f x i` and the
nodes of `dep i` are added to the work-list, giving `(update x i (f x i), W.erase i ∪ dep i)`.
Every node of `W` may be the one removed, so the runs of this relation are the runs of the
algorithm for all removal orders. (Møller and Schwartzbach, *Static Program Analysis*,
Section 5.3) -/
inductive Step [Preorder L] (f : (ι → L) →o (ι → L)) (dep : ι → Finset ι) :
    (ι → L) × Finset ι → (ι → L) × Finset ι → Prop
  | keep {x : ι → L} {W : Finset ι} {i : ι} (hi : i ∈ W) (h : f x i = x i) :
      Step f dep (x, W) (x, W.erase i)
  | update {x : ι → L} {W : Finset ι} {i : ι} (hi : i ∈ W) (h : f x i ≠ x i) :
      Step f dep (x, W) (Function.update x i (f x i), W.erase i ∪ dep i)

variable [PartialOrder L] {f : (ι → L) →o (ι → L)} {dep : ι → Finset ι}

/-- The loop invariant: `x` lies below `f x` and below every fixed point of `f`, and every node
off the work-list satisfies its equation. -/
private def Inv (f : (ι → L) →o (ι → L)) (s : (ι → L) × Finset ι) : Prop :=
  s.1 ≤ f s.1 ∧ (∀ p ∈ fixedPoints f, s.1 ≤ p) ∧ ∀ i ∉ s.2, f s.1 i = s.1 i

private theorem le_update_of_le_map {x : ι → L} (hx : x ≤ f x) (i : ι) :
    x ≤ Function.update x i (f x i) := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · simpa using hx j
  · simp [Function.update_of_ne hj]

private theorem inv_step
    (hdep : ∀ i j, j ∉ dep i → ∀ x a, f (Function.update x i a) j = f x j)
    {s t : (ι → L) × Finset ι} (hs : Inv f s) (hst : Step f dep s t) : Inv f t := by
  obtain ⟨hpost, hleast, hsolved⟩ := hs
  cases hst with
  | @keep x W i hi h =>
    refine ⟨hpost, hleast, fun j hj => ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · exact h
    · exact hsolved j fun hjW => hj (Finset.mem_erase.2 ⟨hji, hjW⟩)
  | @update x W i hi h =>
    have hle := le_update_of_le_map hpost i
    refine ⟨fun j => ?_, fun p hp j => ?_, fun j hj => ?_⟩
    · rcases eq_or_ne j i with rfl | hji
      · simpa using f.monotone hle j
      · simpa [Function.update_of_ne hji] using (hpost j).trans (f.monotone hle j)
    · rcases eq_or_ne j i with rfl | hji
      · simpa [show f p = p from hp] using f.monotone (fun k => hleast p hp k) j
      · simpa [Function.update_of_ne hji] using hleast p hp j
    · simp only [Finset.mem_union, Finset.mem_erase, not_or, not_and] at hj
      rw [hdep i j hj.2]
      rcases eq_or_ne j i with rfl | hji
      · simp
      · simpa [Function.update_of_ne hji] using hsolved j (hj.1 hji)

/-- Each step either strictly increases the values or keeps them and shrinks the work-list. -/
private theorem lex_step {s t : (ι → L) × Finset ι} (hs : Inv f s) (hst : Step f dep s t) :
    Prod.Lex (· > ·) (· < ·) (t.1, t.2.card) (s.1, s.2.card) := by
  cases hst with
  | keep hi h => exact Prod.Lex.right _ (Finset.card_erase_lt_of_mem hi)
  | @update x W i hi h =>
    refine Prod.Lex.left _ _ (lt_of_le_of_ne (le_update_of_le_map hs.1 i) fun heq => h ?_)
    simpa using (congrFun heq i).symm

/-- **The simple work-list algorithm terminates and returns the least fixed point.** Let `L` be a
partial order with a least element and no infinite strictly ascending chain, for example a lattice
of finite height, let the set of nodes `ι` be finite, and let `f : (ι → L) →o (ι → L)` be
monotone; the solutions of the equations `x i = f x i` are the fixed points of `f`. Suppose that
`dep i` contains every node `j` whose constraint function `x ↦ f x j` depends on `x i`, that is,
`f (update x i a) j = f x j` for all `x` and `a` whenever `j ∉ dep i`. Run the simple work-list
algorithm (`Step f dep`) from `x = ⊥` with every node in the work-list. Then, whatever node each
iteration removes, every run is finite (`Relation.SN`), and every state reached from the start
that admits no further step has an empty work-list and values `x` equal to the least fixed point
of `f`, the least solution of the equations. (Møller and Schwartzbach, *Static Program Analysis*,
Section 5.3) -/
theorem sn_and_isLeast_fixedPoints [Fintype ι] [OrderBot L] [WellFoundedGT L]
    (f : (ι → L) →o (ι → L)) (dep : ι → Finset ι)
    (hdep : ∀ i j, j ∉ dep i → ∀ x a, f (Function.update x i a) j = f x j) :
    SN (Step f dep) (⊥, Finset.univ) ∧
      ∀ s, NormalForm (Step f dep) (⊥, Finset.univ) s →
        s.2 = ∅ ∧ IsLeast (fixedPoints f) s.1 := by
  have init : Inv f (⊥, Finset.univ) :=
    ⟨bot_le, fun _ _ => bot_le, fun i hi => absurd (Finset.mem_univ i) hi⟩
  have reach : ∀ s, ReflTransGen (Step f dep) (⊥, Finset.univ) s → Inv f s := fun s hs => by
    induction hs with
    | refl => exact init
    | tail _ hst ih => exact inv_step hdep ih hst
  refine ⟨?_, fun s ⟨hs, hnormal⟩ => ?_⟩
  · have : WellFoundedGT (ι → L) := inferInstanceAs (WellFoundedLT (ι → Lᵒᵈ))
    have wf := InvImage.wf (fun s : (ι → L) × Finset ι => (s.1, s.2.card))
      (wellFounded_gt.prod_lex wellFounded_lt)
    suffices ∀ s, Inv f s → SN (Step f dep) s from this _ init
    intro s
    induction s using wf.induction with
    | _ s ih => exact fun hs => ⟨s, fun t hst => ih t (lex_step hs hst) (inv_step hdep hs hst)⟩
  · obtain ⟨_, hleast, hsolved⟩ := reach s hs
    have hempty : s.2 = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
      by_cases h : f s.1 i = s.1 i
      · exact hnormal ⟨_, Step.keep (x := s.1) hi h⟩
      · exact hnormal ⟨_, Step.update (x := s.1) hi h⟩
    refine ⟨hempty, ?_, hleast⟩
    exact funext fun i => hsolved i (by simp [hempty])

end Cslib.StaticAnalysis.WorkList
