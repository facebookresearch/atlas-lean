/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Weighted place/transition Petri nets

Places and transitions are the two summands of a nonempty vertex type. An arc's
weight is its token multiplicity; zero denotes an absent arc. Markings have no
capacity bound. The old marking must cover every input weight before a firing
can consume those tokens and produce the output tokens, including at a place
which is both an input and an output of the same transition.

`PlaceTransitionNet.run?` evaluates a specified list of transitions. It returns
`some M'` exactly for a labelled multistep to `M'` in the net's `toLTS`.
In contrast, `Cslib.LTS.CanReach` asks whether *some* list has that endpoint.

## References

* T. Murata, “Petri nets: Properties, analysis and applications”, *Proceedings
  of the IEEE* 77(4), 1989, §II, Table 2 and firing rules (p. 543); §IV-A,
  firing sequences (p. 547).
* J. Esparza and M. Nielsen, “Decidability issues for Petri nets – a survey”,
  BRICS RS-94-8, 1994, §2 (p. 2 of the reprint): the ordinary, unit-weight
  case and its occurrence sequences.
-/

@[expose] public section

namespace Cslib

/-- A finite weighted place/transition net without a distinguished marking.
Its vertices are the tagged places and transitions; at least one sort is inhabited.
The two weight maps are zero extensions of the positive weights on the arcs. -/
structure PlaceTransitionNet (P T : Type*) [Fintype P] [Fintype T] where
  /-- There is at least one vertex; neither sort separately has to be inhabited. -/
  nonempty : Nonempty (P ⊕ T)
  /-- Weight from a place to a transition, or zero when there is no such arc. -/
  input : P → T → ℕ
  /-- Weight from a transition to a place, or zero when there is no such arc. -/
  output : T → P → ℕ

/-- A marking gives the number of tokens at each place, with no upper bound. -/
abbrev PlaceTransitionNet.Marking (P : Type*) := P → ℕ

/-- A weighted place/transition net together with its initial marking. -/
structure MarkedPlaceTransitionNet (P T : Type*) [Fintype P] [Fintype T]
    extends PlaceTransitionNet P T where
  /-- Token counts before any transition has fired. -/
  initial : PlaceTransitionNet.Marking P

namespace PlaceTransitionNet

variable {P T : Type*} [Fintype P] [Fintype T] (N : PlaceTransitionNet P T)

/-- Directed arc weight on tagged vertices. Same-sort pairs have weight zero. -/
def weight : P ⊕ T → P ⊕ T → ℕ
  | .inl p, .inr t => N.input p t
  | .inr t, .inl p => N.output t p
  | _, _ => 0

/-- The preset of a vertex consists of the vertices with an arc into it. -/
def preset (y : P ⊕ T) : Set (P ⊕ T) := {x | 0 < N.weight x y}

/-- The postset of a vertex consists of the vertices to which it has an arc. -/
def postset (x : P ⊕ T) : Set (P ⊕ T) := {y | 0 < N.weight x y}

/-- There is no arc from `x` to `y` exactly when its zero-extended weight is zero. -/
theorem notMem_postset_iff (x y : P ⊕ T) : y ∉ N.postset x ↔ N.weight x y = 0 :=
  Nat.not_lt.trans Nat.le_zero

/-- A net is ordinary if every present arc has weight one. -/
def IsOrdinary : Prop := ∀ x y, y ∈ N.postset x → N.weight x y = 1

/-- The old marking covers the input of the transition at every place.
A place not in the transition's preset has input weight zero. -/
def Enabled (M : Marking P) (t : T) : Prop := ∀ p, N.input p t ≤ M p

/-- To test enabling it suffices to check the places in the transition's preset. -/
theorem enabled_iff_preset (M : Marking P) (t : T) :
    N.Enabled M t ↔ ∀ p, Sum.inl p ∈ N.preset (.inr t) → N.input p t ≤ M p := by
  refine ⟨fun h p _ => h p, fun h p => ?_⟩
  by_cases hz : N.input p t = 0
  · simp [hz]
  · exact h p (Nat.pos_of_ne_zero hz)

/-- The finite place type allows the enabling test to be computed. -/
instance (M : Marking P) (t : T) : Decidable (N.Enabled M t) :=
  inferInstanceAs (Decidable (∀ p, N.input p t ≤ M p))

/-- Fire a given transition if enabled, subtracting its input and adding its
output at each place. A disabled transition returns no marking. -/
def fire? (M : Marking P) (t : T) : Option (Marking P) :=
  if N.Enabled M t then some (fun p => M p - N.input p t + N.output t p) else none

/-- The labelled firing relation: the old marking must enable the transition,
and the new marking must have exactly the resulting token count at every place. -/
def toLTS : LTS (Marking P) T where
  Tr M t M' := N.Enabled M t ∧ ∀ p, M' p = M p - N.input p t + N.output t p

/-- The optional firing succeeds with a given marking exactly when the
one-step firing relation holds with that target. -/
theorem fire?_eq_some_iff (M M' : Marking P) (t : T) :
    N.fire? M t = some M' ↔ N.toLTS.Tr M t M' := by
  by_cases h : N.Enabled M t
  · rw [fire?, ite_eq_left h, Option.some.injEq]
    exact ⟨fun e => ⟨h, fun p => congrFun e.symm p⟩, fun e => (funext e.2).symm⟩
  · simp [fire?, toLTS, h]

/-- For a fixed transition and old marking there is at most one successor.
Hence CSLib's labelled multistep determinism applies to this net as well. -/
instance : N.toLTS.Deterministic where
  deterministic _ _ _ _ h₁ h₂ := funext fun p => (h₁.2 p).trans (h₂.2 p).symm

/-- Execute a given finite list of transitions in order. The empty list
returns the old marking; a failed enabling test aborts the whole list. -/
def run? (M : Marking P) (ts : List T) : Option (Marking P) := ts.foldlM N.fire? M

/-- Executing a concatenation runs the suffix only if the prefix succeeds,
starting the suffix at the marking returned by the prefix. -/
theorem run?_append (M : Marking P) (xs ys : List T) :
    N.run? M (xs ++ ys) = (N.run? M xs).bind (fun m => N.run? m ys) :=
  List.foldlM_append

/-- The evaluator returns `M'` exactly when there is a firing sequence with
these transition identities in this order from `M` to `M'`. -/
theorem run?_eq_some_iff (M M' : Marking P) (ts : List T) :
    N.run? M ts = some M' ↔ N.toLTS.MTr M ts M' := by
  induction ts generalizing M with
  | nil => simp [run?]
  | cons t ts ih =>
    change (N.fire? M t).bind (fun m => N.run? m ts) = some M' ↔ _
    simp only [Option.bind_eq_some_iff, N.fire?_eq_some_iff, ih, LTS.MTr.cons_iff]

end PlaceTransitionNet

end Cslib
