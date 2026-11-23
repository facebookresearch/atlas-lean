/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import Cslib.Foundations.Relation.Termination

/-!
# Abstract rewriting: reachable normal forms

An abstract reduction system is a type of states with a relation `r` oriented
from source to reduct. We use Mathlib's `Relation.ReflTransGen`, `Relation.Join`
and `Relation.EqvGen` for multi-step reduction, joinability and conversion, and
CSLib's `Relation.Normal`, `Relation.Normalizable`, `Relation.SN` and
`Relation.Terminating`. In particular termination means well-foundedness of the
**reverse** step relation; normality excludes even a self-loop.

This module adds a predicate for a specified reachable normal form and a
normalizer interface. The latter only chooses a reachable normal form; uniqueness
requires confluence and is developed in `Rewriting.Confluence`.

## Sources

Terese, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer
Science 55, Cambridge University Press, 2003, Chapter 1 (abstract reduction
systems), ISBN 978-0-521-39115-3.
The formal closure and termination infrastructure is reused from Mathlib and
CSLib rather than redeveloped here.
-/

@[expose] public section

namespace Cslib.Semantics.Rewriting

open Relation

variable {α β : Type*} {r : α → α → Prop} {a b n : α}

/-- `n` is a normal form reachable from `a` by zero or more reductions. -/
def NormalForm (r : α → α → Prop) (a n : α) : Prop :=
  ReflTransGen r a n ∧ Normal r n

/-- The reduction certificate of a reachable normal form. -/
theorem NormalForm.reduces (h : NormalForm r a n) : ReflTransGen r a n := h.1

/-- The terminal-state certificate of a reachable normal form. -/
theorem NormalForm.normal (h : NormalForm r a n) : Normal r n := h.2

/-- A normal state is its own reachable normal form. -/
theorem Normal.normalForm (h : Normal r n) : NormalForm r n n := ⟨.refl, h⟩

/-- A normal source has exactly itself as a reachable normal form. -/
@[simp]
theorem normalForm_iff_eq_of_normal (ha : Normal r a) :
    NormalForm r a n ↔ n = a := by
  constructor
  · intro h
    exact (ha.reflTransGen_eq h.reduces).symm
  · rintro rfl
    exact Normal.normalForm ha

/-- Normalizability is existence of a specified reachable normal form. -/
theorem normalizable_iff_exists_normalForm :
    Normalizable r a ↔ ∃ n, NormalForm r a n := Iff.rfl

/-- Prefix a reduction to a normal-form certificate. -/
theorem NormalForm.prepend (h : NormalForm r b n) (hab : ReflTransGen r a b) :
    NormalForm r a n := ⟨hab.trans h.reduces, h.normal⟩

/-- Prefix a single step to a normal-form certificate. -/
theorem NormalForm.prepend_step (h : NormalForm r b n) (hab : r a b) :
    NormalForm r a n := h.prepend (.single hab)

/-- A common reachable normal form witnesses joinability. -/
theorem NormalForm.join (ha : NormalForm r a n) (hb : NormalForm r b n) :
    Join (ReflTransGen r) a b := ⟨n, ha.reduces, hb.reduces⟩

/-- Joining a normal state is equivalent to reducing to that state. -/
theorem join_normal_iff (hn : Normal r n) :
    Join (ReflTransGen r) a n ↔ ReflTransGen r a n := by
  constructor
  · rintro ⟨c, hac, hnc⟩
    obtain rfl := hn.reflTransGen_eq hnc
    exact hac
  · intro han
    exact ⟨n, han, .refl⟩

/-- Two normal states can join precisely when they are equal. -/
theorem normal_join_normal_iff (ha : Normal r a) (hb : Normal r b) :
    Join (ReflTransGen r) a b ↔ a = b := by
  rw [join_normal_iff hb]
  exact ⟨ha.reflTransGen_eq, fun h => h ▸ ReflTransGen.refl⟩

/-- A normal-form certificate also gives convertibility to its result. -/
theorem NormalForm.convertible (h : NormalForm r a n) : EqvGen r a n :=
  EqvGen.reflTransGen_le_eqvGen _ _ _ h.reduces

/-- A function that chooses a reachable normal form for every state.
This interface does not assert that different choices agree. -/
structure Normalizer (r : α → α → Prop) where
  /-- The chosen result. -/
  run : α → α
  /-- The chosen result is reachable. -/
  reduces : ∀ a, ReflTransGen r a (run a)
  /-- The chosen result is terminal. -/
  normal : ∀ a, Normal r (run a)

namespace Normalizer

variable (N : Normalizer r)

/-- Normalizers are determined by their result function; certificates are proof irrelevant. -/
@[ext]
theorem ext {N M : Normalizer r} (h : ∀ a, N.run a = M.run a) : N = M := by
  cases N with
  | mk run reduces normal =>
    cases M with
    | mk run' reduces' normal' =>
      have heq : run = run' := funext h
      cases heq
      rfl

/-- The two certificates together form a normal-form certificate. -/
theorem normalForm (a : α) : NormalForm r a (N.run a) :=
  ⟨N.reduces a, N.normal a⟩

/-- A normalizer witnesses weak normalization. -/
theorem normalizing (N : Normalizer r) : Normalizing r := fun a => ⟨N.run a, N.normalForm a⟩

/-- A normalizer fixes every normal state, even without confluence. -/
theorem run_eq_of_normal (ha : Normal r a) : N.run a = a :=
  (ha.reflTransGen_eq (N.reduces a)).symm

/-- Applying a normalizer twice has the same result as applying it once. -/
@[simp]
theorem run_idempotent (a : α) : N.run (N.run a) = N.run a :=
  N.run_eq_of_normal (N.normal a)

/-- Fixed points of a normalizer are exactly the normal states. -/
theorem run_eq_self_iff : N.run a = a ↔ Normal r a := by
  constructor
  · intro h
    exact h ▸ N.normal a
  · exact N.run_eq_of_normal

/-- Any observable unchanged by a reduction is unchanged by normalization. -/
theorem preserves_observation (observe : α → β)
    (h : ∀ {a b}, r a b → observe a = observe b) (a : α) :
    observe (N.run a) = observe a := by
  have heq : ∀ {a b}, ReflTransGen r a b → observe a = observe b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (h hstep)
  exact (heq (N.reduces a)).symm

/-- Equality of chosen results always implies convertibility. -/
theorem convertible_of_run_eq (h : N.run a = N.run b) : EqvGen r a b := by
  have ha := (N.normalForm a).convertible
  have hb := (N.normalForm b).convertible
  rw [h] at ha
  exact .trans _ _ _ ha (.symm _ _ hb)

/-- Equality of chosen results always gives a common reduct. -/
theorem join_of_run_eq (h : N.run a = N.run b) : Join (ReflTransGen r) a b := by
  exact ⟨N.run b, h ▸ N.reduces a, N.reduces b⟩

end Normalizer

end Cslib.Semantics.Rewriting
