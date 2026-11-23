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

public import CSLibExt.Foundations.Semantics.Rewriting.Basic
public import Cslib.Foundations.Relation.Confluence

/-!
# Confluence and normalization as a semantic interface

The basic diamond, local/global confluence, Church-Rosser, and Newman's lemma
are imported from `Cslib.Foundations.Relation.Confluence`. In particular use
`Relation.Diamond.to_confluent`, `Relation.Confluent.to_locallyConfluent`, and
`Relation.LocallyConfluent.terminating_toConfluent` directly. CSLib in turn uses
Mathlib's relation closures and join primitives.

This module develops their consequences for `NormalForm` and `Normalizer`:
normalizers agree under confluence, reduction and conversion preserve their
results, and equality of results characterizes conversion. Conversely, a
normalizer invariant under single steps certifies confluence. This gives a
useful proof method for evaluators and simplifiers without requiring termination
of every possible reduction strategy.

The classical construction `Normalizer.ofNormalizing` is a specification-level
choice, not an executable normalization algorithm. `Normalizer.ofTerminating_run_eq`
combines existence from termination with CSLib's Newman's lemma.

## Sources

Terese, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer
Science 55, Cambridge University Press, 2003, Chapter 1, ISBN 978-0-521-39115-3.
The scope is abstract reduction systems; term syntax, critical pairs, and
algorithms for deciding termination are outside this development.
-/

@[expose] public section

namespace Cslib.Semantics.Rewriting

open Relation

variable {α β : Type*} {r : α → α → Prop} {a b n m : α}

/-- Under confluence, all reachable normal forms of a state agree. -/
theorem NormalForm.eq (hn : NormalForm r a n) (hm : NormalForm r a m)
    (hc : Confluent r) : n = m := by
  exact ChurchRosser.normal_eq hc.to_churchRosser hn.normal hm.normal
    (.trans _ _ _ (.symm _ _ hn.convertible) hm.convertible)

/-- Conversion of sources preserves a specified normal form under confluence. -/
theorem NormalForm.of_convertible (hn : NormalForm r a n) (hc : Confluent r)
    (hab : EqvGen r b a) : NormalForm r b n := by
  exact ⟨ChurchRosser.normal_eqvGen_reflTransGen hc.to_churchRosser hn.normal
    (.trans _ _ _ hab hn.convertible), hn.normal⟩

/-- Every reduct of a state can still reach its normal form under confluence. -/
theorem NormalForm.of_reduces (hn : NormalForm r a n) (hc : Confluent r)
    (hab : ReflTransGen r a b) : NormalForm r b n :=
  hn.of_convertible hc (.symm _ _ hab.to_eqvGen)

/-- Two convertible states have exactly the same specified normal forms. -/
theorem normalForm_iff_of_convertible (hc : Confluent r) (hab : EqvGen r a b) :
    NormalForm r a n ↔ NormalForm r b n :=
  ⟨fun h => h.of_convertible hc (.symm _ _ hab), fun h => h.of_convertible hc hab⟩

/-- Normal forms of joinable sources agree under confluence. -/
theorem NormalForm.eq_of_join (hn : NormalForm r a n) (hm : NormalForm r b m)
    (hc : Confluent r) (hab : Join (ReflTransGen r) a b) : n = m := by
  exact hn.eq (hm.of_convertible hc (join_reflTransGen_le_eqvGen _ _ hab)) hc

namespace Normalizer

variable (N : Normalizer r)

/-- Construct a specification-level normalizer by classical choice. -/
noncomputable def ofNormalizing (hn : Normalizing r) : Normalizer r where
  run a := Classical.choose (hn a)
  reduces a := (Classical.choose_spec (hn a)).1
  normal a := (Classical.choose_spec (hn a)).2

/-- Termination supplies existence; this construction does not prescribe a strategy. -/
noncomputable def ofTerminating (ht : Terminating r) : Normalizer r :=
  ofNormalizing ht.to_normalizing

/-- Normalizers agree on every state of a confluent system. -/
theorem run_eq (M : Normalizer r) (hc : Confluent r) (a : α) : N.run a = M.run a :=
  (N.normalForm a).eq (M.normalForm a) hc

/-- Confluence makes the normalizer unique, including its proof certificates. -/
theorem unique (M : Normalizer r) (hc : Confluent r) : N = M :=
  Normalizer.ext (N.run_eq M hc)

/-- A normalizer returns any given reachable normal form under confluence. -/
theorem run_eq_of_normalForm (hc : Confluent r) (hn : NormalForm r a n) :
    N.run a = n := (N.normalForm a).eq hn hc

/-- In a confluent system, a normal-form certificate is equality to the chosen result. -/
theorem normalForm_iff (hc : Confluent r) : NormalForm r a n ↔ n = N.run a := by
  constructor
  · intro hn
    exact (N.run_eq_of_normalForm hc hn).symm
  · rintro rfl
    exact N.normalForm a

/-- Conversion preserves the result of normalization under confluence. -/
theorem run_eq_of_convertible (hc : Confluent r) (hab : EqvGen r a b) :
    N.run a = N.run b :=
  N.run_eq_of_normalForm hc ((N.normalForm b).of_convertible hc hab)

/-- Multi-step reduction preserves the result of normalization. -/
theorem run_eq_of_reduces (hc : Confluent r) (hab : ReflTransGen r a b) :
    N.run a = N.run b := N.run_eq_of_convertible hc hab.to_eqvGen

/-- Single-step reduction preserves the result of normalization. -/
theorem run_eq_of_step (hc : Confluent r) (hab : r a b) : N.run a = N.run b :=
  N.run_eq_of_reduces hc (.single hab)

/-- Chosen results decide conversion when equality of those results is decidable. -/
theorem convertible_iff_run_eq (hc : Confluent r) :
    EqvGen r a b ↔ N.run a = N.run b :=
  ⟨N.run_eq_of_convertible hc, N.convertible_of_run_eq⟩

/-- Joinability and equality of chosen results coincide under confluence. -/
theorem join_iff_run_eq (hc : Confluent r) :
    Join (ReflTransGen r) a b ↔ N.run a = N.run b :=
  ⟨fun h => N.run_eq_of_convertible hc (join_reflTransGen_le_eqvGen _ _ h),
    N.join_of_run_eq⟩

/-- A normalizer invariant under steps certifies global confluence.
No termination assumption is needed: its reachability certificate supplies
weak normalization, while invariance supplies a common result for every peak. -/
theorem confluent_of_step_invariant
    (h : ∀ {a b}, r a b → N.run a = N.run b) : Confluent r := by
  have hm : ∀ {a b}, ReflTransGen r a b → N.run a = N.run b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (h hstep)
  intro a b c hab hac
  exact N.join_of_run_eq ((hm hab).symm.trans (hm hac))

/-- Confluence is exactly invariance of a normalizer under each step. -/
theorem confluent_iff_step_invariant :
    Confluent r ↔ ∀ {a b}, r a b → N.run a = N.run b :=
  ⟨fun hc _ _ hab => N.run_eq_of_step hc hab, N.confluent_of_step_invariant⟩

/-- Uniqueness of reachable normal forms is also sufficient, given a normalizer. -/
theorem confluent_of_unique_normalForm (N : Normalizer r)
    (hu : ∀ {a n m}, NormalForm r a n → NormalForm r a m → n = m) :
    Confluent r := by
  apply N.confluent_of_step_invariant
  intro a b hab
  exact hu (N.normalForm a) ((N.normalForm b).prepend_step hab)

/-- Newman's lemma makes the normalizer chosen from termination invariant under conversion. -/
theorem ofTerminating_run_eq (ht : Terminating r) (hl : LocallyConfluent r)
    (hab : EqvGen r a b) :
    (ofTerminating ht).run a = (ofTerminating ht).run b :=
  (ofTerminating ht).run_eq_of_convertible (hl.terminating_toConfluent ht) hab

/-- Normalize into the subtype of terminal states. -/
def result (a : α) : {n : α // Normal r n} := ⟨N.run a, N.normal a⟩

/-- Normalization is a retraction onto normal states. -/
@[simp]
theorem result_normal (n : {n : α // Normal r n}) : N.result n.val = n := by
  apply Subtype.ext
  exact N.run_eq_of_normal n.property

/-- Every normal state occurs as a normalization result. -/
theorem result_surjective : Function.Surjective N.result :=
  fun n => ⟨n.val, N.result_normal n⟩

/-- Equality of subtype results characterizes conversion under confluence. -/
theorem convertible_iff_result_eq (hc : Confluent r) :
    EqvGen r a b ↔ N.result a = N.result b := by
  rw [N.convertible_iff_run_eq hc]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- An observation on normal states extends to all states by normalization. -/
def observe (f : {n : α // Normal r n} → β) (a : α) : β := f (N.result a)

/-- Observations of normalized states are invariant under conversion. -/
theorem observe_convertible (hc : Confluent r)
    (f : {n : α // Normal r n} → β) (hab : EqvGen r a b) :
    N.observe f a = N.observe f b :=
  congrArg f ((N.convertible_iff_result_eq hc).mp hab)

/-- Normalization extends an observation without changing its value on normal states. -/
@[simp]
theorem observe_normal (f : {n : α // Normal r n} → β)
    (n : {n : α // Normal r n}) : N.observe f n.val = f n := by
  simp [observe]

/-- Every conversion-invariant observation factors through normalization. -/
theorem observation_factors (f : α → β)
    (hf : ∀ {a b}, EqvGen r a b → f a = f b) (a : α) :
    f a = N.observe (fun n => f n.val) a :=
  hf (N.normalForm a).convertible

/-- The factorization through normal states is unique because normalization is onto. -/
theorem observation_factor_unique (f : α → β)
    (g : {n : α // Normal r n} → β) (hg : ∀ a, f a = N.observe g a) :
    g = fun n => f n.val := by
  funext n
  simpa using (hg n.val).symm

end Normalizer

end Cslib.Semantics.Rewriting
