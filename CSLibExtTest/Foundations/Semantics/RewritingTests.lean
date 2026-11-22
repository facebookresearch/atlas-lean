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

public import CSLibExt.Foundations.Semantics.Rewriting.Confluence

public import Mathlib.Data.Fintype.Basic

/-!
# Finite abstract rewriting examples

These examples exercise the abstract reduction systems of Terese,
*Term Rewriting Systems*, Cambridge University Press, 2003, Chapter 1.

* `Workflow` has a fork with unequal path lengths and two terminal states.
  It terminates, is locally confluent but fails the one-step diamond property,
  and has a concrete executable normalizer. Newman's lemma establishes confluence.
* `Fork` terminates but fails local confluence and has two distinct normal forms.
* `LoopFork` is locally confluent and normalizing but not confluent or terminating.
  It shows that weak normalization cannot replace termination in Newman's lemma.
* `Spin` is confluent but has no normal forms, so confluence alone gives no existence.

All finite case splits and equality decisions are checked by Lean's kernel.
-/

@[expose] public section

namespace Cslib.Semantics.Rewriting.Tests

open Relation

namespace Workflow

/-- A fork with a delayed join, followed by cleanup; `idle` is a separate normal state. -/
inductive State
  | start | left | right | delayed | joined | done | idle
  deriving DecidableEq

open State

/-- Explicit finite carrier, avoiding any assumption about the reduction relation. -/
instance : Fintype State where
  elems := {start, left, right, delayed, joined, done, idle}
  complete x := by cases x <;> simp

/-- `start → left → joined → done` and `start → right → delayed → joined → done`. -/
inductive Step : State → State → Prop
  | chooseLeft : Step start left
  | chooseRight : Step start right
  | finishLeft : Step left joined
  | delayRight : Step right delayed
  | finishRight : Step delayed joined
  | cleanup : Step joined done

/-- A strictly decreasing rank proves termination independently of confluence. -/
def rank : State → ℕ
  | start => 4
  | right => 3
  | left | delayed => 2
  | joined => 1
  | done | idle => 0

theorem rank_decreases {source target : State} (h : Step source target) : rank target < rank source := by
  cases h <;> decide

theorem terminating : Terminating Step :=
  (measure rank).wf.mono fun _ _ h => rank_decreases h

theorem done_normal : Normal Step done := by
  rintro ⟨target, h⟩
  cases h

theorem idle_normal : Normal Step idle := by
  rintro ⟨target, h⟩
  cases h

/-- The delayed branches join in multiple steps. -/
theorem branches_join : Join (ReflTransGen Step) left right :=
  ⟨joined, .single .finishLeft, (ReflTransGen.single Step.delayRight).tail .finishRight⟩

theorem locallyConfluent : LocallyConfluent Step := by
  intro source target₁ target₂ hab hac
  cases hab <;> cases hac
  · exact ⟨left, .refl, .refl⟩
  · exact branches_join
  · exact ⟨joined, (ReflTransGen.single Step.delayRight).tail .finishRight, .single .finishLeft⟩
  · exact ⟨right, .refl, .refl⟩
  · exact ⟨joined, .refl, .refl⟩
  · exact ⟨delayed, .refl, .refl⟩
  · exact ⟨joined, .refl, .refl⟩
  · exact ⟨done, .refl, .refl⟩

/-- One-step diamond is stronger than local confluence in this example. -/
theorem not_diamond : ¬ Diamond Step := by
  intro hd
  obtain ⟨d, hld, hrd⟩ := hd Step.chooseLeft Step.chooseRight
  cases hld
  cases hrd

/-- This proof uses the upstream Newman's lemma with both hypotheses. -/
theorem confluent : Confluent Step := locallyConfluent.terminating_toConfluent terminating

/-- The two components normalize to different terminal states. -/
def finish : State → State
  | idle => idle
  | _ => done

theorem finish_reachable (a : State) : ReflTransGen Step a (finish a) := by
  cases a with
  | start => exact ((ReflTransGen.single Step.chooseLeft).tail .finishLeft).tail .cleanup
  | left => exact (ReflTransGen.single Step.finishLeft).tail .cleanup
  | right => exact ((ReflTransGen.single Step.delayRight).tail .finishRight).tail .cleanup
  | delayed => exact (ReflTransGen.single Step.finishRight).tail .cleanup
  | joined => exact .single .cleanup
  | done => exact .refl
  | idle => exact .refl

theorem finish_normal (a : State) : Normal Step (finish a) := by
  cases a <;> first | exact done_normal | exact idle_normal

/-- A concrete normalizer with a computable result function. -/
def evaluator : Normalizer Step := ⟨finish, finish_reachable, finish_normal⟩

theorem start_normalForm : NormalForm Step start done := evaluator.normalForm start

theorem right_normalForm : NormalForm Step right done := evaluator.normalForm right

theorem normal_iff (a : State) : Normal Step a ↔ a = done ∨ a = idle := by
  rw [← evaluator.run_eq_self_iff]
  cases a <;> simp [evaluator, finish]

/-- Normalization equates the unequal-length branches. -/
example : evaluator.run left = evaluator.run right :=
  evaluator.run_eq_of_convertible confluent
    (.trans _ _ _ (.symm _ _ (.rel _ _ Step.chooseLeft)) (.rel _ _ Step.chooseRight))

/-- Conversion reduces to an equality decision on the executable normalizer. -/
example : EqvGen Step start delayed :=
  (evaluator.convertible_iff_run_eq confluent).mpr rfl

/-- Having more than one normal state is consistent with confluence. -/
example : ¬ EqvGen Step done idle := by
  rw [evaluator.convertible_iff_run_eq confluent]
  decide

/-- A reachable normal form of the starting state must be `done`. -/
example {n : State} (h : NormalForm Step start n) : n = done :=
  (evaluator.normalForm_iff confluent).mp h

/-- Classical choice and the concrete evaluator agree, without unfolding choice. -/
example (a : State) : (Normalizer.ofTerminating terminating).run a = finish a :=
  Normalizer.run_eq _ evaluator confluent a

/-- The observation factorization can be used directly on the terminal-state subtype. -/
example (a : State) : evaluator.observe (fun n => rank n.val) a = 0 := by
  cases a <;> rfl

end Workflow

namespace Fork

inductive State | root | left | right
  deriving DecidableEq

open State

/-- Explicit finite carrier, avoiding any assumption about the reduction relation. -/
instance : Fintype State where
  elems := {root, left, right}
  complete x := by cases x <;> simp

inductive Step : State → State → Prop
  | left : Step root State.left
  | right : Step root State.right

def rank : State → ℕ | root => 1 | _ => 0

theorem terminating : Terminating Step := by
  apply (measure rank).wf.mono
  intro source target h
  cases h <;> change 0 < 1 <;> decide

theorem left_normal : Normal Step left := by rintro ⟨target, h⟩; cases h

theorem right_normal : Normal Step right := by rintro ⟨target, h⟩; cases h

theorem two_normalForms : NormalForm Step root left ∧ NormalForm Step root right :=
  ⟨⟨.single .left, left_normal⟩, ⟨.single .right, right_normal⟩⟩

/-- Termination alone does not imply unique reachable normal forms. -/
theorem not_confluent : ¬ Confluent Step := by
  intro hc
  have heq := two_normalForms.1.eq two_normalForms.2 hc
  cases heq

/-- The missing Newman's lemma hypothesis is local confluence. -/
theorem not_locallyConfluent : ¬ LocallyConfluent Step := by
  intro hl
  exact not_confluent (hl.terminating_toConfluent terminating)

end Fork

namespace LoopFork

/-- Two cycling states each have a distinct escape to a terminal state. -/
inductive State | a | b | left | right
  deriving DecidableEq

open State

/-- Explicit finite carrier, avoiding any assumption about the reduction relation. -/
instance : Fintype State where
  elems := {a, b, left, right}
  complete x := by cases x <;> simp

inductive Step : State → State → Prop
  | ab : Step a b
  | ba : Step b a
  | exitLeft : Step a left
  | exitRight : Step b right

theorem left_normal : Normal Step left := by rintro ⟨target, h⟩; cases h

theorem right_normal : Normal Step right := by rintro ⟨target, h⟩; cases h

/-- Every one-step peak joins by returning around the cycle. -/
theorem locallyConfluent : LocallyConfluent Step := by
  intro source target₁ target₂ hab hac
  cases hab <;> cases hac
  · exact ⟨b, .refl, .refl⟩
  · exact ⟨left, (ReflTransGen.single Step.ba).tail .exitLeft, .refl⟩
  · exact ⟨a, .refl, .refl⟩
  · exact ⟨right, (ReflTransGen.single Step.ab).tail .exitRight, .refl⟩
  · exact ⟨left, .refl, (ReflTransGen.single Step.ba).tail .exitLeft⟩
  · exact ⟨left, .refl, .refl⟩
  · exact ⟨right, .refl, (ReflTransGen.single Step.ab).tail .exitRight⟩
  · exact ⟨right, .refl, .refl⟩

/-- There is a terminating strategy from every state, despite the cycle. -/
theorem normalizing : Normalizing Step := by
  intro x
  cases x with
  | a => exact ⟨left, .single .exitLeft, left_normal⟩
  | b => exact ⟨right, .single .exitRight, right_normal⟩
  | left => exact ⟨left, .refl, left_normal⟩
  | right => exact ⟨right, .refl, right_normal⟩

/-- One state reaches two different terminal states. -/
theorem not_confluent : ¬ Confluent Step := by
  intro hc
  have hl : NormalForm Step a left := ⟨.single .exitLeft, left_normal⟩
  have hr : NormalForm Step a right := ⟨(ReflTransGen.single Step.ab).tail .exitRight, right_normal⟩
  cases hl.eq hr hc

/-- Newman's lemma cannot use weak normalization in place of termination. -/
theorem not_terminating : ¬ Terminating Step := by
  intro ht
  exact not_confluent (locallyConfluent.terminating_toConfluent ht)

/-- A chosen normalizer need not respect steps without confluence. -/
example : ¬ ∀ {source target}, Step source target →
    (Normalizer.ofNormalizing normalizing).run source =
      (Normalizer.ofNormalizing normalizing).run target := by
  intro h
  exact not_confluent ((Normalizer.ofNormalizing normalizing).confluent_of_step_invariant h)

end LoopFork

namespace Spin

/-- A one-state loop is confluent and never reaches a normal state. -/
def Step (_ _ : Unit) : Prop := True

theorem confluent : Confluent Step := by
  intro source target₁ target₂ hab hac
  exact ⟨(), .single trivial, .single trivial⟩

theorem no_normal (a : Unit) : ¬ Normal Step a := fun h => h ⟨a, trivial⟩

theorem not_normalizable (a : Unit) : ¬ Normalizable Step a := by
  rintro ⟨n, _, hn⟩
  exact no_normal n hn

/-- Normalizer existence cannot be obtained from confluence alone. -/
example : IsEmpty (Normalizer Step) :=
  ⟨fun N => not_normalizable () (N.normalizing ())⟩

end Spin

end Cslib.Semantics.Rewriting.Tests
