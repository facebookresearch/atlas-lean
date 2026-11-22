/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `9db2af32bec4c1fe1731f17c030e9410961257ed`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Head-normal forms for finite CCS
-/
module

public import CSLibExt.Languages.CCS.ExpansionStatic

/-!
# Head-normal forms for finite CCS

Every finite static CCS process is strongly bisimilar to a finite sum of
action-prefixed continuations.  The normalization is compositional: choice
concatenates summands, parallel uses the finite expansion construction, and
the two static operators act pointwise on summands.

This is the finite-process head-normal-form theorem underlying Milner's
expansion method; see Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Compute a top-level head presentation of a finite static CCS process.
Source continuations are normalized recursively, while continuations created
by parallel, restriction, and relabelling remain under those operators. -/
def headSummands : StaticProcess Name → List (Summand Name)
  | .nil => []
  | .prefix action continuation => [(action, sum (headSummands continuation))]
  | .choice left right => headSummands left ++ headSummands right
  | .parallel left right =>
      expansionSummands (headSummands left) (headSummands right)
  | .restriction blocked process => restrictSummands blocked (headSummands process)
  | .relabelling rename process => relabelSummands rename (headSummands process)

/-- The computed top-level head-normal-form process associated with a finite process. -/
def headNormalForm (process : StaticProcess Name) : StaticProcess Name :=
  sum (headSummands process)

@[simp] theorem headSummands_nil :
    headSummands (.nil : StaticProcess Name) = [] := rfl

@[simp] theorem headSummands_prefix (action : Label Name)
    (continuation : StaticProcess Name) :
    headSummands (.prefix action continuation) =
      [(action, headNormalForm continuation)] := rfl

@[simp] theorem headSummands_choice (left right : StaticProcess Name) :
    headSummands (.choice left right) = headSummands left ++ headSummands right := rfl

@[simp] theorem headSummands_parallel (left right : StaticProcess Name) :
    headSummands (.parallel left right) =
      expansionSummands (headSummands left) (headSummands right) := rfl

@[simp] theorem headSummands_restriction (blocked : List Name)
    (process : StaticProcess Name) :
    headSummands (.restriction blocked process) =
      restrictSummands blocked (headSummands process) := rfl

@[simp] theorem headSummands_relabelling (rename : Relabelling Name)
    (process : StaticProcess Name) :
    headSummands (.relabelling rename process) =
      relabelSummands rename (headSummands process) := rfl

@[simp] theorem headNormalForm_nil :
    headNormalForm (.nil : StaticProcess Name) = .nil := rfl

theorem headNormalForm_prefix (action : Label Name)
    (continuation : StaticProcess Name) :
    headNormalForm (.prefix action continuation) =
      sum [(action, headNormalForm continuation)] := rfl

theorem headNormalForm_choice (left right : StaticProcess Name) :
    headNormalForm (.choice left right) =
      sum (headSummands left ++ headSummands right) := rfl

theorem headNormalForm_parallel (left right : StaticProcess Name) :
    headNormalForm (.parallel left right) =
      expansion (headSummands left) (headSummands right) := rfl

theorem headNormalForm_restriction (blocked : List Name)
    (process : StaticProcess Name) :
    headNormalForm (.restriction blocked process) =
      sum (restrictSummands blocked (headSummands process)) := rfl

theorem headNormalForm_relabelling (rename : Relabelling Name)
    (process : StaticProcess Name) :
    headNormalForm (.relabelling rename process) =
      sum (relabelSummands rename (headSummands process)) := rfl

/-- Every finite static CCS process is strongly bisimilar to its computed
head normal form. -/
theorem bisimilar_headNormalForm (process : StaticProcess Name) :
    lts.HomBisimilarity process (headNormalForm process) := by
  induction process with
  | nil => exact HomBisimilarity.refl _
  | «prefix» action continuation ih =>
      exact (prefix_congr action ih).trans
        (sum_singleton_bisimilar_prefix action (headNormalForm continuation)).symm
  | choice left right ihLeft ihRight =>
      exact (choice_congr ihLeft ihRight).trans
        (sum_append_bisimilar_choice (headSummands left) (headSummands right)).symm
  | parallel left right ihLeft ihRight =>
      exact (parallel_congr ihLeft ihRight).trans
        (parallel_sum_bisimilar_expansion (headSummands left) (headSummands right))
  | restriction blocked process ih =>
      exact (restriction_congr blocked ih).trans
        (restriction_sum_bisimilar blocked (headSummands process))
  | relabelling rename process ih =>
      exact (relabelling_congr rename ih).trans
        (relabelling_sum_bisimilar rename (headSummands process))

/-- Head normalization preserves and reflects which actions are enabled. -/
theorem enabled_headNormalForm_iff (process : StaticProcess Name)
    (action : Label Name) :
    lts.HasOutLabel process action ↔ lts.HasOutLabel (headNormalForm process) action :=
  HomBisimilarity.hasOutLabel_iff
    (bisimilar_headNormalForm process) action

end Cslib.CCS.StaticProcess
