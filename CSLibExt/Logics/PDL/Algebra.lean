/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.PDL.Basic
public import CSLibExt.Foundations.RelationAlgebra.Tests

/-!
# Relational interpretation of PDL programs

`Program.toRelation` changes the representation of the existing `ProgRel`
into CSLib's `SquareRelations`; it is not another program semantics.
The interpretation uses the canonical composition, union and diagonal-test
API. PDL iteration remains `ReflTransGen`, not relation converse.

Program-verification bridges and loop invariants are in `PDL.Hoare`.
-/

@[expose] public section

namespace Cslib.PDL

open RelationAlgebra

variable {World Atom Label : Type*}

/-- Interpret a PDL program in CSLib's canonical relation algebra. -/
def Program.toRelation (M : Model World Atom Label)
    (a : Program Atom Label) : SquareRelations World :=
  {(s, t) | ProgRel M a s t}

/-- The representation conversion preserves exactly the executions. -/
@[simp] theorem Program.mem_toRelation (M : Model World Atom Label)
    (a : Program Atom Label) (s t : World) :
    a.toRelation M (s, t) ↔ ProgRel M a s t := Iff.rfl

/-- The interpretation of sequencing uses canonical composition. -/
@[simp] theorem Program.toRelation_seq (M : Model World Atom Label)
    (a b : Program Atom Label) :
    (a.seq b).toRelation M = a.toRelation M * b.toRelation M := rfl

/-- The interpretation of choice uses canonical union. -/
@[simp] theorem Program.toRelation_choice (M : Model World Atom Label)
    (a b : Program Atom Label) :
    (a.choice b).toRelation M = a.toRelation M ⊔ b.toRelation M := rfl

/-- Formula tests use the existing PDL satisfaction predicate. -/
@[simp] theorem Program.toRelation_test (M : Model World Atom Label)
    (φ : Formula Atom Label) :
    (Program.test φ).toRelation M = testSet {s | Sat M φ s} := rfl

/-- Iteration in the canonical carrier is the same reflexive-transitive
closure as in `ProgRel`, including its identity boundary. -/
@[simp] theorem Program.toRelation_star (M : Model World Atom Label)
    (a : Program Atom Label) :
    a.star.toRelation M = {(s, t) |
      Relation.ReflTransGen (fun x y => a.toRelation M (x, y)) s t} :=
  rfl

end Cslib.PDL
