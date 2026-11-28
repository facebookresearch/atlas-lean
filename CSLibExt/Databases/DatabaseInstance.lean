/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Data.Finset.Option

/-!
# Database instances

A **database instance** of a database schema assigns a relation over the schema of each
relation name (`DatabaseInstance`). A query evaluated on an instance is over its inferred
schema (`DatabaseInstance.eval_isOver`); the **active domain** of an instance collects the
values occurring in its relations, and queries create no new values
(`DatabaseInstance.adom_eval_subset`). Selection and projection distribution laws are restated
as query rewrites (`Expr.select_comm`, `Expr.select_union`, `Expr.select_diff`,
`Expr.project_union`, `Expr.select_project`, `Expr.select_join_right`).
-/

@[expose] public section

namespace Cslib.Databases

variable {N A D : Type*}

variable (D) in
/-- A **database instance** of the database schema `sch` (Abiteboul–Hull–Vianu, Section 3.3,
conventional perspective): a relation over `sch n` for each relation name `n`. Values range over
`D`; attributes over `A`. -/
structure DatabaseInstance (sch : N → Finset A) where
  /-- The relation instance assigned to each relation name. -/
  rel : N → Finset (Tuple A D)
  /-- Each relation is over the schema of its name. -/
  conforms : Expr.Conforms sch rel

section adom

variable [Fintype A] [DecidableEq D]

/-- The **active domain** of a relation: the set of values occurring in its tuples. -/
def adom (r : Finset (Tuple A D)) : Finset D :=
  r.biUnion fun t => Finset.univ.biUnion fun a => (t a).toFinset

theorem mem_adom {r : Finset (Tuple A D)} {d : D} :
    d ∈ adom r ↔ ∃ t ∈ r, ∃ a, t a = some d := by
  simp only [adom, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset,
    Option.mem_def]

private theorem adom_mono {r s : Finset (Tuple A D)} (h : r ⊆ s) : adom r ⊆ adom s := by
  intro d hd
  obtain ⟨t, ht, a, ha⟩ := mem_adom.mp hd
  exact mem_adom.mpr ⟨t, h ht, a, ha⟩

end adom

namespace DatabaseInstance

variable {sch : N → Finset A}

/-- **Typing soundness for database instances**: a well-typed query evaluates on a database
instance to a relation over its inferred schema. -/
theorem eval_isOver [Fintype A] [DecidableEq A] [DecidableEq D] (I : DatabaseInstance D sch)
    {e : Expr N A D} {S : Finset A} (h : e.schema sch = some S) : IsOver S (e.eval I.rel) := by
  exact Expr.eval_isOver I.conforms e h

variable [Fintype N] [Fintype A] [DecidableEq D]

/-- The **active domain** `adom(I)` of a database instance: the values occurring in any of its
relations. -/
def adom (I : DatabaseInstance D sch) : Finset D :=
  Finset.univ.biUnion fun n => Databases.adom (I.rel n)

theorem mem_adom {I : DatabaseInstance D sch} {d : D} :
    d ∈ I.adom ↔ ∃ n, ∃ t ∈ I.rel n, ∃ a, t a = some d := by
  simp only [adom, Finset.mem_biUnion, Finset.mem_univ, true_and, Databases.mem_adom]

/-- Queries (which have no constants) create no values: `adom(q(I)) ⊆ adom(I)`. -/
theorem adom_eval_subset [DecidableEq A] (I : DatabaseInstance D sch) (e : Expr N A D) :
    Databases.adom (e.eval I.rel) ⊆ I.adom := by
  induction e with
  | rel n =>
      simp only [Expr.eval]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      exact mem_adom.mpr ⟨n, t, ht, a, ha⟩
  | select c e ih =>
      simp only [Expr.eval, Databases.select]
      exact (Databases.adom_mono (Finset.filter_subset _ _)).trans ih
  | project T e ih =>
      simp only [Expr.eval, Databases.project]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hua : u a = some d := by
        rw [Tuple.restrict_apply] at ha
        split_ifs at ha with hT
        exact ha
      exact ih (Databases.mem_adom.mpr ⟨u, hu, a, hua⟩)
  | join e e' ih ih' =>
      simp only [Expr.eval]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, v, hv, -, rfl⟩ := Databases.mem_join.mp ht
      simp only [Tuple.merge] at ha
      cases hua : u a with
      | none =>
          rw [hua] at ha
          have h2 : v a = some d := ha
          exact ih' (Databases.mem_adom.mpr ⟨v, hv, a, h2⟩)
      | some x =>
          rw [hua] at ha
          have h2 : some x = some d := ha
          simp only [Option.some.injEq] at h2
          have hua' : u a = some d := hua.trans (congrArg some h2)
          exact ih (Databases.mem_adom.mpr ⟨u, hu, a, hua'⟩)
  | union e e' ih ih' =>
      simp only [Expr.eval]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      rcases Finset.mem_union.mp ht with h | h
      · exact ih (Databases.mem_adom.mpr ⟨t, h, a, ha⟩)
      · exact ih' (Databases.mem_adom.mpr ⟨t, h, a, ha⟩)
  | diff e e' ih _ =>
      simp only [Expr.eval]
      exact (Databases.adom_mono Finset.sdiff_subset).trans ih
  | rename f e ih =>
      simp only [Expr.eval, Databases.rename]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      simp only [Function.comp_apply] at ha
      exact ih (Databases.mem_adom.mpr ⟨u, hu, f.symm a, ha⟩)

end DatabaseInstance

namespace Expr

variable [Fintype A] [DecidableEq A] [DecidableEq D] {sch : N → Finset A}

/-- Selections commute, as a query rewrite. -/
theorem select_comm {e : Expr N A D} {S : Finset A} (he : e.schema sch = some S)
    {c c' : Cond A D} (hc : c.attrs ⊆ S) (hc' : c'.attrs ⊆ S) :
    Equiv sch (select c (select c' e)) (select c' (select c e)) := by
  refine ⟨S, by simp [schema, he, hc, hc'], by simp [schema, he, hc, hc'], ?_⟩
  intro db _
  exact Databases.select_comm _ _ _

/-- Selection distributes over union, as a query rewrite. -/
theorem select_union {e e' : Expr N A D} {S : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) {c : Cond A D} (hc : c.attrs ⊆ S) :
    Equiv sch (select c (union e e')) (union (select c e) (select c e')) := by
  refine ⟨S, by simp [schema, he, he', hc], by simp [schema, he, he', hc], ?_⟩
  intro db _
  exact Databases.select_union _ _ _

/-- Selection distributes over difference, as a query rewrite. -/
theorem select_diff {e e' : Expr N A D} {S : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) {c : Cond A D} (hc : c.attrs ⊆ S) :
    Equiv sch (select c (diff e e')) (diff (select c e) (select c e')) := by
  refine ⟨S, by simp [schema, he, he', hc], by simp [schema, he, he', hc], ?_⟩
  intro db _
  exact Databases.select_sdiff _ _ _

/-- Projection distributes over union, as a query rewrite. -/
theorem project_union {e e' : Expr N A D} {S T : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) (hT : T ⊆ S) :
    Equiv sch (project T (union e e')) (union (project T e) (project T e')) := by
  refine ⟨T, by simp [schema, he, he', hT], by simp [schema, he, he', hT], ?_⟩
  intro db _
  exact Databases.project_union _ _ _

/-- Selection commutes with a projection that keeps its attributes, as a query rewrite. -/
theorem select_project {e : Expr N A D} {S T : Finset A} (he : e.schema sch = some S)
    (hT : T ⊆ S) {c : Cond A D} (hc : c.attrs ⊆ T) :
    Equiv sch (select c (project T e)) (project T (select c e)) := by
  refine ⟨T, by simp [schema, he, hT, hc], by simp [schema, he, hT, hc.trans hT], ?_⟩
  intro db _
  exact Databases.select_project _ _ hc

/-- **Selection pushdown** into the right operand of a join, as a query rewrite. -/
theorem select_join_right {e e' : Expr N A D} {S S' : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S') (c : Cond A D) (hc : c.attrs ⊆ S') :
    Equiv sch (select c (join e e')) (join e (select c e')) := by
  refine ⟨S ∪ S', by simp [schema, he, he', hc.trans Finset.subset_union_right],
    by simp [schema, he, he', hc], ?_⟩
  intro db hdb
  exact Databases.select_join_right _ _ (eval_isOver hdb e' he') hc

end Expr

end Cslib.Databases

