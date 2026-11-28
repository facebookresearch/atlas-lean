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
# Active domains

The **active domain** of a relation (`adom`) or of a database (`adomDB`) collects the values
occurring in its tuples. Queries create no new values: for finite relation-name and attribute
types, with decidable equality on attributes and values, the active domain of a query result is
contained in the active domain of the database (`adom_eval_subset`). The database need not
conform to a schema.

This is the relational-algebra model's notion of active domain, over partial tuples; it is
distinct from `RelationalSchema.Instance.activeDomain` in `InclusionDependencies`, which uses
total tuples over a named schema.

## References

Serge Abiteboul, Richard Hull, and Victor Vianu, _Foundations of Databases_ (Addison-Wesley,
1995): Section 4.2 (p. 41) for the active domain, where the active domain of a query result is
contained in the union of the active domains of the query and the instance (stated there for
rule-based conjunctive queries).
-/

@[expose] public section

namespace Cslib.Databases

variable {N A D : Type*}

section adom

variable [Fintype A] [DecidableEq D]

/-- **Active domain of a set of tuples.** For a finite set $r$ of tuples of the relational
algebra (partial assignments of values to attributes) over a finite attribute type, with
decidable value equality (the definition enumerates all attributes), the active domain of $r$
is the set of values that some tuple of $r$ takes at some attribute. -/
def adom (r : Finset (Tuple A D)) : Finset D :=
  r.biUnion fun t => Finset.univ.biUnion fun a => (t a).toFinset

@[simp]
theorem mem_adom {r : Finset (Tuple A D)} {d : D} :
    d ∈ adom r ↔ ∃ t ∈ r, ∃ a, t a = some d := by
  simp only [adom, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset,
    Option.mem_def]

private theorem adom_mono {r s : Finset (Tuple A D)} (h : r ⊆ s) : adom r ⊆ adom s := by
  intro d hd
  obtain ⟨t, ht, a, ha⟩ := mem_adom.mp hd
  exact mem_adom.mpr ⟨t, h ht, a, ha⟩

end adom

/-- **Active domain of a relational-algebra database.** For a database $\mathrm{db}$ assigning a
finite set of tuples to each of finitely many relation names over a finite attribute type, with
decidable value equality, the active domain of $\mathrm{db}$ is the union of the active domains
of the sets $\mathrm{db}(n)$. -/
def adomDB [Fintype N] [Fintype A] [DecidableEq D] (db : N → Finset (Tuple A D)) : Finset D :=
  Finset.univ.biUnion fun n => adom (db n)

@[simp]
theorem mem_adomDB [Fintype N] [Fintype A] [DecidableEq D] {db : N → Finset (Tuple A D)} {d : D} :
    d ∈ adomDB db ↔ ∃ n, ∃ t ∈ db n, ∃ a, t a = some d := by
  simp only [adomDB, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_adom]

/-- **Queries create no values.** For every database `db` (conforming or not) and every query
`e`, every value in the result already occurs in `db`. Both the relation-name type and the
attribute type are finite, and attribute and value equality are decidable; each individual
relation being a finite set would not by itself bound the values across infinitely many names
or attributes. The source's bound also allows the
constants of the query; here they contribute nothing, because constants occur only in selection
conditions, which filter tuples, and no constructor of `Expr` builds a tuple from a constant.

Source: S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
Section 4.2, p. 41, where adom(q(I)) ⊆ adom(q) ∪ adom(I) is stated for rule-based conjunctive
queries. -/
theorem adom_eval_subset [Fintype N] [Fintype A] [DecidableEq A] [DecidableEq D]
    (db : N → Finset (Tuple A D)) (e : Expr N A D) : adom (e.eval db) ⊆ adomDB db := by
  induction e with
  | rel n =>
      simp only [Expr.eval]
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      exact mem_adomDB.mpr ⟨n, t, ht, a, ha⟩
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

end Cslib.Databases
