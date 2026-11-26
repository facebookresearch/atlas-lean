/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

/-!
# Edge covers of full natural joins

The leaves of a join-only `Expr` name relations. Restricting the database schema to these names
retains the incidence information needed for edge covers, without evaluating the query. In
particular two names with the same heading still give two LP variables, unlike edges in the
simple `Hypergraph` model. The vertex set is the union of the headings, not the ambient type.

## Reference

A. Atserias, M. Grohe and D. Marx, *Size Bounds and Query Plans for Relational Joins*, SIAM J.
Comput. 42 (2013), 1737–1767, §§1–2 and §3.1, LP (3.1).
-/

@[expose] public section

namespace Cslib.Databases

variable {N A D : Type*}

/-- **Named join hypergraph.** A finite set of relation names, with a finite heading (set of
attributes) for each of those names. Relations are the edge labels: distinct names may have
identical headings. The vertices are the attributes in at least one heading. -/
structure JoinHypergraph (N A : Type*) where
  /-- Relation names occurring in the join. -/
  relations : Finset N
  /-- Attributes incident to a relation. -/
  heading : relations → Finset A

/-- The vertex set of a named join hypergraph is the union of its relations' headings. -/
def JoinHypergraph.vertices [DecidableEq A] (H : JoinHypergraph N A) : Finset A :=
  H.relations.attach.biUnion H.heading

/-- The distinct relation names of an expression built only from base relations and natural
joins; for all other expressions the result is undefined. -/
def Expr.fullJoinRelations? [DecidableEq N] : Expr N A D → Option (Finset N)
  | .rel r => some {r}
  | .join p q => return (← p.fullJoinRelations?) ∪ (← q.fullJoinRelations?)
  | _ => none

/-- **Hypergraph of a full natural join.** Given a database schema, a relational expression made
only of named relations and binary natural joins yields the family of headings of its distinct
relation names. Repeated uses of one name count once; different names remain separate even when
their headings agree. Any other operator, including a projection, yields no hypergraph. -/
def Expr.joinHypergraph? [DecidableEq N] (sch : N → Finset A) (q : Expr N A D) :
    Option (JoinHypergraph N A) := q.fullJoinRelations?.map fun rs => ⟨rs, fun r => sch r⟩

private theorem Expr.schema_of_joinNames [DecidableEq N] [DecidableEq A] (sch : N → Finset A)
    (q : Expr N A D) {rs : Finset N} (hq : q.fullJoinRelations? = some rs) :
    q.schema sch = some (rs.biUnion sch) := by
  induction q generalizing rs with
  | rel r =>
    have : {r} = rs := Option.some.inj hq
    simp [← this, schema]
  | join p q ihp ihq =>
    obtain ⟨s, hs, t, ht, rfl⟩ := (by simpa [fullJoinRelations?, Option.bind_eq_some_iff] using hq :
      ∃ s, p.fullJoinRelations? = some s ∧ ∃ t, q.fullJoinRelations? = some t ∧ s ∪ t = rs)
    simp [schema, ihp hs, ihq ht, Finset.union_biUnion]
  | _ => simp [fullJoinRelations?] at hq

/-- Whenever a full natural join yields a hypergraph, its inferred output schema is precisely
the vertex set. In particular an unused ambient attribute imposes no cover constraint. -/
theorem Expr.schema_of_joinHypergraph? [DecidableEq N] [DecidableEq A] {sch : N → Finset A}
    {q : Expr N A D} {H : JoinHypergraph N A} (hq : q.joinHypergraph? sch = some H) :
    q.schema sch = some H.vertices := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hq
  simpa [JoinHypergraph.vertices, Finset.attach_biUnion] using q.schema_of_joinNames sch hs

namespace JoinHypergraph

variable [DecidableEq A] (H : JoinHypergraph N A)

/-- An integral edge cover is a set of relation names whose headings cover every vertex of the
join hypergraph. -/
def IsEdgeCover (C : Finset H.relations) : Prop := H.vertices ⊆ C.biUnion H.heading

/-- The integral edge cover number is the minimum cardinality of a set of relations covering
all attributes of the join. -/
noncomputable def edgeCoverNumber : ℕ := sInf (Finset.card '' {C | H.IsEdgeCover C})

/-- The integral edge cover number is attained, and no edge cover uses fewer relations. -/
theorem isLeast_edgeCoverNumber :
    IsLeast (Finset.card '' {C | H.IsEdgeCover C}) H.edgeCoverNumber := by
  have h : (Finset.card '' {C | H.IsEdgeCover C}).Nonempty :=
    ⟨_, H.relations.attach, fun _ ha => ha, rfl⟩
  exact ⟨Nat.sInf_mem h, fun _ => Nat.sInf_le⟩

/-- A fractional edge cover assigns a nonnegative real weight to each relation. For every
attribute in the union of the headings, the weights of the incident relations must sum to at
least one. -/
def IsFractionalEdgeCover (w : H.relations → ℝ) : Prop :=
  0 ≤ w ∧ ∀ a ∈ H.vertices, 1 ≤ ∑ r with a ∈ H.heading r, w r

/-- The fractional edge cover number is the minimum total weight of a fractional edge cover of
the named join hypergraph. -/
noncomputable def fractionalEdgeCoverNumber : ℝ :=
  sInf ((fun w => ∑ r, w r) '' {w | H.IsFractionalEdgeCover w})

private theorem one_feasible : H.IsFractionalEdgeCover 1 := by
  refine ⟨fun _ => zero_le_one, fun a ha => ?_⟩
  obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp ha
  exact Finset.single_le_sum (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩)

private theorem clip_feasible {w : H.relations → ℝ} (hw : H.IsFractionalEdgeCover w) :
    H.IsFractionalEdgeCover (fun r => min (w r) 1) := by
  refine ⟨fun r => le_min (hw.1 r) zero_le_one, fun a ha => ?_⟩
  let I := Finset.univ.filter fun r => a ∈ H.heading r
  change 1 ≤ ∑ r ∈ I, min (w r) 1
  by_cases h : ∃ r ∈ I, 1 ≤ w r
  · obtain ⟨r, hr, hwr⟩ := h
    simpa only [min_eq_right hwr] using Finset.single_le_sum
      (f := fun r => min (w r) 1) (fun r _ => le_min (hw.1 r) zero_le_one) hr
  · calc
      1 ≤ ∑ r ∈ I, w r := hw.2 a ha
      _ = ∑ r ∈ I, min (w r) 1 := Finset.sum_congr rfl fun r hr =>
        (min_eq_left (le_of_not_ge fun hwr => h ⟨r, hr, hwr⟩)).symm

/-- The fractional edge cover number is attained by nonnegative real relation weights, and
bounds the cost of every feasible assignment from below. No nonempty-heading or nonempty-query
hypothesis is required. -/
theorem isLeast_fractionalEdgeCoverNumber :
    IsLeast ((fun w => ∑ r, w r) '' {w | H.IsFractionalEdgeCover w})
      H.fractionalEdgeCoverNumber := by
  let constraints : Set (H.relations → ℝ) :=
    {w | ∀ a ∈ H.vertices, 1 ≤ ∑ r with a ∈ H.heading r, w r}
  let K := Set.Icc (0 : H.relations → ℝ) 1 ∩ constraints
  have closed : IsClosed constraints := by
    simp only [constraints, Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_finsetSum _ fun r _ => continuous_apply r)
  have compact : IsCompact K := isCompact_Icc.inter_right closed
  obtain ⟨w, hw, hmin⟩ := compact.exists_isMinOn ⟨1, ⟨zero_le_one, le_rfl⟩, H.one_feasible.2⟩
    (f := fun v => ∑ r, v r) (continuous_finsetSum _ fun r _ => continuous_apply r).continuousOn
  have least : IsLeast ((fun v => ∑ r, v r) '' {v | H.IsFractionalEdgeCover v}) (∑ r, w r) := by
    refine ⟨⟨w, ⟨hw.1.1, hw.2⟩, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hc := H.clip_feasible hv
    exact (hmin (show (fun r => min (v r) 1) ∈ K from
      ⟨⟨hc.1, fun _ => min_le_right ..⟩, hc.2⟩)).trans
      (Finset.sum_le_sum fun _ _ => min_le_left ..)
  rwa [fractionalEdgeCoverNumber, least.csInf_eq]

/-- The triangle join has relations $R[A,B]$, $S[B,C]$, $T[C,A]$. Numbering the names and
attributes cyclically from zero, relation $i$ has heading $\{i,i+1\}$ modulo three. -/
def triangle : JoinHypergraph (Fin 3) (Fin 3) where
  relations := Finset.univ
  heading r := {r.val, r.val + 1}

/-- The triangle join has integral edge cover number two and fractional edge cover number
three halves. Two relations suffice but no one does. Half weight on every relation is feasible;
summing the three attribute inequalities counts every relation twice. -/
theorem triangle_coverNumbers : triangle.edgeCoverNumber = 2 ∧
    triangle.fractionalEdgeCoverNumber = 3 / 2 := by
  let r : triangle.relations := ⟨0, by decide⟩
  let s : triangle.relations := ⟨1, by decide⟩
  let t : triangle.relations := ⟨2, by decide⟩
  constructor
  · apply triangle.isLeast_edgeCoverNumber.unique
    refine ⟨⟨{r, s}, ?_, by decide⟩, ?_⟩
    · unfold IsEdgeCover; decide
    · rintro _ ⟨C, hC, rfl⟩
      exact (show ∀ C : Finset triangle.relations, triangle.IsEdgeCover C → 2 ≤ C.card by
        unfold IsEdgeCover; decide) C hC
  · let I (a : Fin 3) := Finset.univ.filter fun n => a ∈ triangle.heading n
    have hA : I 0 = {r, t} := by decide
    have hB : I 1 = {r, s} := by decide
    have hC : I 2 = {s, t} := by decide
    have all : (Finset.univ : Finset triangle.relations) = {r, s, t} := by decide
    have hrs : r ≠ s := by decide
    have hrt : r ≠ t := by decide
    have hst : s ≠ t := by decide
    apply triangle.isLeast_fractionalEdgeCoverNumber.unique
    constructor
    · refine ⟨fun _ => 1 / 2, ⟨fun _ => by norm_num, fun a _ => ?_⟩, ?_⟩
      · change 1 ≤ ∑ _ ∈ I a, (1 / 2 : ℝ)
        fin_cases a <;> norm_num [hA, hB, hC, hrs, hrt, hst]
      · rw [all]; norm_num [hrs, hrt, hst]
    · rintro _ ⟨w, hw, rfl⟩
      have h (a : Fin 3) : 1 ≤ ∑ n ∈ I a, w n := hw.2 a ((by decide : ∀ a, a ∈ triangle.vertices) a)
      have ha := h 0
      have hb := h 1
      have hc := h 2
      rw [hA] at ha
      rw [hB] at hb
      rw [hC] at hc
      rw [all]
      simp [hrs, hrt, hst] at ha hb hc ⊢
      linarith

end JoinHypergraph

/-- For a full natural join, the pair consisting of the minimum integral cover size and the
minimum fractional cover weight of its named hypergraph. Expressions outside the fragment of
base relations and natural joins have no such pair. -/
noncomputable def Expr.edgeCoverNumbers? [DecidableEq N] [DecidableEq A] (sch : N → Finset A)
    (q : Expr N A D) : Option (ℕ × ℝ) :=
  (q.joinHypergraph? sch).map fun H => (H.edgeCoverNumber, H.fractionalEdgeCoverNumber)

end Cslib.Databases
