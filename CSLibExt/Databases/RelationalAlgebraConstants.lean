/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.ActiveDomain

/-!
# Relational algebra with constants

Relational algebra queries with unary singleton constants `{⟨a : d⟩}`, after Section 4.4 of
Abiteboul, Hull and Vianu, as a conservative extension of `Expr`. Constants are extra base
relation names: `ConstExpr N A D` is `Expr` over the names `N ⊕ A × D`, where the name `(a, d)`
denotes the singleton `{⟨a : d⟩}` with schema `{a}`. `ConstExpr.eval` and `ConstExpr.schema`
are the underlying `Expr` operations on the extended database (`extDb`) and schema
(`extSchema`); typing is sound (`ConstExpr.eval_isOver`); every `Expr` rewrite law lifts in one
line through `ConstExpr.Equiv.of_expr`; and the extension is conservative
(`ConstExpr.equiv_ofExpr_iff`). Queries with constants create no values beyond their own
constants (`ConstExpr.adom_eval_subset`). The active-domain bound needs a finite relation-name
type; the remaining results need only a finite attribute type, with decidable attribute and
value equality where stated.

## References

Serge Abiteboul, Richard Hull, and Victor Vianu, _Foundations of Databases_ (Addison-Wesley,
1995): Section 4.4 (p. 58) for the unary singleton constants, Section 4.2 (p. 41) for the
active-domain bound, and Section 5.1 (p. 71) for finite constant relations as unions of
singletons.
-/

@[expose] public section

namespace Cslib.Databases

variable {N A D : Type*}

namespace Expr

/-- **Renaming base relations.** The query obtained from a relational algebra query by renaming
each base relation name $n$ to $g(n)$, leaving every operator unchanged. -/
def mapRel {N' : Type*} (g : N → N') : Expr N A D → Expr N' A D
  | rel n => rel (g n)
  | select c e => select c (e.mapRel g)
  | project T e => project T (e.mapRel g)
  | join e e' => join (e.mapRel g) (e'.mapRel g)
  | union e e' => union (e.mapRel g) (e'.mapRel g)
  | diff e e' => diff (e.mapRel g) (e'.mapRel g)
  | rename f e => rename f (e.mapRel g)

/-- Schema inference commutes with renaming base relation names, with decidable attribute
equality. -/
theorem schema_mapRel [DecidableEq A] {N' : Type*} (g : N → N') (sch : N' → Finset A)
    (e : Expr N A D) : (e.mapRel g).schema sch = e.schema (sch ∘ g) := by
  induction e with
  | rel n => simp [mapRel, schema]
  | select c e ih => simp [mapRel, schema, ih]
  | project T e ih => simp [mapRel, schema, ih]
  | join e e' ih ih' => simp [mapRel, schema, ih, ih']
  | union e e' ih ih' => simp [mapRel, schema, ih, ih']
  | diff e e' ih ih' => simp [mapRel, schema, ih, ih']
  | rename f e ih => simp [mapRel, schema, ih]

/-- Evaluation commutes with renaming base relation names. The attribute type is finite,
and attribute and value equality are decidable. -/
theorem eval_mapRel [DecidableEq D] [Fintype A] [DecidableEq A] {N' : Type*} (g : N → N')
    (db : N' → Finset (Tuple A D)) (e : Expr N A D) : (e.mapRel g).eval db = e.eval (db ∘ g) := by
  induction e with
  | rel n => simp [mapRel, eval]
  | select c e ih => simp [mapRel, eval, ih]
  | project T e ih => simp [mapRel, eval, ih]
  | join e e' ih ih' => simp [mapRel, eval, ih, ih']
  | union e e' ih ih' => simp [mapRel, eval, ih, ih']
  | diff e e' ih ih' => simp [mapRel, eval, ih, ih']
  | rename f e ih => simp [mapRel, eval, ih]

end Expr

/-- **Relational algebra queries with constants.** Queries over the base relation names `N`
extended by one name `(a, d)` for each attribute `a` and value `d`; that name denotes the unary
singleton constant `{⟨a : d⟩}` (AHV Section 4.4). -/
abbrev ConstExpr (N A D : Type*) := Expr (N ⊕ A × D) A D

namespace ConstExpr

/-- The tuple `⟨a : d⟩`: value `d` at the attribute `a`, undefined elsewhere. Attribute
equality is decidable. -/
def single [DecidableEq A] (a : A) (d : D) : Tuple A D := fun b => if b = a then some d else none

/-- The tuple `⟨a : d⟩` is over the schema `{a}`. Attribute equality is decidable. -/
theorem single_isOver [DecidableEq A] (a : A) (d : D) : (single a d).IsOver {a} := by
  intro b
  by_cases h : b = a <;> simp [single, h]

/-- The unary singleton constant query `{⟨a : d⟩}`. -/
def const (a : A) (d : D) : ConstExpr N A D := .rel (.inr (a, d))

/-- An original query, read as a query with constants. -/
def ofExpr (e : Expr N A D) : ConstExpr N A D := e.mapRel Sum.inl

/-- The database schema extended to the constant names: `(a, d)` has schema `{a}`. -/
def extSchema (sch : N → Finset A) : N ⊕ A × D → Finset A :=
  Sum.elim sch fun p => {p.1}

/-- The database extended to the constant names: `(a, d)` holds the one tuple `⟨a : d⟩`.
Attribute equality is decidable. -/
def extDb [DecidableEq A] (db : N → Finset (Tuple A D)) : N ⊕ A × D → Finset (Tuple A D) :=
  Sum.elim db fun p => {single p.1 p.2}

/-- **Schema of a query with constants**: the schema of the underlying query over the extended
database schema. Attribute equality is decidable. -/
def schema [DecidableEq A] (sch : N → Finset A) (e : ConstExpr N A D) : Option (Finset A) :=
  Expr.schema (extSchema sch) e

/-- **Value of a query with constants** on a database: the value of the underlying query on the
extended database. The attribute type is finite, and attribute and value equality are
decidable. -/
def eval [DecidableEq D] [Fintype A] [DecidableEq A] (db : N → Finset (Tuple A D))
    (e : ConstExpr N A D) : Finset (Tuple A D) :=
  Expr.eval (extDb db) e

/-- The values of the constant singletons occurring in a query with constants. Value
equality is decidable. -/
def consts [DecidableEq D] : ConstExpr N A D → Finset D
  | Expr.rel (Sum.inl _) => ∅
  | Expr.rel (Sum.inr p) => {p.2}
  | Expr.select _ e => consts e
  | Expr.project _ e => consts e
  | Expr.join e e' => consts e ∪ consts e'
  | Expr.union e e' => consts e ∪ consts e'
  | Expr.diff e e' => consts e ∪ consts e'
  | Expr.rename _ e => consts e

/-- **Query equivalence for queries with constants**: both are well-formed with the same schema
and they agree on every database conforming to `sch`. The attribute type is finite, and
attribute and value equality are decidable. -/
def Equiv [DecidableEq D] [Fintype A] [DecidableEq A] (sch : N → Finset A)
    (e e' : ConstExpr N A D) : Prop :=
  ∃ S, e.schema sch = some S ∧ e'.schema sch = some S ∧
    ∀ db, Expr.Conforms sch db → e.eval db = e'.eval db

/-- Structural induction for queries with constants, with the constant leaf as its own case. -/
@[elab_as_elim]
theorem induction_on {motive : ConstExpr N A D → Prop} (e : ConstExpr N A D)
    (hrel : ∀ n, motive (Expr.rel (Sum.inl n))) (hconst : ∀ a d, motive (const a d))
    (hselect : ∀ c e, motive e → motive (Expr.select c e))
    (hproject : ∀ T e, motive e → motive (Expr.project T e))
    (hjoin : ∀ e e', motive e → motive e' → motive (Expr.join e e'))
    (hunion : ∀ e e', motive e → motive e' → motive (Expr.union e e'))
    (hdiff : ∀ e e', motive e → motive e' → motive (Expr.diff e e'))
    (hrename : ∀ f e, motive e → motive (Expr.rename f e)) : motive e := by
  induction e with
  | rel n =>
      rcases n with n | ⟨a, d⟩
      · exact hrel n
      · exact hconst a d
  | select c e ih => exact hselect c e ih
  | project T e ih => exact hproject T e ih
  | join e e' ih ih' => exact hjoin e e' ih ih'
  | union e e' ih ih' => exact hunion e e' ih ih'
  | diff e e' ih ih' => exact hdiff e e' ih ih'
  | rename f e ih => exact hrename f e ih

/-- The constant query `{⟨a : d⟩}` has inferred schema `{a}`. Attribute equality is
decidable. -/
@[simp] theorem schema_const [DecidableEq A] (sch : N → Finset A) (a : A) (d : D) :
    (const a d : ConstExpr N A D).schema sch = some {a} := by
  rfl

/-- The constant query `{⟨a : d⟩}` evaluates to the singleton `{⟨a : d⟩}`. The attribute
type is finite, and attribute and value equality are decidable. -/
@[simp] theorem eval_const [DecidableEq D] [Fintype A] [DecidableEq A]
    (db : N → Finset (Tuple A D)) (a : A) (d : D) :
    (const a d : ConstExpr N A D).eval db = {single a d} := by
  rfl

/-- An original query keeps its schema when read as a query with constants. Attribute
equality is decidable. -/
@[simp] theorem schema_ofExpr [DecidableEq A] (sch : N → Finset A) (e : Expr N A D) :
    (ofExpr e).schema sch = e.schema sch := by
  have h : (extSchema (D := D) sch) ∘ Sum.inl = sch := funext fun _ => rfl
  simp [schema, ofExpr, Expr.schema_mapRel, h]

/-- An original query keeps its value when read as a query with constants. The attribute
type is finite, and attribute and value equality are decidable. -/
@[simp] theorem eval_ofExpr [DecidableEq D] [Fintype A] [DecidableEq A]
    (db : N → Finset (Tuple A D)) (e : Expr N A D) :
    (ofExpr e).eval db = e.eval db := by
  have h : (extDb db) ∘ Sum.inl = db := funext fun _ => rfl
  simp [eval, ofExpr, Expr.eval_mapRel, h]

/-- The only constant value occurring in `{⟨a : d⟩}` is `d`. Value equality is decidable. -/
@[simp] theorem consts_const [DecidableEq D] (a : A) (d : D) :
    (const a d : ConstExpr N A D).consts = {d} := by
  rfl

/-- Embedding an `Expr` introduces no singleton relation constants; literals in selection
conditions are preserved (and are not counted by `consts`). Value equality is decidable. -/
@[simp] theorem consts_ofExpr [DecidableEq D] (e : Expr N A D) : (ofExpr e).consts = ∅ := by
  induction e with
  | rel n => rfl
  | select c e ih => simp only [ofExpr] at ih ⊢; simp [Expr.mapRel, consts, ih]
  | project T e ih => simp only [ofExpr] at ih ⊢; simp [Expr.mapRel, consts, ih]
  | join e e' ih ih' => simp only [ofExpr] at ih ih' ⊢; simp [Expr.mapRel, consts, ih, ih']
  | union e e' ih ih' => simp only [ofExpr] at ih ih' ⊢; simp [Expr.mapRel, consts, ih, ih']
  | diff e e' ih ih' => simp only [ofExpr] at ih ih' ⊢; simp [Expr.mapRel, consts, ih, ih']
  | rename f e ih => simp only [ofExpr] at ih ⊢; simp [Expr.mapRel, consts, ih]

/-- A conforming database stays conforming on the extended schema and database: each
constant name holds its singleton over its schema. Attribute equality is decidable. -/
theorem conforms_extDb [DecidableEq A] {sch : N → Finset A}
    {db : N → Finset (Tuple A D)} (hdb : Expr.Conforms sch db) :
    Expr.Conforms (extSchema sch) (extDb db) := by
  intro n
  cases n with
  | inl n => exact hdb n
  | inr p =>
      obtain ⟨a, d⟩ := p
      intro t ht
      have ht' : t ∈ ({single a d} : Finset (Tuple A D)) := ht
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact single_isOver a d

/-- **Typing is sound** for queries with constants: on a database conforming to `sch`, a
well-formed query with inferred schema `S` evaluates to a relation over `S`. The attribute
type is finite, and attribute and value equality are decidable. -/
theorem eval_isOver [DecidableEq D] [Fintype A] [DecidableEq A] {sch : N → Finset A}
    {db : N → Finset (Tuple A D)} (hdb : Expr.Conforms sch db) {e : ConstExpr N A D} {S : Finset A}
    (h : e.schema sch = some S) : IsOver S (e.eval db) := by
  exact Expr.eval_isOver (conforms_extDb hdb) e h

/-- An equivalence of the underlying queries over the extended schema is an equivalence of the
queries with constants. The attribute type is finite, and attribute and value equality are
decidable. -/
theorem Equiv.of_expr [DecidableEq D] [Fintype A] [DecidableEq A] {sch : N → Finset A}
    {e e' : ConstExpr N A D} (h : Expr.Equiv (extSchema sch) e e') : Equiv sch e e' := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, fun db hdb => h3 (extDb db) (conforms_extDb hdb)⟩

/-- **Conservativity**: on original queries the two equivalences coincide. The attribute
type is finite, and attribute and value equality are decidable. -/
theorem equiv_ofExpr_iff [DecidableEq D] [Fintype A] [DecidableEq A] {sch : N → Finset A}
    {e e' : Expr N A D} :
    Equiv sch (ofExpr e) (ofExpr e') ↔ Expr.Equiv sch e e' := by
  simp only [Equiv, Expr.Equiv, schema_ofExpr, eval_ofExpr]

section Laws

variable [DecidableEq D] [Fintype A] [DecidableEq A] {sch : N → Finset A}

/-- **Joins commute as a query rewrite.** Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. The attribute type is finite, and
attribute and value equality are decidable. Let $e$ and $e'$ be well-formed queries with
constants, with schemas $S$ and $S'$. Then the query $e \bowtie e'$ is equivalent to the query
$e' \bowtie e$: both are well-formed with the same schema, and they have equal values on every
database conforming to $\mathrm{sch}$. The lift of `Expr.join_comm` to queries with constants. -/
theorem join_comm {e e' : ConstExpr N A D} {S S' : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S') : Equiv sch (Expr.join e e') (Expr.join e' e) := by
  exact Equiv.of_expr (Expr.join_comm he he')

/-- **Joins associate as a query rewrite.** Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. The attribute type is finite, and
attribute and value equality are decidable. Let $e$, $e'$ and $e''$ be well-formed queries
with constants, with schemas $S$, $S'$ and $S''$. Then the query $(e \bowtie e') \bowtie e''$
is equivalent to the query $e \bowtie (e' \bowtie e'')$: both are well-formed with the same
schema, and they have equal values on every database conforming to $\mathrm{sch}$. The lift of
`Expr.join_assoc` to queries with constants. -/
theorem join_assoc {e e' e'' : ConstExpr N A D} {S S' S'' : Finset A}
    (he : e.schema sch = some S) (he' : e'.schema sch = some S')
    (he'' : e''.schema sch = some S'') :
    Equiv sch (Expr.join (Expr.join e e') e'') (Expr.join e (Expr.join e' e'')) := by
  exact Equiv.of_expr (Expr.join_assoc he he' he'')

/-- **Selection pushdown as a query rewrite.** Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. The attribute type is finite, and
attribute and value equality are decidable. Let $e$ and $e'$ be well-formed queries with
constants, with schemas $S$ and $S'$, and let $c$ be a selection condition all of whose
attributes lie in $S$. Then the query $\sigma_c(e \bowtie e')$, the selection by $c$ of the
natural join of $e$ and $e'$, is equivalent to the query $\sigma_c(e) \bowtie e'$: both are
well-formed with the same schema, and they have equal values on every database conforming to
$\mathrm{sch}$. The lift of `Expr.select_join` to queries with constants. -/
theorem select_join {e e' : ConstExpr N A D} {S S' : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S') (c : Cond A D) (hc : c.attrs ⊆ S) :
    Equiv sch (Expr.select c (Expr.join e e')) (Expr.join (Expr.select c e) e') := by
  exact Equiv.of_expr (Expr.select_join he he' c hc)

/-- **Cascade of selections as a query rewrite.** Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. The attribute type is finite,
and attribute and value equality are decidable. Let $e$ be a well-formed query with constants
and schema $S$, and let $c$ and $c'$ be selection conditions all of whose attributes lie in
$S$. Then the query $\sigma_c(\sigma_{c'}(e))$, the selection by $c$ of the selection of $e$
by $c'$, is equivalent to the query $\sigma_{c' \land c}(e)$, the selection of $e$ by the
conjunction $c' \land c$: both are well-formed with the same schema, and they have equal
values on every database conforming to $\mathrm{sch}$. The lift of `Expr.select_select` to
queries with constants. -/
theorem select_select {e : ConstExpr N A D} {S : Finset A} (he : e.schema sch = some S)
    {c c' : Cond A D} (hc : c.attrs ⊆ S) (hc' : c'.attrs ⊆ S) :
    Equiv sch (Expr.select c (Expr.select c' e)) (Expr.select (.and c' c) e) := by
  exact Equiv.of_expr (Expr.select_select he hc hc')

/-- **Cascade of projections as a query rewrite.** Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. The attribute type is finite,
and attribute and value equality are decidable. Let $e$ be a well-formed query with constants
and schema $S$, and let $T \subseteq T' \subseteq S$ be finite sets of attributes. Then the
query $\pi_T(\pi_{T'}(e))$, the projection onto $T$ of the projection of $e$ onto $T'$, is
equivalent to the query $\pi_T(e)$, the projection of $e$ onto $T$: both are well-formed with
the same schema, and they have equal values on every database conforming to $\mathrm{sch}$. The
lift of `Expr.project_project` to queries with constants. -/
theorem project_project {e : ConstExpr N A D} {S T T' : Finset A} (he : e.schema sch = some S)
    (hT' : T' ⊆ S) (hT : T ⊆ T') :
    Equiv sch (Expr.project T (Expr.project T' e)) (Expr.project T e) := by
  exact Equiv.of_expr (Expr.project_project he hT' hT)

/-- **Selections commute as a query rewrite.** Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. The attribute type is finite, and
attribute and value equality are decidable. Let $e$ be a well-formed query with constants and
schema $S$, and let $c$ and $c'$ be selection conditions all of whose attributes lie in $S$.
Then the query $\sigma_c(\sigma_{c'}(e))$ is equivalent to the query
$\sigma_{c'}(\sigma_c(e))$: both are well-formed with the same schema, and they have equal
values on every database conforming to $\mathrm{sch}$. The lift of `Expr.select_comm` to
queries with constants. -/
theorem select_comm {e : ConstExpr N A D} {S : Finset A} (he : e.schema sch = some S)
    {c c' : Cond A D} (hc : c.attrs ⊆ S) (hc' : c'.attrs ⊆ S) :
    Equiv sch (Expr.select c (Expr.select c' e)) (Expr.select c' (Expr.select c e)) := by
  exact Equiv.of_expr (Expr.select_comm he hc hc')

/-- **Selection distributes over union as a query rewrite.** Fix a database schema
$\mathrm{sch}$ assigning a finite set of attributes to each base relation name. The attribute
type is finite, and attribute and value equality are decidable. Let $e$ and $e'$ be
well-formed queries with constants and the same schema $S$, and let $c$ be a selection
condition all of whose attributes lie in $S$. Then the query $\sigma_c(e \cup e')$ is
equivalent to the query $\sigma_c(e) \cup \sigma_c(e')$: both are well-formed with the same
schema, and they have equal values on every database conforming to $\mathrm{sch}$. The lift of
`Expr.select_union` to queries with constants. -/
theorem select_union {e e' : ConstExpr N A D} {S : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) {c : Cond A D} (hc : c.attrs ⊆ S) :
    Equiv sch (Expr.select c (Expr.union e e'))
      (Expr.union (Expr.select c e) (Expr.select c e')) := by
  exact Equiv.of_expr (Expr.select_union he he' hc)

/-- **Selection distributes over difference as a query rewrite.** Fix a database schema
$\mathrm{sch}$ assigning a finite set of attributes to each base relation name. The attribute
type is finite, and attribute and value equality are decidable. Let $e$ and $e'$ be
well-formed queries with constants and the same schema $S$, and let $c$ be a selection
condition all of whose attributes lie in $S$. Then the query $\sigma_c(e \setminus e')$ is
equivalent to the query $\sigma_c(e) \setminus \sigma_c(e')$: both are well-formed with the
same schema, and they have equal values on every database conforming to $\mathrm{sch}$. The
lift of `Expr.select_diff` to queries with constants. -/
theorem select_diff {e e' : ConstExpr N A D} {S : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) {c : Cond A D} (hc : c.attrs ⊆ S) :
    Equiv sch (Expr.select c (Expr.diff e e'))
      (Expr.diff (Expr.select c e) (Expr.select c e')) := by
  exact Equiv.of_expr (Expr.select_diff he he' hc)

/-- **Projection distributes over union as a query rewrite.** Fix a database schema
$\mathrm{sch}$ assigning a finite set of attributes to each base relation name. The attribute
type is finite, and attribute and value equality are decidable. Let $e$ and $e'$ be
well-formed queries with constants and the same schema $S$, and let $T \subseteq S$. Then the
query $\pi_T(e \cup e')$ is equivalent to the query $\pi_T(e) \cup \pi_T(e')$: both are
well-formed with the same schema, and they have equal values on every database conforming to
$\mathrm{sch}$. The lift of `Expr.project_union` to queries with constants. -/
theorem project_union {e e' : ConstExpr N A D} {S T : Finset A} (he : e.schema sch = some S)
    (he' : e'.schema sch = some S) (hT : T ⊆ S) :
    Equiv sch (Expr.project T (Expr.union e e'))
      (Expr.union (Expr.project T e) (Expr.project T e')) := by
  exact Equiv.of_expr (Expr.project_union he he' hT)

/-- **Selection commutes with projection as a query rewrite.** Fix a database schema
$\mathrm{sch}$ assigning a finite set of attributes to each base relation name. The attribute
type is finite, and attribute and value equality are decidable. Let $e$ be a well-formed query
with constants and schema $S$, let $T \subseteq S$, and let $c$ be a selection condition all
of whose attributes lie in $T$, so the projection keeps them. Then the query
$\sigma_c(\pi_T(e))$ is equivalent to the query $\pi_T(\sigma_c(e))$: both are well-formed
with the same schema, and they have equal values on every database conforming to
$\mathrm{sch}$. The lift of `Expr.select_project` to queries with constants. -/
theorem select_project {e : ConstExpr N A D} {S T : Finset A} (he : e.schema sch = some S)
    (hT : T ⊆ S) {c : Cond A D} (hc : c.attrs ⊆ T) :
    Equiv sch (Expr.select c (Expr.project T e)) (Expr.project T (Expr.select c e)) := by
  exact Equiv.of_expr (Expr.select_project he hT hc)

/-- **Selection pushdown into the right operand of a join, as a query rewrite.** Fix a
database schema $\mathrm{sch}$ assigning a finite set of attributes to each base relation name.
The attribute type is finite, and attribute and value equality are decidable. Let $e$ and $e'$
be well-formed queries with constants and schemas $S$ and $S'$, and let $c$ be a selection
condition all of whose attributes lie in $S'$. Then the query $\sigma_c(e \bowtie e')$, the
selection by $c$ of the natural join of $e$ and $e'$, is equivalent to the query $e \bowtie
\sigma_c(e')$: both are well-formed with the same schema, and they have equal values on every
database conforming to $\mathrm{sch}$. The lift of `Expr.select_join_right` to queries with
constants. -/
theorem select_join_right {e e' : ConstExpr N A D} {S S' : Finset A}
    (he : e.schema sch = some S) (he' : e'.schema sch = some S') (c : Cond A D)
    (hc : c.attrs ⊆ S') :
    Equiv sch (Expr.select c (Expr.join e e')) (Expr.join e (Expr.select c e')) := by
  exact Equiv.of_expr (Expr.select_join_right he he' c hc)

end Laws

/-- **Constants are the only new values**: `adom(q(db)) ⊆ adom(db) ∪ consts(q)`, for every
database `db`, conforming or not. Both the relation-name type and the attribute type are
finite, and attribute and value equality are decidable. The source's bound also allows the
constants of the query; here they contribute exactly `consts(q)`, the values of the constant
singletons occurring in the query.

Source: S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
Section 4.2, p. 41, where adom(q(I)) ⊆ adom(q) ∪ adom(I) is stated for rule-based conjunctive
queries. -/
theorem adom_eval_subset [Fintype N] [Fintype A] [DecidableEq A] [DecidableEq D]
    (db : N → Finset (Tuple A D)) (e : ConstExpr N A D) :
    adom (e.eval db) ⊆ adomDB db ∪ e.consts := by
  induction e using induction_on with
  | hrel n =>
      change adom (db n) ⊆ adomDB db ∪ (∅ : Finset D)
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      exact Finset.mem_union.mpr (Or.inl (mem_adomDB.mpr ⟨n, t, ht, a, ha⟩))
  | hconst a d =>
      change adom ({single a d} : Finset (Tuple A D)) ⊆ adomDB db ∪ ({d} : Finset D)
      intro x hx
      obtain ⟨t, ht, b, hb⟩ := Databases.mem_adom.mp hx
      rw [Finset.mem_singleton] at ht
      subst ht
      simp only [single] at hb
      by_cases hba : b = a
      · subst b
        have hx : x = d := by simpa using hb.symm
        rw [hx]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self d))
      · simp [hba] at hb
  | hselect c e ih =>
      change adom (Databases.select c (e.eval db)) ⊆ adomDB db ∪ e.consts
      have hsub : adom (Databases.select c (e.eval db)) ⊆ adom (e.eval db) := by
        unfold adom
        exact Finset.biUnion_subset_biUnion_of_subset_left (Finset.filter_subset _ _)
      exact hsub.trans ih
  | hproject T e ih =>
      change adom (Databases.project T (e.eval db)) ⊆ adomDB db ∪ e.consts
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hua : u a = some d := by
        rw [Tuple.restrict_apply] at ha
        split_ifs at ha with hT
        exact ha
      exact ih (Databases.mem_adom.mpr ⟨u, hu, a, hua⟩)
  | hjoin e e' ih ih' =>
      change adom (Databases.join (e.eval db) (e'.eval db)) ⊆ adomDB db ∪ (e.consts ∪ e'.consts)
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, v, hv, -, rfl⟩ := Databases.mem_join.mp ht
      simp only [Tuple.merge] at ha
      cases hua : u a with
      | none =>
          rw [hua] at ha
          have h2 : v a = some d := ha
          have hmem := ih' (Databases.mem_adom.mpr ⟨v, hv, a, h2⟩)
          rw [Finset.mem_union] at hmem
          refine Finset.mem_union.mpr ?_
          rcases hmem with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_union.mpr (Or.inr h))
      | some x =>
          rw [hua] at ha
          have h2 : some x = some d := ha
          simp only [Option.some.injEq] at h2
          have hua' : u a = some d := hua.trans (congrArg some h2)
          have hmem := ih (Databases.mem_adom.mpr ⟨u, hu, a, hua'⟩)
          rw [Finset.mem_union] at hmem
          refine Finset.mem_union.mpr ?_
          rcases hmem with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_union.mpr (Or.inl h))
  | hunion e e' ih ih' =>
      change adom (e.eval db ∪ e'.eval db) ⊆ adomDB db ∪ (e.consts ∪ e'.consts)
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      rcases Finset.mem_union.mp ht with h | h
      · have hmem := ih (Databases.mem_adom.mpr ⟨t, h, a, ha⟩)
        rw [Finset.mem_union] at hmem
        refine Finset.mem_union.mpr ?_
        rcases hmem with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Finset.mem_union.mpr (Or.inl h'))
      · have hmem := ih' (Databases.mem_adom.mpr ⟨t, h, a, ha⟩)
        rw [Finset.mem_union] at hmem
        refine Finset.mem_union.mpr ?_
        rcases hmem with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Finset.mem_union.mpr (Or.inr h'))
  | hdiff e e' ih _ =>
      change adom (e.eval db \ e'.eval db) ⊆ adomDB db ∪ (e.consts ∪ e'.consts)
      have hsub : adom (e.eval db \ e'.eval db) ⊆ adom (e.eval db) := by
        unfold adom
        exact Finset.biUnion_subset_biUnion_of_subset_left Finset.sdiff_subset
      intro d hd
      have hmem := ih (hsub hd)
      rw [Finset.mem_union] at hmem
      refine Finset.mem_union.mpr ?_
      rcases hmem with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_union.mpr (Or.inl h))
  | hrename f e ih =>
      change adom (Databases.rename f (e.eval db)) ⊆ adomDB db ∪ e.consts
      intro d hd
      obtain ⟨t, ht, a, ha⟩ := Databases.mem_adom.mp hd
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      simp only [Function.comp_apply] at ha
      exact ih (Databases.mem_adom.mpr ⟨u, hu, f.symm a, ha⟩)

end ConstExpr

end Cslib.Databases
