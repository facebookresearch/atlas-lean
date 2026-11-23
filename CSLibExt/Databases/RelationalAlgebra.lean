/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image

/-!
# Relational algebra

The named relational model (Codd). Attributes range over a finite type `A` and values over `D`.
A **tuple** is a partial assignment `A → Option D`; a tuple over the schema `S : Finset A` is
defined exactly on `S` (`Tuple.IsOver`). A **relation** over `S` is a finite set of tuples over
`S` (`IsOver`).

The operators of the relational algebra:
* `select c r` (`σ_c`), for a selection condition `c : Cond A D` built from `a = const`,
  `a = b`, negation and conjunction;
* `project T r` (`π_T`);
* `join r s` (the natural join `⋈`): all merges of a tuple of `r` and a tuple of `s` that agree on
  their common attributes;
* `r ∪ s` and `r \ s` (union and difference, as `Finset` operations);
* `rename f r` (`ρ`), renaming attributes along a permutation `f` of the attributes.

`isOver_select`, `isOver_project`, `isOver_join`, `isOver_union`, `isOver_sdiff` and
`isOver_rename` give the schema of each result, and `mem_join_iff` characterizes the join:
a tuple over `S ∪ S'` is in `r ⋈ s` exactly when its restrictions to `S` and `S'` are in `r` and
`s`.

The standard algebraic equivalences used by query optimizers:
* `join_comm`, `join_assoc`: the natural join is commutative and associative;
* `select_join_left`, `select_join_right` (**selection pushdown**): a selection whose condition
  only mentions attributes of one operand can be evaluated on that operand before the join;
* `select_select` (**cascade of selections**) and `select_comm`;
* `project_project`, `project_project_of_subset` (**cascade of projections**);
* `select_project`: selection commutes with a projection that keeps its attributes;
* `select_union`, `select_sdiff`, `project_union`;
* `join_eq_inter`: on a common schema the join is the intersection.

`Expr` is the syntax of relational algebra queries over named base relations, with its
evaluation `Expr.eval` on a database and its schema inference `Expr.schema`; `Expr.eval_isOver`
says a query that type-checks evaluates to a relation over the inferred schema on every database
conforming to the database schema. `Expr.Equiv` is query equivalence: both queries are
well-formed with the same schema and agree on every conforming database. Join commutativity and
associativity, selection pushdown, and the cascades of selections and of projections are restated
as query rewrites, under the well-formedness hypotheses that make both sides type-check.

## References

* E. F. Codd, *A relational model of data for large shared data banks*, Communications of the
  ACM 13(6), 1970.
* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995:
  Section 3.2 (the named perspective), Sections 4.4, 4.5 and 5.1 (the relational algebra) and
  Section 6.1 (algebraic rewriting in query optimization).
-/

@[expose] public section

namespace Cslib.Databases

variable {A D : Type*}

/-- **Tuple.** For a type $A$ of attributes and a type $D$ of values, a tuple is a partial
assignment of values to attributes: a function that assigns to each attribute $a \in A$ either a
value in $D$ or no value, in which case the tuple is undefined at $a$. -/
abbrev Tuple (A D : Type*) := A → Option D

namespace Tuple

/-- **Tuple over a schema.** A tuple $t$ is over the schema $S$, a finite set of attributes, when
$t$ is defined exactly on the attributes of $S$: for every attribute $a$, the value $t(a)$ is
defined if and only if $a \in S$. -/
def IsOver (S : Finset A) (t : Tuple A D) : Prop := ∀ a, (t a).isSome ↔ a ∈ S

/-- **Compatible tuples.** Two tuples $t$ and $u$ are compatible (joinable) when they agree on
every attribute where both are defined: for every attribute $a$, either $t$ is undefined at $a$,
or $u$ is undefined at $a$, or $t(a) = u(a)$. -/
def Compatible (t u : Tuple A D) : Prop := ∀ a, t a = none ∨ u a = none ∨ t a = u a

/-- **Merge of two tuples.** The merge of tuples $t$ and $u$ is the tuple whose value at each
attribute $a$ is $t(a)$ if $t$ is defined at $a$, and $u(a)$ otherwise; it is undefined at $a$
when neither $t$ nor $u$ is. -/
def merge (t u : Tuple A D) : Tuple A D := fun a => (t a).or (u a)

instance [Fintype A] [DecidableEq D] (t u : Tuple A D) : Decidable (Compatible t u) := by
  unfold Compatible
  infer_instance

theorem IsOver.eq_none {S : Finset A} {t : Tuple A D} (ht : t.IsOver S) {a : A} (h : a ∉ S) :
    t a = none := by
  simpa [Option.not_isSome_iff_eq_none] using mt (ht a).1 h

theorem Compatible.symm {t u : Tuple A D} (h : Compatible t u) : Compatible u t := fun a => by
  rcases h a with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h.symm)

theorem compatible_comm {t u : Tuple A D} : Compatible t u ↔ Compatible u t :=
  ⟨Compatible.symm, Compatible.symm⟩

theorem compatible_self (t : Tuple A D) : Compatible t t := fun _ => Or.inr (Or.inr rfl)

theorem merge_comm {t u : Tuple A D} (h : Compatible t u) : merge t u = merge u t := by
  funext a
  rcases h a with h | h | h <;> simp [merge, h]

theorem merge_assoc (t u v : Tuple A D) : merge (merge t u) v = merge t (merge u v) := by
  funext a
  simp only [merge]
  cases t a <;> rfl

theorem merge_self (t : Tuple A D) : merge t t = t := by
  funext a
  simp only [merge]
  cases t a <;> rfl

private theorem compat_or (o₁ o₂ o₃ : Option D) :
    ((o₁ = none ∨ o₂ = none ∨ o₁ = o₂) ∧
      ((o₁.or o₂) = none ∨ o₃ = none ∨ o₁.or o₂ = o₃)) ↔
      ((o₁ = none ∨ o₂ = none ∨ o₁ = o₂) ∧ (o₁ = none ∨ o₃ = none ∨ o₁ = o₃) ∧
        (o₂ = none ∨ o₃ = none ∨ o₂ = o₃)) := by
  rcases o₁ with _ | x <;> rcases o₂ with _ | y <;> rcases o₃ with _ | z <;> aesop

/-- **Compatibility with a merge, grouped from the left.** For tuples $t$, $u$, $v$: $t$ and $u$
are compatible and the merge of $t$ and $u$ is compatible with $v$ if and only if $t$, $u$, $v$
are pairwise compatible, that is, $t$ and $u$, $t$ and $v$, and $u$ and $v$ are compatible. -/
theorem compatible_merge_left {t u v : Tuple A D} :
    Compatible t u ∧ Compatible (merge t u) v ↔
      Compatible t u ∧ Compatible t v ∧ Compatible u v := by
  simp only [Compatible, merge, ← forall_and]
  exact forall_congr' fun a => compat_or (t a) (u a) (v a)

/-- **Compatibility with a merge, grouped from the right.** For tuples $t$, $u$, $v$: $u$ and $v$
are compatible and $t$ is compatible with the merge of $u$ and $v$ if and only if $t$, $u$, $v$
are pairwise compatible, that is, $t$ and $u$, $t$ and $v$, and $u$ and $v$ are compatible. -/
theorem compatible_merge_right {t u v : Tuple A D} :
    Compatible u v ∧ Compatible t (merge u v) ↔
      Compatible t u ∧ Compatible t v ∧ Compatible u v := by
  constructor
  · rintro ⟨huv, h⟩
    rw [merge_comm huv, compatible_comm] at h
    have := (compatible_merge_left (t := v) (u := u) (v := t)).1 ⟨huv.symm, h⟩
    exact ⟨this.2.2.symm, this.2.1.symm, huv⟩
  · rintro ⟨htu, htv, huv⟩
    refine ⟨huv, ?_⟩
    rw [merge_comm huv, compatible_comm]
    exact ((compatible_merge_left (t := v) (u := u) (v := t)).2
      ⟨huv.symm, htv.symm, htu.symm⟩).2

theorem isOver_merge {S S' : Finset A} [DecidableEq A] {t u : Tuple A D} (ht : t.IsOver S)
    (hu : u.IsOver S') : (merge t u).IsOver (S ∪ S') := fun a => by
  rw [Finset.mem_union, ← ht a, ← hu a]
  simp only [merge]
  cases t a <;> cases u a <;> simp

theorem IsOver.eq_of_compatible {S : Finset A} {t u : Tuple A D} (ht : t.IsOver S)
    (hu : u.IsOver S) (h : Compatible t u) : t = u := by
  funext a
  rcases h a with h' | h' | h'
  · have : a ∉ S := fun ha => by simpa [h'] using (ht a).2 ha
    rw [h', hu.eq_none this]
  · have : a ∉ S := fun ha => by simpa [h'] using (hu a).2 ha
    rw [h', ht.eq_none this]
  · exact h'

variable [DecidableEq A]

/-- **Restriction of a tuple.** For a finite set $T$ of attributes and a tuple $t$, the
restriction $t|_T$ is the tuple that agrees with $t$ on every attribute in $T$ and is undefined
on every attribute outside $T$. -/
def restrict (T : Finset A) (t : Tuple A D) : Tuple A D := fun a => if a ∈ T then t a else none

@[simp] theorem restrict_apply (T : Finset A) (t : Tuple A D) (a : A) :
    t.restrict T a = if a ∈ T then t a else none := rfl

theorem restrict_restrict (T T' : Finset A) (t : Tuple A D) :
    (t.restrict T').restrict T = t.restrict (T ∩ T') := by
  funext a
  by_cases h : a ∈ T <;> by_cases h' : a ∈ T' <;> simp [h, h']

theorem IsOver.restrict_self {S : Finset A} {t : Tuple A D} (ht : t.IsOver S) :
    t.restrict S = t := by
  funext a
  by_cases h : a ∈ S
  · simp [h]
  · simp [h, ht.eq_none h]

theorem IsOver.restrict {S T : Finset A} {t : Tuple A D} (ht : t.IsOver S) (hT : T ⊆ S) :
    (t.restrict T).IsOver T := fun a => by
  by_cases h : a ∈ T
  · simpa [h] using (ht a).2 (hT h)
  · simp [h]

theorem restrict_merge_left {S : Finset A} {t u : Tuple A D} (ht : t.IsOver S) :
    (merge t u).restrict S = t := by
  funext a
  by_cases h : a ∈ S
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((ht a).2 h)
    simp [h, merge, hx]
  · simp [h, ht.eq_none h]

theorem restrict_merge_right {S' : Finset A} {t u : Tuple A D} (hu : u.IsOver S')
    (h : Compatible t u) : (merge t u).restrict S' = u := by
  rw [merge_comm h]
  exact restrict_merge_left hu

end Tuple

open Tuple

/-! ### Selection conditions -/

/-- **Selection conditions.** The selection conditions over attributes $A$ and values $D$ are
generated by: the condition that always holds; the equality $a = c$ of an attribute $a$ with a
constant $c \in D$; the equality $a = b$ of two attributes $a$ and $b$; the negation of a
condition; and the conjunction of two conditions. -/
inductive Cond (A D : Type*)
  /-- The condition that always holds. -/
  | tt
  /-- `a = c` for an attribute `a` and a constant `c`. -/
  | eqConst (a : A) (c : D)
  /-- `a = b` for attributes `a` and `b`. -/
  | eqAttr (a b : A)
  /-- Negation. -/
  | not (c : Cond A D)
  /-- Conjunction. -/
  | and (c c' : Cond A D)

namespace Cond

/-- **Truth value of a selection condition.** The truth value of a selection condition on a
tuple $t$ is defined by recursion: the always-true condition holds; $a = c$ holds when $t$ is
defined at $a$ with value $c$; $a = b$ holds when $t(a) = t(b)$ as possibly undefined values,
so it also holds when $t$ is undefined at both $a$ and $b$; a negation holds when the negated
condition fails; and a conjunction holds when both conditions hold. -/
def eval [DecidableEq D] : Cond A D → Tuple A D → Bool
  | tt, _ => true
  | eqConst a c, t => t a == some c
  | eqAttr a b, t => t a == t b
  | not c, t => !c.eval t
  | and c c', t => c.eval t && c'.eval t

/-- **Attributes of a selection condition.** The set of attributes mentioned by a selection
condition, defined by recursion: it is empty for the always-true condition; for the comparison
$a = d$ of an attribute $a$ with a constant $d$ it is $\{a\}$; for the comparison $a = b$ of
attributes $a$ and $b$ it is $\{a, b\}$; for the negation $\neg \varphi$ of a condition $\varphi$
it is the set of attributes of $\varphi$; and for the conjunction $\varphi \land \psi$ of
conditions $\varphi$ and $\psi$ it is the union of the attributes of $\varphi$ and of $\psi$. -/
def attrs [DecidableEq A] : Cond A D → Finset A
  | tt => ∅
  | eqConst a _ => {a}
  | eqAttr a b => {a, b}
  | not c => c.attrs
  | and c c' => c.attrs ∪ c'.attrs

/-- **Selection conditions depend only on their attributes.** Let $c$ be a selection condition,
$t$ a tuple and $T$ a finite set of attributes containing every attribute of $c$. Then $c$ has
the same truth value on the restriction of $t$ to $T$ as on $t$. -/
theorem eval_restrict [DecidableEq A] [DecidableEq D] {T : Finset A} (t : Tuple A D) :
    ∀ c : Cond A D, c.attrs ⊆ T → c.eval (t.restrict T) = c.eval t
  | tt, _ => rfl
  | eqConst a _, h => by
    have : a ∈ T := h (by simp [attrs])
    simp [eval, this]
  | eqAttr a b, h => by
    have ha : a ∈ T := h (by simp [attrs])
    have hb : b ∈ T := h (by simp [attrs])
    simp [eval, ha, hb]
  | not c, h => by simp [eval, eval_restrict t c h]
  | and c c', h => by
    simp only [attrs, Finset.union_subset_iff] at h
    simp [eval, eval_restrict t c h.1, eval_restrict t c' h.2]

end Cond

/-! ### The operators -/

variable [DecidableEq D]

/-- **Relation over a schema.** A finite set $r$ of tuples is a relation over the schema $S$, a
finite set of attributes, when every tuple $t \in r$ is over $S$, that is, $t$ is defined exactly
on the attributes of $S$. -/
def IsOver (S : Finset A) (r : Finset (Tuple A D)) : Prop := ∀ t ∈ r, t.IsOver S

/-- **Selection.** For a selection condition $c$ and a finite set $r$ of tuples, the selection
$\sigma_c(r)$ is the set of tuples $t \in r$ on which $c$ evaluates to true. -/
def select (c : Cond A D) (r : Finset (Tuple A D)) : Finset (Tuple A D) :=
  r.filter fun t => c.eval t = true

theorem isOver_select {S : Finset A} {r : Finset (Tuple A D)} (c : Cond A D) (hr : IsOver S r) :
    IsOver S (select c r) := fun t ht => hr t (Finset.mem_filter.mp ht).1

/-- **Cascade of selections.** Write $\sigma_c$ for selection by a selection condition $c$. For
selection conditions $c$ and $c'$ and a finite set $r$ of tuples,
$\sigma_c(\sigma_{c'}(r)) = \sigma_{c' \land c}(r)$: selecting by $c'$ and then by $c$ is the same
as selecting once by the conjunction $c' \land c$. -/
theorem select_select (c c' : Cond A D) (r : Finset (Tuple A D)) :
    select c (select c' r) = select (.and c' c) r := by
  ext t
  simp only [select, Finset.mem_filter, Cond.eval, Bool.and_eq_true]
  tauto

/-- **Selections commute.** For all selection conditions $c$ and $c'$ and every finite set $r$ of
tuples, selecting by $c'$ and then by $c$ gives the same result as selecting by $c$ and then by
$c'$: $\sigma_c(\sigma_{c'}(r)) = \sigma_{c'}(\sigma_c(r))$. -/
theorem select_comm (c c' : Cond A D) (r : Finset (Tuple A D)) :
    select c (select c' r) = select c' (select c r) := by
  ext t
  simp [select, and_comm, and_left_comm]

variable [Fintype A]

/-- **Natural join.** The natural join $r \bowtie s$ of finite sets of tuples $r$ and $s$ is the
set of merges of $t$ and $u$ over all pairs of tuples $t \in r$ and $u \in s$ that are
compatible, that is, agree on every attribute where both are defined. The merge of $t$ and $u$
takes the value of $t$ where $t$ is defined and the value of $u$ otherwise. -/
def join (r s : Finset (Tuple A D)) : Finset (Tuple A D) :=
  ((r ×ˢ s).filter fun p => Compatible p.1 p.2).image fun p => merge p.1 p.2

/-- **Renaming of attributes.** For a permutation $f$ of the attributes and a finite set $r$ of
tuples, the renaming $\rho_f(r)$ is the finite set of the tuples $t \circ f^{-1}$ for $t \in r$:
each tuple keeps its values, and its value at an attribute $a$ moves to the attribute $f(a)$. -/
def rename (f : A ≃ A) (r : Finset (Tuple A D)) : Finset (Tuple A D) :=
  r.image fun t => t ∘ f.symm

theorem mem_join {r s : Finset (Tuple A D)} {t : Tuple A D} :
    t ∈ join r s ↔ ∃ u ∈ r, ∃ v ∈ s, Compatible u v ∧ merge u v = t := by
  simp [join, and_assoc]

theorem isOver_union {S : Finset A} {r s : Finset (Tuple A D)} (hr : IsOver S r)
    (hs : IsOver S s) : IsOver S (r ∪ s) := by
  intro t ht
  rcases Finset.mem_union.mp ht with h | h
  exacts [hr t h, hs t h]

theorem isOver_sdiff {S : Finset A} {r : Finset (Tuple A D)} (s : Finset (Tuple A D))
    (hr : IsOver S r) : IsOver S (r \ s) := fun t ht => hr t (Finset.mem_sdiff.mp ht).1

theorem isOver_rename {S : Finset A} {r : Finset (Tuple A D)} (f : A ≃ A) (hr : IsOver S r) :
    IsOver (S.map f.toEmbedding) (rename f r) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  intro a
  simp [Finset.mem_map_equiv, hr u hu (f.symm a)]

/-- **Commutativity of the natural join.** For all finite sets $r$ and $s$ of tuples,
$r \bowtie s = s \bowtie r$, where $\bowtie$ is the natural join. -/
theorem join_comm (r s : Finset (Tuple A D)) : join r s = join s r := by
  ext t
  simp only [mem_join]
  constructor <;> rintro ⟨u, hu, v, hv, hc, rfl⟩ <;>
    exact ⟨v, hv, u, hu, hc.symm, (merge_comm hc).symm⟩

/-- **Associativity of the natural join.** For all finite sets $r$, $s$ and $w$ of tuples,
$(r \bowtie s) \bowtie w = r \bowtie (s \bowtie w)$, where $\bowtie$ is the natural join. -/
theorem join_assoc (r s w : Finset (Tuple A D)) :
    join (join r s) w = join r (join s w) := by
  ext t
  simp only [mem_join]
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, huv, rfl⟩, x, hx, hc, rfl⟩
    obtain ⟨-, hux, hvx⟩ := compatible_merge_left.1 ⟨huv, hc⟩
    exact ⟨u, hu, merge v x, ⟨v, hv, x, hx, hvx, rfl⟩,
      (compatible_merge_right.2 ⟨huv, hux, hvx⟩).2, (merge_assoc u v x).symm⟩
  · rintro ⟨u, hu, _, ⟨v, hv, x, hx, hvx, rfl⟩, hc, rfl⟩
    obtain ⟨huv, hux, -⟩ := compatible_merge_right.1 ⟨hvx, hc⟩
    exact ⟨merge u v, ⟨u, hu, v, hv, huv, rfl⟩, x, hx,
      (compatible_merge_left.2 ⟨huv, hux, hvx⟩).2, merge_assoc u v x⟩

/-- **The natural join on a common schema is the intersection.** If $r$ and $s$ are relations
over the same schema $S$, that is, finite sets of tuples each over $S$, then their natural join
is their intersection: $r \bowtie s = r \cap s$. -/
theorem join_eq_inter {S : Finset A} {r s : Finset (Tuple A D)} (hr : IsOver S r)
    (hs : IsOver S s) : join r s = r ∩ s := by
  ext t
  rw [mem_join, Finset.mem_inter]
  constructor
  · rintro ⟨u, hu, v, hv, hc, rfl⟩
    have huv := (hr u hu).eq_of_compatible (hs v hv) hc
    subst huv
    rw [merge_self]
    exact ⟨hu, hv⟩
  · rintro ⟨hr', hs'⟩
    exact ⟨t, hr', t, hs', compatible_self t, merge_self t⟩

/-- **Selection distributes over union.** Assume the set of attributes is finite. Let $c$ be a
selection condition and write $\sigma_c$ for selection by $c$. For finite sets $r$ and $s$ of
tuples, $\sigma_c(r \cup s) = \sigma_c(r) \cup \sigma_c(s)$. -/
theorem select_union (c : Cond A D) (r s : Finset (Tuple A D)) :
    select c (r ∪ s) = select c r ∪ select c s := Finset.filter_union _ _ _

/-- **Selection distributes over difference.** Assume the set of attributes is finite. Let $c$
be a selection condition and write $\sigma_c$ for selection by $c$. For finite sets $r$ and $s$
of tuples, $\sigma_c(r \setminus s) = \sigma_c(r) \setminus \sigma_c(s)$. -/
theorem select_sdiff (c : Cond A D) (r s : Finset (Tuple A D)) :
    select c (r \ s) = select c r \ select c s := by
  ext t
  simp only [select, Finset.mem_filter, Finset.mem_sdiff]
  tauto

variable [DecidableEq A]

/-- **Projection of a relation.** For a finite set $T$ of attributes and a finite set $r$ of
tuples, the projection $\pi_T(r)$ is the finite set of the restrictions to $T$ of the tuples of
$r$: $\pi_T(r) = \{ t|_T : t \in r \}$. -/
def project (T : Finset A) (r : Finset (Tuple A D)) : Finset (Tuple A D) :=
  r.image (Tuple.restrict T)

theorem isOver_project {S T : Finset A} {r : Finset (Tuple A D)} (hr : IsOver S r)
    (hT : T ⊆ S) : IsOver T (project T r) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  exact (hr u hu).restrict hT

theorem isOver_join {S S' : Finset A} {r s : Finset (Tuple A D)} (hr : IsOver S r)
    (hs : IsOver S' s) : IsOver (S ∪ S') (join r s) := by
  intro t ht
  obtain ⟨u, hu, v, hv, -, rfl⟩ := mem_join.mp ht
  exact isOver_merge (hr u hu) (hs v hv)

/-- **Membership in a join.** Let $r$ be a relation over the schema $S$ and $s$ a relation over
the schema $S'$, that is, finite sets of tuples each over $S$, respectively each over $S'$. A
tuple $t$ belongs to the natural join $r \bowtie s$ if and only if $t$ is over $S \cup S'$, the
restriction of $t$ to $S$ belongs to $r$, and the restriction of $t$ to $S'$ belongs to $s$. -/
theorem mem_join_iff {S S' : Finset A} {r s : Finset (Tuple A D)} (hr : IsOver S r)
    (hs : IsOver S' s) {t : Tuple A D} :
    t ∈ join r s ↔ t.IsOver (S ∪ S') ∧ t.restrict S ∈ r ∧ t.restrict S' ∈ s := by
  constructor
  · intro ht
    obtain ⟨u, hu, v, hv, hc, rfl⟩ := mem_join.mp ht
    exact ⟨isOver_merge (hr u hu) (hs v hv), by rwa [restrict_merge_left (hr u hu)],
      by rwa [restrict_merge_right (hs v hv) hc]⟩
  · rintro ⟨ht, hl, hr'⟩
    refine mem_join.mpr ⟨_, hl, _, hr', fun a => ?_, ?_⟩
    · by_cases ha : a ∈ S <;> by_cases ha' : a ∈ S' <;> simp [ha, ha']
    · funext a
      by_cases ha : a ∈ S
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((ht a).2 (Finset.mem_union_left _ ha))
        simp [merge, ha, hx]
      · by_cases ha' : a ∈ S'
        · simp [merge, ha, ha']
        · have : t a = none := by
            simpa [Option.not_isSome_iff_eq_none] using mt (ht a).1 (by simp [ha, ha'])
          simp [merge, ha, ha', this]

/-- **Selection pushdown into the left operand of a join.** Let $r$ be a relation over a schema
$S$, that is, a finite set of tuples each defined exactly on the attributes of $S$, and let $s$ be
any finite set of tuples. If every attribute of the selection condition $c$ lies in $S$, then
$\sigma_c(r \bowtie s) = \sigma_c(r) \bowtie s$, where $\sigma_c$ is selection by $c$ and
$\bowtie$ is the natural join. -/
theorem select_join_left {S : Finset A} {r : Finset (Tuple A D)} (s : Finset (Tuple A D))
    (c : Cond A D) (hr : IsOver S r) (hc : c.attrs ⊆ S) :
    select c (join r s) = join (select c r) s := by
  have key : ∀ u ∈ r, ∀ v, c.eval (merge u v) = c.eval u := fun u hu v => by
    rw [← c.eval_restrict _ hc, restrict_merge_left (hr u hu)]
  ext t
  simp only [select, Finset.mem_filter, mem_join]
  constructor
  · rintro ⟨⟨u, hu, v, hv, huv, rfl⟩, h⟩
    exact ⟨u, ⟨hu, by rwa [← key u hu v]⟩, v, hv, huv, rfl⟩
  · rintro ⟨u, ⟨hu, h⟩, v, hv, huv, rfl⟩
    exact ⟨⟨u, hu, v, hv, huv, rfl⟩, by rwa [key u hu v]⟩

/-- **Selection pushdown into the right operand of a join.** Let $s$ be a relation over a schema
$S'$, that is, a finite set of tuples each defined exactly on the attributes of $S'$, and let $r$
be any finite set of tuples. If every attribute of the selection condition $c$ lies in $S'$, then
$\sigma_c(r \bowtie s) = r \bowtie \sigma_c(s)$, where $\sigma_c$ is selection by $c$ and
$\bowtie$ is the natural join. -/
theorem select_join_right {S' : Finset A} (r : Finset (Tuple A D)) {s : Finset (Tuple A D)}
    (c : Cond A D) (hs : IsOver S' s) (hc : c.attrs ⊆ S') :
    select c (join r s) = join r (select c s) := by
  rw [join_comm, select_join_left r c hs hc, join_comm]

/-- **Cascade of projections.** Assume the set of attributes is finite. For all finite sets of
attributes $T$ and $T'$ and every finite set $r$ of tuples,
$\pi_T(\pi_{T'}(r)) = \pi_{T \cap T'}(r)$, where $\pi_T$ is projection onto $T$. -/
theorem project_project (T T' : Finset A) (r : Finset (Tuple A D)) :
    project T (project T' r) = project (T ∩ T') r := by
  simp only [project, Finset.image_image]
  congr 1
  funext t
  exact restrict_restrict T T' t

/-- **Cascade of projections onto a subset.** Assume the set of attributes is finite. For finite
sets of attributes $T \subseteq T'$ and every finite set $r$ of tuples,
$\pi_T(\pi_{T'}(r)) = \pi_T(r)$, where $\pi_T$ is projection onto $T$. -/
theorem project_project_of_subset {T T' : Finset A} (h : T ⊆ T') (r : Finset (Tuple A D)) :
    project T (project T' r) = project T r := by
  rw [project_project, Finset.inter_eq_left.mpr h]

/-- **Selection commutes with projection.** Assume the set of attributes is finite. Let $c$ be a
selection condition, $T$ a finite set of attributes containing every attribute of $c$, and $r$ a
finite set of tuples. Then $\sigma_c(\pi_T(r)) = \pi_T(\sigma_c(r))$, where $\sigma_c$ is
selection by $c$ and $\pi_T$ is projection onto $T$. -/
theorem select_project {T : Finset A} (c : Cond A D) (r : Finset (Tuple A D))
    (hc : c.attrs ⊆ T) : select c (project T r) = project T (select c r) := by
  ext t
  simp only [select, project, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, h⟩
    exact ⟨u, ⟨hu, by rwa [c.eval_restrict u hc] at h⟩, rfl⟩
  · rintro ⟨u, ⟨hu, h⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, by rwa [c.eval_restrict u hc]⟩

/-- **Projection distributes over union.** For every finite set $T$ of attributes and all finite
sets $r$ and $s$ of tuples, the projection onto $T$ of $r \cup s$ is the union of the projections
onto $T$ of $r$ and of $s$: $\pi_T(r \cup s) = \pi_T(r) \cup \pi_T(s)$. -/
theorem project_union (T : Finset A) (r s : Finset (Tuple A D)) :
    project T (r ∪ s) = project T r ∪ project T s := Finset.image_union _ _

/-! ### Queries -/

/-- **Relational algebra queries.** The relational algebra queries over base relations named
by $N$, with attributes $A$ and values $D$, are generated by: the base relation named $n$ for
each $n \in N$; the selection $\sigma_c(e)$ of a query $e$ by a selection condition $c$; the
projection $\pi_T(e)$ of a query $e$ on a finite set of attributes $T$; the natural join of two
queries; the union of two queries; the difference of two queries; and the renaming
$\rho_f(e)$ of a query $e$ along a permutation $f$ of $A$. -/
inductive Expr (N A D : Type*)
  /-- The base relation named `n`. -/
  | rel (n : N)
  /-- Selection. -/
  | select (c : Cond A D) (e : Expr N A D)
  /-- Projection. -/
  | project (T : Finset A) (e : Expr N A D)
  /-- Natural join. -/
  | join (e e' : Expr N A D)
  /-- Union. -/
  | union (e e' : Expr N A D)
  /-- Difference. -/
  | diff (e e' : Expr N A D)
  /-- Renaming along a permutation of the attributes. -/
  | rename (f : A ≃ A) (e : Expr N A D)

namespace Expr

variable {N : Type*}

/-- **Value of a query.** Given a database $\mathrm{db}$, which assigns a finite set of tuples
$\mathrm{db}(n)$ to each relation name $n$, the value of a relational algebra query on
$\mathrm{db}$ is the finite set of tuples defined by recursion on the query: the base relation
$n$ has value $\mathrm{db}(n)$; for a query $e$ with value $v$, the selection $\sigma_c(e)$ by a
selection condition $c$, the projection $\pi_T(e)$ onto a finite set $T$ of attributes and the
renaming $\rho_f(e)$ along a permutation $f$ of the attributes have values $\sigma_c(v)$,
$\pi_T(v)$ and $\rho_f(v)$; and the natural join, the union and the difference of queries $e$
and $e'$ with values $v$ and $v'$ have values $v \bowtie v'$, $v \cup v'$ and
$v \setminus v'$. -/
def eval (db : N → Finset (Tuple A D)) : Expr N A D → Finset (Tuple A D)
  | rel n => db n
  | select c e => Databases.select c (e.eval db)
  | project T e => Databases.project T (e.eval db)
  | join e e' => Databases.join (e.eval db) (e'.eval db)
  | union e e' => e.eval db ∪ e'.eval db
  | diff e e' => e.eval db \ e'.eval db
  | rename f e => Databases.rename f (e.eval db)

/-- **Schema of a query.** Given a database schema assigning a finite set $\mathrm{sch}(n)$ of
attributes to each base relation name $n$, the schema of a relational algebra query is either a
finite set of attributes or undefined (the query is ill-formed), defined by recursion on the
query: the base relation $n$ has schema $\mathrm{sch}(n)$; if $e$ has schema $S$, then the
selection $\sigma_c(e)$ has schema $S$ when every attribute of the condition $c$ lies in $S$, the
projection $\pi_T(e)$ has schema $T$ when $T \subseteq S$, and the renaming $\rho_f(e)$ along a
permutation $f$ of the attributes has schema $f(S)$; if $e$ and $e'$ have schemas $S$ and $S'$,
then the natural join of $e$ and $e'$ has schema $S \cup S'$, and their union and their
difference have schema $S$ when $S = S'$. In every other case, including when an operand is
ill-formed, the schema is undefined. -/
def schema (sch : N → Finset A) : Expr N A D → Option (Finset A)
  | rel n => some (sch n)
  | select c e => (e.schema sch).bind fun S => if c.attrs ⊆ S then some S else none
  | project T e => (e.schema sch).bind fun S => if T ⊆ S then some T else none
  | join e e' => (e.schema sch).bind fun S => (e'.schema sch).map fun S' => S ∪ S'
  | union e e' => (e.schema sch).bind fun S => (e'.schema sch).bind fun S' =>
      if S = S' then some S else none
  | diff e e' => (e.schema sch).bind fun S => (e'.schema sch).bind fun S' =>
      if S = S' then some S else none
  | rename f e => (e.schema sch).map fun S => S.map f.toEmbedding

/-- **Databases conforming to a schema.** Let $N$ be a set of relation names. A database
schema assigns to each name $n \in N$ a finite set of attributes $\mathrm{sch}(n)$, and a
database assigns to each name $n$ a finite set of tuples $\mathrm{db}(n)$. The database
$\mathrm{db}$ conforms to the database schema $\mathrm{sch}$ when, for every name $n$, the
set $\mathrm{db}(n)$ is a relation over $\mathrm{sch}(n)$. -/
def Conforms (sch : N → Finset A) (db : N → Finset (Tuple A D)) : Prop :=
  ∀ n, IsOver (sch n) (db n)

/-- **Typing is sound**: a well-formed query evaluates, on every conforming database, to a
relation over its inferred schema. -/
theorem eval_isOver {sch : N → Finset A} {db : N → Finset (Tuple A D)} (hdb : Conforms sch db) :
    ∀ (e : Expr N A D) {S : Finset A}, e.schema sch = some S → IsOver S (e.eval db)
  | rel n, S, h => by
    cases h
    exact hdb n
  | select c e, S, h => by
    simp only [schema, Option.bind_eq_some_iff] at h
    obtain ⟨S₀, h₀, h⟩ := h
    split_ifs at h with hc
    cases h
    exact isOver_select c (eval_isOver hdb e h₀)
  | project T e, S, h => by
    simp only [schema, Option.bind_eq_some_iff] at h
    obtain ⟨S₀, h₀, h⟩ := h
    split_ifs at h with hT
    cases h
    exact isOver_project (eval_isOver hdb e h₀) hT
  | join e e', S, h => by
    simp only [schema, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨S₀, h₀, S₁, h₁, rfl⟩ := h
    exact isOver_join (eval_isOver hdb e h₀) (eval_isOver hdb e' h₁)
  | union e e', S, h => by
    simp only [schema, Option.bind_eq_some_iff] at h
    obtain ⟨S₀, h₀, S₁, h₁, h⟩ := h
    split_ifs at h with hS
    cases h
    subst hS
    exact isOver_union (eval_isOver hdb e h₀) (eval_isOver hdb e' h₁)
  | diff e e', S, h => by
    simp only [schema, Option.bind_eq_some_iff] at h
    obtain ⟨S₀, h₀, S₁, -, h⟩ := h
    split_ifs at h with hS
    cases h
    exact isOver_sdiff _ (eval_isOver hdb e h₀)
  | rename f e, S, h => by
    simp only [schema, Option.map_eq_some_iff] at h
    obtain ⟨S₀, h₀, rfl⟩ := h
    exact isOver_rename f (eval_isOver hdb e h₀)

/-- **Query equivalence.** Let $\mathrm{sch}$ be a database schema, assigning a finite set of
attributes to each relation name. Two queries $e$ and $e'$ are equivalent with respect to
$\mathrm{sch}$ when there is a finite set of attributes $S$ such that the inferred schemas of
$e$ and of $e'$ with respect to $\mathrm{sch}$ are both $S$ (in particular both queries are
well-formed), and $e$ and $e'$ evaluate to the same relation on every database that conforms
to $\mathrm{sch}$. -/
def Equiv (sch : N → Finset A) (e e' : Expr N A D) : Prop :=
  ∃ S, e.schema sch = some S ∧ e'.schema sch = some S ∧
    ∀ db, Conforms sch db → e.eval db = e'.eval db

theorem join_comm {sch : N → Finset A} {e e' : Expr N A D} {S S' : Finset A}
    (he : e.schema sch = some S) (he' : e'.schema sch = some S') :
    Equiv sch (join e e') (join e' e) :=
  ⟨S ∪ S', by simp [schema, he, he'], by simp [schema, he, he', Finset.union_comm],
    fun _ _ => Databases.join_comm _ _⟩

theorem join_assoc {sch : N → Finset A} {e e' e'' : Expr N A D} {S S' S'' : Finset A}
    (he : e.schema sch = some S) (he' : e'.schema sch = some S')
    (he'' : e''.schema sch = some S'') :
    Equiv sch (join (join e e') e'') (join e (join e' e'')) :=
  ⟨S ∪ S' ∪ S'', by simp [schema, he, he', he''],
    by simp [schema, he, he', he'', Finset.union_assoc], fun _ _ => Databases.join_assoc _ _ _⟩

/-- **Selection pushdown as a query rewrite.** Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. Let $e$ and $e'$ be well-formed queries with
schemas $S$ and $S'$, and let $c$ be a selection condition all of whose attributes lie in $S$.
Then the query $\sigma_c(e \bowtie e')$, the selection by $c$ of the natural join of $e$ and $e'$,
is equivalent to the query $\sigma_c(e) \bowtie e'$: both are well-formed with the same schema,
and they have equal values on every database conforming to $\mathrm{sch}$. -/
theorem select_join {sch : N → Finset A} {e e' : Expr N A D} {S S' : Finset A}
    (he : e.schema sch = some S) (he' : e'.schema sch = some S') (c : Cond A D)
    (hc : c.attrs ⊆ S) :
    Equiv sch (select c (join e e')) (join (select c e) e') :=
  ⟨S ∪ S', by simp [schema, he, he', hc.trans Finset.subset_union_left],
    by simp [schema, he, he', hc], fun _ hdb => select_join_left _ c (eval_isOver hdb e he) hc⟩

/-- **Cascade of selections as a query rewrite.** Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. Let $e$ be a well-formed query
with schema $S$, and let $c$ and $c'$ be selection conditions all of whose attributes lie in
$S$. Then the query $\sigma_c(\sigma_{c'}(e))$, the selection by $c$ of the selection of $e$ by
$c'$, is equivalent to the query $\sigma_{c' \land c}(e)$, the selection of $e$ by the
conjunction $c' \land c$: both are well-formed with the same schema, and they have equal values
on every database conforming to $\mathrm{sch}$. -/
theorem select_select {sch : N → Finset A} {e : Expr N A D} {S : Finset A}
    (he : e.schema sch = some S) {c c' : Cond A D} (hc : c.attrs ⊆ S) (hc' : c'.attrs ⊆ S) :
    Equiv sch (select c (select c' e)) (select (.and c' c) e) :=
  ⟨S, by simp [schema, he, hc, hc'], by simp [schema, he, Cond.attrs, Finset.union_subset hc' hc],
    fun _ _ => Databases.select_select _ _ _⟩

/-- **Cascade of projections as a query rewrite.** Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. Let $e$ be a well-formed query
with schema $S$, and let $T \subseteq T' \subseteq S$ be finite sets of attributes. Then the
query $\pi_T(\pi_{T'}(e))$, the projection onto $T$ of the projection of $e$ onto $T'$, is
equivalent to the query $\pi_T(e)$, the projection of $e$ onto $T$: both are well-formed with
the same schema, and they have equal values on every database conforming to $\mathrm{sch}$. -/
theorem project_project {sch : N → Finset A} {e : Expr N A D} {S T T' : Finset A}
    (he : e.schema sch = some S) (hT' : T' ⊆ S) (hT : T ⊆ T') :
    Equiv sch (project T (project T' e)) (project T e) :=
  ⟨T, by simp [schema, he, hT', hT], by simp [schema, he, hT.trans hT'],
    fun _ _ => project_project_of_subset hT _⟩

end Expr

end Cslib.Databases
