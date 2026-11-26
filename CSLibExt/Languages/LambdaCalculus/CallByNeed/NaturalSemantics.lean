/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CallByNeed.Syntax
public import Mathlib.Logic.Equiv.Defs

/-!
# Call-by-need: natural semantics

Launchbury's natural semantics for lazy evaluation in Sestoft's revised form. The judgement
`Eval A Γ e Δ w n` says that in the heap `Γ`, choosing new names outside the set `A`, the
expression `e` evaluates to the value `w`, leaving the heap `Δ`, and performs `n` additions.
A heap is an association list from names to expressions. A variable is evaluated by
evaluating the expression it is bound to, with its binding removed, and then rebinding it to
the value: the binding is updated, so a bound expression is evaluated at most once. A `let`
allocates its bindings under new names.

`Eval.isValue` shows that results are values and `Eval.dom_subset` that heaps only grow.
`Eval.closed` shows that a configuration whose free names are bound in the heap or listed in a
set stays so. `Eval.map` shows that evaluation is invariant under permutations of names, and
`Eval.unique_up_to_renaming` shows that evaluation of a closed configuration is deterministic
up to the choice of new names, with the same number of additions.

## Source and representation

The rules are those of Launchbury [Lau93, §3.2, Figure 1] for abstractions, applications,
variables and `let`, and of [Lau93, §4] for numerals and addition. Two deviations make
freshness locally checkable and evaluation deterministic up to renaming.

* As in Sestoft's revised semantics [Ses97, §2.4, Figure 2], new names are chosen in the
  `let` rule, not in the variable rule: the let-bound names, which must be distinct, are
  replaced by distinct new names outside `A`, outside every name of the heap and outside every
  name of the `let` expression; a variable is evaluated with its name added to `A`. The value
  is not renamed in the variable rule. Launchbury's global freshness condition cannot be
  checked locally [Ses97, §2.3].
* The addition rule of [Lau93, §4] is carried over to judgements with a set of names to avoid,
  and its first operand is evaluated with every name of the second operand added to `A`. This
  widening is an extension made here, not a rule of either source; it applies the principle,
  stated by Breitner [Bre14, §2], that a new name must be fresh for the whole derivation and not
  only for the current judgement. With freshness local to the judgement, a name chosen inside
  the first operand can equal a bound name of the second operand and be captured by
  substitution, and the result is not determined up to renaming.

Heaps are lists; a new binding is put in front and `Heap.erase` removes every binding of a
name. The heap domains grow as in [Lau93, §5.2.1] and [Ses97, Lemma 1]. The closedness
condition `Closed` is the no-dangling-name condition of [Ses97, Definition 1 (2)], and
determinism up to renaming, stated in [Ses97, §2.2], is proved here under it. The last index
counts additions, as in the cost annotations of [Lau93, §6.3]. Black holes have no
derivation [Lau93, §4.1]. Constructors and case expressions, the denotational semantics and
its correctness, and the relation to call-by-name are not formalized.

## References

* [Lau93] J. Launchbury, *A natural semantics for lazy evaluation*, POPL 1993, pp. 144–154.
* [Ses97] P. Sestoft, *Deriving a lazy abstract machine*, Journal of Functional Programming
  7(3), 1997.
* [Bre14] J. Breitner, *The correctness of Launchbury's natural semantics for lazy
  evaluation*, arXiv:1405.3099, 2014; see also the chapter "Launchbury's semantics" of his
  doctoral thesis.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.CallByNeed

universe u

/-- Heaps: lists of bindings of names to expressions, the most recent first. -/
abbrev Heap (V : Type u) := List (V × Expr V)

/-- The names bound by a heap. -/
def Heap.dom {V : Type u} [DecidableEq V] (Γ : Heap V) : Finset V := (Γ.map Prod.fst).toFinset

/-- The expression a heap binds a name to: the first binding of the name. -/
def Heap.lookup {V : Type u} [DecidableEq V] (Γ : Heap V) (x : V) : Option (Expr V) :=
  List.lookup x Γ

/-- The heap without any binding of the name `x`. -/
def Heap.erase {V : Type u} [DecidableEq V] (Γ : Heap V) (x : V) : Heap V :=
  Γ.filter fun b => b.1 ≠ x

/-- The free names of the expressions bound by a heap. -/
def Heap.fv {V : Type u} [DecidableEq V] : Heap V → Finset V
  | [] => ∅
  | b :: Γ => b.2.fv ∪ Heap.fv Γ

/-- Every name occurring in a heap: the bound names and the names of the bound
expressions. -/
def Heap.names {V : Type u} [DecidableEq V] : Heap V → Finset V
  | [] => ∅
  | b :: Γ => insert b.1 (b.2.names ∪ Heap.names Γ)

/-- Apply `f` to every name occurring in a heap. -/
def Heap.map {V : Type u} (f : V → V) (Γ : Heap V) : Heap V :=
  List.map (fun b => (f b.1, b.2.map f)) Γ

/-- The heap that binds the `i`-th name of `ps` to the `i`-th right-hand side of `bs`, in which
the `j`-th name bound by `bs` is replaced by the `j`-th name of `ps`.

Both pairings use `List.zip`, which stops at the end of the shorter list. When `ps` has fewer
names than `bs` has bindings, only the first `ps.length` bindings are allocated, and a bound name
that is not among the first `ps.length` bound names is left in place; when `ps` has more names,
the extra names are ignored. A name that `bs` binds more than once is replaced by the name paired
with its first occurrence. The `let` rule of `Eval` allocates only with exactly one name per
binding, the names distinct and fresh and the bound names distinct, so none of this arises
there. -/
def Binds.alloc {V : Type u} [DecidableEq V] (ps : List V) (bs : Binds V) : Heap V :=
  (ps.zip bs.exprs).map fun b => (b.1, b.2.subst (bs.vars.zip ps))

/-- `Eval A Γ e Δ w n`: in the heap `Γ`, choosing new names outside the set `A`, the expression
`e` evaluates to the value `w`, leaving the heap `Δ`, and performs `n` additions.

This is Launchbury's natural semantics for lazy evaluation in Sestoft's revised form, where new
heap names are chosen in the `let` rule outside the set `A` of names under evaluation, extended
here so that the first operand of an addition also avoids the names of the second operand.

The judgement places no condition on its configuration. The source semantics starts from a
closed expression in the empty heap with `A` empty, and every configuration it then reaches is
good in Sestoft's sense [Ses97, §2.5, Definition 1, Lemma 1]: among other conditions, no bound
name of the heap or of the expression is in `A` or bound in the heap. Sestoft shows that such an
evaluation involves no capture [Ses97, §2.5, Proposition 1]; this is not proved here. From a
configuration that is not good, the naive substitution of the application rule can capture: in
the heap that binds `p` to `7` and `q` to `2`, with `A` empty, the configuration
`((λx. λp. x) p) q` is closed and evaluates to `2`, because the argument `p` is captured under
`λp`, while with the inner binder renamed to a fresh name it evaluates to `7`.

The source semantics also assumes an inexhaustible supply of fresh names. Over a finite type of
names the `let` rule can run out of them, and the `let` then has no evaluation, as an allocation
failure: over `Unit`, where `x` is the only name, `let x = 7 in x` has none. -/
inductive Eval {V : Type u} [DecidableEq V] :
    Finset V → Heap V → Expr V → Heap V → Expr V → ℕ → Prop
  /-- An abstraction is a value. -/
  | lam {A : Finset V} {Γ : Heap V} {x : V} {e : Expr V} :
      Eval A Γ (.lam x e) Γ (.lam x e) 0
  /-- A numeral is a value. -/
  | num {A : Finset V} {Γ : Heap V} {k : ℕ} :
      Eval A Γ (.num k) Γ (.num k) 0
  /-- To evaluate `e p`, evaluate `e` to an abstraction `λy. e'`, then evaluate `e'` with `p`
  substituted for `y`. -/
  | app {A : Finset V} {Γ Δ Θ : Heap V} {e e' w : Expr V} {y p : V} {n₁ n₂ : ℕ} :
      Eval A Γ e Δ (.lam y e') n₁ → Eval A Δ (e'.subst [(y, p)]) Θ w n₂ →
      Eval A Γ (.app e p) Θ w (n₁ + n₂)
  /-- To evaluate a variable `x` bound to `e`, evaluate `e` in the heap without the binding of
  `x`, with `x` added to the names to avoid, and bind `x` to the value. -/
  | var {A : Finset V} {Γ Δ : Heap V} {x : V} {e w : Expr V} {n : ℕ} :
      Γ.lookup x = some e → Eval (insert x A) (Γ.erase x) e Δ w n →
      Eval A Γ (.var x) ((x, w) :: Δ) w n
  /-- To evaluate `let x₁ = e₁, …, xₙ = eₙ in e` with distinct `xᵢ`, choose distinct new
  names `p₁, …, pₙ` outside `A`, outside every name of the heap and outside every name of the
  `let` expression, bind each `pᵢ` to `eᵢ` with every `xⱼ` replaced by `pⱼ`, and evaluate `e`
  with every `xⱼ` replaced by `pⱼ`. -/
  | letrec {A : Finset V} {Γ Δ : Heap V} {bs : Binds V} {e w : Expr V} {n : ℕ}
      (ps : List V) :
      bs.vars.Nodup → ps.Nodup → ps.length = bs.vars.length →
      (∀ p ∈ ps, p ∉ A ∧ p ∉ Γ.names ∧ p ∉ (Expr.letrec bs e).names) →
      Eval A (bs.alloc ps ++ Γ) (e.subst (bs.vars.zip ps)) Δ w n →
      Eval A Γ (.letrec bs e) Δ w n
  /-- To evaluate `e₁ + e₂`, evaluate `e₁` to a numeral avoiding also every name of `e₂`, then
  `e₂` to a numeral, and add; this counts one addition. Without the names of `e₂` in the set
  to avoid, a name chosen inside `e₁` could be captured inside `e₂`. -/
  | add {A : Finset V} {Γ Δ Θ : Heap V} {e₁ e₂ : Expr V} {k₁ k₂ n₁ n₂ : ℕ} :
      Eval (A ∪ e₂.names) Γ e₁ Δ (.num k₁) n₁ → Eval A Δ e₂ Θ (.num k₂) n₂ →
      Eval A Γ (.add e₁ e₂) Θ (.num (k₁ + k₂)) (n₁ + n₂ + 1)

/-- A configuration is closed with respect to `A` when every free name of the heap and of the
expression is bound in the heap or listed in `A`. -/
def Closed {V : Type u} [DecidableEq V] (A : Finset V) (Γ : Heap V) (e : Expr V) : Prop :=
  Γ.fv ∪ e.fv ⊆ A ∪ Γ.dom

/-- The domain of a heap with a binding in front. -/
private theorem heap_dom_cons {V : Type u} [DecidableEq V] (x : V) (e : Expr V) (Γ : Heap V) :
    Heap.dom ((x, e) :: Γ) = insert x Γ.dom := by
  simp [Heap.dom]

/-- The domain of an appended heap. -/
private theorem heap_dom_append {V : Type u} [DecidableEq V] (Γ₁ Γ₂ : Heap V) :
    Heap.dom (Γ₁ ++ Γ₂) = Γ₁.dom ∪ Γ₂.dom := by
  simp [Heap.dom, List.toFinset_append]

/-- A name is free in a heap exactly when it is free in one of its bound expressions. -/
private theorem mem_heap_fv {V : Type u} [DecidableEq V] {y : V} :
    ∀ Γ : Heap V, y ∈ Γ.fv ↔ ∃ b ∈ Γ, y ∈ b.2.fv
  | [] => by simp [Heap.fv]
  | b :: Γ => by simp [Heap.fv, mem_heap_fv Γ]

/-- A name occurs in a heap exactly when it is bound there or occurs in a bound expression. -/
private theorem mem_heap_names {V : Type u} [DecidableEq V] {y : V} :
    ∀ Γ : Heap V, y ∈ Γ.names ↔ ∃ b ∈ Γ, y = b.1 ∨ y ∈ b.2.names
  | [] => by simp [Heap.names]
  | b :: Γ => by
    simp only [Heap.names, Finset.mem_insert, Finset.mem_union, mem_heap_names Γ, List.mem_cons]
    constructor
    · rintro (h | h | ⟨c, hc, h⟩)
      · exact ⟨b, Or.inl rfl, Or.inl h⟩
      · exact ⟨b, Or.inl rfl, Or.inr h⟩
      · exact ⟨c, Or.inr hc, h⟩
    · rintro ⟨c, rfl | hc, h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨c, hc, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨c, hc, Or.inr h⟩)

/-- The free names of an appended heap. -/
private theorem heap_fv_append {V : Type u} [DecidableEq V] (Γ₁ Γ₂ : Heap V) :
    Heap.fv (Γ₁ ++ Γ₂) = Γ₁.fv ∪ Γ₂.fv := by
  ext y
  simp only [mem_heap_fv, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨b, hb | hb, h⟩
    · exact Or.inl ⟨b, hb, h⟩
    · exact Or.inr ⟨b, hb, h⟩
  · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    · exact ⟨b, Or.inl hb, h⟩
    · exact ⟨b, Or.inr hb, h⟩

/-- A name bound by a heap occurs in it. -/
private theorem heap_dom_subset_names {V : Type u} [DecidableEq V] (Γ : Heap V) :
    Γ.dom ⊆ Γ.names := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
  exact (mem_heap_names Γ).mpr ⟨b, hb, Or.inl rfl⟩

/-- Every name bound by a heap is the erased name or still bound after the erasure. -/
private theorem heap_dom_subset_insert_erase {V : Type u} [DecidableEq V] (Γ : Heap V) (x : V) :
    Γ.dom ⊆ insert x (Γ.erase x).dom := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
  by_cases hbx : b.1 = x
  · rw [hbx]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, ?_, rfl⟩))
    exact List.mem_filter.mpr ⟨hb, by simpa using hbx⟩

/-- Results are values: whatever an expression evaluates to is an abstraction or a numeral. -/
theorem Eval.isValue {V : Type u} [DecidableEq V] {A : Finset V} {Γ Δ : Heap V}
    {e w : Expr V} {n : ℕ} (h : Eval A Γ e Δ w n) : w.IsValue := by
  induction h with
  | lam => exact .lam _ _
  | num => exact .num _
  | app _ _ _ ih₂ => exact ih₂
  | var _ _ ih => exact ih
  | letrec _ _ _ _ _ _ ih => exact ih
  | add _ _ _ _ => exact .num _

/-- Heaps only grow: every name bound before an evaluation is bound after it. -/
theorem Eval.dom_subset {V : Type u} [DecidableEq V] {A : Finset V} {Γ Δ : Heap V}
    {e w : Expr V} {n : ℕ} (h : Eval A Γ e Δ w n) : Γ.dom ⊆ Δ.dom := by
  induction h with
  | lam => exact Finset.Subset.refl _
  | num => exact Finset.Subset.refl _
  | app _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @var A Γ Δ x e w n _ _ ih =>
    rw [heap_dom_cons]
    exact (heap_dom_subset_insert_erase Γ x).trans (Finset.insert_subset_insert x ih)
  | letrec _ _ _ _ _ _ ih =>
    rw [heap_dom_append] at ih
    exact Finset.subset_union_right.trans ih
  | add _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The free names of a heap with every binding of `x` erased are free in the heap. -/
private theorem heap_fv_erase_subset {V : Type u} [DecidableEq V] (Γ : Heap V) (x : V) :
    (Γ.erase x).fv ⊆ Γ.fv := by
  intro y hy
  obtain ⟨b, hb, h⟩ := (mem_heap_fv _).mp hy
  exact (mem_heap_fv Γ).mpr ⟨b, (List.mem_filter.mp hb).1, h⟩

/-- The binding a heap gives a name belongs to the heap. -/
private theorem mem_of_lookup_eq_some {V : Type u} [DecidableEq V] {x : V} {e : Expr V} :
    ∀ {Γ : Heap V}, Γ.lookup x = some e → (x, e) ∈ Γ
  | [], h => by simp [Heap.lookup] at h
  | (k, d) :: Γ, h => by
    unfold Heap.lookup at h
    rw [List.lookup_cons] at h
    by_cases hxk : x = k
    · subst hxk
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (x == k) = false := by simpa using hxk
      rw [hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

/-- The free names of an expression a heap binds are free in the heap. -/
private theorem heap_fv_lookup_subset {V : Type u} [DecidableEq V] {Γ : Heap V} {x : V}
    {e : Expr V} (h : Γ.lookup x = some e) : e.fv ⊆ Γ.fv :=
  fun _ hy => (mem_heap_fv Γ).mpr ⟨(x, e), mem_of_lookup_eq_some h, hy⟩

/-- Bindings have one right-hand side per bound name. -/
private theorem length_exprs {V : Type u} : ∀ bs : Binds V, bs.exprs.length = bs.vars.length
  | .nil => rfl
  | .cons _ _ bs => by simp [Binds.exprs, Binds.vars, length_exprs bs]

/-- Substitution in bindings substitutes in each right-hand side. -/
private theorem exprs_subst {V : Type u} [DecidableEq V] (σ : List (V × V)) :
    ∀ bs : Binds V, (bs.subst σ).exprs = bs.exprs.map (Expr.subst σ)
  | .nil => rfl
  | .cons _ e bs => by simp [Binds.subst, Binds.exprs, exprs_subst σ bs]

/-- A name is free in bindings exactly when it is free in one of their right-hand sides. -/
private theorem mem_binds_fv' {V : Type u} [DecidableEq V] {y : V} :
    ∀ bs : Binds V, y ∈ bs.fv ↔ ∃ e ∈ bs.exprs, y ∈ e.fv
  | .nil => by simp [Binds.fv, Binds.exprs]
  | .cons x e bs => by simp [Binds.fv, Binds.exprs, mem_binds_fv' bs]

/-- The heap allocated for bindings binds exactly the new names. -/
private theorem dom_alloc {V : Type u} [DecidableEq V] {bs : Binds V} {ps : List V}
    (hlen : ps.length = bs.vars.length) : (bs.alloc ps).dom = ps.toFinset := by
  unfold Heap.dom Binds.alloc
  rw [List.map_map]
  have hf : (Prod.fst ∘ fun b : V × Expr V => (b.1, b.2.subst (bs.vars.zip ps))) = Prod.fst :=
    rfl
  rw [hf, List.map_fst_zip (by rw [length_exprs]; omega)]

/-- The free names of the heap allocated for bindings are free in the substituted bindings. -/
private theorem fv_alloc_subset {V : Type u} [DecidableEq V] (bs : Binds V) (ps : List V) :
    (bs.alloc ps).fv ⊆ (bs.subst (bs.vars.zip ps)).fv := by
  intro z hz
  obtain ⟨b, hb, hz⟩ := (mem_heap_fv _).mp hz
  unfold Binds.alloc at hb
  obtain ⟨⟨p, e⟩, he, rfl⟩ := List.mem_map.mp hb
  refine (mem_binds_fv' _).mpr ⟨e.subst (bs.vars.zip ps), ?_, hz⟩
  rw [exprs_subst]
  exact List.mem_map_of_mem (List.of_mem_zip he).2

/-- Closedness for a larger set. -/
private theorem closed_mono {V : Type u} [DecidableEq V] {S S' : Finset V} {Γ : Heap V}
    {e : Expr V} (h : S ⊆ S') (hc : Closed S Γ e) : Closed S' Γ e :=
  hc.trans (Finset.union_subset_union h (Finset.Subset.refl _))

/-- The function part of a closed application is closed. -/
private theorem closed_app_fun {V : Type u} [DecidableEq V] {S : Finset V} {Γ : Heap V}
    {e : Expr V} {p : V} (hc : Closed S Γ (.app e p)) : Closed S Γ e := by
  intro z hz
  apply hc
  rcases Finset.mem_union.mp hz with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simp [Expr.fv, h])

/-- The argument of a closed application is bound or in the set. -/
private theorem closed_app_arg {V : Type u} [DecidableEq V] {S : Finset V} {Γ : Heap V}
    {e : Expr V} {p : V} (hc : Closed S Γ (.app e p)) : p ∈ S ∪ Γ.dom :=
  hc (Finset.mem_union_right _ (by simp [Expr.fv]))

/-- Substituting a bound name for the variable of a closed abstraction gives a closed body. -/
private theorem closed_subst_one {V : Type u} [DecidableEq V] {S : Finset V} {Δ : Heap V}
    {y p : V} {e' : Expr V} (hc : Closed S Δ (.lam y e')) (hp : p ∈ S ∪ Δ.dom) :
    Closed S Δ (e'.subst [(y, p)]) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact hc (Finset.mem_union_left _ hz)
  · have h := Expr.fv_subst [(y, p)] e' hz
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.notMem_empty,
      or_false] at h
    rcases h with ⟨h₁, h₂⟩ | rfl
    · exact hc (Finset.mem_union_right _ (by simp [Expr.fv, h₁, h₂]))
    · exact hp

/-- The premise of the variable rule is closed when the variable is. -/
private theorem closed_var {V : Type u} [DecidableEq V] {S : Finset V} {Γ : Heap V} {x : V}
    {e : Expr V} (hl : Γ.lookup x = some e) (hc : Closed S Γ (.var x)) :
    Closed (insert x S) (Γ.erase x) e := by
  have key : ∀ z ∈ Γ.fv, z ∈ insert x S ∪ (Γ.erase x).dom := by
    intro z hz
    rcases Finset.mem_union.mp (hc (Finset.mem_union_left _ hz)) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
    · rcases Finset.mem_insert.mp (heap_dom_subset_insert_erase Γ x h) with rfl | h'
      · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_right _ h'
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact key z (heap_fv_erase_subset Γ x hz)
  · exact key z (heap_fv_lookup_subset hl hz)

/-- Rebinding the variable keeps the result of the variable rule closed. -/
private theorem closed_var_result {V : Type u} [DecidableEq V] {S : Finset V} {Δ : Heap V}
    {x : V} {w : Expr V} (hc : Closed (insert x S) Δ w) : Closed S ((x, w) :: Δ) w := by
  intro z hz
  have hz' : z ∈ Δ.fv ∪ w.fv := by
    simp only [Heap.fv, Finset.mem_union] at hz ⊢
    tauto
  rw [heap_dom_cons]
  rcases Finset.mem_union.mp (hc hz') with h | h
  · rcases Finset.mem_insert.mp h with rfl | h
    · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)

/-- The premise of the `let` rule is closed when the `let` expression is. -/
private theorem closed_letrec {V : Type u} [DecidableEq V] {S : Finset V} {Γ : Heap V}
    {bs : Binds V} {e : Expr V} {ps : List V} (hlen : ps.length = bs.vars.length)
    (hc : Closed S Γ (.letrec bs e)) : Closed S (bs.alloc ps ++ Γ) (e.subst (bs.vars.zip ps)) := by
  have hk : (bs.vars.zip ps).map Prod.fst = bs.vars := List.map_fst_zip (by omega)
  have hv : (bs.vars.zip ps).map Prod.snd = ps := List.map_snd_zip (by omega)
  have hlet : ∀ z, (z ∈ bs.fv ∨ z ∈ e.fv) → z ∉ bs.vars → z ∈ S ∪ Γ.dom := fun z hz hzv =>
    hc (Finset.mem_union_right _ (by simp [Expr.fv, hz, hzv]))
  have hmove : ∀ z, z ∈ S ∪ Γ.dom → z ∈ S ∪ (bs.alloc ps ++ Γ).dom := by
    intro z hz
    rw [heap_dom_append]
    rcases Finset.mem_union.mp hz with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
  have hnew : ∀ z ∈ ps, z ∈ S ∪ (bs.alloc ps ++ Γ).dom := by
    intro z hz
    rw [heap_dom_append, dom_alloc hlen]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hz))
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rw [heap_fv_append] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have h := Binds.fv_subst (bs.vars.zip ps) bs (fv_alloc_subset bs ps hz)
      rw [hk, hv] at h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.mp h
        exact hmove z (hlet z (Or.inl h₁) (by simpa using h₂))
      · exact hnew z (List.mem_toFinset.mp h)
    · exact hmove z (hc (Finset.mem_union_left _ hz))
  · have h := Expr.fv_subst (bs.vars.zip ps) e hz
    rw [hk, hv] at h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.mp h
      exact hmove z (hlet z (Or.inr h₁) (by simpa using h₂))
    · exact hnew z (List.mem_toFinset.mp h)

/-- The first operand of a closed addition is closed. -/
private theorem closed_add_fun {V : Type u} [DecidableEq V] {S : Finset V} {Γ : Heap V}
    {e₁ e₂ : Expr V} (hc : Closed S Γ (.add e₁ e₂)) : Closed S Γ e₁ := by
  intro z hz
  apply hc
  rcases Finset.mem_union.mp hz with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (by simp [Expr.fv, h])

/-- The second operand of a closed addition is closed after the first operand is evaluated. -/
private theorem closed_add_arg {V : Type u} [DecidableEq V] {S : Finset V} {Γ Δ : Heap V}
    {e₁ e₂ : Expr V} {k : ℕ} (hc : Closed S Γ (.add e₁ e₂)) (hΔ : Closed S Δ (.num k))
    (hd : Γ.dom ⊆ Δ.dom) : Closed S Δ e₂ := by
  intro z hz
  rcases Finset.mem_union.mp hz with h | h
  · exact hΔ (Finset.mem_union_left _ h)
  · exact Finset.union_subset_union (Finset.Subset.refl _) hd
      (hc (Finset.mem_union_right _ (by simp [Expr.fv, h])))

/-- A heap is closed with one numeral exactly when it is closed with any other. -/
private theorem closed_num {V : Type u} [DecidableEq V] {S : Finset V} {Θ : Heap V} {k k' : ℕ}
    (hc : Closed S Θ (.num k)) : Closed S Θ (.num k') := by
  simpa [Closed, Expr.fv] using hc

/-- If `Eval A Γ e Δ w n`, closedness is preserved, with respect to any set `S`: if every free
name of `Γ` and `e` is bound in `Γ` or lies in `S`, then every free name of `Δ` and `w` is bound
in `Δ` or lies in `S`. -/
theorem Eval.closed {V : Type u} [DecidableEq V] {A : Finset V} {Γ Δ : Heap V}
    {e w : Expr V} {n : ℕ} (h : Eval A Γ e Δ w n) {S : Finset V} (hc : Closed S Γ e) :
    Closed S Δ w := by
  induction h generalizing S with
  | lam => exact hc
  | num => exact hc
  | app h₁ _ ih₁ ih₂ =>
    exact ih₂ (closed_subst_one (ih₁ (closed_app_fun hc))
      (Finset.union_subset_union (Finset.Subset.refl _) h₁.dom_subset (closed_app_arg hc)))
  | var hl _ ih => exact closed_var_result (ih (closed_var hl hc))
  | letrec _ _ _ hlen _ _ ih => exact ih (closed_letrec hlen hc)
  | add h₁ _ ih₁ ih₂ =>
    exact closed_num (ih₂ (closed_add_arg hc (ih₁ (closed_add_fun hc)) h₁.dom_subset))

/-- Looking up a renamed name in a renamed heap renames the result. -/
private theorem heap_lookup_map {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) (x : V) :
    ∀ Γ : Heap V, (Γ.map f).lookup (f x) = (Γ.lookup x).map (Expr.map f)
  | [] => rfl
  | (k, d) :: Γ => by
    unfold Heap.map Heap.lookup at *
    simp only [List.map_cons, List.lookup_cons]
    by_cases hxk : x = k
    · subst hxk
      simp
    · have hb : (x == k) = false := by simpa using hxk
      have hb' : (f x == f k) = false := by simpa using fun h => hxk (hf h)
      rw [hb, hb']
      exact heap_lookup_map hf x Γ

/-- Renaming commutes with erasing a name. -/
private theorem heap_erase_map {V : Type u} [DecidableEq V] {f : V → V}
    (hf : Function.Injective f) (Γ : Heap V) (x : V) :
    (Γ.erase x).map f = (Γ.map f).erase (f x) := by
  unfold Heap.erase Heap.map
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro b _
  simp only [Function.comp_apply, ne_eq, hf.eq_iff]

/-- The names of a renamed heap are the images of its names. -/
private theorem heap_names_map {V : Type u} [DecidableEq V] (f : V → V) :
    ∀ Γ : Heap V, (Γ.map f).names = Γ.names.image f
  | [] => rfl
  | b :: Γ => by
    have ih := heap_names_map f Γ
    unfold Heap.map at ih ⊢
    simp only [List.map_cons, Heap.names, ih, Expr.names_map, Finset.image_insert,
      Finset.image_union]

/-- Renaming bindings renames their bound names. -/
private theorem vars_map' {V : Type u} (f : V → V) :
    ∀ bs : Binds V, (bs.map f).vars = bs.vars.map f
  | .nil => rfl
  | .cons x e bs => by rw [Binds.map, Binds.vars, Binds.vars, vars_map' f bs, List.map_cons]

/-- Renaming bindings renames their right-hand sides. -/
private theorem exprs_map {V : Type u} (f : V → V) :
    ∀ bs : Binds V, (bs.map f).exprs = bs.exprs.map (Expr.map f)
  | .nil => rfl
  | .cons x e bs => by rw [Binds.map, Binds.exprs, Binds.exprs, exprs_map f bs, List.map_cons]

/-- Allocating renamed bindings under renamed names renames the allocated heap. -/
private theorem alloc_map {V : Type u} [DecidableEq V] {f : V → V} (hf : Function.Injective f)
    (bs : Binds V) (ps : List V) : (bs.alloc ps).map f = (bs.map f).alloc (ps.map f) := by
  unfold Binds.alloc Heap.map
  rw [exprs_map, vars_map', List.zip_map, List.zip_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro b _
  simp [Expr.map_subst hf]

/-- Evaluation is invariant under permutations of names: renaming every name of a derivation
by a permutation `π` gives a derivation, with the same number of additions. -/
theorem Eval.map {V : Type u} [DecidableEq V] {A : Finset V} {Γ Δ : Heap V}
    {e w : Expr V} {n : ℕ} (h : Eval A Γ e Δ w n) (π : Equiv.Perm V) :
    Eval (A.image π) (Γ.map π) (e.map π) (Δ.map π) (w.map π) n := by
  induction h with
  | lam => exact .lam
  | num => exact .num
  | @app A Γ Δ Θ e e' w y p n₁ n₂ _ _ ih₁ ih₂ =>
    have h₂ : Eval (A.image π) (Δ.map π) ((e'.map π).subst [(π y, π p)]) (Θ.map π) (w.map π)
        n₂ := by
      have hs := Expr.map_subst π.injective [(y, p)] e'
      simp only [List.map_cons, List.map_nil, Prod.map_apply] at hs
      rw [← hs]
      exact ih₂
    exact .app ih₁ h₂
  | @var A Γ Δ x e w n hl _ ih =>
    have hl' : (Γ.map π).lookup (π x) = some (e.map π) := by
      rw [heap_lookup_map π.injective, hl]
      rfl
    rw [Finset.image_insert, heap_erase_map π.injective] at ih
    exact .var hl' ih
  | @letrec A Γ Δ bs e w n ps hv hps hlen hfresh _ ih =>
    refine .letrec (ps.map π) ?_ (hps.map π.injective) ?_ ?_ ?_
    · rw [vars_map']
      exact hv.map π.injective
    · rw [vars_map', List.length_map, List.length_map, hlen]
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨h₁, h₂, h₃⟩ := hfresh p hp
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.mem_image]
        rintro ⟨a, ha, hpa⟩
        exact h₁ (π.injective hpa ▸ ha)
      · rw [heap_names_map, Finset.mem_image]
        rintro ⟨a, ha, hpa⟩
        exact h₂ (π.injective hpa ▸ ha)
      · change π p ∉ ((Expr.letrec bs e).map π).names
        rw [Expr.names_map, Finset.mem_image]
        rintro ⟨a, ha, hpa⟩
        exact h₃ (π.injective hpa ▸ ha)
    · have hσ : (bs.vars.zip ps).map (Prod.map π π) = (bs.map π).vars.zip (ps.map π) := by
        rw [vars_map', List.zip_map]
      have ih' := ih
      unfold Heap.map at ih'
      rw [List.map_append] at ih'
      rw [← Heap.map, ← Heap.map, alloc_map π.injective, Expr.map_subst π.injective, hσ] at ih'
      exact ih'
  | @add A Γ Δ Θ e₁ e₂ k₁ k₂ n₁ n₂ _ _ ih₁ ih₂ =>
    rw [Finset.image_union, ← Expr.names_map] at ih₁
    exact .add ih₁ ih₂

/-- Two duplicate-free lists of the same length, both avoiding a finite set `F`, are aligned by a
permutation that fixes every name of `F`: a product of swaps, built from the end of the lists. -/
private theorem exists_perm_align {V : Type u} (F : Finset V) :
    ∀ (ps qs : List V), ps.Nodup → qs.Nodup → ps.length = qs.length →
      (∀ p ∈ ps, p ∉ F) → (∀ q ∈ qs, q ∉ F) →
      ∃ τ : Equiv.Perm V, ps.map τ = qs ∧ ∀ x ∈ F, τ x = x
  | [], [], _, _, _, _, _ => ⟨Equiv.refl V, rfl, fun _ _ => rfl⟩
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp)
  | p :: ps, q :: qs, hp, hq, hl, hpF, hqF => by
    classical
    obtain ⟨hp₁, hp₂⟩ := List.nodup_cons.mp hp
    obtain ⟨hq₁, hq₂⟩ := List.nodup_cons.mp hq
    obtain ⟨τ, hτ, hF⟩ := exists_perm_align F ps qs hp₂ hq₂ (by simpa using hl)
      (fun a ha => hpF a (List.mem_cons_of_mem _ ha))
      (fun a ha => hqF a (List.mem_cons_of_mem _ ha))
    refine ⟨τ.trans (Equiv.swap (τ p) q), ?_, ?_⟩
    · simp only [List.map_cons, Equiv.trans_apply, Equiv.swap_apply_left]
      congr 1
      rw [← hτ]
      apply List.map_congr_left
      intro a ha
      apply Equiv.swap_apply_of_ne_of_ne
      · exact fun h => hp₁ (τ.injective h ▸ ha)
      · intro h
        apply hq₁
        rw [← h, ← hτ]
        exact List.mem_map_of_mem ha
    · intro x hx
      rw [Equiv.trans_apply, hF x hx]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        apply hpF p List.mem_cons_self
        have : τ p = τ x := by rw [hF x hx]; exact h.symm
        exact τ.injective this ▸ hx
      · intro h
        exact hqF q List.mem_cons_self (h ▸ hx)

/-- The names bound by bindings occur in them. -/
private theorem vars_subset_names {V : Type u} [DecidableEq V] :
    ∀ bs : Binds V, ∀ x ∈ bs.vars, x ∈ bs.names
  | .nil, x, hx => by simp [Binds.vars] at hx
  | .cons y d bs, x, hx => by
    simp only [Binds.vars, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Binds.names]
    · simp [Binds.names, vars_subset_names bs x hx]

/-- Renaming an expression by a permutation and then by its inverse changes nothing. -/
private theorem map_symm_map {V : Type u} (π : Equiv.Perm V) (e : Expr V) :
    (e.map π).map π.symm = e := by
  rw [Expr.map_comp]
  have : (⇑π.symm ∘ ⇑π) = id := funext π.symm_apply_apply
  rw [this, Expr.map_id]

/-- Renaming a heap twice. -/
private theorem heap_map_comp {V : Type u} (f g : V → V) (Γ : Heap V) :
    (Γ.map f).map g = Γ.map (g ∘ f) := by
  unfold Heap.map
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  simp [Expr.map_comp]

/-- Renaming a heap by the identity changes nothing. -/
private theorem heap_map_id {V : Type u} (Γ : Heap V) : Γ.map id = Γ := by
  unfold Heap.map
  conv_rhs => rw [← List.map_id Γ]
  apply List.map_congr_left
  intro b _
  simp [Expr.map_id]

/-- Renaming a heap by a permutation and then by its inverse changes nothing. -/
private theorem heap_map_symm_map {V : Type u} (π : Equiv.Perm V) (Γ : Heap V) :
    (Γ.map π).map π.symm = Γ := by
  rw [heap_map_comp]
  have : (⇑π.symm ∘ ⇑π) = id := funext π.symm_apply_apply
  rw [this, heap_map_id]

/-- A function fixing every name of a heap renames it to itself. -/
private theorem heap_map_eq_self {V : Type u} [DecidableEq V] {f : V → V} :
    ∀ {Γ : Heap V}, (∀ x ∈ Γ.names, f x = x) → Γ.map f = Γ
  | [], _ => rfl
  | (x, d) :: Γ, h => by
    have hx := h x (by simp [Heap.names])
    have hd := Expr.map_eq_self (e := d) fun y hy => h y (by simp [Heap.names, hy])
    have hΓ := heap_map_eq_self (Γ := Γ) fun y hy => h y (by simp [Heap.names, hy])
    unfold Heap.map at hΓ ⊢
    simp only [List.map_cons, hx, hd, hΓ]

/-- The inverse of a permutation that fixes every name of a set fixes the set. -/
private theorem image_symm_eq {V : Type u} [DecidableEq V] {π : Equiv.Perm V} {A : Finset V}
    (h : ∀ x ∈ A, π x = x) : A.image π.symm = A := by
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hs : π.symm x = x := by rw [Equiv.symm_apply_eq, h x hx]
    rw [hs]
    exact hx
  · intro hy
    exact ⟨y, hy, by rw [Equiv.symm_apply_eq, h y hy]⟩

/-- The renaming of a heap by a composite permutation, undone by the outer factor. -/
private theorem heap_eq_map_trans {V : Type u} {π₁ π₂ : Equiv.Perm V} {Θ Θ' : Heap V}
    (h : Θ'.map π₁.symm = Θ.map π₂) : Θ' = Θ.map (π₂.trans π₁) := by
  have h' := congrArg (Heap.map π₁) h
  rw [heap_map_comp, show (⇑π₁ ∘ ⇑π₁.symm) = id from funext π₁.apply_symm_apply, heap_map_id,
    heap_map_comp] at h'
  rw [h']
  rfl

/-- The renaming of an expression by a composite permutation, undone by the outer factor. -/
private theorem expr_eq_map_trans {V : Type u} {π₁ π₂ : Equiv.Perm V} {w w' : Expr V}
    (h : w'.map π₁.symm = w.map π₂) : w' = w.map (π₂.trans π₁) := by
  have h' := congrArg (Expr.map π₁) h
  rw [Expr.map_comp, show (⇑π₁ ∘ ⇑π₁.symm) = id from funext π₁.apply_symm_apply, Expr.map_id,
    Expr.map_comp] at h'
  rw [h']
  rfl

/-- Evaluation is deterministic up to renaming of new names. If a configuration is closed with
respect to `A`, then any two of its evaluations perform the same number of additions, and a
permutation fixing every name of `A` and every name bound in `Γ` maps the final heap and value
of the first evaluation to those of the second. Without closedness this fails: a free name
bound neither in the heap nor in `A` can collide with a new name. -/
theorem Eval.unique_up_to_renaming {V : Type u} [DecidableEq V] {A : Finset V}
    {Γ Δ₁ Δ₂ : Heap V} {e w₁ w₂ : Expr V} {n₁ n₂ : ℕ} (h₁ : Eval A Γ e Δ₁ w₁ n₁)
    (h₂ : Eval A Γ e Δ₂ w₂ n₂) (hc : Closed A Γ e) :
    n₁ = n₂ ∧ ∃ π : Equiv.Perm V, (∀ x ∈ A ∪ Γ.dom, π x = x) ∧ Δ₂ = Δ₁.map π ∧
      w₂ = w₁.map π := by
  induction h₁ generalizing Δ₂ w₂ n₂ with
  | lam =>
    cases h₂
    refine ⟨rfl, Equiv.refl V, fun _ _ => rfl, ?_, ?_⟩
    · rw [Equiv.coe_refl, heap_map_id]
    · rw [Equiv.coe_refl, Expr.map_id]
  | num =>
    cases h₂
    refine ⟨rfl, Equiv.refl V, fun _ _ => rfl, ?_, ?_⟩
    · rw [Equiv.coe_refl, heap_map_id]
    · rw [Equiv.coe_refl, Expr.map_id]
  | @app A Γ Δ Θ e e' w y p n₁ n₂ h₁a h₁b ih₁ ih₂ =>
    cases h₂ with
    | app h₂a h₂b =>
      obtain ⟨hn₁, π₁, hπ₁, rfl, hlam⟩ := ih₁ h₂a (closed_app_fun hc)
      simp only [Expr.map, Expr.lam.injEq] at hlam
      obtain ⟨rfl, rfl⟩ := hlam
      have hp : π₁ p = p := hπ₁ p (closed_app_arg hc)
      have hA : A.image π₁.symm = A := image_symm_eq fun x hx => hπ₁ x (Finset.mem_union_left _ hx)
      have h₂b' := Eval.map h₂b π₁.symm
      have hs := Expr.map_subst π₁.symm.injective [(π₁ y, p)] (e'.map π₁)
      simp only [List.map_cons, List.map_nil, Prod.map_apply, Equiv.symm_apply_apply,
        map_symm_map] at hs
      rw [hA, heap_map_symm_map, hs, show π₁.symm p = p by rw [Equiv.symm_apply_eq, hp]] at h₂b'
      have hcl : Closed A Δ (e'.subst [(y, p)]) :=
        closed_subst_one (h₁a.closed (closed_app_fun hc))
          (Finset.union_subset_union (Finset.Subset.refl _) h₁a.dom_subset (closed_app_arg hc))
      obtain ⟨hn₂, π₂, hπ₂, hΘ, hw⟩ := ih₂ h₂b' hcl
      refine ⟨by rw [hn₁, hn₂], π₂.trans π₁, ?_, heap_eq_map_trans hΘ, expr_eq_map_trans hw⟩
      intro x hx
      have hx' : x ∈ A ∪ Δ.dom :=
        Finset.union_subset_union (Finset.Subset.refl _) h₁a.dom_subset hx
      rw [Equiv.trans_apply, hπ₂ x hx', hπ₁ x hx]
  | @var A Γ Δ x e w n hl h₁' ih =>
    cases h₂ with
    | var hl₂ h₂' =>
      rw [hl] at hl₂
      obtain rfl := Option.some.inj hl₂
      obtain ⟨hn, π, hπ, rfl, rfl⟩ := ih h₂' (closed_var hl hc)
      have hx : π x = x := hπ x (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
      refine ⟨hn, π, fun z hz => hπ z ?_, ?_, rfl⟩
      · rcases Finset.mem_union.mp hz with h | h
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
        · rcases Finset.mem_insert.mp (heap_dom_subset_insert_erase Γ x h) with rfl | h'
          · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ h'
      · unfold Heap.map
        rw [List.map_cons, hx]
  | @letrec A Γ Δ bs e w n ps hv hps hlen hfresh h₁' ih =>
    cases h₂ with
    | letrec qs _ hqs hlen₂ hfresh₂ h₂' =>
      obtain ⟨τ, hτ, hτF⟩ := exists_perm_align (A ∪ Γ.names ∪ (Expr.letrec bs e).names) ps qs
        hps hqs (hlen.trans hlen₂.symm)
        (fun a ha => by
          obtain ⟨h₁, h₂, h₃⟩ := hfresh a ha
          simp [h₁, h₂, h₃])
        (fun a ha => by
          obtain ⟨h₁, h₂, h₃⟩ := hfresh₂ a ha
          simp [h₁, h₂, h₃])
      have hfix : ∀ x, x ∈ A ∪ Γ.names ∪ (Expr.letrec bs e).names → τ.symm x = x := fun x hx => by
        rw [Equiv.symm_apply_eq, hτF x hx]
      have hqs' : qs.map τ.symm = ps := by
        rw [← hτ, List.map_map]
        conv_rhs => rw [← List.map_id ps]
        apply List.map_congr_left
        intro a _
        simp
      have hbs : bs.map τ.symm = bs :=
        Binds.map_eq_self fun x hx => hfix x (by simp [Expr.names, hx])
      have he : e.map τ.symm = e :=
        Expr.map_eq_self fun x hx => hfix x (by simp [Expr.names, hx])
      have hΓ : Γ.map τ.symm = Γ := heap_map_eq_self fun x hx => hfix x (by simp [hx])
      have hvars : bs.vars.map τ.symm = bs.vars := by
        conv_rhs => rw [← List.map_id bs.vars]
        apply List.map_congr_left
        intro x hx
        apply hfix
        simp [Expr.names, vars_subset_names bs x hx]
      have h₂'' := Eval.map h₂' τ.symm
      have hA : A.image τ.symm = A := image_symm_eq fun x hx => hτF x (by simp [hx])
      have hal : (bs.alloc qs).map τ.symm = bs.alloc ps := by
        rw [alloc_map τ.symm.injective, hbs, hqs']
      have hsub : (e.subst (bs.vars.zip qs)).map τ.symm = e.subst (bs.vars.zip ps) := by
        rw [Expr.map_subst τ.symm.injective, he, ← List.zip_map, hvars, hqs']
      unfold Heap.map at h₂''
      rw [List.map_append, ← Heap.map, ← Heap.map, hal, hΓ, hsub, hA] at h₂''
      obtain ⟨hn, π, hπ, hΔ, hw⟩ := ih h₂'' (closed_letrec hlen hc)
      refine ⟨hn, π.trans τ, ?_, heap_eq_map_trans ?_, expr_eq_map_trans ?_⟩
      · intro x hx
        have hx₁ : x ∈ A ∪ (bs.alloc ps ++ Γ).dom := by
          rw [heap_dom_append]
          rcases Finset.mem_union.mp hx with h | h
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
        have hx₂ : x ∈ A ∪ Γ.names ∪ (Expr.letrec bs e).names := by
          rcases Finset.mem_union.mp hx with h | h
          · simp [h]
          · simp [heap_dom_subset_names Γ h]
        rw [Equiv.trans_apply, hπ x hx₁, hτF x hx₂]
      · exact hΔ
      · exact hw
  | @add A Γ Δ Θ e₁ e₂ k₁ k₂ n₁ n₂ h₁a h₁b ih₁ ih₂ =>
    cases h₂ with
    | add h₂a h₂b =>
      obtain ⟨hn₁, π₁, hπ₁, rfl, hk₁⟩ :=
        ih₁ h₂a (closed_mono Finset.subset_union_left (closed_add_fun hc))
      simp only [Expr.map, Expr.num.injEq] at hk₁
      subst hk₁
      have hA : A.image π₁.symm = A :=
        image_symm_eq fun x hx => hπ₁ x (by simp [hx])
      have he₂ : e₂.map π₁.symm = e₂ := Expr.map_eq_self fun x hx => by
        rw [Equiv.symm_apply_eq, hπ₁ x (by simp [hx])]
      have h₂b' := Eval.map h₂b π₁.symm
      rw [hA, heap_map_symm_map, he₂] at h₂b'
      have hcl : Closed A Δ e₂ :=
        closed_add_arg hc (h₁a.closed (closed_add_fun hc)) h₁a.dom_subset
      obtain ⟨hn₂, π₂, hπ₂, hΘ, hk₂⟩ := ih₂ h₂b' hcl
      simp only [Expr.map, Expr.num.injEq] at hk₂
      subst hk₂
      refine ⟨by rw [hn₁, hn₂], π₂.trans π₁, ?_, heap_eq_map_trans hΘ, rfl⟩
      intro x hx
      have hx' : x ∈ A ∪ Δ.dom :=
        Finset.union_subset_union (Finset.Subset.refl _) h₁a.dom_subset hx
      have hx'' : x ∈ A ∪ e₂.names ∪ Γ.dom := by
        rcases Finset.mem_union.mp hx with h | h
        · simp [h]
        · simp [h]
      rw [Equiv.trans_apply, hπ₂ x hx', hπ₁ x hx'']

end Cslib.Languages.LambdaCalculus.CallByNeed
