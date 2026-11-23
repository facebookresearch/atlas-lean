/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reduced ordered binary decision diagrams: canonicity and apply
-/
module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

/-!
# Reduced ordered binary decision diagrams: canonicity and apply

A binary decision diagram tests variables and ends in Boolean leaves.  It is
*ordered* when the tested variables strictly increase along every path and
*reduced* when no node has two equal children.  Bryant's canonicity theorem
says that, for a fixed variable order, two reduced ordered BDDs denoting the
same Boolean function are identical.  Bryant's `apply` combines two such BDDs
under a binary Boolean operation and returns one again.

Diagrams are represented as trees (`BDD`), so shared subgraphs appear unfolded.
A DAG is reduced in Bryant's sense (no redundant test and no two isomorphic
subgraphs) exactly when its unfolding is reduced here and the DAG has maximal
sharing; isomorphic DAGs have equal unfoldings.  The tree form therefore
captures canonicity, but not the size of the shared representation: `apply`
below has no memo table and no cost bound is claimed.

## Main definitions

- `BDD.eval σ t` : the value of the diagram under the assignment `σ`.
- `BDD.OrderedFrom n t` : every tested variable is at least `n`, and variables
  strictly increase along every path.
- `BDD.Reduced t` : no node has equal children.  `BDD.IsROBDD t` combines the
  two (variables from `0`).
- `BDD.mk v lo hi` : the node constructor that removes a redundant test.
- `BDD.apply op t₁ t₂` : Bryant's apply for a binary Boolean operation `op`.
- `BDD.ofProposition A` : the ROBDD of an upstream CSLib proposition over
  `Nat` atoms, built by `apply`.

## Main results

- `BDD.eq_of_eval_eq` (canonicity): reduced ordered diagrams with the same
  function are equal.
- `BDD.eval_apply`, `BDD.orderedFrom_apply`, `BDD.reduced_apply`: `apply`
  computes `op` pointwise and preserves reduced orderedness.
- `BDD.eval_ofProposition`, `BDD.isROBDD_ofProposition`, and
  `BDD.ofProposition_eq_iff`: two propositions have the same truth table iff
  their ROBDDs are equal.
- `BDD.eq_leaf_false_iff`: a reduced ordered diagram is unsatisfiable iff it
  is the leaf `false`.

## References

- R. E. Bryant, *Graph-based algorithms for Boolean function manipulation*,
  IEEE Trans. Computers C-35(8), 1986, 677-691.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.PL

/-- **Binary decision diagram.** A binary decision diagram, in tree form, is either a leaf
carrying a Boolean value, or a node consisting of a variable $v \in \mathbb{N}$ and two
diagrams: the low child, for $v$ false, and the high child, for $v$ true. -/
inductive BDD where
  | leaf (b : Bool)
  | node (v : Nat) (lo hi : BDD)
  deriving DecidableEq, Repr

namespace BDD

/-- **Evaluation of a binary decision diagram.** Under an assignment $\sigma$ of a Boolean value
to each variable $v \in \mathbb{N}$, the value of a leaf is its Boolean value, and the value of a
node testing $v$ is the value of its high child if $\sigma(v)$ is true and the value of its low
child if $\sigma(v)$ is false. -/
def eval (σ : Nat → Bool) : BDD → Bool
  | leaf b => b
  | node v lo hi => if σ v then hi.eval σ else lo.eval σ

@[simp] theorem eval_leaf (σ : Nat → Bool) (b : Bool) : (leaf b).eval σ = b := rfl

@[simp] theorem eval_node (σ : Nat → Bool) (v : Nat) (lo hi : BDD) :
    (node v lo hi).eval σ = if σ v then hi.eval σ else lo.eval σ := rfl

/-- **Size of a diagram.** The size of a diagram is its number of leaves and nodes, counted in
tree form: a leaf has size $1$, and a node with children $\ell$ and $h$ has size one more than the
sum of the sizes of $\ell$ and $h$. -/
def size : BDD → Nat
  | leaf _ => 1
  | node _ lo hi => lo.size + hi.size + 1

/-- **Diagrams ordered from a variable.** For a natural number $n$, a diagram is ordered from
$n$ when every variable it tests is at least $n$ and the tested variables strictly increase
along every path. Recursively: every leaf is ordered from $n$, and the node testing $v$ with
children $\ell$ and $h$ is ordered from $n$ when $n \le v$ and both $\ell$ and $h$ are ordered
from $v + 1$. -/
def OrderedFrom : Nat → BDD → Prop
  | _, leaf _ => True
  | n, node v lo hi => n ≤ v ∧ OrderedFrom (v + 1) lo ∧ OrderedFrom (v + 1) hi

/-- **Reduced diagrams.** A diagram is reduced when no node in it has two equal children: every
leaf is reduced, and the node testing $v$ with children $\ell$ and $h$ is reduced when
$\ell \ne h$ and both $\ell$ and $h$ are reduced. -/
def Reduced : BDD → Prop
  | leaf _ => True
  | node _ lo hi => lo ≠ hi ∧ Reduced lo ∧ Reduced hi

/-- **Reduced ordered binary decision diagram.** A binary decision diagram is a reduced ordered
binary decision diagram (ROBDD), for the natural order on variables, when it is ordered from
$0$ (the tested variables strictly increase along every path) and reduced (no node has two
equal children). -/
def IsROBDD (t : BDD) : Prop := OrderedFrom 0 t ∧ Reduced t

theorem OrderedFrom.mono {m n : Nat} {t : BDD} (h : OrderedFrom n t) (hmn : m ≤ n) :
    OrderedFrom m t := by
  cases t with
  | leaf b => trivial
  | node v lo hi => exact ⟨hmn.trans h.1, h.2⟩

/-! ### Independence from variables below the order -/

/-- **Independence from variables below the order.** Let $t$ be a binary decision diagram
ordered from $n \in \mathbb{N}$ and let $v < n$ be a variable. For every assignment $\sigma$ of
Boolean values to the variables and every Boolean $b$, the value of $t$ under
$\sigma[v \mapsto b]$ (the assignment $\sigma$ with $v$ set to $b$) equals the value of $t$ under
$\sigma$. -/
theorem eval_update_of_lt {n v : Nat} {t : BDD} (h : OrderedFrom n t) (hv : v < n)
    (σ : Nat → Bool) (b : Bool) : t.eval (Function.update σ v b) = t.eval σ := by
  induction t generalizing n with
  | leaf c => rfl
  | node w lo hi ihlo ihhi =>
    obtain ⟨hw, hlo, hhi⟩ := h
    have hvw : w ≠ v := by omega
    simp only [eval_node, Function.update_of_ne hvw, ihlo hlo (by omega), ihhi hhi (by omega)]

/-- **Fixing the top variable of an ordered node.** Let $t$ be a node testing the variable $v$
with low child $\ell$ and high child $h$, and suppose $t$ is ordered from some $n \in \mathbb{N}$.
For every assignment $\sigma$ of Boolean values to the variables and every Boolean $b$, the value
of $t$ under $\sigma[v \mapsto b]$ (the assignment $\sigma$ with $v$ set to $b$) is the value of
$h$ under $\sigma$ if $b$ is true, and the value of $\ell$ under $\sigma$ if $b$ is false. -/
theorem eval_update_node {n v : Nat} {lo hi : BDD} (h : OrderedFrom n (node v lo hi))
    (σ : Nat → Bool) (b : Bool) :
    (node v lo hi).eval (Function.update σ v b) = if b then hi.eval σ else lo.eval σ := by
  rw [eval_node, Function.update_self, eval_update_of_lt h.2.2 (by omega),
    eval_update_of_lt h.2.1 (by omega)]

/-! ### Canonicity -/

/-- **Binary decision diagrams have positive size.** For every binary decision diagram $t$,
the size of $t$ (its number of leaves and nodes, counted in tree form) is strictly positive. -/
theorem size_pos (t : BDD) : 0 < t.size := by
  cases t <;> simp [size]

/-- **Canonicity** (Bryant): two reduced ordered diagrams with the same function are
equal. -/
theorem eq_of_eval_eq {n₁ n₂ : Nat} {t₁ t₂ : BDD} (ho₁ : OrderedFrom n₁ t₁) (hr₁ : Reduced t₁)
    (ho₂ : OrderedFrom n₂ t₂) (hr₂ : Reduced t₂) (heq : ∀ σ, t₁.eval σ = t₂.eval σ) :
    t₁ = t₂ := by
  induction hs : t₁.size + t₂.size using Nat.strong_induction_on generalizing n₁ n₂ t₁ t₂ with
  | _ s ih =>
  subst hs
  -- a reduced ordered node whose function ignores its top variable is impossible
  have absurd_node : ∀ {m v : Nat} {lo hi : BDD}, OrderedFrom m (node v lo hi) →
      Reduced (node v lo hi) → lo.size + hi.size < t₁.size + t₂.size →
      (∀ σ, (node v lo hi).eval (Function.update σ v false) =
        (node v lo hi).eval (Function.update σ v true)) → False := by
    intro m v lo hi ho hr hlt hind
    refine hr.1 (ih _ hlt ho.2.1 hr.2.1 ho.2.2 hr.2.2 (fun σ ↦ ?_) rfl)
    simpa [eval_update_node ho] using hind σ
  cases t₁ with
  | leaf a =>
    cases t₂ with
    | leaf b => simpa using heq (fun _ ↦ false)
    | node w lo hi =>
      exact (absurd_node ho₂ hr₂ (by simp [size]; omega) fun σ ↦ by
        rw [← heq, ← heq]; rfl).elim
  | node v lo hi =>
    cases t₂ with
    | leaf b =>
      exact (absurd_node ho₁ hr₁ (by simp [size]; omega) fun σ ↦ by
        rw [heq, heq]; rfl).elim
    | node w lo' hi' =>
      rcases lt_trichotomy v w with hvw | rfl | hwv
      · -- `t₂` does not test `v`
        have ho₂' : OrderedFrom (v + 1) (node w lo' hi') := ⟨hvw, ho₂.2⟩
        exact (absurd_node ho₁ hr₁ (by simp [size]; omega) fun σ ↦ by
          rw [heq, heq, eval_update_of_lt ho₂' (by omega), eval_update_of_lt ho₂' (by omega)]).elim
      · have hlo : lo = lo' := ih _ (by simp [size]; omega) ho₁.2.1 hr₁.2.1 ho₂.2.1 hr₂.2.1
          (fun σ ↦ by
            have := heq (Function.update σ v false)
            rwa [eval_update_node ho₁, eval_update_node ho₂] at this) rfl
        have hhi : hi = hi' := ih _ (by simp [size]; omega) ho₁.2.2 hr₁.2.2 ho₂.2.2 hr₂.2.2
          (fun σ ↦ by
            have := heq (Function.update σ v true)
            rwa [eval_update_node ho₁, eval_update_node ho₂] at this) rfl
        rw [hlo, hhi]
      · have ho₁' : OrderedFrom (w + 1) (node v lo hi) := ⟨hwv, ho₁.2⟩
        exact (absurd_node ho₂ hr₂ (by simp [size]; omega) fun σ ↦ by
          rw [← heq, ← heq, eval_update_of_lt ho₁' (by omega),
            eval_update_of_lt ho₁' (by omega)]).elim

/-- **Reduced ordered diagrams are equal iff they have the same values.** If $t_1$ and $t_2$ are
reduced ordered binary decision diagrams, then $t_1 = t_2$ if and only if $t_1$ and $t_2$ have
the same value under every assignment of Boolean values to the variables. -/
theorem eq_iff_eval_eq {t₁ t₂ : BDD} (h₁ : IsROBDD t₁) (h₂ : IsROBDD t₂) :
    t₁ = t₂ ↔ ∀ σ, t₁.eval σ = t₂.eval σ :=
  ⟨fun h _ ↦ h ▸ rfl, eq_of_eval_eq h₁.1 h₁.2 h₂.1 h₂.2⟩

/-- **Unsatisfiable reduced ordered diagrams.** A reduced ordered binary decision diagram $t$ is
the leaf with value false if and only if $t$ has value false under every assignment of Boolean
values to the variables. -/
theorem eq_leaf_false_iff {t : BDD} (h : IsROBDD t) :
    t = leaf false ↔ ∀ σ, t.eval σ = false :=
  eq_iff_eval_eq h ⟨trivial, trivial⟩

/-! ### Building reduced diagrams -/

/-- **Node constructor removing a redundant test.** For a variable $v \in \mathbb{N}$ and diagrams
$\ell$ and $h$, the diagram $\mathrm{mk}(v, \ell, h)$ is $\ell$ if $\ell = h$, and otherwise the
node that tests $v$ with $\ell$ as its false-child and $h$ as its true-child. -/
def mk (v : Nat) (lo hi : BDD) : BDD := if lo = hi then lo else node v lo hi

@[simp] theorem eval_mk (σ : Nat → Bool) (v : Nat) (lo hi : BDD) :
    (mk v lo hi).eval σ = if σ v then hi.eval σ else lo.eval σ := by
  unfold mk
  split
  · next h => subst h; split <;> rfl
  · rfl

theorem orderedFrom_mk {n v : Nat} {lo hi : BDD} (hv : n ≤ v) (hlo : OrderedFrom (v + 1) lo)
    (hhi : OrderedFrom (v + 1) hi) : OrderedFrom n (mk v lo hi) := by
  unfold mk
  split
  · exact hlo.mono (by omega)
  · exact ⟨hv, hlo, hhi⟩

theorem reduced_mk {v : Nat} {lo hi : BDD} (hlo : Reduced lo) (hhi : Reduced hi) :
    Reduced (mk v lo hi) := by
  unfold mk
  split
  · exact hlo
  · next h => exact ⟨h, hlo, hhi⟩

/-- **Bryant's apply operation.** For a binary Boolean operation $\mathrm{op}$ and binary decision
diagrams $t_1, t_2$, the diagram $A_{\mathrm{op}}(t_1, t_2)$ is defined by recursion. If $t_1$
and $t_2$ are leaves with values $a$ and $b$, it is the leaf with value $\mathrm{op}(a, b)$.
Otherwise let $v$ be the smallest variable tested at the root of $t_1$ or of $t_2$ (a leaf tests
none), and for $i = 1, 2$ let $\ell_i$ and $h_i$ be the low and high children of $t_i$ if its
root tests $v$, and $\ell_i = h_i = t_i$ otherwise. The result is
$\mathrm{mk}(v, A_{\mathrm{op}}(\ell_1, \ell_2), A_{\mathrm{op}}(h_1, h_2))$, where
$\mathrm{mk}(v, \ell, h)$ is $\ell$ if $\ell = h$, and otherwise the node testing $v$ with low
child $\ell$ and high child $h$. -/
def apply (op : Bool → Bool → Bool) : BDD → BDD → BDD
  | leaf a, leaf b => leaf (op a b)
  | leaf a, node w lo hi => mk w (apply op (leaf a) lo) (apply op (leaf a) hi)
  | node v lo hi, leaf b => mk v (apply op lo (leaf b)) (apply op hi (leaf b))
  | node v lo hi, node w lo' hi' =>
    if v = w then mk v (apply op lo lo') (apply op hi hi')
    else if v < w then mk v (apply op lo (node w lo' hi')) (apply op hi (node w lo' hi'))
    else mk w (apply op (node v lo hi) lo') (apply op (node v lo hi) hi')

/-- **Apply computes the operation pointwise.** For every binary Boolean operation
$\mathrm{op}$, all binary decision diagrams $t_1$ and $t_2$, and every assignment $\sigma$ of
Boolean values to the variables, the value under $\sigma$ of the diagram
$\mathrm{apply}(\mathrm{op}, t_1, t_2)$ obtained from $t_1$ and $t_2$ by Bryant's apply operation
under $\mathrm{op}$ is $\mathrm{op}(a_1, a_2)$, where $a_i$ is the value of $t_i$ under $\sigma$. -/
theorem eval_apply (op : Bool → Bool → Bool) (t₁ t₂ : BDD) (σ : Nat → Bool) :
    (apply op t₁ t₂).eval σ = op (t₁.eval σ) (t₂.eval σ) := by
  induction t₁, t₂ using apply.induct with
  | case1 a b => simp [apply]
  | case2 b v lo hi ihlo ihhi =>
    simp only [apply, eval_mk, ihlo, ihhi, eval_node]
    cases σ v <;> simp
  | case3 v lo hi b ihlo ihhi =>
    simp only [apply, eval_mk, ihlo, ihhi, eval_node]
    cases σ v <;> simp
  | case4 lo hi v lo' hi' ihlo ihhi =>
    simp only [apply, ↓reduceIte, eval_mk, ihlo, ihhi, eval_node]
    cases σ v <;> simp
  | case5 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte, eval_mk, ihlo, ihhi, eval_node]
    cases σ v <;> simp
  | case6 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte, eval_mk, ihlo, ihhi, eval_node]
    cases σ w <;> simp

/-- **Apply preserves orderedness.** Let $\mathrm{op}$ be a binary Boolean operation and $n$ a
natural number. If the diagrams $t_1$ and $t_2$ are both ordered from $n$, then the result of
apply with $\mathrm{op}$ on $t_1$ and $t_2$ is ordered from $n$. -/
theorem orderedFrom_apply (op : Bool → Bool → Bool) {n : Nat} {t₁ t₂ : BDD}
    (h₁ : OrderedFrom n t₁) (h₂ : OrderedFrom n t₂) : OrderedFrom n (apply op t₁ t₂) := by
  induction t₁, t₂ using apply.induct generalizing n with
  | case1 a b => simp only [apply]; trivial
  | case2 b v lo hi ihlo ihhi =>
    simp only [apply]
    exact orderedFrom_mk h₂.1 (ihlo trivial h₂.2.1) (ihhi trivial h₂.2.2)
  | case3 v lo hi b ihlo ihhi =>
    simp only [apply]
    exact orderedFrom_mk h₁.1 (ihlo h₁.2.1 trivial) (ihhi h₁.2.2 trivial)
  | case4 lo hi v lo' hi' ihlo ihhi =>
    simp only [apply, ↓reduceIte]
    exact orderedFrom_mk h₁.1 (ihlo h₁.2.1 h₂.2.1) (ihhi h₁.2.2 h₂.2.2)
  | case5 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte]
    have h₂' : OrderedFrom (v + 1) (node w lo' hi') := ⟨hlt, h₂.2⟩
    exact orderedFrom_mk h₁.1 (ihlo h₁.2.1 h₂') (ihhi h₁.2.2 h₂')
  | case6 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte]
    have h₁' : OrderedFrom (w + 1) (node v lo hi) := ⟨by omega, h₁.2⟩
    exact orderedFrom_mk h₂.1 (ihlo h₁' h₂.2.1) (ihhi h₁' h₂.2.2)

/-- **Apply returns reduced diagrams.** For every binary Boolean operation $\mathrm{op}$ and all
diagrams $t_1$ and $t_2$, the result of apply with $\mathrm{op}$ on $t_1$ and $t_2$ is reduced. -/
theorem reduced_apply (op : Bool → Bool → Bool) (t₁ t₂ : BDD) : Reduced (apply op t₁ t₂) := by
  induction t₁, t₂ using apply.induct with
  | case1 a b => simp only [apply]; trivial
  | case2 b v lo hi ihlo ihhi => simp only [apply]; exact reduced_mk ihlo ihhi
  | case3 v lo hi b ihlo ihhi => simp only [apply]; exact reduced_mk ihlo ihhi
  | case4 lo hi v lo' hi' ihlo ihhi =>
    simp only [apply, ↓reduceIte]; exact reduced_mk ihlo ihhi
  | case5 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte]; exact reduced_mk ihlo ihhi
  | case6 v lo hi w lo' hi' hne hlt ihlo ihhi =>
    simp only [apply, hne, hlt, ↓reduceIte]; exact reduced_mk ihlo ihhi

theorem isROBDD_apply (op : Bool → Bool → Bool) {t₁ t₂ : BDD} (h₁ : IsROBDD t₁)
    (h₂ : IsROBDD t₂) : IsROBDD (apply op t₁ t₂) :=
  ⟨orderedFrom_apply op h₁.1 h₂.1, reduced_apply op t₁ t₂⟩

/-! ### ROBDDs of propositions -/

/-- **Diagram of a proposition.** Each proposition $A$ whose atoms are natural numbers is sent
to a binary decision diagram by recursion on $A$: an atom $x$ goes to the node testing $x$ with
the leaf false as its false-child and the leaf true as its true-child, and a conjunction
$A \wedge B$, disjunction $A \vee B$ or implication $A \to B$ goes to the result of apply on the
diagrams of $A$ and $B$ under the Boolean operation and, or, or $(a, b) \mapsto \lnot a \lor b$
respectively. -/
def ofProposition : Proposition Nat → BDD
  | .atom x => node x (leaf false) (leaf true)
  | .and A B => apply (· && ·) (ofProposition A) (ofProposition B)
  | .or A B => apply (· || ·) (ofProposition A) (ofProposition B)
  | .imp A B => apply (fun a b ↦ !a || b) (ofProposition A) (ofProposition B)

theorem eval_ofProposition (A : Proposition Nat) (σ : Nat → Bool) :
    (ofProposition A).eval σ = A.evalBool σ := by
  induction A with
  | atom x => cases h : σ x <;> simp [ofProposition, h]
  | and A B ihA ihB => simp only [ofProposition, eval_apply, ihA, ihB]; rfl
  | or A B ihA ihB => simp only [ofProposition, eval_apply, ihA, ihB]; rfl
  | imp A B ihA ihB => simp only [ofProposition, eval_apply, ihA, ihB]; rfl

theorem isROBDD_ofProposition (A : Proposition Nat) : IsROBDD (ofProposition A) := by
  induction A with
  | atom x => exact ⟨⟨Nat.zero_le x, trivial, trivial⟩, ⟨by simp, trivial, trivial⟩⟩
  | and A B ihA ihB => exact isROBDD_apply _ ihA ihB
  | or A B ihA ihB => exact isROBDD_apply _ ihA ihB
  | imp A B ihA ihB => exact isROBDD_apply _ ihA ihB

/-- **Equal BDDs iff equal truth tables.** For propositions $A$ and $B$ over natural-number
atoms, the binary decision diagrams of $A$ and $B$ are equal if and only if $A$ and $B$ have the
same truth value under every valuation $\sigma : \mathbb{N} \to \mathrm{Bool}$.

Comparing the diagrams therefore decides truth-table equivalence. -/
theorem ofProposition_eq_iff {A B : Proposition Nat} :
    ofProposition A = ofProposition B ↔ ∀ σ, A.evalBool σ = B.evalBool σ := by
  rw [eq_iff_eval_eq (isROBDD_ofProposition A) (isROBDD_ofProposition B)]
  simp only [eval_ofProposition]

/-- **Satisfiable iff the BDD is not the false leaf.** For a proposition $A$ over
natural-number atoms, the binary decision diagram of $A$ is not the leaf false if and only if
some valuation $\sigma : \mathbb{N} \to \mathrm{Bool}$ makes $A$ true.

Both sides always hold: the valuation that makes every atom true satisfies every proposition
built from atoms by conjunction, disjunction and implication. -/
theorem ofProposition_ne_leaf_false_iff {A : Proposition Nat} :
    ofProposition A ≠ leaf false ↔ ∃ σ, A.evalBool σ = true := by
  rw [Ne, eq_leaf_false_iff (isROBDD_ofProposition A)]
  simp [eval_ofProposition]

end BDD

end Cslib.Logic.PL
