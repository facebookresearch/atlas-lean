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

/-- Binary decision diagrams in tree form: Boolean leaves and nodes testing a variable,
with the `lo` child for `false` and the `hi` child for `true`. -/
inductive BDD where
  | leaf (b : Bool)
  | node (v : Nat) (lo hi : BDD)
  deriving DecidableEq, Repr

namespace BDD

/-- The value of a diagram under an assignment of the variables. -/
def eval (σ : Nat → Bool) : BDD → Bool
  | leaf b => b
  | node v lo hi => if σ v then hi.eval σ else lo.eval σ

@[simp] theorem eval_leaf (σ : Nat → Bool) (b : Bool) : (leaf b).eval σ = b := rfl

@[simp] theorem eval_node (σ : Nat → Bool) (v : Nat) (lo hi : BDD) :
    (node v lo hi).eval σ = if σ v then hi.eval σ else lo.eval σ := rfl

/-- The number of leaves and nodes. -/
def size : BDD → Nat
  | leaf _ => 1
  | node _ lo hi => lo.size + hi.size + 1

/-- Every tested variable is at least `n`, and tested variables strictly increase along
every path. -/
def OrderedFrom : Nat → BDD → Prop
  | _, leaf _ => True
  | n, node v lo hi => n ≤ v ∧ OrderedFrom (v + 1) lo ∧ OrderedFrom (v + 1) hi

/-- No node has two equal children. -/
def Reduced : BDD → Prop
  | leaf _ => True
  | node _ lo hi => lo ≠ hi ∧ Reduced lo ∧ Reduced hi

/-- A reduced ordered binary decision diagram, for the natural order on variables. -/
def IsROBDD (t : BDD) : Prop := OrderedFrom 0 t ∧ Reduced t

theorem OrderedFrom.mono {m n : Nat} {t : BDD} (h : OrderedFrom n t) (hmn : m ≤ n) :
    OrderedFrom m t := by
  cases t with
  | leaf b => trivial
  | node v lo hi => exact ⟨hmn.trans h.1, h.2⟩

/-! ### Independence from variables below the order -/

/-- A diagram ordered from `n` does not depend on any variable below `n`. -/
theorem eval_update_of_lt {n v : Nat} {t : BDD} (h : OrderedFrom n t) (hv : v < n)
    (σ : Nat → Bool) (b : Bool) : t.eval (Function.update σ v b) = t.eval σ := by
  induction t generalizing n with
  | leaf c => rfl
  | node w lo hi ihlo ihhi =>
    obtain ⟨hw, hlo, hhi⟩ := h
    have hvw : w ≠ v := by omega
    simp only [eval_node, Function.update_of_ne hvw, ihlo hlo (by omega), ihhi hhi (by omega)]

/-- Fixing the top variable of an ordered node selects a child. -/
theorem eval_update_node {n v : Nat} {lo hi : BDD} (h : OrderedFrom n (node v lo hi))
    (σ : Nat → Bool) (b : Bool) :
    (node v lo hi).eval (Function.update σ v b) = if b then hi.eval σ else lo.eval σ := by
  rw [eval_node, Function.update_self, eval_update_of_lt h.2.2 (by omega),
    eval_update_of_lt h.2.1 (by omega)]

/-! ### Canonicity -/

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

/-- For reduced ordered diagrams, equality is equality of functions. -/
theorem eq_iff_eval_eq {t₁ t₂ : BDD} (h₁ : IsROBDD t₁) (h₂ : IsROBDD t₂) :
    t₁ = t₂ ↔ ∀ σ, t₁.eval σ = t₂.eval σ :=
  ⟨fun h _ ↦ h ▸ rfl, eq_of_eval_eq h₁.1 h₁.2 h₂.1 h₂.2⟩

/-- A reduced ordered diagram is unsatisfiable iff it is the leaf `false`. -/
theorem eq_leaf_false_iff {t : BDD} (h : IsROBDD t) :
    t = leaf false ↔ ∀ σ, t.eval σ = false :=
  eq_iff_eval_eq h ⟨trivial, trivial⟩

/-! ### Building reduced diagrams -/

/-- The node constructor that removes a redundant test. -/
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

/-- Bryant's `apply`: combine two diagrams under a binary Boolean operation, recursing on
the smaller top variable. -/
def apply (op : Bool → Bool → Bool) : BDD → BDD → BDD
  | leaf a, leaf b => leaf (op a b)
  | leaf a, node w lo hi => mk w (apply op (leaf a) lo) (apply op (leaf a) hi)
  | node v lo hi, leaf b => mk v (apply op lo (leaf b)) (apply op hi (leaf b))
  | node v lo hi, node w lo' hi' =>
    if v = w then mk v (apply op lo lo') (apply op hi hi')
    else if v < w then mk v (apply op lo (node w lo' hi')) (apply op hi (node w lo' hi'))
    else mk w (apply op (node v lo hi) lo') (apply op (node v lo hi) hi')

/-- `apply` computes the operation pointwise. -/
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

/-- `apply` preserves orderedness. -/
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

/-- `apply` always returns a reduced diagram. -/
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

/-- The ROBDD of an upstream CSLib proposition over `Nat` atoms, built bottom-up with
`apply`. -/
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

/-- Two propositions have the same truth table iff their ROBDDs are equal; this decides
truth-table equivalence. -/
theorem ofProposition_eq_iff {A B : Proposition Nat} :
    ofProposition A = ofProposition B ↔ ∀ σ, A.evalBool σ = B.evalBool σ := by
  rw [eq_iff_eval_eq (isROBDD_ofProposition A) (isROBDD_ofProposition B)]
  simp only [eval_ofProposition]

/-- A proposition over `Nat` atoms is satisfiable iff its ROBDD is not the leaf `false`.
Both sides always hold (the all-true valuation satisfies every proposition over atoms alone);
`exists_evalBool_eq_false_at_iff` in `Quantify.lean` is the informative version, with one
variable fixed to `false`. -/
theorem ofProposition_ne_leaf_false_iff {A : Proposition Nat} :
    ofProposition A ≠ leaf false ↔ ∃ σ, A.evalBool σ = true := by
  rw [Ne, eq_leaf_false_iff (isROBDD_ofProposition A)]
  simp [eval_ofProposition]

end BDD

end Cslib.Logic.PL
