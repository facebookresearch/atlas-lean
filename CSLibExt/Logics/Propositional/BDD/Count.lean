/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting satisfying assignments of a BDD
-/
module

public import CSLibExt.Logics.Propositional.BDD.Basic

/-!
# Counting satisfying assignments of a BDD

Bryant's satisfy-count: the number of assignments to the variables `0, …, m - 1`
that make an ordered diagram true, computed in one pass over the tree. A node
testing `v` reached with `n` as the next unaccounted variable contributes a
factor `2 ^ (v - n)` for the skipped variables `n, …, v - 1`; a leaf `true`
reached at `n` contributes `2 ^ (m - n)`.

The specification `countModels xs f σ` enumerates the assignments directly: it
tries both values of every variable of `xs` in turn, starting from `σ`, and counts
those on which `f` is true.

## Main definitions

- `BDD.VarsLT m t` : every variable tested in `t` is below `m`.
- `BDD.satCountFrom m n t`, `BDD.satCount m t` : the one-pass count.
- `BDD.countModels xs f σ` : the specification by enumeration.

## Main results

- `BDD.satCount_eq_countModels` : for `t` ordered and with variables below `m`,
  `satCount m t = countModels (List.range m) (eval · t) σ` for every `σ`.

## References

- R. E. Bryant, *Graph-based algorithms for Boolean function manipulation*,
  IEEE Trans. Computers C-35(8), 1986, 677-691 (§4.6, satisfy-count).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.PL.BDD

/-- **Variables below a bound.** For a natural number $m$, a diagram has its variables below $m$
when every variable tested at a node of the diagram is less than $m$. -/
def VarsLT (m : Nat) : BDD → Prop
  | leaf _ => True
  | node v lo hi => v < m ∧ VarsLT m lo ∧ VarsLT m hi

/-- **One-pass satisfy-count from a variable.** For natural numbers $m$ and $n$ and a diagram $t$,
the satisfy-count $c_m(n, t)$ of $t$ from $n$ with bound $m$ is defined by recursion on $t$: a
leaf $\mathrm{true}$ gives $2^{m - n}$, a leaf $\mathrm{false}$ gives $0$, and a node testing the
variable $v$ with child $t_0$ for false and child $t_1$ for true gives
$2^{v - n} (c_m(v + 1, t_0) + c_m(v + 1, t_1))$. Here $m - n$ and $v - n$ are truncated
subtraction, equal to $0$ when the difference would be negative.

For $t$ ordered from $n$ whose tested variables are all below $m$, $c_m(n, t)$ is the number of
assignments to the variables $n, \dots, m - 1$ that make $t$ true. -/
def satCountFrom (m : Nat) : Nat → BDD → Nat
  | n, leaf b => if b then 2 ^ (m - n) else 0
  | n, node v lo hi => 2 ^ (v - n) * (satCountFrom m (v + 1) lo + satCountFrom m (v + 1) hi)

/-- **Satisfy-count.** For a natural number $m$ and a diagram $t$, the satisfy-count of $t$ below
$m$ is the one-pass satisfy-count $c_m(0, t)$ of $t$ from the variable $0$ with bound $m$.

When $t$ is ordered from $0$ and every variable it tests is below $m$, this is the number of
assignments to the variables $0, \dots, m - 1$ that make $t$ true. -/
def satCount (m : Nat) (t : BDD) : Nat := satCountFrom m 0 t

/-- **Model count by enumeration.** An assignment is a map $\sigma$ from the variables, which are
natural numbers, to the truth values $\mathrm{false}$ and $\mathrm{true}$. For a list
$x_1, \dots, x_k$ of variables, a function $f$ from assignments to truth values, and an assignment
$\sigma$, the model count of $f$ over $x_1, \dots, x_k$ from $\sigma$ is the number of tuples
$(b_1, \dots, b_k) \in \{\mathrm{false}, \mathrm{true}\}^k$ such that $f$ is true at the assignment
obtained from $\sigma$ by setting $x_1$ to $b_1$, then $x_2$ to $b_2$, and so on up to setting
$x_k$ to $b_k$, a later setting overriding an earlier one of the same variable.

When $x_1, \dots, x_k$ are distinct, this is the number of assignments that agree with $\sigma$
outside $x_1, \dots, x_k$ and make $f$ true. -/
def countModels : List Nat → ((Nat → Bool) → Bool) → (Nat → Bool) → Nat
  | [], f, σ => if f σ then 1 else 0
  | x :: xs, f, σ =>
    countModels xs f (Function.update σ x false) + countModels xs f (Function.update σ x true)

/-- **Congruence for the model count.** Let $x_1, \dots, x_k$ be a list of variables, $f$ and $g$
functions from assignments to truth values, and $\sigma$ an assignment. If $f(\tau) = g(\tau)$ for
every assignment $\tau$ such that $\tau(x) = \sigma(x)$ for every variable $x$ not in the list,
then the model counts of $f$ and of $g$ over $x_1, \dots, x_k$ from $\sigma$ are equal. -/
theorem countModels_congr {xs : List Nat} {f g : (Nat → Bool) → Bool} {σ : Nat → Bool}
    (h : ∀ τ : Nat → Bool, (∀ x, x ∉ xs → τ x = σ x) → f τ = g τ) :
    countModels xs f σ = countModels xs g σ := by
  induction xs generalizing σ with
  | nil => simp [countModels, h σ fun _ _ ↦ rfl]
  | cons y ys ih =>
    have key : ∀ b, countModels ys f (Function.update σ y b) =
        countModels ys g (Function.update σ y b) := fun b ↦ ih fun τ hτ ↦ h τ fun x hx ↦ by
      have hxy : x ≠ y := fun e ↦ hx (e ▸ List.mem_cons_self ..)
      rw [hτ x fun hx' ↦ hx (List.mem_cons_of_mem _ hx'), Function.update_of_ne hxy]
    simp only [countModels, key]

/-- **The satisfy-count from a variable counts models.** Let $m$ and $n$ be natural numbers and
$t$ a diagram ordered from $n$ (every tested variable is at least $n$, and tested variables
strictly increase along every path) in which every tested variable is below $m$. Then for every
assignment $\sigma$, the one-pass satisfy-count $c_m(n, t)$ of $t$ from $n$ with bound $m$ equals
the model count of the function $\tau \mapsto t(\tau)$ over the variables $n, n + 1, \dots, m - 1$
from $\sigma$ (no variables when $m \le n$), where $t(\tau)$ is the value of $t$ under $\tau$. -/
theorem satCountFrom_eq_countModels (m : Nat) :
    ∀ (k n : Nat), m - n = k → ∀ {t : BDD}, OrderedFrom n t → VarsLT m t →
      ∀ σ : Nat → Bool,
        satCountFrom m n t = countModels (List.range' n (m - n)) (fun τ ↦ t.eval τ) σ := by
  intro k
  induction k with
  | zero =>
    intro n hk t ht hm σ
    rw [hk]
    cases t with
    | leaf b => cases b <;> simp [satCountFrom, countModels, hk]
    | node v lo hi => exact absurd (ht.1.trans_lt hm.1) (by omega)
  | succ k ih =>
    intro n hk t ht hm σ
    have hrange : List.range' n (m - n) = n :: List.range' (n + 1) (m - (n + 1)) := by
      rw [hk, show m - (n + 1) = k by omega, List.range'_succ]
    have hn : n ∉ List.range' (n + 1) (m - (n + 1)) := by simp [List.mem_range'_1]
    rw [hrange, countModels]
    cases t with
    | leaf b =>
      rw [← ih (n + 1) (by omega) (t := leaf b) trivial trivial,
        ← ih (n + 1) (by omega) (t := leaf b) trivial trivial]
      cases b
      · simp [satCountFrom]
      · simp only [satCountFrom, ite_true, show m - n = (m - (n + 1)) + 1 by omega, Nat.pow_succ,
          Nat.mul_two]
    | node v lo hi =>
      obtain ⟨hv, hlo, hhi⟩ := ht
      obtain ⟨hvm, hmlo, hmhi⟩ := hm
      rcases Nat.eq_or_lt_of_le hv with hnv | hlt
      · -- the node tests `n` itself: each value of `n` selects one child
        subst hnv
        have hsel : ∀ b, countModels (List.range' (n + 1) (m - (n + 1)))
            (fun τ ↦ (node n lo hi).eval τ) (Function.update σ n b) =
            countModels (List.range' (n + 1) (m - (n + 1)))
              (fun τ ↦ (if b then hi else lo).eval τ) (Function.update σ n b) :=
          fun b ↦ countModels_congr fun τ hτ ↦ by
            have : τ n = b := by rw [hτ n hn, Function.update_self]
            cases b <;> simp [this]
        rw [hsel false, hsel true]
        simp only [Bool.false_eq_true, ite_false, ite_true]
        rw [← ih (n + 1) (by omega) hlo hmlo, ← ih (n + 1) (by omega) hhi hmhi]
        simp [satCountFrom]
      · -- the node tests a later variable: `n` is free, and doubles the count
        have ht' : OrderedFrom (n + 1) (node v lo hi) := ⟨by omega, hlo, hhi⟩
        rw [← ih (n + 1) (by omega) ht' ⟨hvm, hmlo, hmhi⟩,
          ← ih (n + 1) (by omega) ht' ⟨hvm, hmlo, hmhi⟩]
        simp only [satCountFrom, show v - n = (v - (n + 1)) + 1 by omega, Nat.pow_succ]
        rw [Nat.mul_right_comm, Nat.mul_two]

/-- **Correctness of the satisfy-count.** Let $m$ be a natural number and $t$ a diagram ordered
from $0$ (tested variables strictly increase along every path) in which every tested variable is
below $m$. Then for every assignment $\sigma$, the satisfy-count of $t$ below $m$ equals the model
count of the function $\tau \mapsto t(\tau)$ over the variables $0, 1, \dots, m - 1$ from
$\sigma$, where $t(\tau)$ is the value of $t$ under $\tau$. In other words, it is the number of
assignments to the variables $0, \dots, m - 1$ that make $t$ true. -/
theorem satCount_eq_countModels {m : Nat} {t : BDD} (ht : OrderedFrom 0 t) (hm : VarsLT m t)
    (σ : Nat → Bool) :
    satCount m t = countModels (List.range m) (fun τ ↦ t.eval τ) σ := by
  rw [satCount, satCountFrom_eq_countModels m _ 0 rfl ht hm σ, List.range_eq_range']
  simp

end Cslib.Logic.PL.BDD
