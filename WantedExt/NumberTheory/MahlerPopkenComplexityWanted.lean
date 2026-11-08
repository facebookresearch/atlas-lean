/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A binary version of the Mahler-Popken complexity function

Statements from John M. Campbell, "A Binary Version of the
Mahler-Popken Complexity Function", *INTEGERS* 24 (2024),
Article A94 (<https://math.colgate.edu/~integers/y94/y94.pdf>).

Definition 1 of the paper defines the `m`-ary complexity `∥n∥ₘ` as
the smallest number of possibly repeated selections from
`{1, 2, …, m}` (counting repetitions) that can be used to express
`n` using addition, multiplication, and legally nested brackets.
This generalizes the classical Mahler-Popken integer complexity
`IntegerComplexity.complexity` in MathlibExt, which is the case
`m = 1`.  The expression type below mirrors that MathlibExt
definition, with a leaf `i : Fin m` evaluating to `i + 1 ∈ {1, …, m}`.

Proposition 1 is split into its general-`m` part, where the paper
only asserts the recursion (9) "for all sufficiently large `n`",
and its explicit binary part, where (9) holds for `n ≥ 3`.  The
side conditions `d ≠ 1`, `d ≠ n`, and `0 < η` are the ones the paper
imposes when discussing the classical recursion (8).

Theorem 1 is stated for `1 ≤ n`; the paper's `ℕ` in this context
consists of positive naturals (its proof starts at `n = 1`), and
`∥0∥₂` is not defined by expressions with positive leaves.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.NumberTheory.IntegerComplexity

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

/-- Expressions built from leaves in `{1, …, m}` using `+` and `*`,
with bracketing given by the tree structure.  A leaf `i : Fin m`
stands for the number `i + 1`. -/
inductive MahlerPopkenExpr (m : ℕ) where
  | leaf : Fin m → MahlerPopkenExpr m
  | add : MahlerPopkenExpr m → MahlerPopkenExpr m → MahlerPopkenExpr m
  | mul : MahlerPopkenExpr m → MahlerPopkenExpr m → MahlerPopkenExpr m
  deriving DecidableEq, Repr

namespace MahlerPopkenExpr

/-- The natural number expressed by an `m`-ary complexity
expression. -/
def eval {m : ℕ} : MahlerPopkenExpr m → ℕ
  | .leaf i => i.val + 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- The number of leaf selections (counting repetitions) in an
`m`-ary complexity expression. -/
def count {m : ℕ} : MahlerPopkenExpr m → ℕ
  | .leaf _ => 1
  | .add a b => a.count + b.count
  | .mul a b => a.count + b.count

@[simp] theorem eval_leaf {m : ℕ} (i : Fin m) :
    (leaf i).eval = i.val + 1 := rfl

@[simp] theorem eval_add {m : ℕ} (a b : MahlerPopkenExpr m) :
    (add a b).eval = a.eval + b.eval := rfl

@[simp] theorem eval_mul {m : ℕ} (a b : MahlerPopkenExpr m) :
    (mul a b).eval = a.eval * b.eval := rfl

@[simp] theorem count_leaf {m : ℕ} (i : Fin m) :
    (leaf i).count = 1 := rfl

@[simp] theorem count_add {m : ℕ} (a b : MahlerPopkenExpr m) :
    (add a b).count = a.count + b.count := rfl

@[simp] theorem count_mul {m : ℕ} (a b : MahlerPopkenExpr m) :
    (mul a b).count = a.count + b.count := rfl

theorem count_pos {m : ℕ} (e : MahlerPopkenExpr m) : 0 < e.count := by
  induction e with
  | leaf i => simp
  | add a b iha _ => simp only [count_add]; omega
  | mul a b iha _ => simp only [count_mul]; omega

theorem eval_pos {m : ℕ} (e : MahlerPopkenExpr m) : 0 < e.eval := by
  induction e with
  | leaf i => simp
  | add a b iha _ => simp only [eval_add]; omega
  | mul a b iha ihb => simp only [eval_mul]; exact Nat.mul_pos iha ihb

end MahlerPopkenExpr

/-- The `m`-ary Mahler-Popken complexity `∥n∥ₘ`: the smallest
number of possibly repeated selections from `{1, …, m}` needed to
express `n` with addition, multiplication, and legal bracketing.
For `1 ≤ m` and `1 ≤ n` the set is nonempty (a sum of ones), so
the infimum is attained. -/
noncomputable def mahlerPopkenComplexity (m n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ e : MahlerPopkenExpr m, e.eval = n ∧ e.count = k}

/-- Every positive natural is expressed by some `m`-ary expression
when `1 ≤ m` (a sum of ones). -/
theorem exists_mahlerPopkenExpr_eval {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) : ∃ e : MahlerPopkenExpr m, e.eval = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨.leaf ⟨0, hm⟩, rfl⟩
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨.add e (.leaf ⟨0, hm⟩), by simp [he]⟩

/-- Specification: for `1 ≤ m` and `1 ≤ n`, the complexity is
attained by an optimal expression. -/
theorem mahlerPopkenComplexity_spec {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    ∃ e : MahlerPopkenExpr m, e.eval = n ∧
      e.count = mahlerPopkenComplexity m n := by
  obtain ⟨e, he⟩ := exists_mahlerPopkenExpr_eval hm hn
  have hmem : mahlerPopkenComplexity m n ∈
      {k : ℕ | ∃ e : MahlerPopkenExpr m, e.eval = n ∧ e.count = k} :=
    Nat.sInf_mem ⟨e.count, e, he, rfl⟩
  exact hmem

/-- Minimality: the complexity is at most the leaf count of any
expression for `n`. -/
theorem mahlerPopkenComplexity_min_le {m n : ℕ}
    (e : MahlerPopkenExpr m) (he : e.eval = n) :
    mahlerPopkenComplexity m n ≤ e.count :=
  Nat.sInf_le ⟨e, he, rfl⟩

/-- The complexity of a positive natural is positive. -/
theorem mahlerPopkenComplexity_pos {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) : 0 < mahlerPopkenComplexity m n := by
  obtain ⟨e, -, hcount⟩ := mahlerPopkenComplexity_spec hm hn
  rw [← hcount]
  exact e.count_pos

/-- Subadditivity under addition, the analogue of
`IntegerComplexity.complexity_add_le`. -/
theorem mahlerPopkenComplexity_add_le {m a b : ℕ} (hm : 1 ≤ m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mahlerPopkenComplexity m (a + b) ≤
      mahlerPopkenComplexity m a + mahlerPopkenComplexity m b := by
  obtain ⟨ea, hea, hca⟩ := mahlerPopkenComplexity_spec hm ha
  obtain ⟨eb, heb, hcb⟩ := mahlerPopkenComplexity_spec hm hb
  have h := mahlerPopkenComplexity_min_le (m := m) (n := a + b)
    (.add ea eb) (by simp [hea, heb])
  simpa [hca, hcb] using h

/-- Subadditivity under multiplication, the analogue of
`IntegerComplexity.complexity_mul_le`. -/
theorem mahlerPopkenComplexity_mul_le {m a b : ℕ} (hm : 1 ≤ m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mahlerPopkenComplexity m (a * b) ≤
      mahlerPopkenComplexity m a + mahlerPopkenComplexity m b := by
  obtain ⟨ea, hea, hca⟩ := mahlerPopkenComplexity_spec hm ha
  obtain ⟨eb, heb, hcb⟩ := mahlerPopkenComplexity_spec hm hb
  have h := mahlerPopkenComplexity_min_le (m := m) (n := a * b)
    (.mul ea eb) (by simp [hea, heb])
  simpa [hca, hcb] using h

/-- Translation of classical integer-complexity expressions to
`1`-ary Mahler-Popken expressions. -/
def MahlerPopkenExpr.ofIntegerComplexityExpr :
    IntegerComplexity.Expr → MahlerPopkenExpr 1
  | .one => .leaf 0
  | .add a b => .add (MahlerPopkenExpr.ofIntegerComplexityExpr a)
      (MahlerPopkenExpr.ofIntegerComplexityExpr b)
  | .mul a b => .mul (MahlerPopkenExpr.ofIntegerComplexityExpr a)
      (MahlerPopkenExpr.ofIntegerComplexityExpr b)

/-- Translation of `1`-ary Mahler-Popken expressions back to
classical integer-complexity expressions; the only leaf is `1`. -/
def MahlerPopkenExpr.toIntegerComplexityExpr :
    MahlerPopkenExpr 1 → IntegerComplexity.Expr
  | .leaf _ => .one
  | .add a b => .add a.toIntegerComplexityExpr
      b.toIntegerComplexityExpr
  | .mul a b => .mul a.toIntegerComplexityExpr
      b.toIntegerComplexityExpr

theorem MahlerPopkenExpr.eval_ofIntegerComplexityExpr
    (e : IntegerComplexity.Expr) :
    (MahlerPopkenExpr.ofIntegerComplexityExpr e).eval = e.eval := by
  induction e with
  | one => rfl
  | add a b iha ihb => simp [ofIntegerComplexityExpr, iha, ihb]
  | mul a b iha ihb => simp [ofIntegerComplexityExpr, iha, ihb]

theorem MahlerPopkenExpr.count_ofIntegerComplexityExpr
    (e : IntegerComplexity.Expr) :
    (MahlerPopkenExpr.ofIntegerComplexityExpr e).count = e.count := by
  induction e with
  | one => rfl
  | add a b iha ihb => simp [ofIntegerComplexityExpr, iha, ihb]
  | mul a b iha ihb => simp [ofIntegerComplexityExpr, iha, ihb]

theorem MahlerPopkenExpr.eval_toIntegerComplexityExpr
    (e : MahlerPopkenExpr 1) :
    e.toIntegerComplexityExpr.eval = e.eval := by
  induction e with
  | leaf i => simp [toIntegerComplexityExpr]
  | add a b iha ihb => simp [toIntegerComplexityExpr, iha, ihb]
  | mul a b iha ihb => simp [toIntegerComplexityExpr, iha, ihb]

theorem MahlerPopkenExpr.count_toIntegerComplexityExpr
    (e : MahlerPopkenExpr 1) :
    e.toIntegerComplexityExpr.count = e.count := by
  induction e with
  | leaf i => simp [toIntegerComplexityExpr]
  | add a b iha ihb => simp [toIntegerComplexityExpr, iha, ihb]
  | mul a b iha ihb => simp [toIntegerComplexityExpr, iha, ihb]

/-- The case `m = 1` of Definition 1 is the classical
Mahler-Popken integer complexity `IntegerComplexity.complexity`
(Example 2 of the paper). -/
theorem mahlerPopkenComplexity_one_eq {n : ℕ} (hn : 1 ≤ n) :
    mahlerPopkenComplexity 1 n =
      IntegerComplexity.complexity ⟨n, hn⟩ := by
  apply le_antisymm
  · obtain ⟨e, he, hcount⟩ := IntegerComplexity.exists_optimal ⟨n, hn⟩
    have h := mahlerPopkenComplexity_min_le (m := 1) (n := n)
      (MahlerPopkenExpr.ofIntegerComplexityExpr e) (by
        simp [MahlerPopkenExpr.eval_ofIntegerComplexityExpr, he])
    rwa [MahlerPopkenExpr.count_ofIntegerComplexityExpr, hcount]
      at h
  · obtain ⟨e, he, hcount⟩ :=
      mahlerPopkenComplexity_spec (m := 1) le_rfl hn
    have h := IntegerComplexity.complexity_le_count ⟨n, hn⟩
      e.toIntegerComplexityExpr (by
        simp [MahlerPopkenExpr.eval_toIntegerComplexityExpr, he])
    rwa [MahlerPopkenExpr.count_toIntegerComplexityExpr, hcount]
      at h

/-- The right-hand side of the recursion (9): the minimum of
`∥d∥ₘ + ∥n/d∥ₘ` over divisors `d ∣ n` with `d ≠ 1` and `d ≠ n`,
and of `∥η∥ₘ + ∥n - η∥ₘ` over `0 < η < n`. -/
noncomputable def mahlerPopkenRecursionValue (m n : ℕ) : ℕ :=
  sInf {k : ℕ |
    (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
      k = mahlerPopkenComplexity m d +
        mahlerPopkenComplexity m (n / d)) ∨
    (∃ η : ℕ, 0 < η ∧ η < n ∧
      k = mahlerPopkenComplexity m η +
        mahlerPopkenComplexity m (n - η))}

/-- **Proposition 1, general case**: for fixed `m`, the recursion
(9) holds for all sufficiently large `n`.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem_wanted mahlerPopkenComplexity_eq_recursionValue_eventually
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      mahlerPopkenComplexity m n = mahlerPopkenRecursionValue m n

/-- **Proposition 1, binary case**: for `m = 2`, the recursion (9)
holds for every `n ≥ 3`.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem_wanted mahlerPopkenComplexity_two_eq_recursionValue
    (n : ℕ) (hn : 3 ≤ n) :
    mahlerPopkenComplexity 2 n = mahlerPopkenRecursionValue 2 n

/-- **Theorem 1**: the binary complexity is bounded below by
`log₂ n`.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Theorem 1. -/
theorem_wanted logb_two_le_mahlerPopkenComplexity_two
    (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ (mahlerPopkenComplexity 2 n : ℝ)

/-- **Theorem 2**: the binary complexity is at most
`⌊log₂ n⌋ + ν₂(n) - 1` for `n ≥ 2`, where `ν₂(n)` is the number of
ones in the base-2 expansion of `n`.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Theorem 2. -/
theorem_wanted mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one
    (n : ℕ) (hn : 2 ≤ n) :
    mahlerPopkenComplexity 2 n ≤
      Nat.log 2 n + (Nat.digits 2 n).count 1 - 1

end MahlerPopkenComplexityWanted
