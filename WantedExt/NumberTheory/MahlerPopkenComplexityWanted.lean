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

/-- **Mahler–Popken expressions.** For a natural number $m$, the $m$-ary Mahler–Popken expressions
are the formal expressions built from leaves using the binary operations $+$ and $\times$; the
tree structure plays the role of brackets. Each leaf carries a label $i \in \{0, \dots, m - 1\}$
(so there are $m$ kinds of leaf), and a leaf with label $i$ stands for the number
$i + 1 \in \{1, \dots, m\}$. -/
inductive MahlerPopkenExpr (m : ℕ) where
  | leaf : Fin m → MahlerPopkenExpr m
  | add : MahlerPopkenExpr m → MahlerPopkenExpr m → MahlerPopkenExpr m
  | mul : MahlerPopkenExpr m → MahlerPopkenExpr m → MahlerPopkenExpr m
  deriving DecidableEq, Repr

namespace MahlerPopkenExpr

/-- **Value of an $m$-ary expression.** The natural number expressed by an $m$-ary Mahler–Popken
expression: the leaf with index $i \in \{0, \dots, m-1\}$ has value $i + 1$, and the value of a
sum or of a product of two expressions is the sum or the product of their values. -/
def eval {m : ℕ} : MahlerPopkenExpr m → ℕ
  | .leaf i => i.val + 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- **Number of leaves of an $m$-ary expression.** The number of leaf selections of an $m$-ary
Mahler–Popken expression, counting repetitions: a leaf counts $1$, and the count of a sum or of a
product of two expressions is the sum of their counts. -/
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

/-- **Mahler–Popken complexity.** For natural numbers $m$ and $n$, the $m$-ary Mahler–Popken
complexity $\lVert n \rVert_m$ is the smallest number of leaves (counted with repetition) of an
$m$-ary Mahler–Popken expression whose value is $n$: the smallest number of possibly repeated
selections from $\{1, \dots, m\}$ needed to express $n$ with addition, multiplication and legal
bracketing. If no expression has value $n$ (which happens exactly when $m = 0$ or $n = 0$), the
value is $0$. -/
noncomputable def mahlerPopkenComplexity (m n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ e : MahlerPopkenExpr m, e.eval = n ∧ e.count = k}

/-- **Every positive integer has an $m$-ary expression.** For natural numbers $m \ge 1$ and
$n \ge 1$, there is an $m$-ary Mahler–Popken expression whose value is $n$ (for instance a sum of
ones). -/
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

/-- **The Mahler–Popken complexity is attained.** For all natural numbers $m \ge 1$ and $n \ge 1$,
there is an $m$-ary Mahler–Popken expression whose value is $n$ and whose number of leaves
(counted with repetition) equals the $m$-ary Mahler–Popken complexity $\lVert n \rVert_m$. -/
theorem mahlerPopkenComplexity_spec {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    ∃ e : MahlerPopkenExpr m, e.eval = n ∧
      e.count = mahlerPopkenComplexity m n := by
  obtain ⟨e, he⟩ := exists_mahlerPopkenExpr_eval hm hn
  have hmem : mahlerPopkenComplexity m n ∈
      {k : ℕ | ∃ e : MahlerPopkenExpr m, e.eval = n ∧ e.count = k} :=
    Nat.sInf_mem ⟨e.count, e, he, rfl⟩
  exact hmem

/-- **Expressions bound the $m$-ary complexity from above.** For natural numbers $m$ and $n$ and
every $m$-ary Mahler–Popken expression $e$ whose value is $n$, the $m$-ary Mahler–Popken
complexity $\|n\|_m$ is at most the number of leaves of $e$. -/
theorem mahlerPopkenComplexity_min_le {m n : ℕ}
    (e : MahlerPopkenExpr m) (he : e.eval = n) :
    mahlerPopkenComplexity m n ≤ e.count :=
  Nat.sInf_le ⟨e, he, rfl⟩

/-- **The $m$-ary complexity is positive.** For natural numbers $m \ge 1$ and $n \ge 1$, the
$m$-ary Mahler–Popken complexity $\|n\|_m$ is positive. -/
theorem mahlerPopkenComplexity_pos {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) : 0 < mahlerPopkenComplexity m n := by
  obtain ⟨e, -, hcount⟩ := mahlerPopkenComplexity_spec hm hn
  rw [← hcount]
  exact e.count_pos

/-- **Subadditivity of the $m$-ary complexity under addition.** For natural numbers $m \ge 1$,
$a \ge 1$ and $b \ge 1$, the $m$-ary Mahler–Popken complexity $\|\cdot\|_m$ satisfies
$\|a + b\|_m \le \|a\|_m + \|b\|_m$.

This is the analogue of subadditivity under addition for the classical integer complexity. -/
theorem mahlerPopkenComplexity_add_le {m a b : ℕ} (hm : 1 ≤ m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mahlerPopkenComplexity m (a + b) ≤
      mahlerPopkenComplexity m a + mahlerPopkenComplexity m b := by
  obtain ⟨ea, hea, hca⟩ := mahlerPopkenComplexity_spec hm ha
  obtain ⟨eb, heb, hcb⟩ := mahlerPopkenComplexity_spec hm hb
  have h := mahlerPopkenComplexity_min_le (m := m) (n := a + b)
    (.add ea eb) (by simp [hea, heb])
  simpa [hca, hcb] using h

/-- **Subadditivity of the $m$-ary complexity under multiplication.** For natural numbers
$m \ge 1$, $a \ge 1$ and $b \ge 1$, the $m$-ary Mahler–Popken complexity $\|\cdot\|_m$ satisfies
$\|a b\|_m \le \|a\|_m + \|b\|_m$.

This is the analogue of subadditivity under multiplication for the classical integer
complexity. -/
theorem mahlerPopkenComplexity_mul_le {m a b : ℕ} (hm : 1 ≤ m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    mahlerPopkenComplexity m (a * b) ≤
      mahlerPopkenComplexity m a + mahlerPopkenComplexity m b := by
  obtain ⟨ea, hea, hca⟩ := mahlerPopkenComplexity_spec hm ha
  obtain ⟨eb, heb, hcb⟩ := mahlerPopkenComplexity_spec hm hb
  have h := mahlerPopkenComplexity_min_le (m := m) (n := a * b)
    (.mul ea eb) (by simp [hea, heb])
  simpa [hca, hcb] using h

/-- **Integer-complexity expressions as $1$-ary Mahler–Popken expressions.** The translation of
an expression built from one, addition and multiplication into a $1$-ary Mahler–Popken expression
replaces each occurrence of $1$ by the leaf standing for $1$ and keeps every addition and
multiplication, so the expression tree is unchanged. -/
def MahlerPopkenExpr.ofIntegerComplexityExpr :
    IntegerComplexity.Expr → MahlerPopkenExpr 1
  | .one => .leaf 0
  | .add a b => .add (MahlerPopkenExpr.ofIntegerComplexityExpr a)
      (MahlerPopkenExpr.ofIntegerComplexityExpr b)
  | .mul a b => .mul (MahlerPopkenExpr.ofIntegerComplexityExpr a)
      (MahlerPopkenExpr.ofIntegerComplexityExpr b)

/-- **$1$-ary Mahler–Popken expressions as integer-complexity expressions.** The translation of a
$1$-ary Mahler–Popken expression into an expression built from one, addition and multiplication
replaces each leaf (the only leaf stands for $1$) by $1$ and keeps every addition and
multiplication, so the expression tree is unchanged. -/
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

/-- **The $1$-ary complexity is the integer complexity.** For every natural number $n \ge 1$, the
$1$-ary Mahler–Popken complexity $\|n\|_1$ equals the classical integer complexity of $n$, the
least number of ones needed to write $n$ using $1$, $+$, $\times$ and parentheses.

This is the case $m = 1$ of Definition 1 in Campbell's paper (its Example 2). -/
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

/-- **Right-hand side of the Mahler–Popken recursion.** For natural numbers $m$ and $n$, write
$\lVert k \rVert_m$ for the $m$-ary Mahler–Popken complexity of $k$. The recursion value of $n$
is the smallest of the sums $\lVert d \rVert_m + \lVert n/d \rVert_m$ over the divisors $d$ of
$n$ with $d \ne 1$ and $d \ne n$, and of the sums $\lVert \eta \rVert_m + \lVert n - \eta \rVert_m$
over $0 < \eta < n$; it is $0$ when there are no such sums. This is the right-hand side of the
recursion (9) in Campbell's paper. -/
noncomputable def mahlerPopkenRecursionValue (m n : ℕ) : ℕ :=
  sInf {k : ℕ |
    (∃ d : ℕ, d ∣ n ∧ d ≠ 1 ∧ d ≠ n ∧
      k = mahlerPopkenComplexity m d +
        mahlerPopkenComplexity m (n / d)) ∨
    (∃ η : ℕ, 0 < η ∧ η < n ∧
      k = mahlerPopkenComplexity m η +
        mahlerPopkenComplexity m (n - η))}

/-- **The $m$-ary complexity eventually satisfies its recursion.** For every natural number
$m \ge 1$ there is $N$ such that for every $n \ge N$, the $m$-ary Mahler–Popken complexity
$\|n\|_m$ equals the right-hand side of the recursion (9), that is, the least of the values
$\|d\|_m + \|n/d\|_m$ over divisors $d$ of $n$ with $d \ne 1$ and $d \ne n$, and the values
$\|\eta\|_m + \|n - \eta\|_m$ over $0 < \eta < n$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem_wanted mahlerPopkenComplexity_eq_recursionValue_eventually
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      mahlerPopkenComplexity m n = mahlerPopkenRecursionValue m n

/-- **Recursion for the binary Mahler–Popken complexity.** For every natural number $n \ge 3$,
the binary ($2$-ary) Mahler–Popken complexity $\lVert n \rVert_2$ equals the minimum of the sums
$\lVert d \rVert_2 + \lVert n/d \rVert_2$ over the divisors $d$ of $n$ with $d \ne 1$ and
$d \ne n$, and of the sums $\lVert \eta \rVert_2 + \lVert n - \eta \rVert_2$ over $0 < \eta < n$.
This is the recursion (9) for $m = 2$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem_wanted mahlerPopkenComplexity_two_eq_recursionValue
    (n : ℕ) (hn : 3 ≤ n) :
    mahlerPopkenComplexity 2 n = mahlerPopkenRecursionValue 2 n

/-- **Logarithmic lower bound for the binary Mahler–Popken complexity.** For every natural number
$n \ge 1$, the $2$-ary (binary) Mahler–Popken complexity $\|n\|_2$ satisfies $\log_2 n \le \|n\|_2$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Theorem 1. -/
theorem_wanted logb_two_le_mahlerPopkenComplexity_two
    (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ (mahlerPopkenComplexity 2 n : ℝ)

/-- **Upper bound for the binary Mahler–Popken complexity.** For every natural number $n \ge 2$,
the binary ($2$-ary) Mahler–Popken complexity $\lVert n \rVert_2$ is at most
$\lfloor \log_2 n \rfloor + \nu_2(n) - 1$, where $\nu_2(n)$ is the number of ones in the base-$2$
expansion of $n$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Theorem 2. -/
theorem_wanted mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one
    (n : ℕ) (hn : 2 ≤ n) :
    mahlerPopkenComplexity 2 n ≤
      Nat.log 2 n + (Nat.digits 2 n).count 1 - 1

end MahlerPopkenComplexityWanted
