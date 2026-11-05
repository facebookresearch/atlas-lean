/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace IntegerComplexity

/-- **Expressions built from one, addition and multiplication.** An expression is either the
constant $1$, or a sum $e_1 + e_2$ of two expressions, or a product $e_1 \times e_2$ of two
expressions. Expressions are formal syntax trees, so the tree structure plays the role of
parentheses.

Source: C2. -/
inductive Expr where
  | one : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

/-- **Value of an expression.** The value of an expression is the natural number obtained by
evaluating it: the constant $1$ has value $1$, the value of $e_1 + e_2$ is the sum of the values
of $e_1$ and $e_2$, and the value of $e_1 \times e_2$ is the product of their values.

Source: C2. -/
def eval : Expr → ℕ
  | .one => 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- **Number of ones in an expression.** The number of ones of an expression is the number of
occurrences of the constant $1$ in it: the constant $1$ has one, and both $e_1 + e_2$ and
$e_1 \times e_2$ have as many as $e_1$ and $e_2$ together.

Source: C3. -/
def count : Expr → ℕ
  | .one => 1
  | .add a b => a.count + b.count
  | .mul a b => a.count + b.count

@[simp] theorem eval_one : (one : Expr).eval = 1 := rfl
@[simp] theorem count_one : (one : Expr).count = 1 := rfl
@[simp] theorem eval_add (a b : Expr) : (add a b).eval = a.eval + b.eval := rfl
@[simp] theorem eval_mul (a b : Expr) : (mul a b).eval = a.eval * b.eval := rfl
@[simp] theorem count_add (a b : Expr) : (add a b).count = a.count + b.count := rfl
@[simp] theorem count_mul (a b : Expr) : (mul a b).count = a.count + b.count := rfl

theorem count_pos (e : Expr) : 0 < e.count := by
  induction e with
  | one => simp [count]
  | add a b iha ihb => simp only [count]; exact Nat.add_pos_left iha _
  | mul a b iha ihb => simp only [count]; exact Nat.add_pos_left iha _

theorem eval_pos (e : Expr) : 0 < e.eval := by
  induction e with
  | one => simp [eval]
  | add a b iha ihb => simp only [eval]; exact Nat.add_pos_left iha _
  | mul a b iha ihb => simp only [eval]; exact Nat.mul_pos iha ihb

end Expr

open Expr

/-- **Every positive integer is the value of an expression.** For every natural number
$n > 0$ there is an expression whose value is $n$.

Source: C2/C4 existence side. -/
theorem exists_expr_of_pos {n : ℕ} (h : 0 < n) : ∃ e : Expr, e.eval = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; exact ⟨.one, rfl⟩
    · have hpos : 0 < n := by omega
      obtain ⟨e, he⟩ := ih hpos
      exact ⟨.add e .one, by simp [he]⟩

theorem exists_expr (n : ℕ+) : ∃ e : Expr, e.eval = n.val :=
  exists_expr_of_pos n.pos

/-- **Achievable numbers of ones.** For a positive integer $n$ and a natural number $c$, the
predicate holds when some expression has value $n$ and exactly $c$ ones.

Source: replaces Set S. -/
def Pred (n : ℕ+) (c : ℕ) : Prop := ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = c

theorem Pred_nonempty (n : ℕ+) : ∃ c, Pred n c := by
  obtain ⟨e, he⟩ := exists_expr n
  exact ⟨e.count, e, he, rfl⟩

/-- **Integer complexity.** The integer complexity of a positive integer $n$ is the least
number of ones in an expression whose value is $n$, that is, the least number of ones needed
to write $n$ using $1$, $+$, $\times$ and parentheses.

Source: C4. Implemented via Nat.find on proved existential predicate. -/
noncomputable def complexity (n : ℕ+) : ℕ := by
  classical
  exact Nat.find (Pred_nonempty n)

theorem complexity_spec (n : ℕ+) : Pred n (complexity n) := by
  classical
  exact Nat.find_spec (Pred_nonempty n)

theorem complexity_min_le (n : ℕ+) {m : ℕ} (hm : Pred n m) : complexity n ≤ m := by
  classical
  exact Nat.find_min' (Pred_nonempty n) hm

theorem exists_optimal (n : ℕ+) : ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = complexity n :=
  complexity_spec n

/-- **Expressions bound the integer complexity from above.** Let $n$ be a positive integer. If
an expression $e$ has value $n$, then the integer complexity of $n$ is at most the number of
ones of $e$.

Source: C4. -/
theorem complexity_le {n : ℕ+} {e : Expr} (he : e.eval = (n : ℕ)) : complexity n ≤ e.count :=
  complexity_min_le n ⟨e, he, rfl⟩

theorem complexity_le_count (n : ℕ+) (e : Expr) (he : e.eval = (n : ℕ)) :
    complexity n ≤ e.count := complexity_le he

theorem one_le_complexity (n : ℕ+) : 1 ≤ complexity n := by
  obtain ⟨e, _, hcount⟩ := exists_optimal n
  have hpos := e.count_pos
  omega

theorem complexity_one : complexity (1 : ℕ+) = 1 := by
  apply Nat.le_antisymm
  · exact complexity_min_le _ ⟨.one, rfl, rfl⟩
  · obtain ⟨e, _, hcount⟩ := exists_optimal (1 : ℕ+)
    have hpos := e.count_pos
    omega

/-- **Integer complexity of a sum.** For all positive integers $a$ and $b$, the integer
complexity of $a + b$ is at most the sum of the integer complexities of $a$ and $b$. -/
theorem complexity_add_le (a b : ℕ+) : complexity (a + b) ≤ complexity a + complexity b := by
  obtain ⟨ea, hea, hca⟩ := exists_optimal a
  obtain ⟨eb, heb, hcb⟩ := exists_optimal b
  have h : (Expr.add ea eb).eval = ((a + b : ℕ+) : ℕ) := by simp [hea, heb, PNat.add_coe]
  have hle := complexity_le h
  simp only [count_add, hca, hcb, ge_iff_le] at hle ⊢
  exact hle

/-- **Integer complexity of a product.** For all positive integers $a$ and $b$, the integer
complexity of $ab$ is at most the sum of the integer complexities of $a$ and $b$. -/
theorem complexity_mul_le (a b : ℕ+) : complexity (a * b) ≤ complexity a + complexity b := by
  obtain ⟨ea, hea, hca⟩ := exists_optimal a
  obtain ⟨eb, heb, hcb⟩ := exists_optimal b
  have h : (Expr.mul ea eb).eval = ((a * b : ℕ+) : ℕ) := by simp [hea, heb, PNat.mul_coe]
  have hle := complexity_le h
  simp only [count_mul, hca, hcb, ge_iff_le] at hle ⊢
  exact hle

end IntegerComplexity
