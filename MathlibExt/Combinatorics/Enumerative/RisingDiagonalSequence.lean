/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic

/-!
# Rising diagonals of binary binomial interpolated triangles

Source: L. Németh, *On the binomial interpolated triangles*, Journal of Integer
Sequences 20 (2017), Article 17.7.2,
[`nemeth2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL20/Nemeth/nemeth2.tex).

The Case 1 triangle `BT(a₀,a₁,α,β;α,β)` is fixed by the column-zero recurrence
and the interior recurrence below. Its corollary (source lines 760–865) states
that every rising diagonal of this triangle is constant.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Binary binomial interpolated triangle.** For real numbers $a_0, a_1, \alpha, \beta$, a real
array $(a_{n,k})_{n,k \ge 0}$ is the binary binomial interpolated triangle
$BT(a_0, a_1, \alpha, \beta; \alpha, \beta)$ when $\alpha\beta \ne 0$, $|a_0| + |a_1| \ne 0$,
$a_{0,0} = a_0$, $a_{1,0} = a_1$, $a_{n,0} = \alpha\, a_{n-1,0} + \beta\, a_{n-2,0}$ for every
$n \ge 2$, and $a_{n,k} = \alpha\, a_{n,k-1} + \beta\, a_{n-1,k-1}$ for all $1 \le k \le n$.
Entries $a_{n,k}$ with $k > n$ are not constrained. -/
public def IsBinaryBinomialInterpolatedTriangle
    (a : ℕ → ℕ → ℝ) (a₀ a₁ α β : ℝ) : Prop :=
  α * β ≠ 0 ∧ |a₀| + |a₁| ≠ 0 ∧
    a 0 0 = a₀ ∧ a 1 0 = a₁ ∧
    (∀ n, 2 ≤ n → a n 0 = α * a (n - 1) 0 + β * a (n - 2) 0) ∧
    ∀ n k, 1 ≤ k → k ≤ n →
      a n k = α * a n (k - 1) + β * a (n - 1) (k - 1)

/-- **Rising diagonal.** For a real array $a = (a_{n,k})_{n,k \ge 0}$ and $n \ge 0$, the rising
diagonal of $a$ at level $n$ is the finite sequence $k \mapsto a_{n-k,k}$ indexed by
$0 \le k \le \lfloor n/2 \rfloor$. -/
public def risingDiagonal (a : ℕ → ℕ → ℝ) (n : ℕ) : Fin (n / 2 + 1) → ℝ :=
  fun k => a (n - k) k

/-- Every entry of a rising diagonal equals the entry at the foot of its
column-zero tail: if `2 * k ≤ n` then `a (n - k) k = a n 0`. -/
private theorem risingDiagonal_aux {a : ℕ → ℕ → ℝ} {a₀ a₁ α β : ℝ}
    (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) (k : ℕ) :
    ∀ n : ℕ, 2 * k ≤ n → a (n - k) k = a n 0 := by
  induction k with
  | zero =>
      intro n _
      simp
  | succ k ih =>
      intro n hn
      have h0rec : ∀ m : ℕ, 2 ≤ m →
          a m 0 = α * a (m - 1) 0 + β * a (m - 2) 0 :=
        h.2.2.2.2.1
      have hrec : ∀ m l : ℕ, 1 ≤ l → l ≤ m →
          a m l = α * a m (l - 1) + β * a (m - 1) (l - 1) :=
        h.2.2.2.2.2
      -- The recurrence applies at row `n - (k + 1)`, whose index still
      -- dominates `k + 1` because `2 * (k + 1) ≤ n`.
      have hle : k + 1 ≤ n - (k + 1) := by omega
      have hstep := hrec (n - (k + 1)) (k + 1) (by omega) hle
      rw [Nat.add_sub_cancel] at hstep
      -- Reindex both summands so the induction hypothesis applies at
      -- levels `n - 1` and `n - 2`; each rewrite is valid since `n ≥ 2`.
      have e1 : n - (k + 1) = (n - 1) - k := by omega
      have e2 : n - (k + 1) - 1 = (n - 2) - k := by omega
      have t1 : a (n - (k + 1)) k = a (n - 1) 0 := by
        rw [e1]
        exact ih (n - 1) (by omega)
      have t2 : a (n - (k + 1) - 1) k = a (n - 2) 0 := by
        rw [e2]
        exact ih (n - 2) (by omega)
      have hn0 : a n 0 = α * a (n - 1) 0 + β * a (n - 2) 0 :=
        h0rec n (by omega)
      rw [hstep, t1, t2]
      exact hn0.symm

/-- **Rising diagonals of a binary binomial interpolated triangle are constant.** Let
$a_0, a_1, \alpha, \beta$ be real numbers and let $a = (a_{n,k})_{n,k \ge 0}$ be a real array that
is the binary binomial interpolated triangle $BT(a_0, a_1, \alpha, \beta; \alpha, \beta)$. Then
for every $n \ge 0$ the rising diagonal of $a$ at level $n$ is constant: $a_{n-i,i} = a_{n-j,j}$
for all $0 \le i, j \le \lfloor n/2 \rfloor$. -/
public theorem risingDiagonal_const {a : ℕ → ℕ → ℝ} {a₀ a₁ α β : ℝ}
    (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) (n : ℕ)
    (i j : Fin (n / 2 + 1)) :
    risingDiagonal a n i = risingDiagonal a n j := by
  -- Fin bounds give `2 * i ≤ n` and `2 * j ≤ n` via `omega` on `n / 2`.
  have hi2 : 2 * (i : ℕ) ≤ n := by
    have hilt := i.isLt
    omega
  have hj2 : 2 * (j : ℕ) ≤ n := by
    have hjlt := j.isLt
    omega
  change a (n - (i : ℕ)) (i : ℕ) = a (n - (j : ℕ)) (j : ℕ)
  exact (risingDiagonal_aux h i n hi2).trans (risingDiagonal_aux h j n hj2).symm

end

end MetaMathlibExt
