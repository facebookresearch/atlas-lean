/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Nu,lambda-Pascal matrix with coefficients

Production formalization of the source definition (concept
`jis_sem_48e0bb143520a73f6b828a27`, source statement
`jis_445c3486a9ca32dba0e8a333`) using zero-based indexing.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Nu-lambda Pascal matrix with coefficients.** Let $N$ and $n$ be natural numbers with
$n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$.
An array $S = (S_{i,j})_{i,j \ge 0}$ of complex numbers, indexed from $0$, is a
$(\nu, \lambda)$-Pascal matrix of size $2n$ with coefficients $\beta$ when the following
hold: $S_{i,j} = 0$ whenever $i \ge 2n$ or $j \ge 2n$; $S_{i,j} = -S_{j,i}$ for all $i, j$;
$S_{2n-2,\,2n-1} = 1$; $S_{j,\,2n-1} = \sum_{t=0}^{N-1} \beta_t S_{j+t+1,\,2n-1}$ for every
$j < 2n - 2$; and $S_{i,j} = \lambda S_{i+1,j+1} + \nu (S_{i+1,j} + S_{i,j+1})$ for all
$i, j < 2n - 1$.

The definition also allows $N = 0$; then the sum is empty, so the entries $S_{j,\,2n-1}$
with $j < 2n - 2$ vanish. The intended coefficient families have $N > 0$. -/
public def IsNuLambdaPascalMatrix (N n : ℕ) (nu lam : ℂ) (beta : Fin N → ℂ)
    (S : ℕ → ℕ → ℂ) (_hn : 0 < n) : Prop :=
  (∀ i j, 2 * n ≤ i ∨ 2 * n ≤ j → S i j = 0) ∧
  (∀ i j, S i j = -S j i) ∧
  (S (2 * n - 2) (2 * n - 1) = 1) ∧
  (∀ j, j < 2 * n - 2 →
    S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1)) ∧
  (∀ i j, i < 2 * n - 1 → j < 2 * n - 1 →
    S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)))

/-- **Finite support of a nu-lambda Pascal matrix.** Let $N$ and $n$ be natural numbers
with $n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$,
and let $S = (S_{i,j})_{i,j \ge 0}$ be a $(\nu, \lambda)$-Pascal matrix of size $2n$ with
coefficients $\beta$. Then $S_{i,j} = 0$ for all $i, j$ with $i \ge 2n$ or
$j \ge 2n$. -/
public theorem IsNuLambdaPascalMatrix.finite_support (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) (hij : 2 * n ≤ i ∨ 2 * n ≤ j) : S i j = 0 :=
  h.1 i j hij

/-- **Nu-lambda Pascal matrices are skew-symmetric.** Let $N$ and $n$ be natural numbers
with $n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$,
and let $S = (S_{i,j})_{i,j \ge 0}$ be a $(\nu, \lambda)$-Pascal matrix of size $2n$ with
coefficients $\beta$. Then $S_{i,j} = -S_{j,i}$ for all $i, j$. -/
public theorem IsNuLambdaPascalMatrix.skew (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) : S i j = -S j i :=
  h.2.1 i j

/-- **Corner entry of a nu-lambda Pascal matrix.** Let $N$ and $n$ be natural numbers
with $n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$,
and let $S = (S_{i,j})_{i,j \ge 0}$ be a $(\nu, \lambda)$-Pascal matrix of size $2n$ with
coefficients $\beta$. Then $S_{2n-2,\,2n-1} = 1$. -/
public theorem IsNuLambdaPascalMatrix.corner (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
    S (2 * n - 2) (2 * n - 1) = 1 :=
  h.2.2.1

/-- **Last-column recurrence of a nu-lambda Pascal matrix.** Let $N$ and $n$ be natural numbers
with $n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$,
and let $S = (S_{i,j})_{i,j \ge 0}$ be a $(\nu, \lambda)$-Pascal matrix of size $2n$ with
coefficients $\beta$. Then for every $j < 2n - 2$,
$S_{j,\,2n-1} = \sum_{t=0}^{N-1} \beta_t S_{j+t+1,\,2n-1}$. -/
public theorem IsNuLambdaPascalMatrix.last_column (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (j : ℕ) (hj : j < 2 * n - 2) :
    S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1) :=
  h.2.2.2.1 j hj

/-- **Interior recurrence of a nu-lambda Pascal matrix.** Let $N$ and $n$ be natural numbers
with $n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$,
and let $S = (S_{i,j})_{i,j \ge 0}$ be a $(\nu, \lambda)$-Pascal matrix of size $2n$ with
coefficients $\beta$. Then for all $i, j < 2n - 1$,
$S_{i,j} = \lambda S_{i+1,j+1} + \nu (S_{i+1,j} + S_{i,j+1})$. -/
public theorem IsNuLambdaPascalMatrix.interior (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) (hi : i < 2 * n - 1) (hj : j < 2 * n - 1) :
    S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)) :=
  h.2.2.2.2 i j hi hj

end

end MetaMathlibExt
