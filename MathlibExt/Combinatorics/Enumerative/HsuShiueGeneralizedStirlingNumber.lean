/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic

/-!
Hsu-Shiue generalized Stirling numbers S(n, k; alpha, beta, r),
following the JIS source (source statement jis_7e7402faeeffb59e829d97bc).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>.
-/

namespace MetaMathlibExt

@[expose]
public section

variable {K : Type*} [RCLike K]

/-- **Generalized falling factorial.** Let $K$ be $\mathbb{R}$ or $\mathbb{C}$. For
$z, \alpha \in K$ the generalized falling factorial with increment $\alpha$ is the sequence
defined by $(z \mid \alpha)_0 = 1$ and $(z \mid \alpha)_{n+1} = (z \mid \alpha)_n \, (z - n\alpha)$
for $n \ge 0$, so that $(z \mid \alpha)_n = z (z - \alpha) \cdots (z - (n-1)\alpha)$ for $n \ge 1$.

Source: source statement jis_7e7402faeeffb59e829d97bc. -/
public noncomputable def generalizedFallingFactorial (z alpha : K) : Nat → K
  | 0 => 1
  | n + 1 => generalizedFallingFactorial z alpha n * (z - (n : K) * alpha)

/-- **Characterization of the Hsu–Shiue generalized Stirling numbers.** Let $K$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $\alpha, \beta, r \in K$. For $z \in K$ write $(z \mid \alpha)_0 = 1$ and
$(z \mid \alpha)_n = z (z - \alpha) \cdots (z - (n-1)\alpha)$ for $n \ge 1$ (the generalized
falling factorial). An array $(S(n,k))_{n, k \ge 0}$ in $K$ is a Hsu–Shiue family with
parameters $(\alpha, \beta, r)$ when $\alpha$, $\beta$ and $r$ are not all zero,
$S(n, 0) = (r \mid \alpha)_n$ for every $n \ge 0$, $S(n, k) = 0$ whenever $n < k$, and
$$S(n+1, k+1) = S(n, k) + \bigl((k+1)\beta - n\alpha + r\bigr) S(n, k+1)$$
for all $n, k \ge 0$.

The last condition is the source recurrence
$S(n+1, k) = S(n, k-1) + (k\beta - n\alpha + r) S(n, k)$ at the indices $k \ge 1$; the initial
column and the triangular support fix the remaining values.

Source: source statement `jis_7e7402faeeffb59e829d97bc`. -/
public def IsHsuShiueFamily (S : Nat → Nat → K) (alpha beta r : K) : Prop :=
  ¬ (alpha = 0 ∧ beta = 0 ∧ r = 0) ∧
    (∀ n, S n 0 = generalizedFallingFactorial r alpha n) ∧
      (∀ n k, n < k → S n k = 0) ∧
        ∀ n k, S (n + 1) (k + 1) =
          S n k + (((k : K) + 1) * beta - (n : K) * alpha + r) * S n (k + 1)

end

end MetaMathlibExt
