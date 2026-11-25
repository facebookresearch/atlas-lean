/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section

namespace MetaMathlibExt

/-! # Gibonacci squares satisfy a linear recurrence
-/

/--
**Gibonacci squares recurrence.** Let $g : \mathbb{N} \to \mathbb{Z}$ satisfy
$g(n+2) = g(n+1) + g(n)$ for every $n \in \mathbb{N}$, and let $F_3 = 2$ be the third Fibonacci
number. Then for every $n \in \mathbb{N}$,
$$g(n+3)^2 = F_3\, g(n+2)^2 + F_3\, g(n+1)^2 - g(n)^2.$$

The characteristic polynomial $x^3 - 2x^2 - 2x + 1$ of this recurrence has roots $\alpha^2$,
$\beta^2$ and $-1$, where $\alpha$ and $\beta$ are the roots of $x^2 - x - 1$.

Source: Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci
Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem 2
(label theorem02, equation equation02), lines 149–153,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
-/
theorem gibonacci_sq_recurrence
    (g : ℕ → ℤ) (hg : ∀ n : ℕ, g (n + 2) = g (n + 1) + g n) (n : ℕ) :
    g (n + 3) ^ 2 = (Nat.fib 3 : ℤ) * g (n + 2) ^ 2 +
      (Nat.fib 3 : ℤ) * g (n + 1) ^ 2 - g n ^ 2 := by
  have h0 := hg n
  have h1 := hg (n + 1)
  have e1 : n + 1 + 2 = n + 3 := by omega
  have e2 : n + 1 + 1 = n + 2 := by omega
  rw [e1, e2] at h1
  have hfib : (Nat.fib 3 : ℤ) = 2 := by decide
  rw [hfib, h1, h0]
  ring

end MetaMathlibExt
