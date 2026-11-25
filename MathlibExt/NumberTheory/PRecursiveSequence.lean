/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-!
# P-recursive integer sequences

Source: C. Banderier and F. Luca, *On the Period mod m of Polynomially-Recursive
Sequences: a Case Study*, Journal of Integer Sequences 22 (2019),
[`band3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL22/Banderier/band3.tex).
-/

/-- **P-recursive sequences.** Let $r$ be a natural number, let $P_0, \dots, P_r$ be polynomials
with integer coefficients, and let $(u_n)_{n \ge 0}$ be a sequence of integers. The sequence $u$
is P-recursive of order $r$ with coefficient polynomials $P_0, \dots, P_r$ if for every $n \ge r$,
$$
P_0(n)\, u_n = \sum_{i=1}^{r} P_i(n)\, u_{n-i}.
$$
-/
public def IsPRecursiveSequence (r : ℕ) (P : Fin (r + 1) → Polynomial ℤ)
    (u : ℕ → ℤ) : Prop :=
  ∀ n, r ≤ n →
    (P 0).eval (n : ℤ) * u n =
      ∑ i : Fin r, (P i.succ).eval (n : ℤ) * u (n - (i + 1))

end

end MetaMathlibExt
