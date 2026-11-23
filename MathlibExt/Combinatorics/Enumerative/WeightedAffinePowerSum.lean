/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Basic

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-!
# Weighted affine power sums

Source: M. D. Schmidt, *Jacobi-Type Continued Fractions for the Ordinary Generating Functions
of Generalized Factorial Functions*, Journal of Integer Sequences 20 (2017),
[`schmidt14.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL20/Schmidt/schmidt14.tex).
-/

/-- **Weighted affine power sum.** Let $R$ be a ring, $a, b$ integers, $u \in R$ and $n, p$
natural numbers. The weighted affine power sum is

$$S_p(a, b; u, n + 1) = \sum_{k=0}^{n} u^k (ak + b)^p,$$

computed in $R$ with $a$, $b$ and $k$ mapped into $R$.

Unlike later generating-function identities in the source, this finite definition does not
require $u$ to be nonzero. -/
public def weightedAffinePowerSum {R : Type*} [Ring R]
    (a b : ℤ) (u : R) (n p : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), u ^ k * ((a : R) * (k : R) + (b : R)) ^ p

end

end MetaMathlibExt
