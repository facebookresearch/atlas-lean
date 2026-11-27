/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Module.LinearMap.Basic

namespace MetaMathlibExt.Polynomial

@[expose] public section

/-- **Formally orthogonal polynomial family.** Let $R$ be a field. A family $(p_n)_{n \ge 0}$ of
polynomials over $R$ is formally orthogonal if there is an $R$-linear functional
$L \colon R[x] \to R$ such that each $p_n$ has degree $n$, $L(p_n p_m) = 0$ whenever $n \ne m$,
and $L(p_n^2) \ne 0$ for every $n$.

Source: Barry, JIS VOL14 (`Barry1/barry97r2.tex`), lines 326-331.
URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry1/barry97r2.tex
Source SHA-256:
390bd7d75055d92085e8cd502df8b435fc1e45b1bbf8920038605d3fa1d1fe80
Span SHA-256 (lines 326-331):
b07808c63afc70c48dba4ed787a9177647fe9407b297ab37164f8350bbfbc8d6 -/
public def IsFormallyOrthogonal {R : Type*} [Field R]
    (p : ℕ → Polynomial R) : Prop :=
  ∃ L : Polynomial R →ₗ[R] R, (∀ n, (p n).natDegree = n) ∧
    (∀ n m, n ≠ m → L (p n * p m) = 0) ∧ ∀ n, L (p n ^ 2) ≠ 0

end

end MetaMathlibExt.Polynomial
