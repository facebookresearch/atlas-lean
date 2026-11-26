/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Explicit formulas for Bernoulli and Genocchi numbers

Statements from Schehrazade Zerroukhat and Laala Khaldi,
"A Note on Explicit Formulas for Bernoulli and Genocchi
Numbers", *Journal of Integer Sequences* 28 (2025),
Article 25.6.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>).

Notation: `Bₙ` is Mathlib's `bernoulli`, `Gₙ` is
MathlibExt's `genocchiNumber`, `S(n,k)` is
`Nat.stirlingSecond`, and `Δ` is the forward-difference
operator, with `Δᵏ xⁿ` evaluated at `x` written
`diffPowEval x k n` (the paper's `Δᵏ0ⁿ` and `Δᵏ1ⁿ` are
the cases `x = 0, 1`). The paper's auxiliary sums
`U(m,k) = ∑_{j ≥ 0} (-1)^{k+j+m} (k+j-1)!/2^{k+j-1} S(m,j)`
(finite, since `S(m,j) = 0` for `j > m`) and
`H_{n,m} = (-1)ⁿ n ∑_{k ≥ 1} U(m+1,k) S(n-m,k)` are
`zerroU` and `zerroH`. The first equality of Theorem 1,
`2(1-2ⁿ)Bₙ = Gₙ`, is MathlibExt's proved
`genocchiNumber_eq_bernoulli`; the second equality is
`genocchiNumber_eq_sum`, proved in
`MathlibExt.NumberTheory.GenocchiExplicitGenocchiNumberEqSum`.
All identities were verified by exact rational computation
before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.GenocchiExplicit
public import MathlibExt.NumberTheory.GenocchiNumber
public import MathlibExt.NumberTheory.GenocchiExplicitGenocchiNumberEqSum

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.GenocchiExplicitWanted

end MathlibExt.NumberTheory.GenocchiExplicitWanted
