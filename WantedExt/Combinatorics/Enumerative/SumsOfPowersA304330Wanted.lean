/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of powers of integers and the sequence A304330

Statements from José L. Cereceda, "Sums of Powers of Integers and
the Sequence A304330", *Journal of Integer Sequences* 28 (2025),
Article 25.1.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Cereceda/cere9.html>).
Definitions are taken from the publisher TeX.

`S_k(n) = 1^k + ⋯ + n^k` is `powerSum`.  The array `R(k, m)`
(OEIS A304330 rows: `1; 1, 12; 1, 60, 360; …`) is defined by
`R(k, m) = Σ_{j=0}^m (-1)^j C(2m, j) (m - j)^{2k}`, and
`U(k, m) = (2/(2m)!)·R(k, m)`.  The inverse array `u(k, m)`, defined by
`Σ_{m=1}^k u(k, m) x^m = ∏_{i=0}^{k-1} (x - i^2)`, is the
existing specialization `MetaMathlibExt.jacobiStirlingFirst k m
(0 : ℤ)`, and the Legendre-Stirling numbers of the first kind
`Ps_m^{(r)}` (which the paper only names) are the existing
`MetaMathlibExt.legendreStirlingFirst`, i.e. the standard signed
convention `∏_{j=0}^{m-1} (x - j(j+1)) = Σ_r Ps_m^{(r)} x^r`,
which is the convention satisfying Proposition 12 (checked
numerically; the opposite sign fails).  The polynomial
identities below are stated for all `n : ℕ` where they hold at
`n = 0` as well; Lemma 4 keeps the paper's `n ≥ 1`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind
public import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330
public import MathlibExt.Combinatorics.Enumerative.OddPowerSumKnuth

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
