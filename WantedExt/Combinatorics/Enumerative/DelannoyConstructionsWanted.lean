/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Delannoy constructions

Statements from Steven Edwards and William Griffiths, "Delannoy
Constructions", *Journal of Integer Sequences* 27 (2024), Article 24.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Edwards/ed6.html>).

The Delannoy number `D(m, n)` is taken from the existing Delannoy triangle
`MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (m + n) m 1
= ∑_j C(m, j) C(m + n - j, m)`.

The generalized Delannoy numbers `D^k(m, n)` and `D_k(m, n)` are the paper's binomial sums
(`genDelannoyUpper`, `genDelannoyLower`); a Delannoy array is any `R : ℕ → ℕ → ℤ` satisfying the
Delannoy recurrence, and `R^i` is its `i`-fold horizontal sum. The lattice-path interpretations
(Theorems 1 and 2) are not stated.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions
public import MathlibExt.Combinatorics.Enumerative.DelannoyRowsParity
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

set_option autoImplicit false

namespace MetaMathlibExt

namespace DelannoyConstructions

@[expose] public section

open Finset

/-- The four relationship identities for `D_k` (`k ≥ 1`, `m, n ≥ k`):
`D_k(m, n) + D_k(m, n + 1) = 2 D_(k-1)(m, n)`, `D_k(m, n) + D_k(m + 1, n) = D_(k+1)(m + 1, n + 1)`,
`D_k(m, n + 1) - D_k(m, n) = 2 D_(k-1)(m - 1, n)`, `D_k(m + 1, n) - D_k(m, n) = D_(k+1)(m + 1, n)`.
The fourth identity additionally requires `k < n`, so that its right-hand side is in the
intended domain of `D_(k+1)`.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 7
(`jis-2024-24.1.8-thm-7`). -/
public theorem_wanted genDelannoyLower_relations (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    genDelannoyLower k m n + genDelannoyLower k m (n + 1) = 2 * genDelannoyLower (k - 1) m n ∧
      genDelannoyLower k m n + genDelannoyLower k (m + 1) n =
        genDelannoyLower (k + 1) (m + 1) (n + 1) ∧
      (genDelannoyLower k m (n + 1) : ℤ) - genDelannoyLower k m n =
        2 * genDelannoyLower (k - 1) (m - 1) n ∧
      (k < n → (genDelannoyLower k (m + 1) n : ℤ) - genDelannoyLower k m n =
        genDelannoyLower (k + 1) (m + 1) n)

end

end DelannoyConstructions

end MetaMathlibExt
