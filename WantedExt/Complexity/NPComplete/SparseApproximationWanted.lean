/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE APPROXIMATION is NP-complete

Source:
B. K. Natarajan, "Sparse approximate solutions to linear systems", SIAM Journal on Computing 24
(1995), 227-234, doi:10.1137/S0097539792240406.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SparseApproximationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseApproximation

open QuadraticProgramming (RatCode ratVal)

/-!
# SPARSE APPROXIMATION is NP-complete

INSTANCE: a matrix `A ∈ ℚ^{m × n}`, a vector `b ∈ ℚ^m`, a rational `ε > 0`, and a nonnegative
integer `k`.
QUESTION: is there a vector `x ∈ ℝ^n` with at most `k` nonzero entries and `‖Ax - b‖₂ ≤ ε`?

Natarajan considers the problem "given a matrix A in R^{m×n}, a vector b in R^m, and ε > 0,
compute a vector x satisfying ‖Ax - b‖₂ ≤ ε if such exists, such that x has the fewest number of
non-zero entries over all such vectors" and shows that it is NP-hard; this is its decision
version with the bound `k` on the number of nonzero entries. It is in NP: a support of size at
most `k` is a certificate, and for a fixed support the least residual is a least-squares problem
solvable exactly over `ℚ`.

The input numbers are rationals, given as `((a, b), d)` with value `(a - b) / d` and `0 < d`
(`QuadraticProgramming.RatCode`, `QuadraticProgramming.ratVal`, reused from
`QuadraticProgrammingWanted`);
`ε` must be positive. The matrix is a list of `m` rows of `n` entries and `b` a list of `m`
entries. `x` ranges over real vectors `Fin n → ℝ`, the number of nonzero entries is the size of
its support, and `‖·‖₂` is the Euclidean norm `√(∑ᵢ (∑ⱼ Aᵢⱼ xⱼ - bᵢ)²)`. All numbers use the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SPARSE APPROXIMATION is NP-complete.** Source: Natarajan (1995). -/
public theorem_wanted sparseApproximation_npComplete :
    sparseApproximationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sparseApproximationDec

end MetaMathlibExt.Complexity.NPComplete.SparseApproximation
