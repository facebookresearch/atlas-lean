/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING INTEGER PROGRAMMING is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM COVERING INTEGER PROGRAMMING (decision version);
A. Srinivasan, "Improved approximation guarantees for packing and covering integer programs",
SIAM Journal on Computing 29(2) (1999), 648-670, doi:10.1137/S0097539796314240,
Definition 1.1 (STOC 1995 version, pp. 268-276, doi:10.1145/225058.225138);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (SET COVERING).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringIntegerProgramming

/-!
# COVERING INTEGER PROGRAMMING is NP-complete

INSTANCE: a rational `m × n` matrix `A ∈ [0, 1]^{m·n}`, a rational `m`-vector
`b ∈ [1, ∞)^m`, a rational `n`-vector `c ∈ [0, 1]^n`, and a positive integer `K`.
QUESTION: is there a vector `x` of `n` non-negative integers such that `A x ≥ b` and
`c · x = ∑ᵢ cᵢ xᵢ ≤ K`?

This is the decision version of MINIMUM COVERING INTEGER PROGRAMMING of Crescenzi and Kann, whose
instance class is that of Srinivasan's covering integer programs (Definition 1.1: `A ∈ [0,
1]^{m×n}`, `b ∈ [1, ∞)^m`, `c ∈ [0, 1]^n`; minimize `cᵀ x` subject to `x ∈ ℤ₊ⁿ` and `A x ≥ b`).
Crescenzi and Kann print the solution as "a rational `n`-vector `x ∈ [0, 1]^n`"; read literally,
that is a linear program, solvable in polynomial time, so the integrality of Srinivasan's
definition, `x ∈ ℤ₊ⁿ`, is used. Srinivasan also normalizes `maxⱼ cⱼ = 1`, which Crescenzi and Kann
omit; the larger class without it is stated.

Hardness: with `A` the 0/1 incidence matrix of a set system (rows are elements, columns are
sets), `b = 1` and `c = 1`, a feasible `x` with `c · x ≤ K` gives a cover by at most `K` sets
(the columns with `xⱼ > 0`), and a cover gives a 0/1 vector `x`; this is SET COVERING, which
Karp (1972) proved NP-complete (`SetCoverWanted`). Membership in NP: lowering `xⱼ` to
`⌈max {bᵢ / Aᵢⱼ : Aᵢⱼ > 0}⌉` (to `0` for a zero column) keeps `A x ≥ b` and does not increase
`c · x`, so some feasible `x` has entries of polynomial bit length.

Rationals are pairs `(numerator, denominator)` of naturals with a positive denominator (every
entry is non-negative). The matrix and `b` are given row by row as a list of pairs
`(row Aᵢ, bᵢ)`; `c` and `x` are lists of length `n`. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, the rows `(Aᵢ, bᵢ)` of the constraints
`Aᵢ · x ≥ bᵢ`, the cost vector `c`, and the bound `K`; rationals are pairs
`(numerator, denominator)`. -/
abbrev CoveringIntegerProgrammingInstance :=
  ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ)) × List (ℕ × ℕ) × ℕ

/-- The rational number `p / q` encoded by the pair `(p, q)`. -/
def toRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / (q.2 : ℚ)

/-- The scalar product of an encoded rational vector with a vector of naturals. -/
def dot (a : List (ℕ × ℕ)) (x : List ℕ) : ℚ :=
  (List.zipWith (fun q k => toRat q * (k : ℚ)) a x).sum

/-- An encoded rational lies in `[0, 1]`: positive denominator, numerator at most the
denominator. -/
def InUnit (q : ℕ × ℕ) : Prop := 0 < q.2 ∧ q.1 ≤ q.2

/-- Well-formedness of an instance: every row `Aᵢ` has `n` entries in `[0, 1]`, every `bᵢ`
is at least `1`, `c` has `n` entries in `[0, 1]`, and `K` is positive. -/
def WellFormed (i : CoveringIntegerProgrammingInstance) : Prop :=
  (∀ r ∈ i.2.1, r.1.length = i.1 ∧ (∀ q ∈ r.1, InUnit q) ∧ 0 < r.2.2 ∧ r.2.2 ≤ r.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ q ∈ i.2.2.1, InUnit q) ∧ 0 < i.2.2.2

/-- Some vector `x` of `n` non-negative integers satisfies `Aᵢ · x ≥ bᵢ` for every row and
`c · x ≤ K`. -/
def CoveringIntegerProgrammingFeasible (i : CoveringIntegerProgrammingInstance) : Prop :=
  ∃ x : List ℕ, x.length = i.1 ∧ (∀ r ∈ i.2.1, toRat r.2 ≤ dot r.1 x) ∧
    dot i.2.2.1 x ≤ (i.2.2.2 : ℚ)

open Classical in
/-- COVERING INTEGER PROGRAMMING as a decision problem over bitstrings. -/
noncomputable def coveringIntegerProgrammingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringIntegerProgrammingInstance) x with
  | some i => decide (WellFormed i ∧ CoveringIntegerProgrammingFeasible i)
  | none => false

/-- **COVERING INTEGER PROGRAMMING is NP-complete.** Source: Crescenzi and Kann, MINIMUM COVERING
INTEGER PROGRAMMING; Srinivasan (1999); Karp (1972). -/
public theorem_wanted coveringIntegerProgramming_npComplete :
    coveringIntegerProgrammingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coveringIntegerProgrammingDec

end MetaMathlibExt.Complexity.NPComplete.CoveringIntegerProgramming
