/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING INTEGER PROGRAMMING: definitions

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

public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringIntegerProgramming

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

end MetaMathlibExt.Complexity.NPComplete.CoveringIntegerProgramming
