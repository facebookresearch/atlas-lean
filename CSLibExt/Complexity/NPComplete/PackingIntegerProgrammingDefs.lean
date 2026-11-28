/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING INTEGER PROGRAMMING: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM PACKING INTEGER PROGRAMMING (decision version);
A. Srinivasan, "Improved approximations of packing and covering problems", Proc. 27th Annual
ACM Symposium on Theory of Computing (1995), 268-276, doi:10.1145/225058.225138;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (SET PACKING is
NP-complete).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingIntegerProgramming

/-- An instance: the rows of `A` (each a list of `n` rationals), the vector `b` (one rational
per row), the vector `c` (`n` rationals), and `K`; a rational is a pair `(p, q)` for `p / q`. -/
abbrev PackingIntegerProgrammingInstance :=
  List (List (ℕ × ℕ)) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The rational number `p / q` given by the pair `(p, q)`. -/
def ratOf (x : ℕ × ℕ) : ℚ := (x.1 : ℚ) / x.2

/-- Well-formedness of an instance: every denominator is positive; every row of `A` has one
entry per entry of `c`, and `b` has one entry per row; the entries of `A` and `c` lie in
`[0, 1]` and those of `b` in `[1, ∞)`; and `K` is positive. -/
def WellFormed (i : PackingIntegerProgrammingInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.2.2.1.length ∧ ∀ a ∈ row, 0 < a.2 ∧ a.1 ≤ a.2) ∧
    i.2.1.length = i.1.length ∧ (∀ x ∈ i.2.1, 0 < x.2 ∧ x.2 ≤ x.1) ∧
    (∀ x ∈ i.2.2.1, 0 < x.2 ∧ x.1 ≤ x.2) ∧ 0 < i.2.2.2

/-- Some `x ∈ {0,1}^n` satisfies `∑ⱼ a_{r,j} xⱼ ≤ b_r` for every row `r` and
`∑ⱼ cⱼ xⱼ ≥ K`. -/
def PackingIntegerProgrammingFeasible (i : PackingIntegerProgrammingInstance) : Prop :=
  ∃ x : Fin i.2.2.1.length → ℕ, (∀ j, x j ≤ 1) ∧
    (∀ r : Fin i.1.length,
      ∑ j : Fin i.2.2.1.length, ratOf ((i.1.get r).getD j (0, 1)) * x j ≤
        ratOf (i.2.1.getD r (1, 1))) ∧
    (i.2.2.2 : ℚ) ≤ ∑ j, ratOf (i.2.2.1.get j) * x j

open Classical in
/-- PACKING INTEGER PROGRAMMING as a decision problem over bitstrings. -/
noncomputable def packingIntegerProgrammingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PackingIntegerProgrammingInstance) x with
  | some i => decide (WellFormed i ∧ PackingIntegerProgrammingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PackingIntegerProgramming
