/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER PROGRAMMING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP1] INTEGER
PROGRAMMING;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press
(1972), 85-103, doi:10.1007/978-1-4684-2001-2_9;
I. Borosh and L. B. Treybig, "Bounds on positive integral solutions of linear
Diophantine equations", Proceedings of the American Mathematical Society 55
(1976), 299-304, doi:10.1090/S0002-9939-1976-0396605-3;
C. H. Papadimitriou, "On the complexity of integer programming", Journal of
the ACM 28 (1981), 765-768, doi:10.1145/322276.322287.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerProgramming

/-!
# INTEGER PROGRAMMING is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer, an `m`-tuple `c` of integers, and an integer `B`. QUESTION: is there an `m`-tuple `y`
of integers such that `x · y ≤ b` for all `(x, b) ∈ X` and such that `c · y ≥ B`?

Integers are encoded as pairs of naturals `(positive part, negative part)` standing for their
difference, as in `ZeroOneILPWanted`; `m`-tuples are lists of length `m`, and `X` is a list of
pairs. The variables `y` range over all of `ℤ` (no sign or `{0, 1}` restriction, which is what
separates this problem from 0-1 INTEGER PROGRAMMING). Membership in NP is the Borosh-Treybig and
Papadimitriou bound on the size of a smallest solution; the binary encoding of the numbers is
the one the bound is stated for.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `m`, the constraint list `X` of pairs (coefficient tuple,
right-hand side), the objective tuple `c`, and the bound `B`, every integer as a pair
`(positive part, negative part)`. -/
abbrev IntegerProgrammingInstance :=
  ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ)) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The integer encoded by a pair of naturals. -/
def toInt (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The dot product of an encoded integer tuple with an integer tuple. -/
def dot (x : List (ℕ × ℕ)) (y : List ℤ) : ℤ :=
  (List.zipWith (fun a b => toInt a * b) x y).sum

/-- Well-formedness of an instance: every constraint tuple and the objective tuple have length
`m`. -/
def WellFormed (i : IntegerProgrammingInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1.length = i.1) ∧ i.2.2.1.length = i.1

/-- Some integer `m`-tuple `y` satisfies every constraint `x · y ≤ b` and the objective bound
`c · y ≥ B`. -/
def IntegerProgrammingFeasible (i : IntegerProgrammingInstance) : Prop :=
  ∃ y : List ℤ, y.length = i.1 ∧ (∀ p ∈ i.2.1, dot p.1 y ≤ toInt p.2) ∧
    toInt i.2.2.2 ≤ dot i.2.2.1 y

open Classical in
/-- INTEGER PROGRAMMING as a decision problem over bitstrings. -/
noncomputable def integerProgrammingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegerProgrammingInstance) x with
  | some i => decide (WellFormed i ∧ IntegerProgrammingFeasible i)
  | none => false

/-- **INTEGER PROGRAMMING is NP-complete.** Source: Garey and Johnson (1979), [MP1];
Karp (1972); Borosh and Treybig (1976); Papadimitriou (1981). -/
public theorem_wanted integerProgramming_npComplete :
    integerProgrammingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integerProgrammingDec

end MetaMathlibExt.Complexity.NPComplete.IntegerProgramming
