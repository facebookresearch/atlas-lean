/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER PROGRAMMING: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerProgramming

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

end MetaMathlibExt.Complexity.NPComplete.IntegerProgramming
