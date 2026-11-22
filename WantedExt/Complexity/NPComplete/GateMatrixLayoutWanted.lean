/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GATE MATRIX LAYOUT is NP-complete

Source:
T. Kashiwabara and T. Fujisawa, "An NP-complete problem on interval graphs", Proceedings of the
IEEE International Symposium on Circuits and Systems (1979), 82-83;
N. Deo, M. S. Krishnamoorthy and M. A. Langston, "Exact and approximate solutions for the gate
matrix layout problem", IEEE Transactions on Computer-Aided Design 6(1) (1987), 79-84,
doi:10.1109/TCAD.1987.1270248 (abstract: the problem "is known to be NP-complete");
R. Govindan, M. A. Langston and S. Ramachandramurthi, "A practical approach to layout
optimization", University of Tennessee Computer Science Technical Report CS-92-176 (1992),
Section 3 (problem statement; "Since GML is NP-Complete [KF]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GateMatrixLayout

/-!
# GATE MATRIX LAYOUT is NP-complete

Govindan, Langston and Ramachandramurthi (1992), Section 3: an instance of the gate matrix layout
problem consists of a collection of nets (rows) and their connections to a set of gates
(columns). "More formally, we are given a Boolean matrix `M` and a positive integer `k`, and are
asked whether we can permute the columns of `M` so that, if in each row we change to `*` every
`0` lying between the row's leftmost and rightmost `1`, then no column contains more than `k`
`1`s and `*`s." The problem is NP-complete (Kashiwabara and Fujisawa 1979, via interval graphs;
recorded by Deo, Krishnamoorthy and Langston 1987 and by Govindan et al.).

INSTANCE: an `n × m` Boolean matrix `M` and a positive integer `k`.
QUESTION: can the columns of `M` be permuted so that, after filling in every `0` between the
leftmost and rightmost `1` of each row, no column has more than `k` entries `1` or `*`?

The matrix is given row by row; `WellFormed` requires rows of equal length and `k ≥ 1`. A column
permutation is `σ : Equiv.Perm (Fin m)`, moving column `a` to position `σ a`. After the
permutation, the entry of row `r` at position `p` is `1` or `*` exactly when row `r` has a `1` at
some position `≤ p` and a `1` at some position `≥ p`; the condition bounds the number of such
rows by `k` at every position.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the Boolean matrix `M` row by row, and the bound `k`. -/
abbrev GateMatrixLayoutInstance := List (List Bool) × ℕ

/-- The number of rows `n` (nets). -/
def rows (i : GateMatrixLayoutInstance) : ℕ := i.1.length

/-- The number of columns `m` (gates; the length of the first row). -/
def cols (i : GateMatrixLayoutInstance) : ℕ := (i.1.headD []).length

/-- The entry of `M` in row `r` and column `c`. -/
def entry (i : GateMatrixLayoutInstance) (r c : ℕ) : Bool :=
  (i.1.getD r []).getD c false

/-- Well-formedness: rows of equal length, and `k` a positive integer. -/
def WellFormed (i : GateMatrixLayoutInstance) : Prop :=
  (∀ row ∈ i.1, row.length = cols i) ∧ 1 ≤ i.2

/-- After the column permutation `σ`, the entry of row `r` at position `p` is `1` or `*`: the
row has a `1` in columns `a` and `b` moved to positions `σ a ≤ p ≤ σ b`. -/
def Covers (i : GateMatrixLayoutInstance) (σ : Equiv.Perm (Fin (cols i))) (r : Fin (rows i))
    (p : Fin (cols i)) : Prop :=
  ∃ a b : Fin (cols i), entry i r a = true ∧ entry i r b = true ∧ σ a ≤ p ∧ p ≤ σ b

instance (i : GateMatrixLayoutInstance) (σ : Equiv.Perm (Fin (cols i))) (r : Fin (rows i))
    (p : Fin (cols i)) : Decidable (Covers i σ r p) := by
  unfold Covers; infer_instance

/-- Some column permutation leaves at most `k` entries `1` or `*` in every column. -/
def GateMatrixLayoutFeasible (i : GateMatrixLayoutInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin (cols i)), ∀ p : Fin (cols i),
    (Finset.univ.filter fun r : Fin (rows i) => Covers i σ r p).card ≤ i.2

open Classical in
/-- GATE MATRIX LAYOUT as a decision problem over bitstrings. -/
noncomputable def gateMatrixLayoutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GateMatrixLayoutInstance) x with
  | some i => decide (WellFormed i ∧ GateMatrixLayoutFeasible i)
  | none => false

/-- **GATE MATRIX LAYOUT is NP-complete.** Source: Kashiwabara and Fujisawa (1979); Deo,
Krishnamoorthy and Langston (1987); Govindan, Langston and Ramachandramurthi (1992). -/
public theorem_wanted gateMatrixLayout_npComplete :
    gateMatrixLayoutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L gateMatrixLayoutDec

end MetaMathlibExt.Complexity.NPComplete.GateMatrixLayout
