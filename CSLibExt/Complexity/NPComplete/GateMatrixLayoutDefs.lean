/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GATE MATRIX LAYOUT: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GateMatrixLayout

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

end MetaMathlibExt.Complexity.NPComplete.GateMatrixLayout
