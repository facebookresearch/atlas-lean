/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-FACILITY LOCATION: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-FACILITY LOCATION;
G. Cornuéjols, M. L. Fisher, and G. L. Nemhauser, "Location of bank accounts to optimize
float: an analytic study of exact and approximate algorithms", Management Science 23 (1977),
789-810, doi:10.1287/mnsc.23.8.789.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityLocation

/-- An instance: the profit matrix (row `v`, column `f` is `p(v, f)`; `|V|` is the number of
rows), the number `k` of facilities, and the bound `K`. -/
abbrev KFacilityLocationInstance := List (List ℕ) × ℕ × ℕ

/-- The profit `p(v, f)`: entry `f` of row `v` of the matrix. -/
def profit (i : KFacilityLocationInstance) (v f : ℕ) : ℕ := (i.1.getD v []).getD f 0

/-- Well-formedness of an instance: the matrix is square and `0 < K`. -/
def WellFormed (i : KFacilityLocationInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧ 0 < i.2.2

/-- Some set `F` of exactly `k` vertices has total profit `∑_{v ∈ V} max_{f ∈ F} p(v, f)` at
least `K`. -/
def KFacilityLocationFeasible (i : KFacilityLocationInstance) : Prop :=
  ∃ F : Finset (Fin i.1.length), F.card = i.2.1 ∧
    i.2.2 ≤ ∑ v : Fin i.1.length, F.sup fun f => profit i v f

open Classical in
/-- K-FACILITY LOCATION as a decision problem over bitstrings. -/
noncomputable def kFacilityLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KFacilityLocationInstance) x with
  | some i => decide (WellFormed i ∧ KFacilityLocationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KFacilityLocation
