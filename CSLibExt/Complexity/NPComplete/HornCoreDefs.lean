/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HORN CORE: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM HORN CORE (decision version);
D. Kavvadias, C. H. Papadimitriou and M. Sideri, "On Horn envelopes and hypergraph
transversals", Algorithms and Computation (ISAAC 1993), Lecture Notes in Comput. Sci. 762,
Springer (1993), 399-405, doi:10.1007/3-540-57568-5_271;
G. Gogic, C. H. Papadimitriou and M. Sideri, "Incremental recompilation of knowledge",
J. Artificial Intelligence Res. 8 (1998), 23-37, doi:10.1613/jair.380, Theorem 1.
-/
module

public import CSLibExt.Algorithms.SAT.Horn.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HornCore

open Cslib.Logic.LegacyPL Cslib.Algorithms.SAT.Horn

/-- An instance: the number `n` of variables, the set `M` of truth assignments (each a list of
`n` Booleans), and the bound `K`. -/
abbrev HornCoreInstance := ℕ × List (List Bool) × ℕ

/-- Well-formedness of an instance: every assignment in `M` has length `n`, `M` has no
duplicates, and `K` is positive. -/
def WellFormed (i : HornCoreInstance) : Prop :=
  (∀ a ∈ i.2.1, a.length = i.1) ∧ i.2.1.Nodup ∧ 0 < i.2.2

/-- The assignment to the variables `0, 1, …` given by a truth assignment `a` on `n` variables
(variables `x ≥ n`, which the formulas considered do not use, are set to `false`). -/
def extend {n : ℕ} (a : Fin n → Bool) : ℕ → Bool := fun x =>
  if h : x < n then a ⟨x, h⟩ else false

/-- `φ` is a Horn formula on the `n` variables whose set of satisfying truth assignments on
those variables is exactly `M'`. -/
def IsHornModelSet (n : ℕ) (M' : List (List Bool)) (φ : CNF) : Prop :=
  IsHorn φ ∧ (∀ C ∈ φ, ∀ l ∈ C, l.1 < n) ∧
    ∀ a : Fin n → Bool, φ.Satisfies (extend a) ↔ List.ofFn a ∈ M'

/-- There is a Horn core `M' ⊆ M` with `|M'| ≥ K`. -/
def HornCoreFeasible (i : HornCoreInstance) : Prop :=
  ∃ M' : List (List Bool), M'.Sublist i.2.1 ∧ (∃ φ : CNF, IsHornModelSet i.1 M' φ) ∧
    i.2.2 ≤ M'.length

open Classical in
/-- HORN CORE as a decision problem over bitstrings. -/
noncomputable def hornCoreDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HornCoreInstance) x with
  | some i => decide (WellFormed i ∧ HornCoreFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HornCore
