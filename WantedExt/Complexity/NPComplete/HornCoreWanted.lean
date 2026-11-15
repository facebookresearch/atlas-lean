/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HORN CORE is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.SAT.Horn.Basic
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HornCore

open Cslib.Logic.PL Cslib.Algorithms.SAT.Horn

/-!
# HORN CORE is NP-complete

INSTANCE: a set `M` of truth assignments on `n` variables, and a positive integer `K`.
QUESTION: is there a Horn core of `M`, that is, a subset `M' ⊆ M` such that `M'` is equal to
the set of truth assignments satisfying a Horn Boolean formula, with `|M'| ≥ K`?

A truth assignment on `n` variables is a list of `n` Booleans (entry `x` is the value of
variable `x`), and `M` is a duplicate-free list of such lists. A Horn formula is a CNF formula
(`Cslib.Logic.PL.CNF`) in which every clause has at most one positive literal
(`Cslib.Algorithms.SAT.Horn.IsHorn`); a formula on the `n` variables uses only the variables
`0, …, n - 1`, and its set of satisfying truth assignments on the `n` variables must be exactly
`M'`. The subset `M'` is a sublist of `M`, so it has no duplicates and its length is `|M'|`.

Kavvadias, Papadimitriou and Sideri (1993) call such a formula a Horn core when `M'` is
maximal; a subset of size at least `K` exists iff a maximal one does, so the question is the
same. Gogic, Papadimitriou and Sideri (1998), Theorem 1, record their result that selecting
the Horn core with the maximum number of models is NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HORN CORE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM HORN CORE; Kavvadias,
Papadimitriou and Sideri (1993); Gogic, Papadimitriou and Sideri (1998), Theorem 1. -/
public theorem_wanted hornCore_npComplete :
    hornCoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hornCoreDec

end MetaMathlibExt.Complexity.NPComplete.HornCore
