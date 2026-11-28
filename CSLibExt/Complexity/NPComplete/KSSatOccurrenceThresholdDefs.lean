/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (k,s)-SAT at the occurrence threshold: definitions

Source:
J. Kratochvíl, P. Savický and Z. Tuza, "One more occurrence of variables makes satisfiability
jump from trivial to NP-complete", SIAM Journal on Computing 22 (1993), 203-210,
doi:10.1137/0222015.
-/
module

public import CSLibExt.Logics.Propositional.CNF.Basic
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSSatOccurrenceThreshold

open Cslib.Logic.LegacyPL

/-- `φ` is a `(k, s)`-formula: every clause has exactly `k` literals, on pairwise distinct
variables, and every variable occurs in at most `s` clauses. -/
def IsKSFormula (k s : ℕ) (φ : CNF) : Prop :=
  (∀ C ∈ φ, C.length = k ∧ (C.map Prod.fst).Nodup) ∧
    ∀ x : ℕ, φ.countP (fun C => decide (x ∈ C.map Prod.fst)) ≤ s

/-- `f(k)`: the supremum of the `s` such that every `(k, s)`-formula is satisfiable. For
`k ≥ 3` the set contains `0` (a `(k, 0)`-formula has no clauses) and is bounded (the `2^k`
clauses with all sign patterns on `k` variables form an unsatisfiable `(k, 2^k)`-formula), so
this is its largest element. For `k = 0` the set is empty (`[[]]` is unsatisfiable) and the
supremum is `0`; the theorem assumes `k ≥ 3`. -/
noncomputable def kSThreshold (k : ℕ) : ℕ :=
  sSup {s : ℕ | ∀ φ : CNF, IsKSFormula k s φ → CNFSat φ}

open Classical in
/-- `(k, s)`-SAT as a decision problem over bitstrings. -/
noncomputable def kSSatDec (k s : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CNF) x with
  | some φ => decide (IsKSFormula k s φ ∧ CNFSat φ)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KSSatOccurrenceThreshold
