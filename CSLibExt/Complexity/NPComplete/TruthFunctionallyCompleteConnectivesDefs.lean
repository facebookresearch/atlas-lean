/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO10] TRUTH-FUNCTIONALLY COMPLETE
CONNECTIVES, p. 261 (reference: R. Statman (1976), private communication; transformation from
3SAT).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NonTautologyDefs
public import Cslib.Computability.Circuit.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

open Cslib.Logic.LegacyPL

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, and the expressions of `C`, each
a postfix token list as in `NonTautologyWanted`. -/
abbrev TruthFunctionallyCompleteConnectivesInstance := ℕ × List (List (ℕ × ℕ))

/-- The binary truth function `(a, b) ↦ s(E)` that the expression `E` defines under the
substitution `s`, which sends `uₓ` to `a` if `s x = true` and to `b` if `s x = false`. -/
def substOp (E : Proposition (WithBot ℕ)) (s : ℕ → Bool) (a b : Bool) : Bool :=
  E.evalBool (NonTautology.valuation fun x => if s x then a else b)

/-- Well-formedness of an instance: every member of `C` is an expression over
`u₀, …, u_{n-1}` (`NonTautology.WellFormed`). -/
def WellFormed (i : TruthFunctionallyCompleteConnectivesInstance) : Prop :=
  ∀ t ∈ i.2, NonTautology.WellFormed (i.1, t)

/-- Some set `D` of connectives, each defined by an expression of `C` under a substitution
`s : U → {a, b}`, is truth-functionally complete: for every arity `m ≥ 1`, every `m`-ary truth
function `f` is computed by a one-output CSLib circuit whose gates are the members of `D` (the
operation symbol `k : Fin D.length` has arity `2` and is interpreted by `D.get k`). -/
def TruthFunctionallyCompleteConnectivesFeasible
    (i : TruthFunctionallyCompleteConnectivesInstance) : Prop :=
  ∃ D : List (Bool → Bool → Bool),
    (∀ θ ∈ D, ∃ t ∈ i.2, ∃ E, NonTautology.parse t = some E ∧
      ∃ s : ℕ → Bool, substOp E s = θ) ∧
    ∀ m, 0 < m → ∀ f : (Fin m → Bool) → Bool,
      ∃ c : Cslib.Circuits.Circuit ⟨Fin D.length, fun _ => 2⟩ m 1,
        c.Computes (fun k args => D.get k (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩))
          (Cslib.Circuits.single f)

open Classical in
/-- TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES as a decision problem over bitstrings. -/
noncomputable def truthFunctionallyCompleteConnectivesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TruthFunctionallyCompleteConnectivesInstance) x with
  | some i => decide (WellFormed i ∧ TruthFunctionallyCompleteConnectivesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives
