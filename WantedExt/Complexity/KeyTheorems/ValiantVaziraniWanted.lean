/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Valiant-Vazirani: SAT reduces to UniqueSAT

Source:
L. G. Valiant and V. V. Vazirani, "NP is as easy as detecting unique solutions", Theoretical
Computer Science 47 (1986), 85-93 (STOC 1985).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ValiantVazirani

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Valiant-Vazirani: SAT reduces to UniqueSAT

There is a randomized polynomial-time reduction from SAT to UniqueSAT: if the formula is
unsatisfiable, the reduction always outputs an unsatisfiable formula; if it is satisfiable,
with probability at least `1 / (8 * (n + 1))` the output has exactly one satisfying assignment,
where `n` is the input length. SAT and UniqueSAT are the canonical bitstring-encoded CNF
decision problems, with the variable count given in unary.
-/

open Classical in
/-- SAT as a decision problem over bitstrings: `(unary, φ)` with variables below `unary.length`. -/
noncomputable def satDec' :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some i => decide (∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1.length) ∧
      decide (∃ a : Fin i.1.length → Bool,
        Cslib.Logic.PL.CNF.Satisfies
          (fun v => if h : v < i.1.length then a ⟨v, h⟩ else false) i.2)
  | none => false

open Classical in
/-- UniqueSAT: exactly one satisfying assignment. -/
noncomputable def uniqueSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some i => decide (∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1.length) ∧
      decide (∃! a : Fin i.1.length → Bool,
        Cslib.Logic.PL.CNF.Satisfies
          (fun v => if h : v < i.1.length then a ⟨v, h⟩ else false) i.2)
  | none => false

/-- **Valiant-Vazirani: SAT reduces to UniqueSAT.** Source: L. G. Valiant and V. V. Vazirani,
"NP is as easy as detecting unique solutions", Theoretical Computer Science 47 (1986),
85-93 (STOC 1985). -/
public theorem_wanted valiant_vazirani :
    ∃ p : Polynomial ℕ, ∃ red : List Bool × List Bool → List Bool, IsPolyTime red ∧
      ∀ x : List Bool, let n := x.length
        (satDec' x = false →
          ∀ r : List Bool, r.length = p.eval n →
            satDec' (red (x, r)) = false ∧ uniqueSatDec (red (x, r)) = false) ∧
        (satDec' x = true →
          8 * (n + 1) * Set.ncard {r : Fin (p.eval n) → Bool |
            uniqueSatDec (red (x, List.ofFn r)) = true} ≥ 2 ^ (p.eval n))

end MetaMathlibExt.Complexity.KeyTheorems.ValiantVazirani
