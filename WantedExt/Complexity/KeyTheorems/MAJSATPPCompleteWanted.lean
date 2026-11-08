/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAJSAT is PP-complete

Source:
J. Gill, "Computational complexity of probabilistic Turing machines", SIAM Journal on Computing
6 (1977), 675-695.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MAJSATPPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# MAJSAT is PP-complete

MAJSAT, the language of CNF formulas with a strict majority of satisfying assignments, is
`PP`-complete: it is in `PP` and every `PP` language polynomial-time many-one reduces to it.
The formula decodes to a unary variable count `n` (a bitstring of length `n`) and a formula `φ`
with variables below `n`; malformed inputs are no-instances.
-/

open Classical in
/-- MAJSAT as a decision problem over bitstrings. -/
noncomputable def majSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some i => decide (
      (∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1.length) ∧
      2 * Set.ncard {a : Fin i.1.length → Bool |
        Cslib.Logic.PL.CNF.Satisfies
          (fun v => if h : v < i.1.length then a ⟨v, h⟩ else false) i.2} > 2 ^ i.1.length)
  | none => false

/-- **MAJSAT is PP-complete.** Source: J. Gill, "Computational complexity of probabilistic
Turing machines", SIAM Journal on Computing 6 (1977), 675-695. -/
public theorem_wanted majsat_pp_complete :
    majSatDec ∈ PP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PP → Cslib.CookLevin.PolyManyOneRed L majSatDec

end MetaMathlibExt.Complexity.KeyTheorems.MAJSATPPComplete
