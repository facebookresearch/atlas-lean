/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Satisfiability of the modal μ-calculus is EXPTIME-complete

Sources:
D. Kozen, "Results on the propositional μ-calculus", Theoretical Computer Science 27
(1983), 333-354 (decidability; EXPTIME upper bound via tableau / automata);
E. A. Emerson and C. S. Jutla, "Tree automata, μ-calculus and determinacy",
Proceedings of FOCS 1991, 368-377 (EXPTIME-hardness via alternating tree automata,
hence EXPTIME-completeness of satisfiability).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Modal.MuCalculusEncoding


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MuCalculusEXPTIMEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Satisfiability of the modal μ-calculus is EXPTIME-complete

A closed μ-calculus formula over `ℕ` atoms is *satisfiable* when some Kripke model has a
world satisfying it under the empty environment. `muSat` quantifies over all Kripke
models (worlds ranging over an arbitrary type); the decision problem takes a formula
code (see `Cslib.Modal.MuCalculus.muCode`) decoded from the input bitstring and answers
whether the decoded formula is closed and satisfiable. The EXPTIME-completeness
statement below is the standard formulation of this fact: membership in `EXP`
(Kozen's tableau / automata upper bound) plus hardness, i.e. every `EXP` language
reduces to it (Emerson–Jutla's alternating-tree-automata lower bound).
-/

/-- A closed μ-calculus formula is satisfiable: some Kripke model has a world
satisfying it under the empty environment. -/
def muSat (φ : Cslib.Modal.MuCalculus.MuFormula ℕ) : Prop :=
  ∃ (World : Type) (M : Cslib.Modal.KripkeModel World ℕ) (w : World),
    Cslib.Modal.MuCalculus.sat M (fun _ _ => False) φ w

open Classical in
/-- Satisfiability of the modal μ-calculus as a decision problem over bitstrings:
the input decodes to a formula code, which decodes to a formula; the answer is
whether that formula is closed and satisfiable. -/
noncomputable def muCalculusSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ) x with
  | some c =>
    match Cslib.Modal.MuCalculus.muDecode c with
    | some φ =>
      if Cslib.Modal.MuCalculus.MuFormula.Closed φ ∧ muSat φ then true else false
    | none => false
  | none => false

/-- **Satisfiability of a modal μ-calculus formula is EXPTIME-complete.** Sources:
D. Kozen, "Results on the propositional μ-calculus", Theoretical Computer Science 27
(1983), 333-354; E. A. Emerson and C. S. Jutla, "Tree automata, μ-calculus and
determinacy", FOCS 1991, 368-377. -/
public theorem_wanted mu_calculus_sat_exp_complete :
    muCalculusSatDec ∈ EXP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ EXP → Cslib.CookLevin.PolyManyOneRed L muCalculusSatDec

end MetaMathlibExt.Complexity.KeyTheorems.MuCalculusEXPTIMEComplete
