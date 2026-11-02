/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Model checking, satisfiability and validity of the linear modal μ-calculus are
# PSPACE-complete

Sources:
M. Y. Vardi, "A temporal fixpoint calculus", Proceedings of POPL 1988, 250-259
(linear-time μ-calculus; PSPACE-completeness of its satisfiability, validity and
model-checking problems);
A. P. Sistla and E. M. Clarke, "The complexity of propositional linear temporal
logics", Journal of the ACM 32 (1985), 733-749 (the analogous PSPACE-completeness
result for linear temporal logic).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Modal.LinearMuCalculus


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.LinearMuCalculusPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Model checking, satisfiability and validity of the linear modal μ-calculus are
# PSPACE-complete

The linear μ-calculus is interpreted over infinite words: a formula is evaluated at
a position `n : ℕ` of a word `val : ℕ → ℕ → Prop`, with `next` moving to the next
position. The three decision problems below are the standard ones:

* *Satisfiability*: some word and position satisfy a closed formula.
* *Validity*: every word and position satisfy a closed formula.
* *Model checking*: given a finite Kripke structure (worlds `0, …, n - 1`,
  edges, a valuation `worldVals` listing the atoms true at each world) and a
  start world, every infinite path from the start satisfies the formula at
  position `0`. The path turns the structure's valuation into a word valuation.

Each problem is stated as a decision problem over bitstrings: the input decodes
to a formula code (see `Cslib.Modal.LinearMuCalculus.linearMuCode`), plus the
finite structure for model checking. The PSPACE-completeness statement is the
standard formulation: membership in `PSPACE` plus hardness for each of the three
problems (Vardi, POPL 1988).
-/

/-- A closed linear μ-calculus formula is satisfiable: some word and position
satisfy it under the empty environment. -/
def linearMuSat (φ : Cslib.Modal.LinearMuCalculus.LinearMuFormula ℕ) : Prop :=
  ∃ (val : ℕ → ℕ → Prop) (n : ℕ),
    Cslib.Modal.LinearMuCalculus.sat val (fun _ _ => False) φ n

/-- A closed linear μ-calculus formula is valid: every word and position satisfy
it under the empty environment. -/
def linearMuValid (φ : Cslib.Modal.LinearMuCalculus.LinearMuFormula ℕ) : Prop :=
  ∀ (val : ℕ → ℕ → Prop) (n : ℕ),
    Cslib.Modal.LinearMuCalculus.sat val (fun _ _ => False) φ n

/-- Model checking a linear μ-calculus formula against a finite Kripke structure:
every infinite path `π` from `start` following `edges` satisfies `φ` at
position `0`, where the path turns the structure's valuation `worldVal` into a
word valuation. -/
def linearMuModelCheck (edges : List (ℕ × ℕ)) (worldVal : ℕ → ℕ → Prop)
    (start : ℕ) (φ : Cslib.Modal.LinearMuCalculus.LinearMuFormula ℕ) : Prop :=
  ∀ π : ℕ → ℕ, π 0 = start ∧ (∀ t, (π t, π (t + 1)) ∈ edges) →
    Cslib.Modal.LinearMuCalculus.sat (fun t a => worldVal (π t) a)
      (fun _ _ => False) φ 0

open Classical in
/-- Satisfiability of the linear μ-calculus as a decision problem over bitstrings:
the input decodes to a formula code, which decodes to a formula; the answer is
whether that formula is closed and satisfiable. -/
noncomputable def linearMuSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ) x with
  | some c =>
    match Cslib.Modal.LinearMuCalculus.linearMuDecode c with
    | some φ =>
      if Cslib.Modal.LinearMuCalculus.LinearMuFormula.Closed φ ∧ linearMuSat φ
      then true else false
    | none => false
  | none => false

open Classical in
/-- Validity of the linear μ-calculus as a decision problem over bitstrings. -/
noncomputable def linearMuValidDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ) x with
  | some c =>
    match Cslib.Modal.LinearMuCalculus.linearMuDecode c with
    | some φ =>
      if Cslib.Modal.LinearMuCalculus.LinearMuFormula.Closed φ ∧ linearMuValid φ
      then true else false
    | none => false
  | none => false

open Classical in
/-- Model checking of the linear μ-calculus as a decision problem over bitstrings:
the input decodes to `(n, edges, worldVals, start, code)`, where `worldVals`
lists, per world, the atoms true at that world; the answer is whether the
decoded formula is closed, the structure is well-formed, and every path from
`start` satisfies the formula. -/
noncomputable def linearMuModelCheckDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × List (List ℕ) × ℕ × ℕ) x with
  | some (n, edges, worldVals, start, c) =>
    match Cslib.Modal.LinearMuCalculus.linearMuDecode c with
    | some φ =>
      if Cslib.Modal.LinearMuCalculus.LinearMuFormula.Closed φ ∧ start < n ∧
          (∀ e ∈ edges, e.1 < n ∧ e.2 < n) ∧
          linearMuModelCheck edges (fun w a => a ∈ worldVals.getD w []) start φ
      then true else false
    | none => false
  | none => false

/-- **The model checking, satisfiability and validity problems of the linear modal
μ-calculus are PSPACE-complete**, like for linear temporal logic. Source:
M. Y. Vardi, "A temporal fixpoint calculus", POPL 1988, 250-259; cf. A. P. Sistla
and E. M. Clarke, "The complexity of propositional linear temporal logics",
JACM 32 (1985), 733-749. -/
public theorem_wanted linear_mu_calculus_pspace_complete :
    (linearMuSatDec ∈ PSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L linearMuSatDec) ∧
    (linearMuValidDec ∈ PSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L linearMuValidDec) ∧
    (linearMuModelCheckDec ∈ PSPACE ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L linearMuModelCheckDec)

end MetaMathlibExt.Complexity.KeyTheorems.LinearMuCalculusPSPACEComplete
