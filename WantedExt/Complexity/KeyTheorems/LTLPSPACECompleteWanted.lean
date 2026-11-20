/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.LTL.Encoding
public import CSLibExt.Logics.LTL.Satisfiability
public import CSLibExt.Logics.LTL.ModelChecking

/-!
# Satisfiability, validity and model checking of LTL are PSPACE-complete

The three problems take an LTL formula over atoms in `ℕ`, given by its linear-size token
encoding (`Cslib.LTL.Formula.tokens`, one token per occurrence), and, for model checking, a
finite Kripke structure:

* *Satisfiability*: some infinite word over the alphabet of sets of atoms satisfies the
  formula (`Cslib.LTL.Satisfiable`, letters read by membership).
* *Validity*: every such word satisfies it (`Cslib.LTL.Valid`).
* *Model checking*: given worlds `0, …, n - 1`, a list of edges, the list of atoms true at each
  world and a start world, every infinite path from the start satisfies the formula
  (`Cslib.LTL.ModelChecking.Models`). The structure is required to be total (every world has
  a successor), as for finite-state programs in the source; without totality a deadlocked
  start world would satisfy every formula vacuously. In the encoding, row `w` of the list of
  atoms belongs to world `w`: a world without a row (the list is shorter than `n`) has no true
  atom, and rows beyond the last world are ignored.

Each is a decision problem over bitstrings, in the format of
`WantedExt.Complexity.KeyTheorems.LinearMuCalculusPSPACECompleteWanted`, and the statement is
membership in `PSPACE` plus hardness under polynomial many-one reductions. For model checking
this is the combined complexity (program and formula both part of the input); it follows from
the specification-complexity hardness and the space bound of Vardi's Theorem 25.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Theorems 24 and 25 (author's posted version `banff94rj.pdf`).
* A. P. Sistla and E. M. Clarke, "The complexity of propositional linear temporal logics",
  *J. ACM* 32 (1985), 733-749.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.LTLPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-- **Kripke structure as a transition system.** The labelled transition system on worlds
`ℕ`, with a single label, whose transitions are the listed edges. -/
def kripkeLTS (edges : List (ℕ × ℕ)) : Cslib.LTS ℕ Unit where
  Tr s _ t := (s, t) ∈ edges

open Classical in
/-- **LTL satisfiability as a decision problem.** The input decodes to a token list, which
decodes to an LTL formula over atoms in `ℕ`; the answer is whether some infinite word over
sets of atoms satisfies it. -/
noncomputable def ltlSatDec : DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List ℕ) x with
  | some toks =>
    match Cslib.LTL.Formula.decodeList toks with
    | some φ => if Cslib.LTL.Satisfiable (fun (s : Set ℕ) a => a ∈ s) φ then true else false
    | none => false
  | none => false

open Classical in
/-- **LTL validity as a decision problem.** The input decodes to a token list, which decodes
to an LTL formula over atoms in `ℕ`; the answer is whether every infinite word over sets of
atoms satisfies it. -/
noncomputable def ltlValidDec : DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List ℕ) x with
  | some toks =>
    match Cslib.LTL.Formula.decodeList toks with
    | some φ => if Cslib.LTL.Valid (fun (s : Set ℕ) a => a ∈ s) φ then true else false
    | none => false
  | none => false

open Classical in
/-- **LTL model checking as a decision problem.** The input decodes to
`(n, edges, worldVals, start, tokens)`, where `worldVals` lists the atoms true at each world;
the answer is whether the structure is well formed and total (every world below `n` has a
successor below `n`) and every infinite path from `start` satisfies the decoded formula. The
atoms true at world `w` are read as `worldVals.getD w []`, and this is part of the encoding: a
world `w` with `worldVals.length ≤ w` has no true atom, and the rows of `worldVals` beyond world
`n - 1` are ignored, so the length of `worldVals` is not required to be `n`. -/
noncomputable def ltlModelCheckDec : DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × List (List ℕ) × ℕ × List ℕ) x with
  | some (n, edges, worldVals, start, toks) =>
    match Cslib.LTL.Formula.decodeList toks with
    | some φ =>
      if start < n ∧ (∀ e ∈ edges, e.1 < n ∧ e.2 < n) ∧
          (∀ w, w < n → ∃ v, v < n ∧ (w, v) ∈ edges) ∧
          Cslib.LTL.ModelChecking.Models (kripkeLTS edges) {start}
            (fun w a => a ∈ worldVals.getD w []) φ
      then true else false
    | none => false
  | none => false

/-- **Satisfiability, validity and model checking of LTL are PSPACE-complete.** Each of the
three problems, with the formula given by its linear-size token encoding, is in `PSPACE` and
every `PSPACE` problem reduces to it in polynomial time (Sistla and Clarke, J. ACM 1985; Vardi,
"An automata-theoretic approach to linear temporal logic", LNCS 1043, 1996, Theorem 24 for
satisfiability and validity, Theorem 25 for model checking). -/
public theorem_wanted ltl_pspace_complete :
    (ltlSatDec ∈ PSPACE ∧ ∀ L : DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L ltlSatDec) ∧
    (ltlValidDec ∈ PSPACE ∧ ∀ L : DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L ltlValidDec) ∧
    (ltlModelCheckDec ∈ PSPACE ∧ ∀ L : DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L ltlModelCheckDec)

end MetaMathlibExt.Complexity.KeyTheorems.LTLPSPACEComplete
