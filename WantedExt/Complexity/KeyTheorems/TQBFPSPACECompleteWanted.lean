/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TQBF is PSPACE-complete

Source:
L. J. Stockmeyer and A. R. Meyer, "Word problems requiring exponential time", Proceedings of
the Fifth Annual ACM Symposium on Theory of Computing (STOC 1973), 1-9; C. H. Papadimitriou,
Computational Complexity, 1994, Theorem 7.4.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.TQBFPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# TQBF is PSPACE-complete

True quantified Boolean formulas are `PSPACE`-complete: `tqbfDec` is in `PSPACE` and every
`PSPACE` language polynomial-time many-one reduces to it. The instance decodes to a quantifier
prefix (existential `true` / universal `false` paired with a variable index) and a CNF formula;
well-formedness requires the prefix to quantify each variable `0, …, m - 1` exactly once and
every formula variable to be quantified.
-/


/-- Evaluation of a quantified Boolean formula over an assignment. -/
def EvalQBF (pref : List (Bool × ℕ)) (φ : Cslib.Logic.PL.CNF)
    (assign : ℕ → Bool) : Prop :=
  match pref with
  | [] => Cslib.Logic.PL.CNF.Satisfies assign φ
  | (isEx, v) :: rest =>
    if isEx then
      EvalQBF rest φ (Function.update assign v true) ∨
        EvalQBF rest φ (Function.update assign v false)
    else
      EvalQBF rest φ (Function.update assign v true) ∧
        EvalQBF rest φ (Function.update assign v false)

open Classical in
/-- TQBF as a decision problem over bitstrings. -/
noncomputable def tqbfDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List (Bool × ℕ) × Cslib.Logic.PL.CNF) x with
  | some i => decide (
      List.Perm (i.1.map Prod.snd) (List.range i.1.length) ∧
      (∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1.length) ∧
      EvalQBF i.1 i.2 (fun _ => false))
  | none => false

/-- **TQBF is PSPACE-complete.** Source: L. J. Stockmeyer and A. R. Meyer, "Word problems
requiring exponential time", Proceedings of the Fifth Annual ACM Symposium on Theory of
Computing (STOC 1973), 1-9; C. H. Papadimitriou, Computational Complexity, 1994, Theorem
7.4. -/
public theorem_wanted tqbf_pspace_complete :
    tqbfDec ∈ PSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L tqbfDec

end MetaMathlibExt.Complexity.KeyTheorems.TQBFPSPACEComplete
