/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSAT is coNP-complete

Source:
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the Third Annual
ACM Symposium on Theory of Computing (STOC 1971), 151-158; L. A. Levin, "Universal search
problems", Problems of Information Transmission 9 (1973), 265-266.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.UNSATCoNPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# UNSAT is coNP-complete

UNSAT, the set of unsatisfiable CNF formulas, is `coNP`-complete: it is in `coNP` (its
complement, SAT, is in `NP`), and every `coNP` language polynomial-time many-one reduces to
it, by the Cook-Levin theorem applied to complements. TAUT, the set of tautologies, is
`coNP`-complete for the same reason: a formula is a tautology iff its negation is
unsatisfiable. The instance decodes to a variable count `n` and a CNF formula whose
variables are below `n`; malformed inputs are satisfiable (not in UNSAT).
-/

open Classical in
/-- **UNSAT as a decision problem.** The UNSAT decision problem accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, \varphi)$ of a natural
number $n$ and a CNF formula $\varphi$ such that every variable occurring in $\varphi$ is less
than $n$ and, for every assignment $a$ of booleans to the variables $0, \dots, n - 1$, the
assignment that agrees with $a$ below $n$ and sends every variable $v \ge n$ to false does not
satisfy $\varphi$. -/
noncomputable def unsatDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × Cslib.Logic.PL.CNF) x with
  | some i => decide ((∀ clause ∈ i.2, ∀ l ∈ clause, l.1 < i.1) ∧
      ∀ assign : Fin i.1 → Bool,
        ¬ Cslib.Logic.PL.CNF.Satisfies
          (fun v => if h : v < i.1 then assign ⟨v, h⟩ else false) i.2)
  | none => false

/-- **UNSAT is coNP-complete.** The UNSAT decision problem lies in coNP, and every decision
problem in coNP has a polynomial-time many-one reduction to it.

Source: S. A. Cook, "The complexity of theorem-proving
procedures", Proceedings of the Third Annual ACM Symposium on Theory of Computing (STOC
1971), 151-158; L. A. Levin, "Universal search problems", Problems of Information
Transmission 9 (1973), 265-266. -/
public theorem_wanted unsat_conp_complete :
    unsatDec ∈ MetaMathlibExt.ComplexityTheory.coNP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.coNP →
          Cslib.CookLevin.PolyManyOneRed L unsatDec

end MetaMathlibExt.Complexity.KeyTheorems.UNSATCoNPComplete
