/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QSAT_k is Sigma_k^P-complete, uniformly in k

Source:
L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3 (1977),
1-22; A. R. Meyer, "A polynomial hierarchy" (see also S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Chapter 5).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.QSATKComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# QSAT_k is Sigma_k^P-complete, uniformly in k

`QSAT_k`, the set of true quantified Boolean formulas whose quantifier prefix has exactly `k`
alternating blocks (starting with `∃`), is `Σ_k^p`-complete, uniformly in `k`: for every
`k ≥ 1`, `QSAT_k` is in `Σ_k^p` and every `Σ_k^p` language polynomial-time many-one
reduces to it. The case `k = 1` is SAT, the case of unbounded `k` is TQBF. (For `k = 0` the
statement would be false: quantifier-free satisfiability is NP-complete, while `Σ_0^p = P`,
so the uniform statement is over `k + 1`.) The matrix is an unrestricted Boolean circuit
(AND/OR/NOT gates over the quantified variables, with sharing), not a CNF: a CNF
matrix does not give the claimed complete problem at every depth. For example, with a CNF
matrix, `QSAT_2` is `∃ ∀ CNF`, and after guessing the existential variables the universal
part is checkable clause-by-clause in polynomial time (a CNF is universally valid iff
every clause is), so the CNF version would lie in `NP`, and `Σ_2^p`-hardness would collapse
`Σ_2^p` to `NP`. The instance decodes to a quantifier prefix (existential `true` /
universal `false` paired with a variable index) and an unrestricted circuit matrix;
well-formedness requires the prefix to be nonempty with first quantifier existential,
to quantify each variable `0, …, m - 1` exactly once, every formula variable to be
quantified, and the prefix to have exactly `k` blocks.
-/

/-- A gate of the matrix circuit: `(kind, refs)` with kinds `0` variable (refs `[v]`),
`1` constant (refs `[b]`, true iff `b = 1`), `2` negation, `3` conjunction, `4`
disjunction. A circuit matrix is an unrestricted Boolean formula (with sharing), not a
CNF: see above. -/
abbrev QBFMatrixGate := ℕ × List ℕ

/-- Value of one matrix-circuit gate, given the values of earlier gates and the
variable assignment. This evaluator stays local (it does not use the shared
`circuitEval`): the assignment here is `ℕ → Bool`, with unbounded variable
indices coming from the quantifier prefix, so the typed `Fin n` evaluator
does not apply directly. -/
def qbfGateEval (vs : List Bool) (assign : ℕ → Bool) : QBFMatrixGate → Bool
  | (0, [v]) => assign v
  | (1, [b]) => b = 1
  | (2, [a]) => !(vs.getD a false)
  | (3, l) => l.all (fun a => vs.getD a false)
  | (4, l) => l.any (fun a => vs.getD a false)
  | _ => false

/-- Values of all gates of a matrix circuit, in order. -/
def qbfCircuitEval (C : List QBFMatrixGate) (assign : ℕ → Bool) : List Bool :=
  C.foldl (fun vs g => vs ++ [qbfGateEval vs assign g]) []

/-- Variables occurring in a matrix circuit. -/
def qbfCircuitVars (C : List QBFMatrixGate) : List ℕ :=
  C.flatMap (fun g => match g with | (0, [v]) => [v] | _ => [])

/-- Well-formedness of a matrix circuit: every non-variable, non-constant gate
references only strictly earlier gates. -/
def qbfCircuitWellFormed (C : List QBFMatrixGate) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ (C[j]'h).2,
    (C[j]'h).1 = 2 ∨ (C[j]'h).1 = 3 ∨ (C[j]'h).1 = 4 → a < j

/-- Evaluation of a quantified Boolean formula over an assignment. -/
def EvalQBFK (pref : List (Bool × ℕ)) (φ : List QBFMatrixGate)
    (assign : ℕ → Bool) : Prop :=
  match pref with
  | [] => (qbfCircuitEval φ assign).getLast? = some true
  | (isEx, v) :: rest =>
    if isEx then
      EvalQBFK rest φ (Function.update assign v true) ∨
        EvalQBFK rest φ (Function.update assign v false)
    else
      EvalQBFK rest φ (Function.update assign v true) ∧
        EvalQBFK rest φ (Function.update assign v false)

/-- Number of blocks of the current quantifier run, given the previous quantifier. -/
def blockCountAux (prev : Bool) : List (Bool × ℕ) → ℕ
  | [] => 0
  | (b, _) :: rest => (if b = prev then 0 else 1) + blockCountAux b rest

/-- Number of alternating quantifier blocks in a prefix. -/
def blockCount : List (Bool × ℕ) → ℕ
  | [] => 0
  | (b, _) :: rest => 1 + blockCountAux b rest

open Classical in
/-- `QSAT_k` as a decision problem over bitstrings, decoding to `(prefix, φ)`. -/
noncomputable def qsatKDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List (Bool × ℕ) × List QBFMatrixGate) x with
  | some i => decide (
      i.1.head?.map Prod.fst = some true ∧
      List.Perm (i.1.map Prod.snd) (List.range i.1.length) ∧
      (∀ v ∈ qbfCircuitVars i.2, v < i.1.length) ∧ qbfCircuitWellFormed i.2 ∧
      blockCount i.1 = k ∧
      EvalQBFK i.1 i.2 (fun _ => false))
  | none => false

/-- **QSAT_k is Sigma_k^P-complete, uniformly in k.** Source: L. J. Stockmeyer, "The
polynomial-time hierarchy", Theoretical Computer Science 3 (1977), 1-22; A. R. Meyer, "A
polynomial hierarchy" (see also S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Chapter 5). -/
public theorem_wanted qsat_k_sigma_k_complete :
    ∀ k : ℕ, qsatKDec (k + 1) ∈ SigmaK (k + 1) ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ SigmaK (k + 1) → Cslib.CookLevin.PolyManyOneRed L (qsatKDec (k + 1))

end MetaMathlibExt.Complexity.KeyTheorems.QSATKComplete
