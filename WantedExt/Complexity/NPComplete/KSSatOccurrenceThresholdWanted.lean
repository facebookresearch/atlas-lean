/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (k,s)-SAT at the occurrence threshold is NP-complete

Source:
J. Kratochvíl, P. Savický and Z. Tuza, "One more occurrence of variables makes satisfiability
jump from trivial to NP-complete", SIAM Journal on Computing 22 (1993), 203-210,
doi:10.1137/0222015.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Basic
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSSatOccurrenceThreshold

open Cslib.Logic.PL

/-!
# (k,s)-SAT at the occurrence threshold is NP-complete

A `(k, s)`-formula is a CNF formula in which every clause contains exactly `k` distinct
variables and every variable occurs in at most `s` clauses; `(k, s)`-SAT is satisfiability
restricted to `(k, s)`-formulas. For `k ≥ 3`, `f(k)` is the largest `s` for which every
`(k, s)`-formula is satisfiable.

INSTANCE (`k ≥ 3` fixed, `s ≥ f(k) + 1` fixed): a `(k, s)`-formula `φ`.
QUESTION: is `φ` satisfiable?

Kratochvíl, Savický and Tuza prove that for every `k ≥ 3` such an `f(k)` exists, that
`(k, s)`-SAT is trivial for `s ≤ f(k)` (every `(k, s)`-formula is satisfiable), and that it is
NP-complete for every `s ≥ f(k) + 1`; the case `s = f(k) + 1` is the occurrence threshold. They
also show `⌊2^k / (e k)⌋ ≤ f(k) ≤ 2^(k-1) - 2^(k-4) - 1` for `k ≥ 4`.

Formulas are CSLib's `Cslib.Logic.PL.CNF` (clauses are lists of literals
`(variable, polarity)`, a formula is a list of clauses) and satisfiability is
`Cslib.Logic.PL.CNFSat`. A clause contains exactly `k` distinct variables when it has `k`
literals whose variables are pairwise distinct. A variable occurs in a clause when the clause
has a literal on it; occurrences are counted over the list of clauses, so a repeated clause is
counted each time. `f(k)` is `kSThreshold k`, the supremum of the `s` for which every
`(k, s)`-formula is satisfiable, which for `k ≥ 3` is the largest such `s`; the theorem is
stated for every fixed `k ≥ 3` and every fixed `s ≥ kSThreshold k + 1`, each pair giving its
own decision problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **(k,s)-SAT is NP-complete for every `k ≥ 3` and every `s ≥ f(k) + 1`**, in particular at
the occurrence threshold `s = f(k) + 1`. Source: Kratochvíl, Savický and Tuza (1993). -/
public theorem_wanted kSSatOccurrenceThreshold_npComplete (k s : ℕ) (hk : 3 ≤ k)
    (hs : kSThreshold k + 1 ≤ s) :
    kSSatDec k s ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kSSatDec k s)

end MetaMathlibExt.Complexity.NPComplete.KSSatOccurrenceThreshold
