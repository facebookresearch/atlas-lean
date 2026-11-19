/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO16] CONJUNCTIVE SATISFIABILITY
WITH FUNCTIONS AND INEQUALITIES;
V. R. Pratt, "Two easy theories whose combination is hard", technical report, Massachusetts
Institute of Technology (1977), http://boole.stanford.edu/pub/sefnp.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities

/-!
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete

Given a conjunction of literals `t₁ R t₂` with `R ∈ {≤, >, =, ≠}`, where the terms `t₁, t₂` are
built from variables, integer constants and uninterpreted function symbols, is there an
assignment of integers to the variables and of functions on the integers to the function
symbols that satisfies every literal? Here `≤` and the integer constants have their standard
meaning on `ℤ`, and `>`, `≠` are the negations of `≤`, `=` (Pratt's "literals (possibly
negated atomic formulae)").

Terms are given as a list of nodes, each node one term occurrence:

* `(0, (x, 0), [])` is the variable number `x`;
* `(1, (p, q), [])` is the integer constant `p - q`;
* `(2, (f, 0), [j₁, …, jₖ])` is the function symbol number `f` applied to the terms at the
  earlier nodes `j₁, …, jₖ`.

A literal `(r, l, l')` relates the terms at nodes `l` and `l'` by `≤`, `>`, `=` or `≠` for
`r = 0, 1, 2, 3`. `WellFormed` requires every node to be used at most once (as an argument or a
literal side), so the nodes form a forest of term trees, the usual syntax of terms, and each
function symbol to have one arity. A function symbol `f` of arity `k` is interpreted by
`φ f : List ℤ → ℤ` on lists of length `k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A term node `(kind, (a, b), args)`: a variable (`kind = 0`), an integer constant `a - b`
(`kind = 1`), or the function symbol `a` applied to earlier nodes `args` (`kind = 2`). -/
abbrev TermNode := ℕ × (ℕ × ℕ) × List ℕ

/-- A literal `(r, l, l')`: the terms at nodes `l` and `l'` related by `≤`, `>`, `=`, `≠` for
`r = 0, 1, 2, 3`. -/
abbrev Literal := ℕ × ℕ × ℕ

/-- An instance: the term nodes and the literals. -/
abbrev ConjunctiveSatisfiabilityInstance := List TermNode × List Literal

/-- The value of one node given the values `vals` of the earlier nodes, under the variable
assignment `σ` and the interpretation `φ` of the function symbols. -/
def nodeValue (σ : ℕ → ℤ) (φ : ℕ → List ℤ → ℤ) (vals : List ℤ) (t : TermNode) : ℤ :=
  match t.1 with
  | 0 => σ t.2.1.1
  | 1 => (t.2.1.1 : ℤ) - t.2.1.2
  | _ => φ t.2.1.1 (t.2.2.map fun j => vals.getD j 0)

/-- The values of all nodes, computed in order. -/
def termValues (σ : ℕ → ℤ) (φ : ℕ → List ℤ → ℤ) (nodes : List TermNode) : List ℤ :=
  nodes.foldl (fun vals t => vals ++ [nodeValue σ φ vals t]) []

/-- The literal `l` holds for the node values `v`. -/
def LiteralHolds (v : List ℤ) (l : Literal) : Prop :=
  match l.1 with
  | 0 => v.getD l.2.1 0 ≤ v.getD l.2.2 0
  | 1 => v.getD l.2.2 0 < v.getD l.2.1 0
  | 2 => v.getD l.2.1 0 = v.getD l.2.2 0
  | _ => v.getD l.2.1 0 ≠ v.getD l.2.2 0

/-- Well-formedness of an instance: node kinds are `0`, `1` or `2`; only applications have
arguments, and those point to earlier nodes; unused number fields are `0`; each function
symbol has one arity; literal relations are `0` to `3` and literal sides are nodes; and every
node is used at most once, so the terms are trees. -/
def WellFormed (i : ConjunctiveSatisfiabilityInstance) : Prop :=
  (∀ k < i.1.length, (i.1.getD k (0, (0, 0), [])).1 ≤ 2 ∧
      ((i.1.getD k (0, (0, 0), [])).1 = 2 → ∀ j ∈ (i.1.getD k (0, (0, 0), [])).2.2, j < k) ∧
      ((i.1.getD k (0, (0, 0), [])).1 ≠ 2 → (i.1.getD k (0, (0, 0), [])).2.2 = []) ∧
      ((i.1.getD k (0, (0, 0), [])).1 ≠ 1 → (i.1.getD k (0, (0, 0), [])).2.1.2 = 0)) ∧
    (∀ t ∈ i.1, ∀ t' ∈ i.1, t.1 = 2 → t'.1 = 2 → t.2.1.1 = t'.2.1.1 →
      t.2.2.length = t'.2.2.length) ∧
    (∀ l ∈ i.2, l.1 ≤ 3 ∧ l.2.1 < i.1.length ∧ l.2.2 < i.1.length) ∧
    (i.1.flatMap (fun t => t.2.2) ++ i.2.flatMap (fun l => [l.2.1, l.2.2])).Nodup

/-- Some integer assignment `σ` and interpretation `φ` of the function symbols satisfy every
literal. -/
def ConjunctiveSatisfiabilityFeasible (i : ConjunctiveSatisfiabilityInstance) : Prop :=
  ∃ σ : ℕ → ℤ, ∃ φ : ℕ → List ℤ → ℤ, ∀ l ∈ i.2, LiteralHolds (termValues σ φ i.1) l

open Classical in
/-- CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES as a decision problem over
bitstrings. -/
noncomputable def conjunctiveSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveSatisfiabilityFeasible i)
  | none => false

/-- **CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES is NP-complete.** Source: Garey
and Johnson (1979), [LO16]; Pratt (1977). -/
public theorem_wanted conjunctiveSatisfiability_npComplete :
    conjunctiveSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities
