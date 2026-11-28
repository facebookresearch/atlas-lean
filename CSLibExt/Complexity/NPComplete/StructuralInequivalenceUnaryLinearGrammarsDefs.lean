/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL13] STRUCTURAL INEQUIVALENCE
FOR LINEAR GRAMMARS, comment ("NP-complete if `|Σ| = 1`");
H. B. Hunt III, D. J. Rosenkrantz and T. G. Szymanski, "On the equivalence, containment,
and covering problems for the regular and context-free languages", Journal of Computer and
System Sciences 12 (1976), 222-268, doi:10.1016/S0022-0000(76)80038-4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembershipDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StructuralInequivalenceUnaryLinearGrammars

open MetaMathlibExt.Complexity.NPComplete.QuasiRealTimeLanguageMembership
  (GrammarData toEncodedCFG GrammarWellFormed)

/-- An instance: the number `k` of terminals (the terminal alphabet is `{0, ..., k - 1}`)
and the grammars `G₁` and `G₂`. -/
abbrev StructuralInequivalenceUnaryLinearGrammarsInstance := ℕ × GrammarData × GrammarData

/-- A grammar is linear when no production has more than one nonterminal symbol on its
right-hand side. -/
def IsLinear (g : GrammarData) : Prop :=
  ∀ p ∈ g.2.2, (p.2.filter fun x => !x.1).length ≤ 1

/-- The parenthesized grammar over the terminals `{0, ..., k + 1}`: every production
`A → w` is replaced by `A → (w)`, where `(` is the new terminal `k` and `)` is the new
terminal `k + 1`. -/
def parenthesize (k : ℕ) (g : GrammarData) : GrammarData :=
  (g.1, g.2.1, g.2.2.map fun p => (p.1, (true, k) :: p.2 ++ [(true, k + 1)]))

/-- Well-formedness of an instance: the terminal alphabet has exactly one letter (`k = 1`),
and both grammars are well-formed over it and linear. -/
def WellFormed : StructuralInequivalenceUnaryLinearGrammarsInstance → Prop
  | (k, g₁, g₂) =>
    k = 1 ∧ GrammarWellFormed k g₁ ∧ GrammarWellFormed k g₂ ∧ IsLinear g₁ ∧ IsLinear g₂

/-- `G₁` and `G₂` are structurally inequivalent: their parenthesized grammars generate
different languages. -/
def StructuralInequivalenceUnaryLinearGrammarsFeasible :
    StructuralInequivalenceUnaryLinearGrammarsInstance → Prop
  | (k, g₁, g₂) =>
    (toEncodedCFG (parenthesize k g₁)).language ≠ (toEncodedCFG (parenthesize k g₂)).language

open Classical in
/-- STRUCTURAL INEQUIVALENCE FOR LINEAR GRAMMARS over a one-letter alphabet as a decision
problem over bitstrings. -/
noncomputable def structuralInequivalenceUnaryLinearGrammarsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StructuralInequivalenceUnaryLinearGrammarsInstance) x with
  | some i => decide (WellFormed i ∧ StructuralInequivalenceUnaryLinearGrammarsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StructuralInequivalenceUnaryLinearGrammars
