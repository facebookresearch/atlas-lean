/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REYNOLDS COVERING FOR REGULAR GRAMMARS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL11] REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS, p. 268, comment: "Remains NP-complete even if G₁ and G₂ are
restricted to "regular" grammars", attributed to
H. B. Hunt III and D. J. Rosenkrantz, "Complexity of grammatical similarity relations:
preliminary report", Proc. Conference on Theoretical Computer Science, University of
Waterloo (1977), 139-148 (original not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ReynoldsCoveringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReynoldsCoveringRegularGrammars

/-!
# REYNOLDS COVERING FOR REGULAR GRAMMARS is NP-complete

The problem REYNOLDS COVERING FOR CONTEXT-FREE GRAMMARS
(`MetaMathlibExt.Complexity.NPComplete.ReynoldsCovering`), restricted to instances in which
both grammars `G₁` and `G₂` are regular. Given context-free grammars
`G₁ = (N₁, Σ, Π₁, S₁)` and `G₂ = (N₂, Σ, Π₂, S₂)`, both regular, does `G₂` Reynolds cover
`G₁`: is there a function `f` from `N₁ ∪ Σ` to `N₂ ∪ Σ` with `f x = x` for every terminal `x`,
`f A ∈ N₂` for every `A ∈ N₁`, `f S₁ = S₂`, and such that for every production
`A → x₁ ⋯ xᵣ` of `Π₁` the image `f A → f x₁ ⋯ f xᵣ` is a production of `Π₂`?

The instance encoding, the well-formedness of the two grammars and the covering question are
those of `ReynoldsCovering`. A grammar is regular when it is right-linear: every production has
the form `A → w` or `A → w B` with `w ∈ Σ*` and `B` a nonterminal, i.e., every right-hand-side
symbol except possibly the last is a terminal. This is the broadest of the usual definitions
of a regular grammar (the forms `A → a B`, `A → a`, `A → ε` are special cases); a left-linear
version is equivalent, since reversing every right-hand side preserves Reynolds covers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A production `(A, w)` is right-linear when every symbol of `w` except possibly the last is
a terminal: it has the form `A → x₁ ⋯ xⱼ` or `A → x₁ ⋯ xⱼ B` with terminals `xᵢ`. -/
def IsRightLinearProduction (p : ℕ × List (Bool × ℕ)) : Prop :=
  ∀ x ∈ p.2.dropLast, x.1 = true

/-- A grammar is regular (right-linear) when every production is right-linear. -/
def IsRegularGrammar (g : ReynoldsCovering.GrammarData) : Prop :=
  ∀ p ∈ g.2.2, IsRightLinearProduction p

/-- Well-formedness of an instance: the instance is well-formed for REYNOLDS COVERING FOR
CONTEXT-FREE GRAMMARS, and both grammars are regular. -/
def WellFormed (i : ReynoldsCovering.ReynoldsCoveringInstance) : Prop :=
  ReynoldsCovering.WellFormed i ∧ IsRegularGrammar i.2.1 ∧ IsRegularGrammar i.2.2

open Classical in
/-- REYNOLDS COVERING FOR REGULAR GRAMMARS as a decision problem over bitstrings. -/
noncomputable def reynoldsCoveringRegularGrammarsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReynoldsCovering.ReynoldsCoveringInstance) x with
  | some i => decide (WellFormed i ∧ ReynoldsCovering.ReynoldsCoveringFeasible i)
  | none => false

/-- **REYNOLDS COVERING FOR REGULAR GRAMMARS is NP-complete.** Source: Garey and Johnson
(1979), [AL11], comment; Hunt and Rosenkrantz (1977). -/
public theorem_wanted reynoldsCoveringRegularGrammars_npComplete :
    reynoldsCoveringRegularGrammarsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reynoldsCoveringRegularGrammarsDec

end MetaMathlibExt.Complexity.NPComplete.ReynoldsCoveringRegularGrammars
