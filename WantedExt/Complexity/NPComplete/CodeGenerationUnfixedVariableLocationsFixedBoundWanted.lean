/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS with B = 31 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO8] CODE GENERATION WITH UNFIXED
VARIABLE LOCATIONS, p. 274, comment: "Remains NP-complete even for certain fixed values of B,
e.g., B = 31" (reference [Robertson, 1977]: E. L. Robertson, "Code generation for short/long
address machines", technical report, 1977; not available, the result and its attribution are
those recorded by Garey and Johnson);
journal version: E. L. Robertson, "Code generation and storage allocation for machines with
span-dependent instructions", ACM Transactions on Programming Languages and Systems 1 (1979),
71-83, doi:10.1145/357062.357067.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocationsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocationsFixedBound

open MetaMathlibExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocations
  (CodeGenerationUnfixedVariableLocationsFeasible)

/-!
# CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS with B = 31 is NP-complete

INSTANCE: a sequence `I = (I₁, I₂, …, Iₙ)` of instructions, a finite set `V` of variables, an
assignment `g : I → I ∪ V`, and a positive integer `M`; the bound is fixed at `B = 31`.
QUESTION: is there a one-to-one function `f : I ∪ V → {1, 2, …, M}` such that
`f(Iᵢ) < f(Iⱼ)` whenever `i < j` and such that, for `1 ≤ i ≤ n`, either
`|f(Iᵢ) - f(g(Iᵢ))| < 31` or `f(Iᵢ) + 1` is not in the range of `f`?

This is [PO8] (`WantedExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocationsWanted`)
with `B` no longer part of the instance but fixed at the value the [PO8] comment names,
`B = 31`. The encoding of `V` and `g`, its well-formedness and the question (including the
requirement that a two-byte instruction's second byte also lies in `{1, …, M}`) are those of
that module, applied to `(m, g, 31, M)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(m, g, M)`: the number `m` of variables, the targets `g(I₁), …, g(Iₙ)`
(encoded as in [PO8]), and the memory bound `M`. -/
abbrev CodeGenerationUnfixedVariableLocationsFixedBoundInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The [PO8] instance with `B = 31`. -/
def withBound (i : CodeGenerationUnfixedVariableLocationsFixedBoundInstance) :
    CodeGenerationUnfixedVariableLocations.CodeGenerationUnfixedVariableLocationsInstance :=
  (i.1, i.2.1, 31, i.2.2)

/-- Well-formedness of an instance: the [PO8] instance with `B = 31` is well formed (every
`g(Iᵢ)` names an instruction or a variable, and `M` is positive). -/
def WellFormed (i : CodeGenerationUnfixedVariableLocationsFixedBoundInstance) : Prop :=
  CodeGenerationUnfixedVariableLocations.WellFormed (withBound i)

/-- The [PO8] question with `B = 31`. -/
def CodeGenerationUnfixedVariableLocationsFixedBoundFeasible
    (i : CodeGenerationUnfixedVariableLocationsFixedBoundInstance) : Prop :=
  CodeGenerationUnfixedVariableLocationsFeasible (withBound i)

open Classical in
/-- CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS with `B = 31` as a decision problem over
bitstrings. -/
noncomputable def codeGenerationUnfixedVariableLocationsFixedBoundDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationUnfixedVariableLocationsFixedBoundInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationUnfixedVariableLocationsFixedBoundFeasible i)
  | none => false

/-- **CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS with `B = 31` is NP-complete.** Source:
Garey and Johnson (1979), [PO8], comment; Robertson (1977). -/
public theorem_wanted codeGenerationUnfixedVariableLocationsFixedBound_npComplete :
    codeGenerationUnfixedVariableLocationsFixedBoundDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationUnfixedVariableLocationsFixedBoundDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationUnfixedVariableLocationsFixedBound
