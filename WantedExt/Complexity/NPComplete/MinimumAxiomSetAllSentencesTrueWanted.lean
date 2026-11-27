/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AXIOM SET with all sentences true is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO17] MINIMUM AXIOM SET, comment on
p. 263 ("Remains NP-complete even if T = S");
P. Pudlák, "Polynomially complete problems in the logic of automated
discovery", Mathematical Foundations of Computer Science 1975, Lecture Notes in
Computer Science 32, Springer (1975), 358-361, doi:10.1007/3-540-07389-2_221.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumAxiomSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue

open MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
  (MinimumAxiomSetInstance MinimumAxiomSetFeasible)

/-!
# MINIMUM AXIOM SET with all sentences true is NP-complete

INSTANCE: a finite set `S` of "sentences", the subset `T = S` of "true sentences", an
"implication relation" `R` consisting of pairs `(A, s)` where `A ⊆ S` and `s ∈ S`, and a
positive integer `K ≤ |S|`. QUESTION: is there a subset `S₀ ⊆ T` with `|S₀| ≤ K` and a
positive integer `n` such that, if we define `Sᵢ`, `1 ≤ i ≤ n`, to consist of exactly those
`s ∈ S` for which either `s ∈ Sᵢ₋₁` or there exists a `U ⊆ Sᵢ₋₁` such that `(U, s) ∈ R`, then
`Sₙ = T`?

The instance and the question are those of MINIMUM AXIOM SET
(`WantedExt.Complexity.NPComplete.MinimumAxiomSetWanted`: sentences `0, ..., |S| - 1`, the true
sentences `T` as a list, the pairs of `R` as premise lists with a conclusion, and the bound `K`
with `0 < K ≤ |S|`; the question asks for at most `K` true sentences whose `n`-th derivation
round, for some `n ≥ 1`, is exactly `T`). The restriction `T = S` adds that every sentence
`x < |S|` is listed in `T`; the parent's well-formedness already puts every listed true sentence
below `|S|`.

Garey and Johnson record that the problem remains NP-complete when `T = S`, in the entry whose
reference is Pudlák (1975) (transformation from EXACT COVER BY 3-SETS); that paper was not
available. Membership in NP is inherited from MINIMUM AXIOM SET: the certificate is `S₀`, and
the rounds stabilize after at most `|S|` steps, so the existence of `n` is checked in
polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MINIMUM AXIOM SET instance in which every
sentence is true (`T = S`). -/
def WellFormed (i : MinimumAxiomSetInstance) : Prop :=
  MinimumAxiomSet.WellFormed i ∧ ∀ x < i.1, x ∈ i.2.1

open Classical in
/-- MINIMUM AXIOM SET with all sentences true as a decision problem over bitstrings. -/
noncomputable def minimumAxiomSetAllSentencesTrueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAxiomSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumAxiomSetFeasible i)
  | none => false

/-- **MINIMUM AXIOM SET with all sentences true is NP-complete.** Source: Garey and Johnson
(1979), [LO17]; Pudlák (1975). -/
public theorem_wanted minimumAxiomSetAllSentencesTrue_npComplete :
    minimumAxiomSetAllSentencesTrueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumAxiomSetAllSentencesTrueDec

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue
