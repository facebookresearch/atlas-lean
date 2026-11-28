/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasDefs

/-!
# MATCHING FOR FINITELY PRESENTED ALGEBRAS: definitions

UNIFICATION FOR FINITELY PRESENTED ALGEBRAS ([AN17],
`UnificationForFinitelyPresentedAlgebrasWanted`) restricted to instances in which only one of
the two expressions `e` and `f` contains variable symbols. INSTANCE: a finite presentation of an
algebra `A` (generators `G`, operators `O` of various finite dimensions, defining relations `Γ`),
a variable set `V`, and two well-formed expressions `e` and `f` over `G`, `O` and `V`, exactly
one of which contains a variable symbol. QUESTION: is there an assignment to each `v ∈ V` of a
unique term `I(v)` over `G` and `O` such that `I(e)` and `I(f)` represent the same element of
`A`?

The instance, the term encoding and the question are those of
`UnificationForFinitelyPresentedAlgebrasDefs`; only the restriction is new, in `WellFormed`.
In the token lists of the instance a variable symbol is a token `(0, v)` (`HasVariable`), and
"only one of `e` and `f`" is read as exactly one; the comment treats the case where neither
expression contains a variable separately (solvable in polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN17] UNIFICATION FOR FINITELY
PRESENTED ALGEBRAS, p. 253 (comment: "Remains NP-complete if only one of e and f contains
variable symbols, but is solvable in polynomial time if neither contains variable symbols.");
D. Kozen, "Complexity of finitely presented algebras", Proceedings of the 9th
Annual ACM Symposium on Theory of Computing (STOC 1977), 164-177,
doi:10.1145/800105.803406.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatchingForFinitelyPresentedAlgebras

open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras
  (UnificationForFinitelyPresentedAlgebrasInstance UnificationForFinitelyPresentedAlgebrasFeasible)

/-- A token list contains a variable symbol: some token `(0, v)`. -/
def HasVariable (l : List (ℕ × ℕ)) : Prop :=
  ∃ t ∈ l, t.1 = 0

/-- Well-formedness of an instance: the [AN17] well-formedness, and exactly one of the two
expressions `e`, `f` contains a variable symbol. -/
def WellFormed (i : UnificationForFinitelyPresentedAlgebrasInstance) : Prop :=
  UnificationForFinitelyPresentedAlgebras.WellFormed i ∧
    (HasVariable i.2.2.2.2.1 ∧ ¬ HasVariable i.2.2.2.2.2 ∨
      HasVariable i.2.2.2.2.2 ∧ ¬ HasVariable i.2.2.2.2.1)

open Classical in
/-- MATCHING FOR FINITELY PRESENTED ALGEBRAS as a decision problem over bitstrings. -/
noncomputable def matchingForFinitelyPresentedAlgebrasDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnificationForFinitelyPresentedAlgebrasInstance) x with
  | some i => decide (WellFormed i ∧ UnificationForFinitelyPresentedAlgebrasFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatchingForFinitelyPresentedAlgebras
