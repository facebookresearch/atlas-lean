/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) is
# NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO4] CODE GENERATION ON A
ONE-REGISTER MACHINE (comment: NP-complete even if every vertex of in-degree larger than one has
arcs only to leaves, credited to Aho, Johnson and Ullman 1977);
A. V. Aho, S. C. Johnson and J. D. Ullman, "Code generation for expressions with common
subexpressions", Journal of the ACM 24(1) (1977), 146-160, doi:10.1145/321992.322001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OneRegisterCodeGenerationSharedLeafArcsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneRegisterCodeGenerationSharedLeafArcs

open CodeGenerationOnAOneRegisterMachine (Graph)

/-!
# CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) is
# NP-complete

The restriction of CODE GENERATION ON A ONE-REGISTER MACHINE to directed acyclic graphs in which
every vertex of in-degree larger than one (a shared subexpression) has arcs only to leaves
(vertices of out-degree `0`). The instance type, the base well-formedness, the machine and the
question are those of `CodeGenerationOnAOneRegisterMachineWanted`, reused unchanged; this module
adds only the restriction to `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) is
NP-complete.** Source: Garey and Johnson (1979), [PO4]; Aho, Johnson and Ullman (1977). -/
public theorem_wanted oneRegisterCodeGenerationSharedLeafArcs_npComplete :
    oneRegisterCodeGenerationSharedLeafArcsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oneRegisterCodeGenerationSharedLeafArcsDec

end MetaMathlibExt.Complexity.NPComplete.OneRegisterCodeGenerationSharedLeafArcs
