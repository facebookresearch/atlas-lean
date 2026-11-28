/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR36] SAFETY OF FILE PROTECTION
SYSTEMS, p. 235 (comment: "If no command can contain more than one operation, then the problem
is NP-complete in general and solvable in polynomial time for fixed systems");
M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems",
Communications of the ACM 19 (1976), 461-471, doi:10.1145/360303.360333 (Section 3: the
model; Section 4: safety, mono-operational systems, and NP-completeness of their safety
problem by a reduction from CLIQUE).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystemsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems

/-!
# SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS is NP-complete

INSTANCE: a set `R` of generic rights, a set `O` of objects, a set `S ⊆ O` of subjects, sets
`P(s, o) ⊆ R` of rights for each subject `s ∈ S` and object `o ∈ O` (the access matrix), a
finite set `C` of commands, each of the form "if `r₁ ∈ P(X₁, Y₁)` and ... and `rₘ ∈ P(Xₘ, Yₘ)`
then `θ`" (`m ≥ 0`) with a single operation `θ` of the form "enter `r` into `P(X, Y)`" or
"delete `r` from `P(X, Y)`", and a specified right `r' ∈ R`.
QUESTION: is there a sequence of commands from `C`, with actual parameters, such that at some
point in its execution the right `r'` is entered into a set `P(s, o)` that previously did not
contain `r'`?

This is [SR36] SAFETY OF FILE PROTECTION SYSTEMS restricted, as in Garey and Johnson's comment,
to commands with at most one operation (Harrison, Ruzzo and Ullman's "mono-operational"
systems). In [SR36] every operation has the form "enter `rᵢ` into `P(Xⱼ, Yₖ)`" or "delete `rᵢ`
from `P(Xⱼ, Yₖ)`"; operations that create or destroy subjects or objects are not part of the
problem (Garey and Johnson's comment: it becomes undecidable if they are allowed), so the sets
`S` and `O` stay fixed. A command without an
operation changes nothing and enters nothing, so every command here has exactly one operation.
Garey and Johnson defer the execution of commands to Harrison, Ruzzo and Ullman, whose
definitions are followed:

* `R = {0, …, g - 1}`, `O = {0, …, |O| - 1}`, and `S = {0, …, |S| - 1}` with `|S| ≤ |O|`. An
  access matrix is the set of triples `(s, o, r)` with `r ∈ P(s, o)`.
* A command `(k, conds, (e, r, a, b))` has the formal parameters `X₀, …, X_{k-1}`, the
  conditions `(r₁, a₁, b₁) ∈ conds`, each "`r₁` in `(X_{a₁}, X_{b₁})`", and the operation
  "enter `r` into `(X_a, X_b)`" (`e = true`) or "delete `r` from `(X_a, X_b)`" (`e = false`).
  The rights in a command are fixed generic rights; only objects are parameters.
* Running a command replaces its formal parameters by actual parameters, which are objects
  (`x j < |O|`). It is executable when its conditions hold (`r₁ ∈ P(x a₁, x b₁)`) and its
  operation can be executed, which requires the row `x a` to be a subject (`x a < |S|`). It
  then enters `r` into, or deletes `r` from, the cell `(x a, x b)` (`Step`). A command whose
  conditions fail leaves the matrix unchanged, so such runs are omitted from `Step`.
* A command leaks `r'` from a matrix `P` when it is executable there and enters `r'` into a
  cell that does not contain `r'` (`Leaks`); the question asks for a matrix reachable from the
  initial one by `Step` from which some command leaks `r'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS is NP-complete.** Source: Garey and
Johnson (1979), [SR36], comment; Harrison, Ruzzo and Ullman (1976). -/
public theorem_wanted safetyOfMonoOperationalProtectionSystems_npComplete :
    safetyOfMonoOperationalProtectionSystemsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L safetyOfMonoOperationalProtectionSystemsDec

end MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems
