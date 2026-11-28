/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LOBBYING IN MULTIPLE REFERENDA is NP-complete

Source:
R. Christian, M. Fellows, F. Rosamond, and A. Slinko, "On complexity of lobbying in multiple
referenda", Review of Economic Design 11(3) (2007), 217-224, doi:10.1007/s10058-007-0028-1
(OPTIMAL LOBBYING is W[2]-complete for the parameter `b`, hence NP-hard);
problem statement as restated by G. Erdélyi, H. Fernau, J. Goldsmith, N. Mattei, D. Raible,
and J. Rothe, "The complexity of probabilistic lobbying", arXiv:0906.4431 (Section 1.1,
OPTIMAL LOBBYING; Section 4.2: the W[2]-hardness "implies NP-hardness of OL").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LobbyingInMultipleReferendaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda

/-!
# LOBBYING IN MULTIPLE REFERENDA is NP-complete

OPTIMAL LOBBYING. INSTANCE: an `m × n` 0/1 matrix `E`, each row a voter and each column an issue
(entry `1` if the voter votes "yes" on the issue), a 0/1 target vector `Z` of length `n` (the
lobby's desired outcome), and a positive integer `b`. QUESTION: is there a choice of `b` rows of
`E` (`b` voters) that can be changed so that in each column of the resulting matrix a strict
majority vote yields the outcome targeted by the lobby?

Following the source, the lobby needs a strict majority for its target on every issue: more
than half of the `m` voters vote the targeted outcome (`m < 2 · #target`); a tie is a strict
majority for neither outcome. (`majorityOutcome` is the yes-majority outcome, which reads a tie
as "no"; feasibility does not use it.) The matrix is given by its rows, each a list of `n`
Booleans, so the instance lists all `m · n` entries; "a choice of `b` rows" presupposes
`b ≤ m`, which `WellFormed` records.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LOBBYING IN MULTIPLE REFERENDA is NP-complete.** Source: Christian, Fellows, Rosamond,
and Slinko (2007); Erdélyi, Fernau, Goldsmith, Mattei, Raible, and Rothe (arXiv:0906.4431). -/
public theorem_wanted lobbyingInMultipleReferenda_npComplete :
    lobbyingInMultipleReferendaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lobbyingInMultipleReferendaDec

end MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda
