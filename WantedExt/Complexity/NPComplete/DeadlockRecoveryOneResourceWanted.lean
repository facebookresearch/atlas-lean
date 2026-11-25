/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK RECOVERY with a single resource type is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4(3)
(1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem [3] DEADLOCK RECOVERY, comment
("NP-complete but solvable in time pseudo-polynomial in K if m = 1", credited there to
J. Y.-T. Leung, "Complexity of optimal deadlock recovery", manuscript (1983), which was not
available), with the question as corrected in the column of Journal of Algorithms 5(1) (1984),
147-160, doi:10.1016/0196-6774(84)90045-2 (which says the results of that manuscript and of
Leung and Lai concern the sequential version);
J. Y.-T. Leung and E. K. Lai, "On minimum cost recovery from system deadlock", IEEE Transactions
on Computers C-28(9) (1979), 671-677, doi:10.1109/TC.1979.1675435.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DeadlockRecoveryWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockRecoveryOneResource

open MetaMathlibExt.Complexity.NPComplete.DeadlockRecovery
  (DeadlockRecoveryInstance numResources DeadlockRecoveryFeasible)

/-!
# DEADLOCK RECOVERY with a single resource type is NP-complete

INSTANCE: DEADLOCK RECOVERY with `m = 1`: one resource `R₁` with integer bound `B₁`, a set `P`
of blocked processes, each process `p` having a non-negative integer cost `c(p)`, a currently
allocated amount `r₁(p)` and a current request `a₁(p)` with (a) `r₁(p) + a₁(p) ≤ B₁` and
(b) `a₁(p) + Σ_{p ∈ P} r₁(p) > B₁`, and an overall cost bound `K`.
QUESTION: is there a subset `P' ⊆ P` with `Σ_{p ∈ P'} c(p) ≤ K` such that, if all processes in
`P'` are aborted and their resources returned to the common pool, the remaining processes can
proceed to completion in some sequence, each in turn taking all it requests, finishing, and
returning all it holds?

The instance, the well-formedness and the question are those of DEADLOCK RECOVERY
(`WantedExt.Complexity.NPComplete.DeadlockRecoveryWanted`: the resource bounds, the processes
`(c(p), r(p), a(p))` and `K`, with the sequential question of the March 1984 column as a
reduction sequence of the remaining processes). The restriction adds that the bound list has
length `m = 1`. Johnson's March 1984 column says the results of Leung's 1983 manuscript, the
source of the `m = 1` case, concern this sequential version.

Numbers use the canonical binary encoding: with `m = 1` the problem is NP-complete but solvable
in time pseudo-polynomial in `K` (Johnson's September 1983 column).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DEADLOCK RECOVERY instance with exactly one
resource type (`m = 1`). -/
def WellFormed (i : DeadlockRecoveryInstance) : Prop :=
  DeadlockRecovery.WellFormed i ∧ numResources i = 1

open Classical in
/-- DEADLOCK RECOVERY with a single resource type as a decision problem over bitstrings. -/
noncomputable def deadlockRecoveryOneResourceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DeadlockRecoveryInstance) x with
  | some i => decide (WellFormed i ∧ DeadlockRecoveryFeasible i)
  | none => false

/-- **DEADLOCK RECOVERY with a single resource type is NP-complete.** Source: Johnson (1983,
1984), NP-completeness column, crediting Leung (1983); Leung and Lai (1979). -/
public theorem_wanted deadlockRecoveryOneResource_npComplete :
    deadlockRecoveryOneResourceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deadlockRecoveryOneResourceDec

end MetaMathlibExt.Complexity.NPComplete.DeadlockRecoveryOneResource
