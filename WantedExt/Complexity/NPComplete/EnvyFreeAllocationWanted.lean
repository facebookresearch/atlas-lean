/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS is NP-complete

Source:
R. J. Lipton, E. Markakis, E. Mossel, and A. Saberi, "On approximately fair allocations of
indivisible goods", Proceedings of the 5th ACM Conference on Electronic Commerce (EC 2004),
125-131, doi:10.1145/988772.988792, Section 3.1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnvyFreeAllocation

/-!
# ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS is NP-complete

INSTANCE: a set `N = {1, ..., n}` of players, a set `M = {1, ..., m}` of indivisible goods, and
additive utilities given by an `n × m` matrix `V = (v_{p,i})` of nonnegative integers, so that
player `p` values a bundle `S ⊆ M` at `v_p(S) = ∑_{i ∈ S} v_{p,i}`.
QUESTION: is there an allocation `A = (A_1, ..., A_n)`, a partition of `M` in which some `A_p`
may be empty, that is envy-free, i.e. `v_p(A_q) ≤ v_p(A_p)` for all players `p` and `q`?

The definitions are those of Lipton, Markakis, Mossel and Saberi (Section 2: an allocation is a
partition of all goods into the players' bundles, player `p` envies `q` if
`v_p(A_p) < v_p(A_q)`; Section 3.1: additive utilities given by the matrix `V`). Their Section
3.1.1 states that deciding whether an envy-free allocation exists is NP-complete, already for
two players with the same utility function, where it is PARTITION. Membership in NP is
immediate: the allocation is the certificate.

Players are the rows of `V` and goods are `0, ..., m - 1`. An allocation assigns every good to
exactly one player, a function `A : Fin m → Fin n`; the bundle of `q` is `A⁻¹(q)`. Utilities
use the canonical binary encoding (for fixed `n` the problem is only weakly NP-complete).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of goods `m` and the utility matrix `V`, one row of `m` values per
player. -/
abbrev EnvyFreeAllocationInstance := ℕ × List (List ℕ)

/-- The utility `v_{p,g}` of good `g` for player `p`. -/
def utility (i : EnvyFreeAllocationInstance) (p : Fin i.2.length) (g : Fin i.1) : ℕ :=
  (i.2.get p).getD g 0

/-- Player `p`'s additive utility `v_p(A_q)` for the bundle `A_q = A⁻¹(q)` of player `q`. -/
def bundleUtility (i : EnvyFreeAllocationInstance) (A : Fin i.1 → Fin i.2.length)
    (p q : Fin i.2.length) : ℕ :=
  ∑ g ∈ Finset.univ.filter (fun g => A g = q), utility i p g

/-- Well-formedness of an instance: every row of `V` lists one utility per good. -/
def WellFormed (i : EnvyFreeAllocationInstance) : Prop :=
  ∀ row ∈ i.2, row.length = i.1

/-- Some allocation of all goods is envy-free: no player values another player's bundle more
than her own. -/
def EnvyFreeAllocationFeasible (i : EnvyFreeAllocationInstance) : Prop :=
  ∃ A : Fin i.1 → Fin i.2.length, ∀ p q, bundleUtility i A p q ≤ bundleUtility i A p p

open Classical in
/-- ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS as a decision problem over bitstrings. -/
noncomputable def envyFreeAllocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnvyFreeAllocationInstance) x with
  | some i => decide (WellFormed i ∧ EnvyFreeAllocationFeasible i)
  | none => false

/-- **ENVY-FREE ALLOCATION OF INDIVISIBLE GOODS is NP-complete.** Source: Lipton, Markakis,
Mossel, and Saberi (2004), Section 3.1.1. -/
public theorem_wanted envyFreeAllocation_npComplete :
    envyFreeAllocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L envyFreeAllocationDec

end MetaMathlibExt.Complexity.NPComplete.EnvyFreeAllocation
