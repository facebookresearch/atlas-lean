/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete

Source:
E. Ronn, "NP-complete stable matching problems", Journal of Algorithms 11 (1990), 285-304,
doi:10.1016/0196-6774(90)90007-2;
problem definitions as in Á. Cseh, R. W. Irving and D. F. Manlove, "The stable roommates
problem with short lists", Theory of Computing Systems 63 (2019), 128-149,
doi:10.1007/s00224-017-9810-9, Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies

/-!
# STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete

Cseh, Irving and Manlove (2019), Section 1: in the Stable Roommates problem with Incomplete
lists (SRI) a graph `G = (A, E)` and preference lists are given; agent `aᵢ`'s list `≺ᵢ` is a
linear order on the agents adjacent to `aᵢ`. For a matching `M` of `G`, `M(aᵢ)` is the partner
of `aᵢ`. An edge `aᵢaⱼ ∉ M` blocks `M` if `aᵢ` is unmatched or prefers `aⱼ` to `M(aᵢ)`, and
similarly `aⱼ` is unmatched or prefers `aᵢ` to `M(aⱼ)`; `M` is stable if no edge blocks it,
and an instance is solvable if it admits a stable matching. In SRTI each `≺ᵢ` is a strict weak
ordering (ties allowed), preference meaning strict preference; SRT is the special case
`G = Kₙ` (every agent ranks all others). Ronn (1990) proved that deciding whether a given SRT
instance is solvable is NP-complete.

Agents are `0, …, n - 1`. Agent `v`'s strict weak ordering is given by ranks: `v` prefers `w`
to `w'` iff `rank v w < rank v w'`, and equal ranks are ties (every strict weak ordering of a
finite set arises this way; the rank of `v` itself is ignored). A matching of `Kₙ` is given by
its partner function `μ`, an involution: `μ v = w ≠ v` means `v` and `w` are matched, and
`μ v = v` means `v` is unmatched.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of agents and the rank table; row `v`, entry `w` is the rank of
`w` in agent `v`'s preference list (smaller is better, equal ranks are ties). -/
abbrev StableRoommatesWithTiesInstance := ℕ × List (List ℕ)

/-- The rank of agent `w` in agent `v`'s preference list. -/
def rank (i : StableRoommatesWithTiesInstance) (v w : Fin i.1) : ℕ :=
  (i.2.getD v []).getD w 0

/-- The edge `vw` blocks the matching with partner function `μ`: `v ≠ w`, they are not matched
to each other, `v` is unmatched or strictly prefers `w` to its partner, and `w` is unmatched
or strictly prefers `v` to its partner. -/
def Blocks (i : StableRoommatesWithTiesInstance) (μ : Fin i.1 → Fin i.1) (v w : Fin i.1) :
    Prop :=
  v ≠ w ∧ μ v ≠ w ∧ (μ v = v ∨ rank i v w < rank i v (μ v)) ∧
    (μ w = w ∨ rank i w v < rank i w (μ w))

/-- Well-formedness of an instance: one rank row per agent, each with an entry for every
agent. -/
def WellFormed (i : StableRoommatesWithTiesInstance) : Prop :=
  i.2.length = i.1 ∧ ∀ row ∈ i.2, row.length = i.1

/-- The instance is solvable: some matching (an involutive partner function) is blocked by no
edge. -/
def StableRoommatesWithTiesFeasible (i : StableRoommatesWithTiesInstance) : Prop :=
  ∃ μ : Fin i.1 → Fin i.1, Function.Involutive μ ∧ ∀ v w, ¬ Blocks i μ v w

open Classical in
/-- STABLE ROOMMATES WITH TIES as a decision problem over bitstrings. -/
noncomputable def stableRoommatesWithTiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StableRoommatesWithTiesInstance) x with
  | some i => decide (WellFormed i ∧ StableRoommatesWithTiesFeasible i)
  | none => false

/-- **STABLE ROOMMATES WITH TIES (weak stability, complete lists) is NP-complete.** Source:
Ronn (1990); Cseh, Irving and Manlove (2019), Section 1. -/
public theorem_wanted stableRoommatesWithTies_npComplete :
    stableRoommatesWithTiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stableRoommatesWithTiesDec

end MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies
