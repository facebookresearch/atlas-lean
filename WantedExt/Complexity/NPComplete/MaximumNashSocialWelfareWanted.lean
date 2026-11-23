/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM NASH SOCIAL WELFARE with additive valuations is NP-complete

Source:
S. Ramezani and U. Endriss, "Nash social welfare in multiagent resource allocation",
Agent-Mediated Electronic Commerce (AMEC/TADA 2009), Lecture Notes in Business Information
Processing 59 (2010), 117-131, doi:10.1007/978-3-642-15117-0_9 (Section 1.2: allocations and
the Nash collective utility function; Section 1.3.2: the decision problem Nash).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare

/-!
# MAXIMUM NASH SOCIAL WELFARE with additive valuations is NP-complete

INSTANCE: a finite set `A` of agents, a finite set `R` of indivisible goods, for each agent `i`
and good `r` a value `v_i(r) ∈ ℤ₀⁺` (agent `i`'s utility for a bundle is the sum of the values of
its goods), and an integer `W`. QUESTION: is there an allocation, a partition of all of `R`
among the agents, such that the product `∏_{i ∈ A} u_i(A(i))` of the agents' utilities is at
least `W`?

Ramezani and Endriss define an allocation as a map `A` from agents to pairwise disjoint bundles
covering `R` (every good goes to exactly one agent) and the Nash collective utility as the
product of the agents' utilities; their decision problem asks whether some allocation has Nash
welfare above a rational `K`, which for integer utilities is the question "at least `W`" with
`W = ⌊K⌋ + 1`. Here the utilities are additive, given by a value matrix.

Hardness, from PARTITION: for sizes `s(r)` with even sum `S`, take two agents who both value
good `r` at `s(r)`, and `W = (S / 2)²`. For every allocation `u₁ + u₂ = S`, so
`u₁ u₂ ≤ (S / 2)²` with equality iff `u₁ = u₂ = S / 2`; hence some allocation reaches `W` iff
the goods split into two halves of equal size (an odd `S` is a no-instance of PARTITION). It is
in NP: the allocation is a certificate, and the product of the `|A|` utilities has a binary
length polynomial in the input, so the comparison takes polynomial time. All numbers use the
binary encoding.

An allocation is a map `f : R → A` (good `r` goes to agent `f r`), so agent `i` receives
`{r | f r = i}`. Agents are `Fin |A|` and goods `Fin m`; the value matrix lists one row per
agent, each of length `m`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(m, v, W)`: the number `m` of goods (goods `Fin m`), the value matrix `v` with
one row `v_i = [v_i(0), …, v_i(m - 1)]` per agent, and the bound `W`. -/
abbrev MaximumNashSocialWelfareInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: there is at least one agent and every row of the value
matrix has one entry per good. -/
def WellFormed (i : MaximumNashSocialWelfareInstance) : Prop :=
  0 < i.2.1.length ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- The utility of agent `a` under the allocation `f : goods → agents`: the sum of `a`'s values
of the goods `f` gives it (`getD` reads the value matrix; under `WellFormed` every entry
exists). -/
def utility (i : MaximumNashSocialWelfareInstance) (f : Fin i.1 → Fin i.2.1.length)
    (a : Fin i.2.1.length) : ℕ :=
  ∑ r ∈ Finset.univ.filter (fun r => f r = a), (i.2.1[a].getD r 0)

/-- Some allocation of all goods has Nash social welfare, the product of the agents' utilities,
at least `W`. -/
def MaximumNashSocialWelfareFeasible (i : MaximumNashSocialWelfareInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.1.length, i.2.2 ≤ ∏ a, utility i f a

open Classical in
/-- MAXIMUM NASH SOCIAL WELFARE as a decision problem over bitstrings. -/
noncomputable def maximumNashSocialWelfareDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumNashSocialWelfareInstance) x with
  | some i => decide (WellFormed i ∧ MaximumNashSocialWelfareFeasible i)
  | none => false

/-- **MAXIMUM NASH SOCIAL WELFARE with additive valuations is NP-complete.** Source: Ramezani
and Endriss (2010) (problem); hardness from PARTITION as in the module docstring. -/
public theorem_wanted maximumNashSocialWelfare_npComplete :
    maximumNashSocialWelfareDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumNashSocialWelfareDec

end MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare
