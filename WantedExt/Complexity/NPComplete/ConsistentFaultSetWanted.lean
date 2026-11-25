/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT FAULT SET is NP-complete

Source:
H. Fujiwara and K. Kinoshita, "On the computational complexity of system diagnosis", IEEE
Transactions on Computers C-27 (1978), 881-885, doi:10.1109/TC.1978.1674966, Problem 1 (P1)
and Theorem 1, recording the result of S. N. Maheshwari and S. L. Hakimi, "On models for
diagnosable systems and probabilistic fault diagnosis", IEEE Transactions on Computers C-25
(1976), 228-236, doi:10.1109/TC.1976.5009249.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentFaultSet

/-!
# CONSISTENT FAULT SET is NP-complete

System diagnosis in the graph-theoretic model of Preparata et al. A system of units
capable of testing one another is a directed graph `G = (V, E)`, with an arc `(u_i, u_j) ∈ E`
when unit `u_i` tests unit `u_j`. Each test has an outcome `a_ij ∈ {0, 1}`; a fault-free tester
reports `a_ij = 0` on a fault-free unit and `a_ij = 1` on a faulty one, and a faulty tester may
report either value. The outcomes form the syndrome `σ`. A set `F ⊆ V` is a consistent fault set
with respect to `σ` when (1) `a_ij = 1` for every `(u_i, u_j) ∈ E` with `u_i ∉ F` and
`u_j ∈ F`, and (2) `a_ij = 0` for every `(u_i, u_j) ∈ E` with `u_i, u_j ∉ F`.

INSTANCE: a system given by a directed graph `G = (V, E)`, a syndrome `σ`, and a positive integer
`t`. QUESTION: is there a consistent fault set `F` with respect to `σ` with `|F| ≤ t`?

This is Problem 1 of Fujiwara and Kinoshita (1978), who prove it P-complete in Sahni's sense
(Theorem 1, from Maheshwari and Hakimi's result for the minimum consistent fault set). The many-one
form stated here also follows directly from VERTEX COVER: with mutual tests `(u, v)`, `(v, u)`
of outcome `1` for every edge `uv`, the consistent fault sets are exactly the vertex covers.

The units are `Fin n`. Each test is listed once as `((u, v), a)` with `a = true` for outcome `1`
and `a = false` for outcome `0`; tests name two different units (a unit does not test itself)
and no arc is listed twice. Binary encoding of all numbers. Membership in NP holds for this
encoding even though `n` is written in binary: removing from a consistent fault set the units on
no listed test keeps it consistent and does not increase its size, so a certificate lists only
units that occur in the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of units, the tests `((u_i, u_j), a_ij)` (unit `u_i` tests unit
`u_j` with outcome `a_ij`, `true` for `1`), and the bound `t`. -/
abbrev ConsistentFaultSetInstance := ℕ × List ((ℕ × ℕ) × Bool) × ℕ

/-- Well-formedness of an instance: every test names two different units, no arc is listed
twice, and `t` is positive. -/
def WellFormed (i : ConsistentFaultSetInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.1 < i.1 ∧ e.1.2 < i.1 ∧ e.1.1 ≠ e.1.2) ∧ (i.2.1.map Prod.fst).Nodup ∧
    0 < i.2.2

/-- Some set `F` of at most `t` units is a consistent fault set: for every test
`((u_i, u_j), a_ij)` with `u_i ∉ F`, (1) `a_ij = 1` if `u_j ∈ F` and (2) `a_ij = 0` if
`u_j ∉ F`. -/
def ConsistentFaultSetFeasible (i : ConsistentFaultSetInstance) : Prop :=
  ∃ F : Finset (Fin i.1), F.card ≤ i.2.2 ∧
    ∀ e ∈ i.2.1, ∀ (h1 : e.1.1 < i.1) (h2 : e.1.2 < i.1), (⟨e.1.1, h1⟩ : Fin i.1) ∉ F →
      ((⟨e.1.2, h2⟩ : Fin i.1) ∈ F → e.2 = true) ∧ ((⟨e.1.2, h2⟩ : Fin i.1) ∉ F → e.2 = false)

open Classical in
/-- CONSISTENT FAULT SET as a decision problem over bitstrings. -/
noncomputable def consistentFaultSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsistentFaultSetInstance) x with
  | some i => decide (WellFormed i ∧ ConsistentFaultSetFeasible i)
  | none => false

/-- **CONSISTENT FAULT SET is NP-complete.** Source: Fujiwara and Kinoshita (1978), Problem 1
and Theorem 1; Maheshwari and Hakimi (1976). -/
public theorem_wanted consistentFaultSet_npComplete :
    consistentFaultSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consistentFaultSetDec

end MetaMathlibExt.Complexity.NPComplete.ConsistentFaultSet
