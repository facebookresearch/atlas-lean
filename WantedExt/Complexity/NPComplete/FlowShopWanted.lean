/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-MACHINE FLOW SHOP SCHEDULING is NP-complete

Source:
M. R. Garey, D. S. Johnson, and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129; T. F. Gonzalez and S. Sahni, "Flowshop
and jobshop schedules: complexity and approximation", Operations Research 26 (1978), 36-52.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop

/-!
# 3-MACHINE FLOW SHOP SCHEDULING is NP-complete

A list of jobs, each with three nonnegative integer processing times (on machines 1, 2, 3, in
that order), together with a deadline `D`. The question is whether there are start times, one
per job per machine, so that each job visits the machines in order, no machine processes two
jobs at once, and every job completes by `D`. This is the general (non-permutation) flow shop:
different machines may order the jobs differently.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A flow-shop instance: jobs as triples of processing times, deadline. -/
abbrev FlowShopInstance := List (List ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : FlowShopInstance) : Prop :=
  ∀ job ∈ i.1, job.length = 3

/-- Start times meeting job order, machine exclusion, and the deadline. -/
def FlowShopFeasible
    (i : FlowShopInstance) : Prop :=
  ∃ start : List (List ℕ), start.length = i.1.length ∧
    (∀ row ∈ start, row.length = 3) ∧
    (∀ j < i.1.length, (start.getD j []).getD 0 0 + (i.1.getD j []).getD 0 0 ≤
        (start.getD j []).getD 1 0 ∧
      (start.getD j []).getD 1 0 + (i.1.getD j []).getD 1 0 ≤
        (start.getD j []).getD 2 0 ∧
      (start.getD j []).getD 2 0 + (i.1.getD j []).getD 2 0 ≤ i.2) ∧
    ∀ k < 3, ∀ a < i.1.length, ∀ b < i.1.length, a < b →
      (start.getD a []).getD k 0 + (i.1.getD a []).getD k 0 ≤
          (start.getD b []).getD k 0 ∨
        (start.getD b []).getD k 0 + (i.1.getD b []).getD k 0 ≤
          (start.getD a []).getD k 0

open Classical in
/-- 3-MACHINE FLOW SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def flowShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlowShopInstance) x with
  | some i => decide (WellFormed i ∧ FlowShopFeasible i)
  | none => false

/-- **3-MACHINE FLOW SHOP SCHEDULING is NP-complete.** Source: M. R. Garey, D. S. Johnson, and
R. Sethi, "The complexity of flowshop and jobshop scheduling", Mathematics of Operations
Research 1 (1976), 117-129; T. F. Gonzalez and S. Sahni, "Flowshop and jobshop schedules:
complexity and approximation", Operations Research 26 (1978), 36-52. -/
public theorem_wanted flowShop_npComplete :
    flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flowShopDec

end MetaMathlibExt.Complexity.NPComplete.FlowShop
