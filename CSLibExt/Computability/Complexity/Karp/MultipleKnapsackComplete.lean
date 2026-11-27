/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Basic
public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsackHardness
public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsackVerify
public import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete

/-!
# MULTIPLE KNAPSACK is NP-complete

Membership: the certificate check `mkCheck` of `MultipleKnapsack` is computed by the verifier
machine of `MultipleKnapsackVerify` in polynomial time, and certificates of quadratic length
suffice (`multipleKnapsackDec_mem_NP`). Hardness: SUBSET-SUM reduces to MULTIPLE KNAPSACK by the
map of `MultipleKnapsack`, sending numbers `as` and a target `t` to the items `(a, a)`, one
knapsack of capacity `t` and the target value `t`; the machine of `MultipleKnapsackHardness`
computes it on all bit strings (`subsetSum_polyManyOneRed_multipleKnapsack`). With
NP-hardness of SUBSET-SUM (`Karp.SubsetSumComplete`) this gives `multipleKnapsack_npComplete`.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack

open Cslib.Complexity Cslib.Complexity.Karp

/-- **MULTIPLE KNAPSACK is in NP.** The decision problem MULTIPLE KNAPSACK belongs to NP. A
certificate lists, for each knapsack, one bit per item selecting the items it holds, and a
polynomial-time verifier checks every knapsack's load against its capacity and the value of the
selected items against the target.

Source: original to this formalization. -/
theorem multipleKnapsackDec_mem_NP : multipleKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨Polynomial.X ^ 2, fun q => mkCheck q.1 q.2, Verify.isPolyTime_mkCheck, fun x => by
    rw [multipleKnapsackDec_iff_check]
    simp⟩

/-- **SUBSET-SUM reduces to MULTIPLE KNAPSACK.** The bit-string map sending a SUBSET-SUM
instance with numbers $a$ and target $t$ to the multiple-knapsack instance with items
$(a_i, a_i)$, one knapsack of capacity $t$ and target $t$, and every malformed string to a fixed
no-instance, is a polynomial-time many-one reduction.

Source: original to this formalization. -/
theorem subsetSum_polyManyOneRed_multipleKnapsack :
    Cslib.CookLevin.PolyManyOneRed subsetSumDec multipleKnapsackDec :=
  ⟨reduceFromSubsetSum, HardnessMachine.isPolyTime_reduceFromSubsetSum,
    reduceFromSubsetSum_correct⟩

/-- **MULTIPLE KNAPSACK is NP-complete.** The decision problem MULTIPLE KNAPSACK belongs to NP,
and every decision problem in NP has a polynomial-time many-one reduction to MULTIPLE KNAPSACK.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), MULTIPLE KNAPSACK. -/
theorem multipleKnapsack_npComplete :
    multipleKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleKnapsackDec :=
  ⟨multipleKnapsackDec_mem_NP, fun L hL =>
    (subsetSumDec_npHard L hL).trans subsetSum_polyManyOneRed_multipleKnapsack⟩

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
