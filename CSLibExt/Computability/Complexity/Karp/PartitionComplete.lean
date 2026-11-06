/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionMembership
public import CSLibExt.Computability.Complexity.Karp.PartitionHardness

/-!
# Binary-coded PARTITION is NP-complete

The exact List Nat/Sublist problem reduces to canonical SUBSET-SUM for NP
membership. The reverse reduction adds the total sum and twice the target.
Both total encoded maps are realized by finite machines with quadratic
bounds in raw input length, including malformed and noncanonical inputs.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition

open Cslib.CookLevin Cslib.Complexity.Karp ComplexityTheory

/-- **Polynomial-time reduction from SUBSET-SUM to PARTITION.**
Binary-coded SUBSET-SUM reduces to the exact PARTITION decision problem. -/
theorem subsetSum_polyManyOneRed_partition :
    PolyManyOneRed subsetSumDec partitionDec :=
  ⟨reduceFromSubsetSum, HardnessMachine.isPolyTime_reduceFromSubsetSum,
    reduceFromSubsetSum_correct⟩

/-- **PARTITION is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), PARTITION; R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
theorem partition_npComplete :
    partitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionDec :=
  ⟨partitionDec_mem_NP,
    npHard_of_polyManyOneRed subsetSumDec_npHard
      subsetSum_polyManyOneRed_partition⟩

end MetaMathlibExt.Complexity.NPComplete.Partition
