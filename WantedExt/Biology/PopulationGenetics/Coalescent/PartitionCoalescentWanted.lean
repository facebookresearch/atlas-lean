/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consistency of the jump chain of Kingman's partition-valued coalescent

The jump chain of Kingman's `n`-coalescent (`PartitionCoalescent.jumpMatrix`) starts from the
partition of the sample `Fin n` into singletons and merges a uniformly random pair of blocks at
each step, so for `n ≥ 1` its path is a list of `n` partitions, from `n` blocks down to one.
Kingman (1982) showed that the coalescents are consistent: restricting the
`(n + 1)`-coalescent to the first `n` genes gives the `n`-coalescent. For the jump chains this
reads as follows: restrict every partition of a path of the `(n + 1)`-chain to `Fin n`
(`Finpartition.comap Fin.castSucc`); a step
that merges the block of the gene `n` with another block leaves the restriction unchanged,
so delete the repeated entries (`List.destutter (· ≠ ·)`); the resulting list of `n` distinct
partitions of `Fin n` is distributed as the path of the `n`-chain.

The time-`t` form of consistency is proved in
`MathlibExt/Biology/PopulationGenetics/Coalescent/PartitionCoalescent.lean`
(`sum_timeLaw_restrict`); the path-level statement for the jump chains is deferred here.

Sources: J. F. C. Kingman, "The coalescent", Stochastic Process. Appl. 13 (1982) 235–248;
R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), ch. 1.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent

@[expose] public section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescentWanted

open PartitionCoalescent

open scoped Classical in
/-- The probability that the jump chain of Kingman's `n`-coalescent, started from the partition
into singletons, follows the list of partitions `l`: `0` unless `l` starts at the partition
into singletons, and otherwise the product of the one-step transition probabilities
`jumpMatrix n` along `l`. The empty list has probability `0`. -/
noncomputable def pathProb (n : ℕ) : List (SamplePartition n) → ℝ
  | [] => 0
  | π :: l => (if π = ⊥ then 1 else 0) * (List.zipWith (jumpMatrix n) (π :: l) l).prod

open scoped Classical in
/-- **Consistency of the jump chains** (Kingman 1982): for `n ≥ 1`, restricting each
partition of a path of the `(n + 1)`-jump chain (a list of `n + 1` partitions) to the first `n`
genes and deleting consecutive repetitions gives a list of `n` partitions of `Fin n` distributed
as the path of the `n`-jump chain.

Source: Kingman (1982); Durrett (2008), ch. 1. -/
theorem_wanted sum_pathProb_restrict (n : ℕ) (hn : 1 ≤ n) (ρs : List (SamplePartition n))
    (hρs : ρs.length = n) :
    ∑ p : Fin (n + 1) → SamplePartition (n + 1)
        with ((List.ofFn p).map (Finpartition.comap Fin.castSucc)).destutter (· ≠ ·) = ρs,
      pathProb (n + 1) (List.ofFn p) = pathProb n ρs

end MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescentWanted
