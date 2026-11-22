/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

@[expose] public section

/-- **Basic set partition.** A partition $P$ of $\{1, \dots, n\}$ is basic when its blocks can
  be listed without repetition as $B_1, \dots, B_k$ with $|B_1| \ge |B_2| \ge \dots \ge |B_k|$
  so that $B_1 \cup \dots \cup B_i = \{1, \dots, |B_1| + \dots + |B_i|\}$ for every $i$ with
  $1 \le i \le k$.

  Source: concept `jis_sem_a7cf8b184541b1aad513e021`, statement `jis_a15ca13d7bcc157dc6123a58`. -/
public def IsBasicSetPartition (n : ℕ) (P : Finpartition (Finset.Icc 1 n)) : Prop :=
  ∃ blocks : List (Finset ℕ),
    blocks.Nodup ∧
    blocks.toFinset = P.parts ∧
    (∀ B ∈ blocks, 0 < B.card) ∧
    List.Pairwise (fun earlier later => later.card ≤ earlier.card) blocks ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ blocks.length →
      (blocks.take i).foldl (· ∪ ·) (∅ : Finset ℕ) =
        Finset.Icc 1 (((blocks.take i).map Finset.card).sum)

end

end MetaMathlibExt
