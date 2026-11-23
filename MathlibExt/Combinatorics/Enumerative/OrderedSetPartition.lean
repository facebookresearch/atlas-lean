/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Ordered set partitions of a finite set.** For a finite set $V$, a list $(B_1, \dots, B_k)$
of finite sets is an ordered set partition (set composition) of $V$ when every block $B_i$ is
nonempty and contained in $V$, the blocks are pairwise disjoint, and
$B_1 \cup \dots \cup B_k = V$.

Equivalently, an ordered set partition of $V$ is a structure of the composite species of lists
of nonempty sets on $V$.

Source: statement `jis_0874746b31275e17727c6370`, concept `jis_sem_de11a43abe164463205fe64c`. -/
def IsOrderedSetPartition {α : Type*} [DecidableEq α] (V : Finset α)
    (blocks : List (Finset α)) : Prop :=
  (∀ B ∈ blocks, B.Nonempty) ∧
    (∀ B ∈ blocks, B ⊆ V) ∧
    blocks.Pairwise (fun A B => Disjoint A B) ∧
    V = blocks.foldl (· ∪ ·) ∅

end MetaMathlibExt
