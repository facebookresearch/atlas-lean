/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared pure-subgroup predicate (Kourovka Notebook batch)

Pure subgroups of abelian groups, shared by the `WantedExt` statements of Kourovka Notebook
Problems 2.4, 3.21 and 3.22.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Int.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.PureSubgroupShared

/-- **Pure subgroups of abelian groups.** A subgroup $B$ of an abelian group $A$ is pure when
$nA \cap B = nB$ for every integer $n$: for every integer $n$ and every $a \in A$ with
$na \in B$ there is some $b \in B$ with $nb = na$. -/
def IsPureSubgroup {A : Type} [AddCommGroup A] (B : AddSubgroup A) : Prop :=
  ∀ (n : ℤ) (a : A), n • a ∈ B → ∃ b ∈ B, n • b = n • a

end MathlibExt.GroupTheory.PureSubgroupShared
