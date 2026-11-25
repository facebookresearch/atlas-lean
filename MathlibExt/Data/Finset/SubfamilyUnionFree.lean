/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Union-free families of finite sets

A family of finite sets is union-free over its subfamilies when no member
is the union of other members of the family.
-/

@[expose] public section

namespace Finset

/-- **Families in which no member is a union of other members.** A family $F$ of finite sets
is union-free over its subfamilies if no member $A \in F$ is the union of a nonempty
subfamily of $F$ that does not contain $A$. -/
def SubfamilyUnionFree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ T ⊆ F.erase A, T.Nonempty → T.sup id ≠ A

end Finset
