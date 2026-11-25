/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Lattice

/-!
# Right-orderable groups

`IsRightOrderable` expresses the existence of a right-invariant linear order on a group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

/-- **Right-orderable groups.** A group $G$ is right-orderable when it admits a linear order $\le$
that is invariant under right multiplication: $a \le b$ implies $ac \le bc$ for all
$a, b, c \in G$. -/
def IsRightOrderable (G : Type*) [Group G] : Prop :=
  ∃ _ : LinearOrder G, ∀ a b c : G, a ≤ b → a * c ≤ b * c

end MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted
