/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.IsSubnormal

/-!
# Composition factors via subnormal subgroups

This module defines composition factors as simple quotients of subnormal subgroups.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Composition factors via subnormal subgroups.** A group $S$ is a composition factor of a group
$K$ if $S$ is simple and some subnormal subgroup $H$ of $K$ has a surjective homomorphism onto $S$.

For finite $K$ this is the same as $S$ occurring as a factor of a composition series of $K$
(refine the subnormal chain through the kernel). -/
def IsCompositionFactor (S K : Type*) [Group S] [Group K] : Prop :=
  IsSimpleGroup S ∧ ∃ H : Subgroup K, H.IsSubnormal ∧ ∃ f : H →* S, Function.Surjective f

end MathlibExt.GroupTheory.KourovkaNotebookShared
