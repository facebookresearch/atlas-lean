/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared SQ-universality predicate

SQ-universal groups (every countable group embeds in a quotient), shared by the WantedExt entries
for Kourovka Notebook Problems 4.39 and 4.45 so that both speak about the same notion.
-/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Basic.Countable.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.SQUniversalShared

/-- `G` is SQ-universal: every countable group is isomorphic to a subgroup of a quotient of `G`.
A quotient of `G` is a group `Q` with a surjective homomorphism `G → Q`, and a subgroup of `Q`
isomorphic to `C` is the image of an injective homomorphism `C → Q`. -/
def IsSQUniversal (G : Type*) [Group G] : Prop :=
  ∀ (C : Type) [Group C] [Countable C], ∃ (Q : Type) (_ : Group Q) (q : G →* Q),
    Function.Surjective q ∧ ∃ f : C →* Q, Function.Injective f

end MathlibExt.GroupTheory.SQUniversalShared
