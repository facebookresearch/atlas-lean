/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang, Steven Warner
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Tree.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 23, Logic 12, Logic 8

/-!
# $\kappa$-Aronszajn tree; Aronszajn tree; ω₁-tree

## References

* Kunen (for `IsAronszajnTreeAt`)
* Jech (for `IsAronszajnTree`, `IsOmega1Tree`)
-/

namespace MetaMathlibExt

-- Logic 23: $\kappa$-Aronszajn tree

open Cardinal in

/-- A κ-Aronszajn tree is a κ-tree such that there are no cofinal branch through the tree. -/
def IsAronszajnTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTreeAt κ α ∧ ∀ C : Set α, IsChain (· ≤ ·) C → #C < κ

-- Logic 12: Aronszajn tree

open Cardinal in

/-- An *Aronszajn tree* is a tree of height $\aleph_1}$ all of whose levels are at most countable
and which has no uncountable branches.
-/
def IsAronszajnTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsAronszajnTreeAt (aleph 1) α

-- Logic 8: ω₁-tree

open Cardinal in

/-- An *ω₁-tree* is a tree of height ω₁ all of whose levels are countable: every node has height <
ω₁, every level Lev_α(T) with α < ω₁ is nonempty, and every such level is countable.
-/
def IsOmega1Tree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt (aleph 1 : Cardinal.{u}) α

end MetaMathlibExt

end
