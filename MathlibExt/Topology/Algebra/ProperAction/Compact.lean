/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Proper continuous actions with compact group carrier

Let a group with a compact topology act jointly continuously on a Hausdorff space `X`. The
action is proper: the map `(g,x) ↦ (g • x,x)` from `G×X` to `X×X` is proper.

The additive form uses `(g,x) ↦ (g +ᵥ x,x)`. Continuity of the group operations is not an extra
hypothesis of these action criteria.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v

variable (G : Type u) (X : Type v)
variable [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- **Proper multiplicative action of a compact group carrier.** Let `G` be a group with
compact topology, `X` a Hausdorff space and `G` act on `X` with jointly continuous scalar
action. Then `(g,x) ↦ (g • x,x)` is a proper map, so `ProperSMul G X`. No continuity of
group operations is assumed. -/
@[to_additive
  /-- **Proper additive action of a compact group carrier.** Let `G` be an additive group with
compact topology, `X` a Hausdorff space and `G` act on `X` with jointly continuous vector
addition. Then `(g,x) ↦ (g +ᵥ x,x)` is a proper map, so the additive action is proper.
Continuity of group operations is not required. -/]
theorem ProperSMul.ofCompactGroup [CompactSpace G] [T2Space X]
    [ContinuousSMul G X] : ProperSMul G X where
  isProperMap_smul_pair := by
    apply isProperMap_of_comp_of_t2
      (continuous_smul.prodMk continuous_snd) continuous_snd
    change IsProperMap (Prod.snd : G × X → X)
    exact isProperMap_snd_of_compactSpace
