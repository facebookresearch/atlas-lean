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
# Proper actions of compact groups

A continuous action of a compact group on a Hausdorff space is proper.  The
result and its additive counterpart are explicit constructors rather than
global instances, avoiding instance-search loops and diamonds.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v

variable (G : Type u) (X : Type v)
variable [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- A continuous action of a compact group on a Hausdorff space is proper. -/
@[to_additive
  /-- A continuous action of a compact additive group on a Hausdorff space is proper. -/]
theorem ProperSMul.ofCompactGroup [CompactSpace G] [T2Space X]
    [ContinuousSMul G X] : ProperSMul G X where
  isProperMap_smul_pair := by
    apply isProperMap_of_comp_of_t2
      (continuous_smul.prodMk continuous_snd) continuous_snd
    change IsProperMap (Prod.snd : G × X → X)
    exact isProperMap_snd_of_compactSpace
