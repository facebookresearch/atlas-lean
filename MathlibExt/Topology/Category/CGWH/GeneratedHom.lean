/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy

/-!
# Generated mapping carriers for CGWH spaces

Maps that are continuous on every compact Hausdorff probe of a CGWH source
are precisely its ordinary continuous maps. This is an equivalence of
carrier types; no equality or comparison of mapping-space topologies is
asserted here.
-/

public section

set_option autoImplicit false

universe u v

open Topology

namespace CGWH

/-- Compact-Hausdorff-probe-continuous maps out of a CGWH space are exactly
ordinary continuous maps. This compares only the carrier types. -/
@[expose] def generatedMapEquivContinuousMap (A B : CGWH.{u, v}) :
    ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A B ≃
      C(A, B) := by
  letI : IsGeneratedBy
      CompactlyGenerated.compactHausProbes.{u} A :=
    (isGeneratedBy_compactHausProbes_iff (Y := A)).2 inferInstance
  exact
    { toFun := fun f =>
        ⟨f, (IsGeneratedBy.continuous_iff
          CompactlyGenerated.compactHausProbes.{u} f).2 f.prop⟩
      invFun := fun f => ⟨f, f.continuous.continuousGeneratedBy⟩
      left_inv := fun f => by ext a; rfl
      right_inv := fun f => by ext a; rfl }

@[simp]
theorem generatedMapEquivContinuousMap_apply
    (A B : CGWH.{u, v})
    (f : ContinuousMapGeneratedBy
      CompactlyGenerated.compactHausProbes.{u} A B)
    (a : A) :
    generatedMapEquivContinuousMap A B f a = f a :=
  rfl

end CGWH
