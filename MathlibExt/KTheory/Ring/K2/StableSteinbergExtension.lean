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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergSurjective
public import MathlibExt.GroupTheory.CentralExtension

/-! # The stable Steinberg extension

Packages the canonical map from the stable Steinberg group as a group extension of `StableE`.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

/-- The canonical Steinberg extension `1 → ker(toStableE) → St(R) → E∞(R) → 1`. -/
public noncomputable def steinbergExtension (R : Type*) [Ring R] :
    GroupExtension (toStableE (R := R)).ker (StableSteinberg R) (StableE R) where
  inl := Subgroup.subtype _
  rightHom := toStableE
  inl_injective := Subgroup.subtype_injective _
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := toStableE_surjective

end StableSteinberg

end AlgebraicKTheory

end
