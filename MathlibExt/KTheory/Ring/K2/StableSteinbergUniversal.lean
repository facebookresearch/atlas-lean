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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergCentrality
public import MathlibExt.KTheory.Ring.K2.StableSteinbergExtension
public import MathlibExt.KTheory.Ring.K2.StableSteinbergLift
public import MathlibExt.KTheory.Ring.K2.StableSteinbergPerfect

/-! # Universality of the stable Steinberg extension

Combines centrality, existence of lifts, and perfectness to prove the universal property.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory.StableSteinberg

/-- The stable Steinberg extension is central. -/
public theorem steinbergExtension_isCentral (R : Type u) [Ring R] :
    (steinbergExtension R).IsCentral := by
  change MonoidHom.ker (toStableE (R := R)) ≤ Subgroup.center (StableSteinberg R)
  exact AlgebraicKTheory.StableSteinberg.ker_toStableE_le_center

/-- The stable Steinberg extension is universal among central extensions. -/
public theorem steinbergExtension_isUniversal (R : Type u) [Ring R] :
    (steinbergExtension R).IsUniversal := by
  constructor
  · exact steinbergExtension_isCentral R
  · intro N' E' instN' instE' S hS
    refine ⟨liftToCentralExtension S hS, rightHom_comp_liftToCentralExtension S hS, ?_⟩
    intro f hf
    have h_eq : S.rightHom.comp f = S.rightHom.comp (liftToCentralExtension S hS) := by
      calc S.rightHom.comp f = (steinbergExtension R).rightHom := hf
        _ = toStableE := rfl
        _ = S.rightHom.comp (liftToCentralExtension S hS) :=
          (rightHom_comp_liftToCentralExtension S hS).symm
    exact MonoidHom.eq_of_comp_eq_of_ker_le_center hS h_eq

end AlgebraicKTheory.StableSteinberg
