/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# General arithmetic interface probes

The actual trivial abelian scheme over Spec Z checks that the public group
and zero-section interfaces require no field base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.AbelianSchemes

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes

def trivial (S : Scheme) : AbelianScheme S where
  model := 𝟙_ (Over S)
  group := inferInstance
  commutative := inferInstance
  smooth := by change Smooth (𝟙 S); infer_instance
  proper := by change IsProper (𝟙 S); infer_instance
  connected := by
    change GeometricallyConnected (𝟙 S)
    constructor
    intro K _ y Z fst snd h
    have : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.connectedSpace_iff.mpr inferInstance

example (T : Over (Spec (.of ℤ))) :
    zeroSectionAt (trivial (Spec (.of ℤ))) T ≫
      (prod.snd : prod (trivial (Spec (.of ℤ))).model T ⟶ T) = 𝟙 T := by
  exact prod.lift_snd _ _

end MathlibExtTest.AlgebraicGeometry.AbelianSchemes
