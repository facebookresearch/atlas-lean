/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Triality preserves every product in the actual source-coordinate Griess algebra. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFinalReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual extra symmetry preserves the full concrete Griess product.
Every source product and cubic family is proved and instantiated. -/
theorem sExtra_preserves_griessProd (x y : GriessSpace) :
    sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) :=
  sExtra_preserves_product_of_two_octad_cubics
    trialityOctadXYZ_cubic_X_to_Y trialityOctadXYZ_cubic_Y_to_Z x y

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
