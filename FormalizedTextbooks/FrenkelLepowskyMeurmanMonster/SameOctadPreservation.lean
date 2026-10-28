/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual triality preservation for every product within one signed-octad block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SameOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCOctad

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual triality operator preserves every same-octad basis product. -/
theorem sExtra_preserves_sameOctad_product (o : Fin 759) (e f : Fin 64) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis o f) := by
  apply sExtra_sameOctad_product_of_ABC o _ e f
  intro s p g
  exact sExtra_preserves_ABC_octad_product s p o g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
