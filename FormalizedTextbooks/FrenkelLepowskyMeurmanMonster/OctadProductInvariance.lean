/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual triality preservation of every octad basis product. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadFourPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadFourierPreservation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Triality preserves all actual octad×octad products, including the
four-point intersection case with its proved physical Fourier identity. -/
theorem sExtra_preserves_octad_product (o : Fin 759) (e : Fin 64)
    (p : Fin 759) (f : Fin 64) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) :=
  sExtra_octad_product_of_sum_cubics griessForm_transformed_octad_cubic_four o e p f

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
