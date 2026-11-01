/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinProfiles
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi

/-! Genuine complete signed spin certificates transport exact integer spin vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Integer signed pullback, retaining the complete original quadratic central phase. -/
def generatedSixthSpinIntegerModel (a : RepresentativeSpinModel)
    (v : NortonUIntegerVector) : NortonUIntegerVector := fun n =>
  let t := golayLabelCoefficients n
  nortonUIntegerSign (monsterMonomialQuadratic a.phase t) *
    v (nortonUIntegerLabel (a.coordinate *ᵥ t))

/-- A full genuine operator certificate proves the exact integer action on every spin vector. -/
theorem generatedSixth_spin_integer_model_embed (g : SpinHolomorph)
    (a : RepresentativeSpinModel) (hg : representativeSpinCertificate g a.coordinate a.phase)
    (v : NortonUIntegerVector) :
    g.val (nortonUIntegerEmbed v) = nortonUIntegerEmbed (generatedSixthSpinIntegerModel a v) := by
  ext t
  rw [hg]
  simp only [nortonUIntegerEmbed, generatedSixthSpinIntegerModel,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
