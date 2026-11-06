/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedWhole

/-! The complete original matrix, short and tensor constituents give four actual full-axis lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every corrected original monomial fixes the entire actual sixth axis with all original
phases. -/
theorem generatedSixth_monomial_full_fixed (k : Fin 4) :
    rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)))
      generatedSixthAxis = generatedSixthAxis :=
  generatedSixth_corrected_generator_full_fixed_of_blocks (Fin.castAdd 1 k)
    (generatedSixth_monomial_short_fixed k) (generatedSixth_monomial_tensor_fixed k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
