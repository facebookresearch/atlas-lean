/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFixed0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFixed1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFixed2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFixed3

/-! The four corrected original monomials fix the entire actual tensor constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every corrected original monomial fixes the complete actual tensor, including its zeros. -/
theorem generatedSixth_monomial_tensor_fixed (k : Fin 4) :
    localTensorRepresentation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.2 =
        (griessConwayEncode generatedSixthAxis).2.2 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · have hk : Fin.castAdd 1 (0 : Fin 4) = (0 : Fin 5) := rfl
    rw [hk]
    exact generatedSixth_monomial_tensor_fixed0
  · have hk : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := rfl
    rw [hk]
    exact generatedSixth_monomial_tensor_fixed1
  · have hk : Fin.castAdd 1 (2 : Fin 4) = (2 : Fin 5) := rfl
    rw [hk]
    exact generatedSixth_monomial_tensor_fixed2
  · have hk : Fin.castAdd 1 (3 : Fin 4) = (3 : Fin 5) := rfl
    rw [hk]
    exact generatedSixth_monomial_tensor_fixed3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
