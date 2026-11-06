/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTransport

/-! An original source word moving the sixth plane into the actual Xi fixed coordinate triple. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Thirteen original permutation letters carrying the actual sixth triple to 1,2,3. -/
def leechRootedA2SixthXiTransportWord : List (Fin 4) :=
  [2, 1, 0, 0, 1, 0, 0, 1, 0, 1, 2, 2, 2]

/-- The actual Mathieu transporter into the Xi fixed coordinate triple. -/
def leechRootedA2SixthXiTransport : golayAutomorphismSubgroup :=
  golayGeneratingWord leechRootedA2SixthXiTransportWord

/-- Original physical arrays certify the exact three transporter images. -/
theorem leechRootedA2SixthXiTransport_word_certificate : ∀ k : Fin 3,
    golayGeneratingWordArray leechRootedA2SixthXiTransportWord
      ((![16, 17, 19] : Fin 3 → Fin 24) k) = (![1, 2, 3] : Fin 3 → Fin 24) k := by
  decide +kernel

/-- The genuine transporter carries the sixth root coordinates into the Xi fixed triple. -/
theorem leechRootedA2SixthXiTransport_spec :
    leechRootedA2SixthXiTransport.val 16 = 1 ∧
      leechRootedA2SixthXiTransport.val 17 = 2 ∧
        leechRootedA2SixthXiTransport.val 19 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [leechRootedA2SixthXiTransport, leechRootedA2GeneratingWord_apply]
  · exact leechRootedA2SixthXiTransport_word_certificate 0
  · exact leechRootedA2SixthXiTransport_word_certificate 1
  · exact leechRootedA2SixthXiTransport_word_certificate 2

/-- The full original transporter fiber retains the actual spin and spatial operators. -/
def leechRootedA2SixthXiTransportFiber : localFiberSubgroup :=
  leechRootedA2GeneratingWordFiber leechRootedA2SixthXiTransportWord

/-- Its spatial projection is precisely the original Mathieu transporter isometry. -/
theorem leechRootedA2SixthXiTransportFiber_spatial :
    leechRootedA2SixthXiTransportFiber.val.2 =
      golayPermutationIsometry leechRootedA2SixthXiTransport :=
  leechRootedA2GeneratingWordFiber_spatial _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
