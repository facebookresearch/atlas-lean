/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorCircuitData

/-! Exact complete source-row versions of the original incoming and outgoing Fourier circuits. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The whole original outgoing two-Fourier action retains its exact row and offset changes. -/
theorem generatedTwelfth_tensor_fourier_pair_block (k l : Fin 12)
    (v : NortonUIntegerVector) (b : Fin 16) (u : Fin 256) :
    generatedTwelfthSpinTensorFourierInteger k (generatedTwelfthSpinTensorFourierInteger l v)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedNinthLowerSpinTensorBlockFourier k
        (generatedNinthLowerSpinTensorBlockFourier l
          (fun c z => v (generatedNinthLowerSpinTensorBlockIndex c z))) b u :=
  generatedNinth_lower_spin_tensor_fourier_pair_block k l v b u

/-- The whole original incoming two-Fourier action retains its exact row and offset changes. -/
theorem generatedTwelfth_incoming_tensor_fourier_pair_block (k l : Fin 12)
    (v : NortonUIntegerVector) (b : Fin 16) (u : Fin 256) :
    generatedTwelfthIncomingSpinTensorFourierInteger k
        (generatedTwelfthIncomingSpinTensorFourierInteger l v)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedNinthLowerSpinTensorBlockFourier k
        (generatedNinthLowerSpinTensorBlockFourier l
          (fun c z => v (generatedNinthLowerSpinTensorBlockIndex c z))) b u :=
  generatedNinth_lower_spin_tensor_fourier_pair_block k l v b u

/-- Every complete outgoing packed source coordinate equals the original fixed-row decoding. -/
theorem generatedTwelfth_tensor_packed_coordinate_block
    (words : Fin 16 → Fin 16 → ℕ) (b : Fin 16) (u : Fin 256) :
    generatedTwelfthSpinTensorPackedCoordinate words (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedTwelfthSpinTensorDecode (words b ⟨u.val / 16, by omega⟩) (u.val % 16) :=
  generatedNinth_lower_spin_tensor_packed_coordinate_block words b u

/-- Every complete incoming packed source coordinate equals the original fixed-row decoding. -/
theorem generatedTwelfth_incoming_tensor_packed_coordinate_block
    (words : Fin 16 → Fin 16 → ℕ) (b : Fin 16) (u : Fin 256) :
    generatedTwelfthIncomingSpinTensorPackedCoordinate words
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedTwelfthIncomingSpinTensorDecode (words b ⟨u.val / 16, by omega⟩) (u.val % 16) :=
  generatedNinth_lower_spin_tensor_packed_coordinate_block words b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
