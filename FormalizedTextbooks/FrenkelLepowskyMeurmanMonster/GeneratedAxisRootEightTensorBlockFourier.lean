/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitData

/-! Genuine Fourier pairs are evaluated on complete fixed source rows before finite replay. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine unnormalized Fourier action restricted to an entire 256-coordinate row. -/
def generatedRootEightTensorBlockFourier (k : Fin 8) (v : Fin 256 → ℤ)
    (u : Fin 256) : ℤ :=
  (if u.val.testBit k.val then (-1 : ℤ) else 1) * v u +
    v (generatedNinthLowerSpinTensorBlockXorLow (Fin.castAdd 4 k) u)

private theorem block_testBit (k : Fin 8) (b : Fin 16) (u : Fin 256) :
    (generatedNinthLowerSpinTensorBlockIndex b u).val.testBit k.val = u.val.testBit k.val := by
  have hm : (b.val * 256 + u.val) % 256 = u.val := by omega
  have h := Nat.testBit_mod_two_pow (b.val * 256 + u.val) 8 k.val
  simpa only [generatedNinthLowerSpinTensorBlockIndex,
    show 2 ^ 8 = 256 by decide, hm, k.isLt, decide_true, Bool.true_and]
    using h.symm

private theorem block_xor_high (k : Fin 8) (b : Fin 16) :
    generatedNinthLowerSpinTensorBlockXorHigh (Fin.castAdd 4 k) b = b := by
  have hk : 2 ^ k.val < 256 := by
    simpa only [show 2 ^ 8 = 256 by decide] using
      Nat.pow_lt_pow_right (by decide : 1 < 2) k.isLt
  apply Fin.ext
  simp only [generatedNinthLowerSpinTensorBlockXorHigh, Fin.val_castAdd,
    Nat.div_eq_of_lt hk]
  change b.val ^^^ 0 = b.val
  exact Nat.xor_zero b.val

/-- Every original Fourier coefficient retains the same full source row and exact XOR slot. -/
theorem generatedRootEight_tensor_fourier_block (k : Fin 8) (v : NortonUIntegerVector)
    (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 k) v
      (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedRootEightTensorBlockFourier k
        (fun z => v (generatedNinthLowerSpinTensorBlockIndex b z)) u := by
  unfold generatedNinthLowerSpinTensorFourierInteger generatedRootEightTensorBlockFourier
  rw [generatedNinth_lower_spin_tensor_block_xor, block_xor_high]
  simp only [Fin.val_castAdd, block_testBit]

/-- An entire genuine Fourier pair is evaluated from the original fixed row alone. -/
theorem generatedRootEight_tensor_fourier_pair_block (k l : Fin 8)
    (v : NortonUIntegerVector) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 k)
      (generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 l) v)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
      generatedRootEightTensorBlockFourier k
        (generatedRootEightTensorBlockFourier l
          (fun z => v (generatedNinthLowerSpinTensorBlockIndex b z))) u := by
  rw [generatedRootEight_tensor_fourier_block]
  have h : (fun z => generatedNinthLowerSpinTensorFourierInteger (Fin.castAdd 4 l) v
      (generatedNinthLowerSpinTensorBlockIndex b z)) =
      generatedRootEightTensorBlockFourier l
        (fun z => v (generatedNinthLowerSpinTensorBlockIndex b z)) := by
    funext z
    exact generatedRootEight_tensor_fourier_block l v b z
  rw [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
