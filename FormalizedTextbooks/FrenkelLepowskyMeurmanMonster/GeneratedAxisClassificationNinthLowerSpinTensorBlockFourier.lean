/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Every genuine Fourier bit is evaluated on complete source rows, retaining the exact
row transitions of bits eight through eleven and every original integer sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Full original Fourier action on exact source rows and their 256-coordinate offsets. -/
def generatedNinthLowerSpinTensorBlockFourier (k : Fin 12)
    (v : Fin 16 → Fin 256 → ℤ) (b : Fin 16) (u : Fin 256) : ℤ :=
  (if (if k.val < 8 then u.val.testBit k.val else b.val.testBit (k.val - 8))
    then (-1 : ℤ) else 1) * v b u +
      v (generatedNinthLowerSpinTensorBlockXorHigh k b)
        (generatedNinthLowerSpinTensorBlockXorLow k u)

private theorem block_testBit (k : Fin 12) (b : Fin 16) (u : Fin 256) :
    (generatedNinthLowerSpinTensorBlockIndex b u).val.testBit k.val =
      if k.val < 8 then u.val.testBit k.val else b.val.testBit (k.val - 8) := by
  change (b.val * 256 + u.val).testBit k.val = _
  by_cases h : k.val < 8
  · rw [ite_eq_left h]
    have hm : (b.val * 256 + u.val) % 256 = u.val := by omega
    have ht := Nat.testBit_mod_two_pow (b.val * 256 + u.val) 8 k.val
    simpa only [show 2 ^ 8 = 256 by decide, hm, h, decide_true, Bool.true_and] using ht.symm
  · rw [ite_eq_right h]
    have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
    have he : k.val - 8 + 8 = k.val := by omega
    have ht := Nat.testBit_add (b.val * 256 + u.val) (k.val - 8) 8
    simpa only [show 2 ^ 8 = 256 by decide, he, hb] using ht

/-- Every original full Fourier value equals its complete source-row evaluation. -/
theorem generatedNinth_lower_spin_tensor_fourier_block (k : Fin 12)
    (v : NortonUIntegerVector) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorFourierInteger k v
      (generatedNinthLowerSpinTensorBlockIndex b u) =
        generatedNinthLowerSpinTensorBlockFourier k
          (fun c z => v (generatedNinthLowerSpinTensorBlockIndex c z)) b u := by
  unfold generatedNinthLowerSpinTensorFourierInteger generatedNinthLowerSpinTensorBlockFourier
  rw [generatedNinth_lower_spin_tensor_block_xor, block_testBit]

/-- The complete two-Fourier action retains every row transition, offset and original sign. -/
theorem generatedNinth_lower_spin_tensor_fourier_pair_block (k l : Fin 12)
    (v : NortonUIntegerVector) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorFourierInteger k
      (generatedNinthLowerSpinTensorFourierInteger l v)
        (generatedNinthLowerSpinTensorBlockIndex b u) =
          generatedNinthLowerSpinTensorBlockFourier k
            (generatedNinthLowerSpinTensorBlockFourier l
              (fun c z => v (generatedNinthLowerSpinTensorBlockIndex c z))) b u := by
  rw [generatedNinth_lower_spin_tensor_fourier_block]
  have h : (fun c z => generatedNinthLowerSpinTensorFourierInteger l v
      (generatedNinthLowerSpinTensorBlockIndex c z)) =
        generatedNinthLowerSpinTensorBlockFourier l
          (fun c z => v (generatedNinthLowerSpinTensorBlockIndex c z)) := by
    funext c z
    exact generatedNinth_lower_spin_tensor_fourier_block l v c z
  rw [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
