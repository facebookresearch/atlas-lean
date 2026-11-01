/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairTri

/-! # Packed evaluation of the tensor-to-tensor part of `pairTri`

The tensor-to-tensor part `Σ k, Σ j, tPartQ fwd L.ten k j * W.ten k j` of the triality pairing
(`GeneratedAxisGlobalIdentPairTri`) is a packed dot product when both tensors are packed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- The triality tensor term `tPartQ` of a packed tensor is the packed triality part. -/
theorem tPartQ_packed (fwd : Bool) {w B : ℕ} {X : List SVec} (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) (D : ℚ) (k : Fin 4096) (j : Fin 24) :
    tPartQ fwd (tensorRat w X D) k j = tensorRat w (trialityTensorT w (!fwd) X) (2 * D) k j := by
  simp only [tPartQ, tensorRat]
  rw [(trialityTensorT_spec (!fwd) hX hB).2 j.val j.isLt k.val k.isLt]
  have hsg := tpred_sign (!fwd) j k
  push_cast
  rw [hsg]
  simp only [oddWeightSign, oddCoordSign]
  cases fwd
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    field_simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, one_mul]
    field_simp
    ring

/-- The tensor-to-tensor part of `pairTri` on packed tensors is a packed dot product. -/
theorem tPart_sum (fwd : Bool) {w B : ℕ} {X : List SVec} (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) (Y : List SVec) (D E : ℚ) :
    ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ fwd (tensorRat w X D) k j * tensorRat w Y E k j =
      (tdot w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E) := by
  have h := tdot_rat w (trialityTensorT w (!fwd) X) Y (2 * D) E
  simp only [tPartQ_packed fwd hX hB D]
  calc ∑ k : Fin 4096, ∑ j : Fin 24,
        tensorRat w (trialityTensorT w (!fwd) X) (2 * D) k j * tensorRat w Y E k j
      = (∑ k : Fin 4096, ∑ j : Fin 24,
          tensorRat w (trialityTensorT w (!fwd) X) (2 * D) k j * tensorRat w Y E k j / 2) * 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
        rw [h]
        ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
