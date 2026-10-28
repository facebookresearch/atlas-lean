/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedLinear

/-! Ungated residual-divisibility specialization of the genuine signed linear packing theorem.
No unweighted word gap or numerical bound is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Divisibility of the eight source coefficients makes the weighted residual divisible by4. -/
theorem generatedTenth_source_column_spin_sum_packed_residual_dvd
    (k : Fin 4096) (w : Fin 8 → ℕ) (t : ℕ) (i : Fin 16) :
    4 ∣ ((∑ r : Fin 8, generatedTenthSourceColumnSpinSumCache r k *
      generatedRootEightPackedSignedDigit (w r) i) -
        4 * generatedRootEightPackedSignedDigit t i) := by
  apply dvd_sub
  · apply Finset.dvd_sum
    intro r _
    obtain ⟨a, ha⟩ := generatedTenth_source_column_spin_sum_four_dvd r k
    refine ⟨a * generatedRootEightPackedSignedDigit (w r) i, ?_⟩
    rw [ha]
    ring
  · exact ⟨generatedRootEightPackedSignedDigit t i, rfl⟩

/-- An exact whole-word relation and certified residual bounds give all16 weighted B equations. -/
theorem generatedTenth_source_column_spin_sum_packed_linear
    (k : Fin 4096) (w : Fin 8 → ℕ) (t : ℕ)
    (hw : ∀ r, w r < 512 ^ 16) (ht : t < 512 ^ 16)
    (hb : ∀ i : Fin 16,
      |(∑ r : Fin 8, generatedTenthSourceColumnSpinSumCache r k *
        generatedRootEightPackedSignedDigit (w r) i) -
          4 * generatedRootEightPackedSignedDigit t i| < 4 * 512)
    (hword : (∑ r : Fin 8, generatedTenthSourceColumnSpinSumCache r k *
      generatedRootEightPackedSignedWord (w r)) = 4 * generatedRootEightPackedSignedWord t) :
    ∀ i : Fin 16, (∑ r : Fin 8, generatedTenthSourceColumnSpinSumCache r k *
      generatedRootEightPackedSignedDigit (w r) i) = 4 * generatedRootEightPackedSignedDigit t i :=
  generatedRootEight_packed_signed_linear w t (fun r => generatedTenthSourceColumnSpinSumCache r k)
    4 4 (by norm_num) hw ht
    (generatedTenth_source_column_spin_sum_packed_residual_dvd k w t) hb hword

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

