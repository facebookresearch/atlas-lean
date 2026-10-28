/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroCachedIncoming
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinPauliFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

/-! Exact full source Pauli signs and translations for every shifted delta-zero value. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual source translation label, retaining all twelve original low bits. -/
def generatedTenthSourcePauliLow (p : GeneratedTenthSourceInitialTensorSparseIndex)
    (b : Fin 2) : Fin 4096 :=
  ⟨generatedTenthSourceSparseFastQWord b p.1 p.2 % 4096, Nat.mod_lt _ (by decide)⟩

/-- Actual source modulation label, retaining all twelve original upper base bits. -/
def generatedTenthSourcePauliHigh (p : GeneratedTenthSourceInitialTensorSparseIndex)
    (b : Fin 2) : Fin 4096 :=
  ⟨generatedTenthSourceSparseFastQWord b p.1 p.2 / 4096 % 4096, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 4000000 in
-- Check all128 fixed Pauli translations, modulations and original central signs.
private theorem source_pauli_metadata :
    ∀ (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2),
      (∀ i, spinTranslation (generatedTenthSourceSparseFastQ p b) i =
        golayLabelCoefficients (generatedTenthSourcePauliLow p b) i) ∧
      (∀ i, spinModulation (generatedTenthSourceSparseFastQ p b) i =
        golayLabelCoefficients (generatedTenthSourcePauliHigh p b) i) ∧
      nortonUIntegerSign (toAdd (generatedTenthSourceSparseFastQ p b).coeff) =
        (if (generatedTenthSourceSparseFastQWord b p.1 p.2).testBit 24 then -1 else 1) := by
  decide +kernel

/-- Full original central sign, modulation and shifted delta-zero value via bit arithmetic. -/
def generatedTenthSourcePauliCachedSign (p : GeneratedTenthSourceInitialTensorSparseIndex)
    (b : Fin 2) (k : Fin 4096) : ℤ :=
  (if (generatedTenthSourceSparseFastQWord b p.1 p.2).testBit 24 then -1 else 1) *
    (if (generatedNinthLowerSpinCircuitDotTwelve
      (generatedTenthSourcePauliHigh p b).val k.val).testBit 0 then -1 else 1) *
    generatedTenthSourceDeltaZeroSignCache
      (generatedAxisGlobalSpinLabelXor k (generatedTenthSourcePauliLow p b))

/-- The evaluator equals the complete genuine cached source sign at every original label. -/
theorem generatedTenth_source_pauli_cached_sign_actual
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (k : Fin 4096) :
    generatedTenthSourceDeltaZeroCachedSign p b (golayLabelCoefficients k) =
      generatedTenthSourcePauliCachedSign p b k := by
  have ht := funext (source_pauli_metadata p b).1
  have hm := funext (source_pauli_metadata p b).2.1
  unfold generatedTenthSourceDeltaZeroCachedSign generatedTenthSourcePauliCachedSign
  dsimp only
  change nortonUIntegerSign (spinPhase (generatedTenthSourceSparseFastQ p b)
    (golayLabelCoefficients k)) * _ = _
  rw [generatedTwelfth_spin_pauli_sign_fast, ht, hm, nortonUIntegerLabel_coeff]
  rw [(source_pauli_metadata p b).2.2,
    ← generatedAxisGlobalSpinLabelXor_coeff, generatedAxisGlobalSpinLabel_coeff,
    ← generatedNinth_lower_spin_circuit_dot_twelve]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
