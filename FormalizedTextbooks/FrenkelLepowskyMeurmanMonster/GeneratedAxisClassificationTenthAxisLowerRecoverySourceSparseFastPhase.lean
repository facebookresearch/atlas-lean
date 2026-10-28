/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactSparseIncomingFormula

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastLinear
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinQuadraticFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

/-! Ungated exact source quadratic circuit. Frozen parity is reused for arbitrary12-bit rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Four-XOR dot circuits evaluate each selected complete quadratic row without a new lookup. -/
def generatedTenthSourceSparseFastQuadratic (rows : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if n.testBit i.val then generatedNinthLowerSpinCircuitDotTwelve (rows i) n else 0))

/-- The circuit equals the existing genuine complete quadratic fast evaluator. -/
theorem generatedTenth_source_sparse_fast_quadratic_eq (rows : Fin 12 → ℕ) (n : ℕ) :
    generatedTenthSourceSparseFastQuadratic rows n = generatedTwelfthSpinQuadraticFast rows n := by
  unfold generatedTenthSourceSparseFastQuadratic generatedTwelfthSpinQuadraticFast
  simp_rw [generatedNinth_lower_spin_circuit_dot_twelve]

/-- The full spin quadratic is represented, including all144 diagonal/off-diagonal terms. -/
def generatedTenthSourceSparseFastQuadraticPhase (rows : Fin 12 → ℕ) (t : SpinIndex) : ZMod 2 :=
  if (generatedTenthSourceSparseFastQuadratic rows
    (generatedAxisGlobalSpinLabel t).val).testBit 0 then 1 else 0

/-- The fast quadratic phase is the original genuine quadratic at every spin coordinate. -/
theorem generatedTenth_source_sparse_fast_quadratic_phase
    (rows : Fin 12 → ℕ) (t : SpinIndex) :
    generatedTenthSourceSparseFastQuadraticPhase rows t =
      monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase rows) t := by
  unfold generatedTenthSourceSparseFastQuadraticPhase
  rw [generatedTenth_source_sparse_fast_quadratic_eq,
    generatedTwelfth_spin_quadratic_fast_actual, generatedAxisGlobalSpinLabel_decode]

/-- Original delta0 central Pauli, shift, inverse-coordinate map, and postquadratic all remain. -/
def generatedTenthSourceSparseFastDeltaZeroPhase (t : SpinIndex) : ZMod 2 :=
  spinPhase (generatedTenthAxisLowerRecoverySourceCompactPauli 0) t +
    generatedTenthSourceSparseFastQuadraticPhase
      (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0)
      (generatedTenthSourceSparseFastLeftInverse
        (t + spinTranslation (generatedTenthAxisLowerRecoverySourceCompactPauli 0)))

/-- Circuit evaluation does not change the actual compact delta0 phase. -/
theorem generatedTenth_source_sparse_fast_delta_zero_phase (t : SpinIndex) :
    generatedTenthSourceSparseFastDeltaZeroPhase t =
      generatedTenthSourceCompactDeltaZeroPhase t := by
  unfold generatedTenthSourceSparseFastDeltaZeroPhase generatedTenthSourceCompactDeltaZeroPhase
  rw [generatedTenth_source_sparse_fast_quadratic_phase,
    generatedTenth_source_sparse_fast_left_inverse]

/-- Each fixed source image contributes its original central/modulation phase and translation. -/
def generatedTenthSourceSparseFastDeltaPhase
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (t : SpinIndex) : ZMod 2 :=
  let q := generatedTenthSourceSparseFastQ p b
  spinPhase q t + generatedTenthSourceSparseFastDeltaZeroPhase (t + spinTranslation q)

/-- Full cached Pauli image binding proves every fast shifted-delta phase equality. -/
theorem generatedTenth_source_sparse_fast_delta_phase
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (t : SpinIndex) :
    generatedTenthSourceSparseFastDeltaPhase p b t =
      generatedTenthSourceCompactDeltaPhase
        (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b)) t := by
  unfold generatedTenthSourceSparseFastDeltaPhase generatedTenthSourceCompactDeltaPhase
  dsimp only
  rw [generatedTenth_source_sparse_fast_q_actual hQ,
    generatedTenth_source_sparse_fast_delta_zero_phase]

/-- Exact signed source coefficient numerator, using a cached full image rather than Q replay. -/
def generatedTenthSourceSparseFastSign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) (t : SpinIndex) : ℤ :=
  generatedAxisGlobalIntSign (generatedTenthSourceSparseFastDeltaPhase p b t)

/-- Original lower source signs retain the whole genuine central phase. -/
theorem generatedTenth_source_sparse_fast_low_sign
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (t : SpinIndex) :
    generatedTenthSourceSparseFastSign p 0 t =
      generatedTenthSourceCompactSparseIncomingLowSign p t := by
  exact congrArg generatedAxisGlobalIntSign
    (generatedTenth_source_sparse_fast_delta_phase hQ p 0 t)

/-- Original upper source signs retain their independent genuine central phase. -/
theorem generatedTenth_source_sparse_fast_high_sign
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (t : SpinIndex) :
    generatedTenthSourceSparseFastSign p 1 t =
      generatedTenthSourceCompactSparseIncomingHighSign p t := by
  exact congrArg generatedAxisGlobalIntSign
    (generatedTenth_source_sparse_fast_delta_phase hQ p 1 t)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

