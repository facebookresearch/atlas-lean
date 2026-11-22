/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Measurements.POVM


/-!
# Quantum channels as CPTP maps (Physlib crosswalk)

The Watrous definition of a quantum channel (Def. 2.13: completely positive and trace preserving) crosswalked to Physlib `CPTPMap`, with the arbitrary-ancilla form of complete positivity.

Receipts (dependency crosswalk; states, measurement, and partial-trace API are
consumed, not redefined): channels map states to states
(`CPTPMap.instMFunLike`); composition (`CPTPMap.compose_eq`), tensor products
(`CPTPMap.prod_apply_prod`), and unitary conjugation
(`CPTPMap.ofUnitary_eq_conj`); partial-trace channels (`CPTPMap.traceLeft`,
`CPTPMap.traceRight`, `CPTPMap.traceLeft_eq_MState_traceLeft`) with
product-state partial traces (`MState.traceLeft_prod_eq`,
`MState.traceRight_prod_eq`); measurement maps (`POVM.measurementMap`,
`POVM.traceLeft_measurementMap_eq_measure`, `POVM.measureDiscard_apply`); and
state preparation (`CPTPMap.replacement_apply`). Complete positivity is
`MatrixMap.IsCompletelyPositive`, with arbitrary finite ancillae via
`MatrixMap.IsCompletelyPositive.of_Fintype`; trace preservation is
`MatrixMap.IsTracePreserving` (`CPTPMap.IsTracePreserving`).
-/

@[expose] public section


namespace PhyslibExt.QuantumInfo.Channels

set_option autoImplicit false

/-- Watrous Def. 2.13(1) with Sec. 1.2 CP definition (arbitrary finite ancilla Z) -/
lemma kron_id_isPositive {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] (Λ : CPTPMap dIn dOut) (Z : Type*) [Fintype Z] [DecidableEq Z] : (Λ.map.kron (LinearMap.id : MatrixMap Z Z ℂ)).IsPositive := by
  exact Λ.cp.of_Fintype Z

/-- Watrous Def. 2.13 (channel = CP and TP linear map) <-> Physlib CPTPMap -/
lemma exists_cptpMap_iff {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] (Φ : MatrixMap dIn dOut ℂ) : (∃ Λ : CPTPMap dIn dOut, Λ.map = Φ) ↔ ((∀ (Z : Type) [Fintype Z] [DecidableEq Z], (Φ.kron (LinearMap.id : MatrixMap Z Z ℂ)).IsPositive) ∧ Φ.IsTracePreserving) := by
  constructor
  · rintro ⟨Λ, rfl⟩
    exact ⟨fun Z _ _ => Λ.cp.of_Fintype Z, Λ.TP⟩
  · rintro ⟨hCP, hTP⟩
    exact ⟨{ toLinearMap := Φ, cp := fun n => hCP (Fin n), TP := hTP }, rfl⟩

end PhyslibExt.QuantumInfo.Channels
