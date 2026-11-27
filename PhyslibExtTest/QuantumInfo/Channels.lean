/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Channels

/-!
# Tests: Quantum channels as CPTP maps (Physlib crosswalk)
-/

@[expose] public section


namespace PhyslibExtTest.QuantumInfo.Channels

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Channels

#print axioms kron_id_isPositive
#print axioms exists_cptpMap_iff

/-- Trace preservation is load-bearing: the zero map is not a channel. -/
theorem not_exists_cptpMap_zero_map :
    ¬ ∃ Λ : CPTPMap (Fin 1) (Fin 1), Λ.map = 0 := by
  rintro ⟨Λ, h⟩
  have hTP : Λ.map.IsTracePreserving := Λ.TP
  have h1 := hTP (1 : Matrix (Fin 1) (Fin 1) ℂ)
  rw [h] at h1
  simp at h1

/-- The identity map is a channel. -/
theorem exists_cptpMap_id {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d] :
    ∃ Λ : CPTPMap d d, Λ.map = (LinearMap.id : MatrixMap d d ℂ) := by
  exact ⟨CPTPMap.id, CPTPMap.id_map⟩

/-- The arbitrary-ancilla lemma at a concrete channel with ancilla `Fin 4`. -/
theorem kron_id_isPositive_concrete :
    ((CPTPMap.id (dIn := Fin 2)).map.kron
      (LinearMap.id : MatrixMap (Fin 4) (Fin 4) ℂ)).IsPositive :=
  kron_id_isPositive CPTPMap.id (Fin 4)

/-- Backward direction of the characterization on the identity map. -/
theorem exists_cptpMap_of_id_cp_tp {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d] :
    ∃ Λ : CPTPMap d d, Λ.map = (LinearMap.id : MatrixMap d d ℂ) := by
  apply (exists_cptpMap_iff (LinearMap.id : MatrixMap d d ℂ)).mpr
  refine ⟨?_, MatrixMap.IsTracePreserving.id⟩
  intro Z _ _
  rw [show (LinearMap.id : MatrixMap d d ℂ) = MatrixMap.id d ℂ from rfl,
    show (LinearMap.id : MatrixMap Z Z ℂ) = MatrixMap.id Z ℂ from rfl,
    MatrixMap.kron_id_id]
  exact MatrixMap.IsPositive.id

/-- Forward direction of the characterization on the partial-trace channel. -/
theorem forward_traceLeft_of_exists {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] [Nonempty d₁] [Nonempty d₂] :
    (∀ (Z : Type) [Fintype Z] [DecidableEq Z],
      ((CPTPMap.traceLeft (d₁ := d₁) (d₂ := d₂)).map.kron
        (LinearMap.id : MatrixMap Z Z ℂ)).IsPositive)
      ∧ (CPTPMap.traceLeft (d₁ := d₁) (d₂ := d₂)).map.IsTracePreserving :=
  (exists_cptpMap_iff _).mp ⟨CPTPMap.traceLeft, rfl⟩

/-- Partial traces of product states, through the trace channels. -/
theorem trace_prod_states {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]
    [DecidableEq d₁] [DecidableEq d₂] (ρ₁ : MState d₁) (ρ₂ : MState d₂) :
    (CPTPMap.traceLeft (d₁ := d₁) (d₂ := d₂) (ρ₁ ⊗ᴹ ρ₂) = ρ₂)
      ∧ (CPTPMap.traceRight (d₁ := d₁) (d₂ := d₂) (ρ₁ ⊗ᴹ ρ₂) = ρ₁) := by
  constructor
  · rw [CPTPMap.traceLeft_eq_MState_traceLeft, MState.traceLeft_prod_eq]
  · rw [CPTPMap.traceRight_eq_MState_traceRight, MState.traceRight_prod_eq]

/-- The replacement channel prepares its state. -/
theorem replacement_prepares {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dOut] [Nonempty dIn] (ρ : MState dOut) (ρ₀ : MState dIn) :
    CPTPMap.replacement ρ ρ₀ = ρ :=
  CPTPMap.replacement_apply ρ ρ₀

end PhyslibExtTest.QuantumInfo.Channels
