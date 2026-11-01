/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages

/-! Complete one-vector source arithmetic and its genuine tensor-stage interface.
All retained coordinates occur in the explicit arithmetic conditions. No finite
source evaluation is asserted here without a certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The complete seven-stage original word has a deep expression spine.
set_option maxRecDepth 10000

/-- All eight complete original spin numerator states. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpin : Fin 8 → Fin 4096 → ℤ :=
  ![generatedTenthAxisLowerRecoverySourceDeltaTensorData00Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData01Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData02Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData03Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData04Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData05Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData06Spin,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData07Spin]

/-- All eight complete original physical numerator states. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial : Fin 8 → Fin 24 → ℤ :=
  ![generatedTenthAxisLowerRecoverySourceDeltaTensorData00Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData01Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData02Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData03Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData04Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData05Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData06Spatial,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData07Spatial]

/-- The exact positive spin scale at every original stage. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator : Fin 8 → ℕ :=
  ![generatedTenthAxisLowerRecoverySourceDeltaTensorData00SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData01SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData02SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData03SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData04SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData05SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData06SpinDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData07SpinDenominator]

/-- The exact positive physical scale at every original stage. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator : Fin 8 → ℕ :=
  ![generatedTenthAxisLowerRecoverySourceDeltaTensorData00SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData01SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData02SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData03SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData04SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData05SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData06SpatialDenominator,
    generatedTenthAxisLowerRecoverySourceDeltaTensorData07SpatialDenominator]

/-- The packet retains all physical columns and all original spin coordinates. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorPacket (n : Fin 8) :
    SpinIndex → Fin 24 → ℝ :=
  generatedAxisGlobalTensorIntegerPacket
    (generatedAxisGlobalOddTensorFactor (generatedTenthAxisLowerRecoverySourceDeltaTensorSpin n)
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial n))
    (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator n *
      generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator n)

/-- Each original stage binds all4096 retained spin numerators, with their exact denominators. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpinStageCondition (j : Fin 7) : Prop :=
  ∀ k : Fin 4096,
    (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.succ : ℤ) *
        generatedTwelfthTensorSourceStageSpin 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpin j.castSucc) k =
      (generatedTwelfthTensorSourceStageSpinDenominator 2 j
        (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.castSucc) : ℤ) *
          generatedTenthAxisLowerRecoverySourceDeltaTensorSpin j.succ k

/-- Each original stage binds all24 physical numerators, with their exact denominators. -/
def generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialStageCondition (j : Fin 7) : Prop :=
  ∀ i : Fin 24,
    (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.succ : ℤ) *
        generatedTwelfthTensorSourceStageSpatial 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial j.castSucc) i =
      (generatedTwelfthTensorSourceStageSpatialDenominator 2 j
        (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.castSucc) : ℤ) *
          generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial j.succ i

/-- Cross-multiplied complete integer packets agree at their genuine nonzero scales. -/
theorem generatedTenth_axis_lower_recovery_integer_packet_rescale
    (N M : Fin 4096 → Fin 24 → ℤ) (D E : ℕ) (hD : D ≠ 0) (hE : E ≠ 0)
    (h : ∀ k i, (E : ℤ) * N k i = (D : ℤ) * M k i) :
    generatedAxisGlobalTensorIntegerPacket N D = generatedAxisGlobalTensorIntegerPacket M E := by
  funext t i
  unfold generatedAxisGlobalTensorIntegerPacket
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hd : (D : ℝ) * Real.sqrt 2 ≠ 0 := mul_ne_zero (by exact_mod_cast hD) hs
  have he : (E : ℝ) * Real.sqrt 2 ≠ 0 := mul_ne_zero (by exact_mod_cast hE) hs
  apply (div_eq_div_iff hd he).mpr
  have hh : (E : ℝ) * (N (generatedAxisGlobalSpinLabel t) i : ℝ) =
      (D : ℝ) * (M (generatedAxisGlobalSpinLabel t) i : ℝ) := by
    exact_mod_cast h (generatedAxisGlobalSpinLabel t) i
  calc
    (N (generatedAxisGlobalSpinLabel t) i : ℝ) * ((E : ℝ) * Real.sqrt 2) =
        ((E : ℝ) * (N (generatedAxisGlobalSpinLabel t) i : ℝ)) * Real.sqrt 2 := by ring
    _ = ((D : ℝ) * (M (generatedAxisGlobalSpinLabel t) i : ℝ)) * Real.sqrt 2 := by rw [hh]
    _ = (M (generatedAxisGlobalSpinLabel t) i : ℝ) * ((D : ℝ) * Real.sqrt 2) := by ring

/-- The separated complete certificates yield one genuine original tensor stage action. -/
theorem generatedTenth_axis_lower_recovery_source_delta_tensor_stage
    (j : Fin 7)
    (hs : generatedTenthAxisLowerRecoverySourceDeltaTensorSpinStageCondition j)
    (hv : generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialStageCondition j)
    (hD : generatedTwelfthTensorSourceStageSpinDenominator 2 j
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.castSucc) *
        generatedTwelfthTensorSourceStageSpatialDenominator 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.castSucc) ≠ 0)
    (hE : generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.succ *
      generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.succ ≠ 0) :
    localTensorRepresentation (generatedAxisGlobalFifthShortNormalizationFiber 2 j)
        (generatedTenthAxisLowerRecoverySourceDeltaTensorPacket j.castSucc) =
      generatedTenthAxisLowerRecoverySourceDeltaTensorPacket j.succ := by
  unfold generatedTenthAxisLowerRecoverySourceDeltaTensorPacket
  rw [generatedTwelfth_tensor_source_stage_packet]
  apply generatedTenth_axis_lower_recovery_integer_packet_rescale _ _ _ _ hD hE
  intro k i
  unfold generatedAxisGlobalOddTensorFactor
  push_cast
  calc
    _ = ((generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.succ : ℤ) *
        generatedTwelfthTensorSourceStageSpin 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpin j.castSucc) k) *
      ((generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.succ : ℤ) *
        generatedTwelfthTensorSourceStageSpatial 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatial j.castSucc) i) := by ring
    _ = _ := by rw [hs k, hv i]; ring

/-- A bounded chain is assembled with variable fibers and variable packets. -/
private theorem generatedTenth_source_delta_chain_generic
    (u : Fin 7 → localFiberSubgroup) (v : Fin 8 → SpinIndex → Fin 24 → ℝ)
    (hstage : ∀ j : Fin 7, localTensorRepresentation (u j) (v j.castSucc) = v j.succ) :
    localTensorRepresentation (generatedAxisGlobalWordChain
      (fun j => u ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7) (v 0) = v 7 := by
  have hstep : ∀ (n : ℕ) (hn : n ≤ 7),
      localTensorRepresentation (generatedAxisGlobalWordChain
        (fun j => u ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n) (v ⟨0, by decide⟩) =
          v ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero => intro hn; simp [generatedAxisGlobalWordChain]
    | succ n ih =>
      intro hn
      rw [generatedAxisGlobalWordChain, map_mul, LinearEquiv.mul_apply, ih (by omega)]
      have hm : n % 7 = n := Nat.mod_eq_of_lt (by omega)
      simpa only [hm, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] using
        hstage ⟨n, by omega⟩
  have hzero : (0 : Fin 8) = ⟨0, by decide⟩ := rfl
  have hseven : (7 : Fin 8) = ⟨7, by decide⟩ := rfl
  rw [hzero, hseven]
  exact hstep 7 (by omega)

/-- Seven actual stage actions assemble the exact original whole source tensor word. -/
theorem generatedTenth_axis_lower_recovery_source_delta_tensor_chain
    (hstage : ∀ j : Fin 7,
      localTensorRepresentation (generatedAxisGlobalFifthShortNormalizationFiber 2 j)
        (generatedTenthAxisLowerRecoverySourceDeltaTensorPacket j.castSucc) =
          generatedTenthAxisLowerRecoverySourceDeltaTensorPacket j.succ) :
    localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2)
      (generatedTenthAxisLowerRecoverySourceDeltaTensorPacket 0) =
        generatedTenthAxisLowerRecoverySourceDeltaTensorPacket 7 := by
  unfold generatedAxisGlobalFifthShortWordFiber
  rw [← generatedTenth_source_delta_chain_generic
    (generatedAxisGlobalFifthShortNormalizationFiber 2)
    generatedTenthAxisLowerRecoverySourceDeltaTensorPacket hstage]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
