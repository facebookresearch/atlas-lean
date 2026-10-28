/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source points have trace 276; noncentral Q traces are independent of central phase. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTraceParts

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The literal central extraspecial element has spin trace minus 4096. -/
theorem monsterGeometryQ_central_spin_trace :
    LinearMap.trace ℝ SpinSpace (spinRepresentation qCentralInvolution).toLinearMap = -4096 := by
  rw [← spinCoordinateTrace_eq_trace]
  change spinCoordinateTrace (spinRepresentation (qCentral 1)).toLinearMap = -4096
  rw [spinRepresentation_trace_central]
  norm_num [qSign]

/-- The central extraspecial element fixes every actual short coordinate, hence has trace 98280. -/
theorem monsterGeometryQ_central_short_trace :
    LinearMap.trace ℝ (GriessShortIndex → ℝ)
      (localShortRepresentation (localFiberIncl qCentralInvolution)).toLinearMap = 98280 := by
  rw [monsterGeometryQ_short_trace]
  change (∑ r : GriessShortIndex,
    qSign (qBeta 0 (toAdd (griessShortQ r).base) +
      qBeta (toAdd (griessShortQ r).base) 0)) = 98280
  simp only [qBeta_zero_left, qBeta_zero_right, zero_add, qSign_zero, Finset.sum_const,
    Finset.card_univ, griessShortIndex_card, nsmul_eq_mul, mul_one]
  norm_num

/-- The actual distinguished involution has Griess trace 276 from its full source block actions. -/
theorem monsterGeometryCentral_trace : monsterGeometryTrace generatedCentralInvolution = 276 := by
  change monsterGeometryTrace (qIntoGenerated qCentralInvolution) = 276
  rw [monsterGeometryQ_trace, monsterGeometryQ_central_short_trace,
    monsterGeometryQ_tensor_trace, monsterGeometryQ_central_spin_trace]
  norm_num

/-- Every actual original Monster geometry point has the concrete Griess trace 276. -/
theorem monsterGeometryPoint_trace276 (p : MonsterGeometryPoint) :
    monsterGeometryTrace p.val = 276 := by
  rw [monsterGeometryPoint_trace, monsterGeometryCentral_trace]

/-- Noncentral actual extraspecial elements with the same binary coordinate have equal traces. -/
theorem monsterGeometryQ_trace_eq_of_base_eq (q k : Q) (hb : q.base = k.base)
    (hq : q ∉ centerQ) (hk : k ∉ centerQ) :
    monsterGeometryTrace (qIntoGenerated q) = monsterGeometryTrace (qIntoGenerated k) := by
  rw [monsterGeometryQ_trace, monsterGeometryQ_trace,
    monsterGeometryQ_tensor_trace_noncentral q hq,
    monsterGeometryQ_tensor_trace_noncentral k hk,
    monsterGeometryQ_short_trace, monsterGeometryQ_short_trace, hb]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
