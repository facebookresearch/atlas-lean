/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine diagonal short and Pauli tensor traces for actual extraspecial elements. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTraceLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Actual local Q short phases are precisely the extraspecial commutator pairing. -/
theorem monsterGeometryQ_short_phase (q : Q) (r : GriessShortIndex) :
    localShortPhase (localFiberIncl q) r =
      qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
        qBeta (toAdd (griessShortQ r).base) (toAdd q.base) := by
  change toAdd (spinConjugation (spinHolomorphIncl q) (griessShortQ r)).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]

/-- Actual extraspecial short operators are diagonal with their genuine pairing signs. -/
theorem monsterGeometryQ_short_apply (q : Q) (x : GriessShortIndex → ℝ) (r : GriessShortIndex) :
    localShortRepresentation (localFiberIncl q) x r =
      qSign (qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
        qBeta (toAdd (griessShortQ r).base) (toAdd q.base)) * x r := by
  have hp : griessShortPermutation (localFiberIncl q).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  have he := localShortOperator_image (localFiberIncl q) x r
  rw [hp, monsterGeometryQ_short_phase] at he
  exact he

/-- The actual short-block trace is the sum of its checked diagonal pairing signs. -/
theorem monsterGeometryQ_short_trace (q : Q) :
    LinearMap.trace ℝ (GriessShortIndex → ℝ)
      (localShortRepresentation (localFiberIncl q)).toLinearMap =
        ∑ r : GriessShortIndex,
          qSign (qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
            qBeta (toAdd (griessShortQ r).base) (toAdd q.base)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ GriessShortIndex)]
  simp [Matrix.trace, monsterGeometryQ_short_apply]

/-- The actual Q tensor block is the original Pauli map tensored with the spatial identity. -/
theorem monsterGeometryQ_tensor_map (q : Q) :
    (localTensorRepresentation (localFiberIncl q)).toLinearMap =
      conwayTensorCoordinates.conj
        (TensorProduct.map (spinRepresentation q).toLinearMap
          (LinearMap.id : (Fin 24 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ))) := by
  rfl

/-- Tensor trace is twenty-four times the genuine spin trace. -/
theorem monsterGeometryQ_tensor_trace (q : Q) :
    LinearMap.trace ℝ (SpinIndex → Fin 24 → ℝ)
      (localTensorRepresentation (localFiberIncl q)).toLinearMap =
        LinearMap.trace ℝ SpinSpace (spinRepresentation q).toLinearMap * 24 := by
  rw [monsterGeometryQ_tensor_map, LinearMap.trace_conj', LinearMap.trace_tensorProduct',
    LinearMap.trace_id, Module.finrank_pi, Fintype.card_fin]
  norm_num

/-- The actual tensor trace vanishes for every noncentral extraspecial element. -/
theorem monsterGeometryQ_tensor_trace_noncentral (q : Q) (hq : q ∉ centerQ) :
    LinearMap.trace ℝ (SpinIndex → Fin 24 → ℝ)
      (localTensorRepresentation (localFiberIncl q)).toLinearMap = 0 := by
  rw [monsterGeometryQ_tensor_trace, spinRepresentation_trace_noncentral' q hq, zero_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
