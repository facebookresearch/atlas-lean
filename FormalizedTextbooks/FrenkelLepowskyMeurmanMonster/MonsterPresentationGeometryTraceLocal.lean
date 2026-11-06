/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical three-block trace formula for genuine extraspecial Griess operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTraceBlocks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Q operator fixes the matrix block and retains its original short and spin actions. -/
theorem monsterGeometryQ_trace_blocks_apply (q : Q) (x : GriessSpace) :
    monsterGeometryGriessTraceBlocks (rhoLocal (inclQ q) x) =
      ((monsterGeometryGriessTraceBlocks x).1,
        (localShortRepresentation (localFiberIncl q) (monsterGeometryGriessTraceBlocks x).2.1,
          localTensorRepresentation (localFiberIncl q)
            (monsterGeometryGriessTraceBlocks x).2.2)) := by
  have h := localGriessRepresentation_encode (localFiberIncl q) x
  rw [localConwayRawRepresentation_apply] at h
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    change (griessConwayEncode (rhoLocal (inclQ q) x)).1 = (griessConwayEncode x).1
    have hm := congrArg Prod.fst h
    change (griessConwayEncode (rhoLocal (inclQ q) x)).1 =
      conwayMatrixAction 1 (griessConwayEncode x).1 at hm
    simpa only [map_one, LinearEquiv.coe_one, id_eq] using hm
  · change (griessConwayEncode (rhoLocal (inclQ q) x)).2 =
      (localShortRepresentation (localFiberIncl q) (griessConwayEncode x).2.1,
        localTensorRepresentation (localFiberIncl q) (griessConwayEncode x).2.2)
    exact congrArg Prod.snd h

/-- Conjugating the actual Q operator into physical blocks gives a literal product map. -/
theorem monsterGeometryQ_trace_blocks_conj (q : Q) :
    monsterGeometryGriessTraceBlocks.conj (rhoLocal (inclQ q)).toLinearMap =
      LinearMap.prodMap (LinearMap.id : monsterGeometrySymmetricMatrices →ₗ[ℝ]
        monsterGeometrySymmetricMatrices)
        (LinearMap.prodMap (localShortRepresentation (localFiberIncl q)).toLinearMap
          (localTensorRepresentation (localFiberIncl q)).toLinearMap) := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply]
  simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe,
    monsterGeometryGriessTraceBlocks.apply_symm_apply] using
    monsterGeometryQ_trace_blocks_apply q (monsterGeometryGriessTraceBlocks.symm x)

/-- Exact actual Griess trace formula for an arbitrary extraspecial element. -/
theorem monsterGeometryQ_trace (q : Q) :
    monsterGeometryTrace (qIntoGenerated q) = 300 +
      (LinearMap.trace ℝ (GriessShortIndex → ℝ)
        (localShortRepresentation (localFiberIncl q)).toLinearMap +
      LinearMap.trace ℝ (SpinIndex → Fin 24 → ℝ)
        (localTensorRepresentation (localFiberIncl q)).toLinearMap) := by
  change LinearMap.trace ℝ GriessSpace (rhoLocal (inclQ q)).toLinearMap = _
  rw [← LinearMap.trace_conj' (rhoLocal (inclQ q)).toLinearMap monsterGeometryGriessTraceBlocks,
    monsterGeometryQ_trace_blocks_conj, LinearMap.trace_prodMap', LinearMap.trace_id,
    monsterGeometrySymmetricMatrices_finrank, LinearMap.trace_prodMap']
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
