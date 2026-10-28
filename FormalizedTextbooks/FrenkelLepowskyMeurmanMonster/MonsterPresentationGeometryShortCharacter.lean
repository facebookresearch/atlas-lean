/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original three short-coordinate families have total character 4072. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryShortSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryShortCounts

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A finite sign sum is twice its positive count minus its total population. -/
theorem monsterGeometrySignedCount {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then (1 : ℝ) else -1) = 2 * (s.filter p).card - s.card := by
  have ht : ∀ i, (if p i then (1 : ℝ) else -1) =
      2 * (if p i then (1 : ℝ) else 0) - 1 := by
    intro i
    split_ifs <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- The original 759 octad supports have sign sum 55 at the first two physical positions. -/
theorem monsterGeometryShort_octad_character :
    (∑ d : Fin 759, monsterGeometryShortCodeSign (golayOctadLabel d).val) = 55 := by
  change (∑ d : Fin 759, (fun x : golayOctads => monsterGeometryShortCodeSign x.val.val)
    ((golayOctads.orderIsoOfFin golayOctads_card).toEquiv d)) = 55
  rw [(golayOctads.orderIsoOfFin golayOctads_card).toEquiv.sum_comp
    (fun x : golayOctads => monsterGeometryShortCodeSign x.val.val),
    golayOctads.sum_coe_sort (fun x : Fin 4096 => monsterGeometryShortCodeSign x.val)]
  simp only [monsterGeometryShortCodeSign]
  rw [monsterGeometrySignedCount, monsterGeometryShort_octads_agree_card, golayOctads_card]
  norm_num

/-- The original low eleven-bit odd-family labels have zero character. -/
theorem monsterGeometryShort_odd_character :
    (∑ d : Fin 2048, monsterGeometryShortCodeSign d.val) = 0 := by
  simp only [monsterGeometryShortCodeSign]
  rw [monsterGeometrySignedCount, monsterGeometryShort_odd_agree_card]
  norm_num

/-- The literal actual Q short-block trace is 4072 on the physical minus-pair representative. -/
theorem monsterGeometryShortBase_short_trace :
    LinearMap.trace ℝ (GriessShortIndex → ℝ)
      (localShortRepresentation (localFiberIncl monsterGeometryShortBaseQ)).toLinearMap =
        4072 := by
  rw [monsterGeometryQ_short_trace]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
    monsterGeometryShortBase_pair_sign, monsterGeometryShortBase_octad_sign,
    monsterGeometryShortBase_odd_sign]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum, monsterGeometryShort_octad_character,
    monsterGeometryShort_odd_character]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
