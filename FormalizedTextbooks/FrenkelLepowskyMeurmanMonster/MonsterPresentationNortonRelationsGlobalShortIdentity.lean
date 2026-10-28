/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A global finite identity test from genuine pure-short vectors and one tensor vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairCentralizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each actual signed short axis is a polynomial in its genuine pure-short vector. -/
theorem monsterNortonShortAxis_polynomial (r : GriessShortIndex) (c : ZMod 2) :
    conwayShortAxis r c =
      (2 : ℝ) • griessProd (monsterNortonPureShort r) (monsterNortonPureShort r) -
        (8 * qSign c : ℝ) • monsterNortonPureShort r := by
  have hs : griessConwayEncode (monsterNortonPureShort r) = conwayShortBasis r :=
    griessConwayEncode_decode _ (by intros; rfl)
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode _ = griessConwayEncodeLinear _
  rw [map_sub, map_smul, map_smul]
  change griessConwayEncode _ = (2 : ℝ) •
    griessConwayEncode (griessProd (monsterNortonPureShort r) (monsterNortonPureShort r)) -
      (8 * qSign c : ℝ) • griessConwayEncode (monsterNortonPureShort r)
  rw [conwayShortAxis_encode, griessProd_encode, hs, conwayRawProduct_shortBasis_square]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp [conwayShortAxisRaw, conwayShortBasis, Matrix.vecMulVec_apply]
  · ext s
    simp [conwayShortAxisRaw, conwayShortBasis]
  · ext t i
    simp [conwayShortAxisRaw, conwayShortBasis]

/-- Fixing one actual pure-short vector fixes both signed axes without a local-action assumption. -/
theorem monsterNortonGenerated_fix_short_axis (g : G) (r : GriessShortIndex)
    (h : g.val (monsterNortonPureShort r) = monsterNortonPureShort r) (c : ZMod 2) :
    g.val (conwayShortAxis r c) = conwayShortAxis r c := by
  have hp := generated_group_preserves_griessProduct sExtra_preserves_griessProd g
    (monsterNortonPureShort r) (monsterNortonPureShort r)
  rw [monsterNortonShortAxis_polynomial, map_sub, map_smul, map_smul, hp, h]

/-- Any global generated element fixing one genuine pure-short vector lies in actual H. -/
theorem monsterNortonGenerated_fix_short_mem_local (g : G) (r : GriessShortIndex)
    (h : g.val (monsterNortonPureShort r) = monsterNortonPureShort r) :
    g ∈ localIntoGenerated.range :=
  generated_fix_shortAxis_pair_local g r
    (monsterNortonGenerated_fix_short_axis g r h 0)
    (monsterNortonGenerated_fix_short_axis g r h 1)

/-- The 24 genuine short tests and one nonzero tensor test force global identity directly. -/
theorem monsterNortonGenerated_global_short_identity (g : G)
    (hb : ∀ j : Fin 24,
      g.val (monsterNortonPureShort (monsterNortonShortBasisIndex j)) =
        monsterNortonPureShort (monsterNortonShortBasisIndex j))
    (x : GriessSpace) (hx : g.val x = x) (ht : (griessConwayEncode x).2.2 ≠ 0) : g = 1 :=
  monsterNortonGenerated_identity_of_short_basis_and_tensor g
    (monsterNortonGenerated_fix_short_mem_local g (monsterNortonShortBasisIndex 0) (hb 0))
    hb x hx ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
