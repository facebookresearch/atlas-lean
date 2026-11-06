/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSignComparison

/-! Matching matrix and zero tensor coordinates turns the actual short-character
comparison into equality under the genuine local action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An actual Q element with the required short phases carries one zero-tensor
vector to another with the same matrix coordinate. -/
theorem generatedAxis_Q_compare_coordinates (q : Q) (x y : GriessSpace)
    (hm : (griessConwayEncode x).1 = (griessConwayEncode y).1)
    (htx : (griessConwayEncode x).2.2 = 0)
    (hty : (griessConwayEncode y).2.2 = 0)
    (hs : ∀ r, qSign (toAdd (localAxisQPhase r q)) *
      (griessConwayEncode x).2.1 r = (griessConwayEncode y).2.1 r) :
    rhoLocal (inclQ q) x = y := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q) x) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 (griessConwayEncode x).1 = _
    rw [map_one]
    exact hm
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image (localFiberIncl q) (griessConwayEncode x).2.1 r
      change localShortOperator (localFiberIncl q) _ (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator (localFiberIncl q) _ r = _
      rw [hd, localAxisQPhase_eq_short_phase]
      exact hs r
    · rw [htx, hty, map_zero]

/-- Supported unit 64-idempotents with the same matrix, zero tensors, and
pairing four lie in one genuine Q orbit. -/
theorem generatedOctad_idempotents_Q_related (x y : GriessSpace)
    (hm : (griessConwayEncode x).1 = (griessConwayEncode y).1)
    (htx : (griessConwayEncode x).2.2 = 0) (hty : (griessConwayEncode y).2.2 = 0)
    (hx : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      (griessConwayEncode x).2.1 r ^ 2 = 1)
    (hy : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      (griessConwayEncode y).2.1 r ^ 2 = 1)
    (hzx : ∀ r, ¬ generatedOctadShortSupport generatedOctadBasisOctad r →
      (griessConwayEncode x).2.1 r = 0)
    (hzy : ∀ r, ¬ generatedOctadShortSupport generatedOctadBasisOctad r →
      (griessConwayEncode y).2.1 r = 0)
    (hp : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      conwayShortPairing (griessConwayEncode x).1 r = 4)
    (hix : ∀ r, (conwayRawProduct (griessConwayEncode x) (griessConwayEncode x)).2.1 r =
      64 * (griessConwayEncode x).2.1 r)
    (hiy : ∀ r, (conwayRawProduct (griessConwayEncode y) (griessConwayEncode y)).2.1 r =
      64 * (griessConwayEncode y).2.1 r) :
    ∃ q : Q, rhoLocal (inclQ q) x = y := by
  have hpy : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      conwayShortPairing (griessConwayEncode y).1 r = 4 := by
    rw [← hm]
    exact hp
  obtain ⟨q, hq⟩ := generatedOctad_idempotent_sign_comparison
    (griessConwayEncode x) (griessConwayEncode y) htx hty hx hy hzx hzy hp hpy hix hiy
  refine ⟨q, generatedAxis_Q_compare_coordinates q x y hm htx hty ?_⟩
  intro r
  by_cases hr : generatedOctadShortSupport generatedOctadBasisOctad r
  · exact hq r hr
  · rw [hzx r hr, hzy r hr, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
