/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- All actual short-type extraspecial involutions have Griess trace 4372. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryShortCharacter
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivity

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every genuine short-coordinate lift is noncentral in the actual extraspecial group. -/
theorem monsterGeometryShortQ_noncentral (r : GriessShortIndex) :
    griessShortQ r ∉ centerQ := by
  rw [q_mem_center_iff_base_eq_one]
  exact griessShortQ_base_ne_one r

/-- The literal physical minus-pair lift has full Griess trace 4372. -/
theorem monsterGeometryShortBase_trace :
    monsterGeometryTrace (qIntoGenerated monsterGeometryShortBaseQ) = 4372 := by
  rw [monsterGeometryQ_trace, monsterGeometryShortBase_short_trace,
    monsterGeometryQ_tensor_trace_noncentral]
  · norm_num
  · exact monsterGeometryShortQ_noncentral monsterGeometryShortBaseIndex

/-- Actual local conjugation transports the chosen short class to every original short label. -/
theorem monsterGeometryShort_reached (r : GriessShortIndex) :
    ∃ f : localFiberSubgroup,
      (spinConjugation f.val.1 monsterGeometryShortBaseQ).base = (griessShortQ r).base := by
  obtain ⟨e, _, he⟩ := leechShort_concrete_label_transitive monsterGeometryShortBaseIndex r
  obtain ⟨f, hf⟩ := monsterGeometryFrame_fiber_lift (QuotientGroup.mk' signsSubgroup e)
  refine ⟨f, ?_⟩
  apply Multiplicative.toAdd.injective
  change toAdd (qQuotHom (spinConjugation f.val.1 monsterGeometryShortBaseQ)) =
    toAdd (qQuotHom (griessShortQ r))
  rw [← qBinaryAction_apply]
  change spinBinaryAction f.val.1
    (leechHyperbolicCoordinates (griessShortClass monsterGeometryShortBaseIndex)) = _
  rw [f.property]
  have hb : leechBinaryAction f.val.2 = leechBinaryAction e := by
    change co1BinaryAction (projH (localFiberIntoH f)) =
      co1BinaryAction (QuotientGroup.mk' signsSubgroup e)
    rw [hf]
  rw [hb, leechBinaryAction_coordinates, ← griessShortPermutation_class, he]
  rfl

/-- The actual Griess trace of every preferred short lift is 4372. -/
theorem monsterGeometryShort_trace (r : GriessShortIndex) :
    monsterGeometryTrace (qIntoGenerated (griessShortQ r)) = 4372 := by
  obtain ⟨f, hf⟩ := monsterGeometryShort_reached r
  have hn : spinConjugation f.val.1 monsterGeometryShortBaseQ ∉ centerQ := by
    rw [q_mem_center_iff_base_eq_one, hf]
    exact griessShortQ_base_ne_one r
  rw [← monsterGeometryQ_trace_eq_of_base_eq _ _ hf hn (monsterGeometryShortQ_noncentral r)]
  have hg := congrArg localIntoGenerated (inclQ_spinConjugation f monsterGeometryShortBaseQ)
  change qIntoGenerated (spinConjugation f.val.1 monsterGeometryShortBaseQ) = _ at hg
  rw [map_mul, map_mul, map_inv] at hg
  rw [hg, monsterGeometryTrace_conjugation]
  exact monsterGeometryShortBase_trace

/-- Both actual central phases over a short binary class have the same concrete trace 4372. -/
theorem monsterGeometryQ_short_trace4372 (q : Q) (r : GriessShortIndex)
    (hq : q.base = (griessShortQ r).base) :
    monsterGeometryTrace (qIntoGenerated q) = 4372 := by
  have hn : q ∉ centerQ := by
    rw [q_mem_center_iff_base_eq_one, hq]
    exact griessShortQ_base_ne_one r
  rw [monsterGeometryQ_trace_eq_of_base_eq q (griessShortQ r) hq hn
    (monsterGeometryShortQ_noncentral r), monsterGeometryShort_trace]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
