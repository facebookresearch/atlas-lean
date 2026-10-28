/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup
public import Mathlib.Data.Fintype.Card

/-! Complete signed-permutation transport follows from every nonzero source and exact support cardinality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine signed short permutation transports the whole vector when all nonzero sources
have their actual target coefficients and the two complete supports have equal cardinality. -/
theorem generatedRootEight_short_transport_of_nonzero_sources (f : localFiberSubgroup)
    (X Y : GriessShortIndex → ℝ)
    (hcard : Nat.card {r : GriessShortIndex // X r ≠ 0} =
      Nat.card {r : GriessShortIndex // Y r ≠ 0})
    (h : ∀ r, X r ≠ 0 → localShortRepresentation f X
      (griessShortPermutation f.val.2 r) = Y (griessShortPermutation f.val.2 r)) :
    localShortRepresentation f X = Y := by
  classical
  let S := {r : GriessShortIndex // X r ≠ 0}
  let T := {r : GriessShortIndex // Y r ≠ 0}
  have hforward (r : S) : Y (griessShortPermutation f.val.2 r.val) ≠ 0 := by
    have hs := localShortOperator_image f X r.val
    have hh := h r.val r.property
    change localShortOperator f X (griessShortPermutation f.val.2 r.val) = _ at hh
    rw [hh] at hs
    have hsign : qSign (localShortPhase f r.val) ≠ 0 := by
      intro hz
      have hsq := qSign_sq (localShortPhase f r.val)
      rw [hz, zero_mul] at hsq
      norm_num at hsq
    intro hz
    rw [hz] at hs
    exact (mul_ne_zero hsign r.property) hs.symm
  let F : S → T := fun r => ⟨griessShortPermutation f.val.2 r.val, hforward r⟩
  have hF : Function.Injective F := by
    intro r s hs
    apply Subtype.ext
    apply (griessShortPermutation f.val.2).injective
    exact congrArg Subtype.val hs
  let _ : Fintype S := Fintype.ofFinite S
  let _ : Fintype T := Fintype.ofFinite T
  have hc : Fintype.card S = Fintype.card T := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have honto : Function.Surjective F := by
    by_contra hn
    have hl := Fintype.card_lt_of_injective_not_surjective F hF hn
    omega
  funext s
  obtain ⟨r, rfl⟩ := (griessShortPermutation f.val.2).surjective s
  by_cases hr : X r ≠ 0
  · exact h r hr
  · have hz : Y (griessShortPermutation f.val.2 r) = 0 := by
      by_contra hnonzero
      obtain ⟨u, hu⟩ := honto ⟨griessShortPermutation f.val.2 r, hnonzero⟩
      have he : griessShortPermutation f.val.2 u.val = griessShortPermutation f.val.2 r :=
        congrArg Subtype.val hu
      have hur : u.val = r := (griessShortPermutation f.val.2).injective he
      exact hr (hur ▸ u.property)
    change localShortOperator f X (griessShortPermutation f.val.2 r) = _
    rw [localShortOperator_image, not_ne_iff.mp hr, mul_zero, hz]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
