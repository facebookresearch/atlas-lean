/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Covariance of the short-short Griess product.

The binary product conditions and their central signs transform under the
actual spin/Leech fiber action. These lemmas concern both the short output
and the central product contributing to the symmetric matrix output. -/

@[expose] public section
open Multiplicative
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

theorem qCentral_mul (c d : ZMod 2) : qCentral c * qCentral d = qCentral (c + d) := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact one_mul _
  · apply Multiplicative.toAdd.injective
    exact qCentral_mul_coeff c (qCentral d)

theorem qCentral_commute (c : ZMod 2) (q : Q) : q * qCentral c = qCentral c * q := by
  apply Subgroup.mem_center_iff.mp
  exact (q_mem_center_iff_base_eq_one _).mpr rfl

theorem qCentral_mul_products (c d : ZMod 2) (g h : Q) :
    (qCentral c * g) * (qCentral d * h) = qCentral (c + d) * (g * h) := by
  calc
    _ = qCentral c * (g * qCentral d) * h := by group
    _ = qCentral c * (qCentral d * g) * h := by rw [qCentral_commute]
    _ = (qCentral c * qCentral d) * (g * h) := by group
    _ = _ := by rw [qCentral_mul]

theorem q_base_equal_iff_aut (a : MulAut Q) (g h : Q) :
    g.base = h.base ↔ (a g).base = (a h).base := by
  constructor
  · intro hgh
    apply Multiplicative.toAdd.injective
    have he := congrArg (fun v => qBinaryAction a (toAdd v)) hgh
    change qBinaryAction a (toAdd (qQuotHom g)) =
      qBinaryAction a (toAdd (qQuotHom h)) at he
    rw [qBinaryAction_apply, qBinaryAction_apply] at he
    exact he
  · intro hgh
    have he := congrArg toAdd hgh
    change toAdd (qQuotHom (a g)) = toAdd (qQuotHom (a h)) at he
    rw [← qBinaryAction_apply, ← qBinaryAction_apply] at he
    exact Multiplicative.toAdd.injective ((qBinaryAction a).injective he)

theorem griessShortQ_product_image (f : localFiberSubgroup) (r s : GriessShortIndex) :
    spinConjugation f.val.1 (griessShortQ r * griessShortQ s) =
      qCentral (localShortPhase f r + localShortPhase f s) *
        (griessShortQ (griessShortPermutation f.val.2 r) *
          griessShortQ (griessShortPermutation f.val.2 s)) := by
  rw [map_mul, griessShortQ_image, griessShortQ_image, qCentral_mul_products]

theorem griessShortQ_product_base_covariant (f : localFiberSubgroup)
    (r s u : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = (griessShortQ u).base ↔
      (griessShortQ (griessShortPermutation f.val.2 r) *
        griessShortQ (griessShortPermutation f.val.2 s)).base =
        (griessShortQ (griessShortPermutation f.val.2 u)).base := by
  rw [q_base_equal_iff_aut (spinConjugation f.val.1),
    griessShortQ_product_image, griessShortQ_image, qCentral_mul_base, qCentral_mul_base]

theorem griessShortQ_product_base_one_covariant (f : localFiberSubgroup)
    (r s : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = 1 ↔
      (griessShortQ (griessShortPermutation f.val.2 r) *
        griessShortQ (griessShortPermutation f.val.2 s)).base = 1 := by
  change (griessShortQ r * griessShortQ s).base = (1 : Q).base ↔ _
  rw [q_base_equal_iff_aut (spinConjugation f.val.1), map_one,
    griessShortQ_product_image, qCentral_mul_base]
  rfl

theorem q_eq_central_short_of_base (g : Q) (u : GriessShortIndex)
    (hu : g.base = (griessShortQ u).base) :
    g = qCentral (toAdd g.coeff) * griessShortQ u := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    exact hu
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero]

theorem griessShortQ_product_phase_covariant (f : localFiberSubgroup)
    (r s u : GriessShortIndex)
    (hu : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * qSign (localShortPhase f u) =
      qSign (localShortPhase f r) * qSign (localShortPhase f s) *
        qSign (toAdd (griessShortQ (griessShortPermutation f.val.2 r) *
          griessShortQ (griessShortPermutation f.val.2 s)).coeff) := by
  have h := griessShortQ_product_image f r s
  conv_lhs at h => rw [q_eq_central_short_of_base _ u hu]
  rw [map_mul, spinConjugation_central, griessShortQ_image] at h
  have hc := congrArg (fun g : Q => toAdd g.coeff) h
  simp only [qCentral_mul_coeff, griessShortQ_coeff, add_zero] at hc
  have hs := congrArg qSign hc
  simpa only [qSign_add, mul_assoc] using hs

theorem griessShortQ_product_phase_one_covariant (f : localFiberSubgroup)
    (r s : GriessShortIndex) (hu : (griessShortQ r * griessShortQ s).base = 1) :
    qSign (toAdd (griessShortQ r * griessShortQ s).coeff) =
      qSign (localShortPhase f r) * qSign (localShortPhase f s) *
        qSign (toAdd (griessShortQ (griessShortPermutation f.val.2 r) *
          griessShortQ (griessShortPermutation f.val.2 s)).coeff) := by
  have hprod : griessShortQ r * griessShortQ s =
      qCentral (toAdd (griessShortQ r * griessShortQ s).coeff) := by
    apply NormalizedCocycleExtension.Extension.ext
    · exact hu
    · rfl
  have h := griessShortQ_product_image f r s
  conv_lhs at h => rw [hprod]
  rw [spinConjugation_central] at h
  have hc := congrArg (fun g : Q => toAdd g.coeff) h
  rw [qCentral_mul_coeff] at hc
  change toAdd (griessShortQ r * griessShortQ s).coeff =
    (localShortPhase f r + localShortPhase f s) +
      toAdd (griessShortQ (griessShortPermutation f.val.2 r) *
        griessShortQ (griessShortPermutation f.val.2 s)).coeff at hc
  have hs := congrArg qSign hc
  simpa only [qSign_add, mul_assoc] using hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
