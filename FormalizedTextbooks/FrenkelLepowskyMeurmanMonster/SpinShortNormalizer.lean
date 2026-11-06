/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinShortGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! Recognition of spin operators fixing the actual short labels up to central sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem finite_forward_normalizer {E : Type*} [Group E]
    (K : Subgroup E) [Finite K] (e : E)
    (he : ∀ h ∈ K, e * h * e⁻¹ ∈ K) : e ∈ Subgroup.normalizer (K : Set E) := by
  let f : K → K := fun h => ⟨e * h.val * e⁻¹, he h.val h.property⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hv := congrArg Subtype.val hab
    change e * a.val * e⁻¹ = e * b.val * e⁻¹ at hv
    exact mul_left_cancel (mul_right_cancel hv)
  have hs := Finite.surjective_of_injective hi
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · exact he h
  · intro hh
    obtain ⟨a, ha⟩ := hs ⟨e * h * e⁻¹, hh⟩
    have hv := congrArg Subtype.val ha
    change e * a.val * e⁻¹ = e * h * e⁻¹ at hv
    have heq : a.val = h := mul_left_cancel (mul_right_cancel hv)
    exact heq ▸ a.property

private theorem spinShort_conjugate_central (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (c : ZMod 2) :
    e * spinRepresentation (qCentral c) * e⁻¹ = spinRepresentation (qCentral c) := by
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, spinRepresentation_central, map_smul]
  rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- Signed conjugation of the actual short operators forces normalization of the
entire actual extraspecial image. -/
theorem spinShort_normalizer (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      e * spinRepresentation (griessShortQ r) * e⁻¹ =
        spinRepresentation (qCentral c * griessShortQ r)) :
    e ∈ Subgroup.normalizer (spinImage : Set (SpinSpace ≃ₗ[ℝ] SpinSpace)) := by
  let K : Subgroup Q := spinImage.comap
    ((MulAut.conj e).toMonoidHom.comp spinRepresentation)
  have hK : K = ⊤ := by
    apply spinShort_subgroup_eq_top
    · intro r
      obtain ⟨c, hc⟩ := hshort r
      change e * spinRepresentation (griessShortQ r) * e⁻¹ ∈ spinImage
      rw [hc]
      exact ⟨qCentral c * griessShortQ r, rfl⟩
    · change e * spinRepresentation (qCentral 1) * e⁻¹ ∈ spinImage
      rw [spinShort_conjugate_central]
      exact ⟨qCentral 1, rfl⟩
  let : Finite spinImage := Finite.of_surjective spinImageEquiv spinImageEquiv.surjective
  apply finite_forward_normalizer
  rintro _ ⟨q, rfl⟩
  have hq : q ∈ K := by rw [hK]; exact Subgroup.mem_top q
  exact hq

/-- A normalizer fixing each actual short operator up to central sign acts trivially
on the genuine binary quotient. -/
theorem spinShort_binary_trivial (s : SpinHolomorph)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      s.val * spinRepresentation (griessShortQ r) * s.val⁻¹ =
        spinRepresentation (qCentral c * griessShortQ r)) :
    spinBinaryAction s = 1 := by
  let K : Subgroup Q :=
    { carrier := {q | qQuotHom (spinConjugation s q) = qQuotHom q}
      one_mem' := by change qQuotHom (spinConjugation s 1) = qQuotHom 1; rw [map_one]
      mul_mem' := by
        intro a b ha hb
        change qQuotHom (spinConjugation s (a * b)) = qQuotHom (a * b)
        rw [map_mul, map_mul, map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change qQuotHom (spinConjugation s a⁻¹) = qQuotHom a⁻¹
        rw [map_inv, map_inv, map_inv, ha] }
  have hK : K = ⊤ := by
    apply spinShort_subgroup_eq_top
    · intro r
      obtain ⟨c, hc⟩ := hshort r
      have hq : spinConjugation s (griessShortQ r) = qCentral c * griessShortQ r := by
        apply spinRepresentation_injective
        rw [spinConjugation_representation, hc]
      change qQuotHom (spinConjugation s (griessShortQ r)) = _
      rw [hq]
      exact qCentral_mul_base c (griessShortQ r)
    · change qQuotHom (spinConjugation s (qCentral 1)) = _
      rw [spinConjugation_central]
      rfl
  apply LinearEquiv.ext
  intro v
  obtain ⟨q, hq⟩ := qQuotHom_surjective (ofAdd v)
  have hv : toAdd (qQuotHom q) = v := congrArg toAdd hq
  rw [← hv]
  change qBinaryAction (spinConjugation s) (toAdd (qQuotHom q)) = toAdd (qQuotHom q)
  rw [qBinaryAction_apply]
  have hk : q ∈ K := by rw [hK]; exact Subgroup.mem_top q
  exact congrArg toAdd hk

/-- An orthogonal spin operator fixing all actual short labels up to sign is an
actual represented Q element. -/
theorem spinShort_recognize (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (he : e ∈ spinOrthogonalSubgroup)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      e * spinRepresentation (griessShortQ r) * e⁻¹ =
        spinRepresentation (qCentral c * griessShortQ r)) :
    ∃ q : Q, spinRepresentation q = e := by
  let s : SpinHolomorph := ⟨e, spinShort_normalizer e hshort, he⟩
  obtain ⟨q, hq⟩ := spinBinaryAction_kernel_image s (spinShort_binary_trivial s hshort)
  exact ⟨q, congrArg Subtype.val hq⟩

/-- The equivalent operator form of short-label recognition, using the actual
binary central sign function. -/
theorem spinShort_recognize_operator (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (he : e ∈ spinOrthogonalSubgroup)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      ∀ x : SpinSpace, e (spinOperator (griessShortQ r) x) =
        qSign c • spinOperator (griessShortQ r) (e x)) :
    ∃ q : Q, spinRepresentation q = e := by
  apply spinShort_recognize e he
  intro r
  obtain ⟨c, hc⟩ := hshort r
  refine ⟨c, LinearEquiv.ext fun x => ?_⟩
  rw [map_mul]
  simp only [LinearEquiv.mul_apply, spinRepresentation_central]
  change e (spinOperator (griessShortQ r) (e.symm x)) =
    qSign c • spinOperator (griessShortQ r) x
  rw [hc, LinearEquiv.apply_symm_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
