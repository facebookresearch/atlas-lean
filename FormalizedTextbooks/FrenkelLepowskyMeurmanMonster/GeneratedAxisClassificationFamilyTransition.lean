/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPairTransition

/-! Exhaustive first-orbit return test for the three actual short families.
The Fourier entry is evaluated for every octad sign label. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every octad sign label has the same nonzero Fourier coordinate at zero. -/
theorem generatedAxis_triality_octad_family_coordinate
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inr (Sum.inl (o, 0))) = -qSign c := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o) 0 = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)).2.2.1 o =
      (-8 * qSign c : ℝ) • Pi.single e 1 := by
    funext f
    by_cases hf : f = e <;> simp [conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, Pi.single_apply, hf]
  rw [hrow, map_smul]
  simp [trialityOctadAction, trialityHadamardEquiv, trialitySignEquiv,
    trialityNormalizedHadamard, trialityHadamard, trialityEvenMask, trialityBitWeight8,
    Matrix.toLin'OfInv_apply]
  ring

/-- No actual octad-family axis returns to the first local orbit under triality. -/
theorem generatedAxis_triality_octad_family_not_signed
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) ∉ generatedSignedShortAxes := by
  rintro ⟨⟨r, d⟩, he⟩
  have hc := congrArg (fun x : GriessSpace =>
    (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, 0)))) he
  rw [conwayShortAxis_encode, generatedAxis_triality_octad_family_coordinate] at hc
  by_cases hr : r = Sum.inr (Sum.inl (o, 0))
  · subst r
    simp only [conwayShortAxisRaw, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      mul_one] at hc
    fin_cases c <;> fin_cases d <;> norm_num [qSign] at hc
  · simp [conwayShortAxisRaw, Ne.symm hr] at hc
    have hs := qSign_sq c
    nlinarith

/-- The first-orbit triality return condition is exactly the actual pair family. -/
theorem generatedAxis_triality_first_return_iff (r : GriessShortIndex) (c : ZMod 2) :
    sExtra (conwayShortAxis r c) ∈ generatedSignedShortAxes ↔
      ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact ⟨fun _ => ⟨s, p, rfl⟩, fun _ => generatedAxis_triality_pair_mem_signed p s c⟩
  · simp only [generatedAxis_triality_octad_family_not_signed o e c,
      Sum.inr_ne_inl, exists_false]
  · simp only [generatedAxis_triality_odd_not_signed d i c,
      Sum.inr_ne_inl, exists_false]

/-- The actual subset of the first orbit which returns to it under triality. -/
noncomputable def generatedAxisFirstReturnAxes : Set GriessSpace :=
  {x | x ∈ generatedSignedShortAxes ∧ sExtra x ∈ generatedSignedShortAxes}

/-- Exactly 1,104 genuine first-orbit axes return to the first orbit under
triality. This counts actual vectors, before transition-coset normalization. -/
theorem generatedAxis_first_return_card : Nat.card generatedAxisFirstReturnAxes = 1104 := by
  let f : (Fin 2 × Fin 276) × ZMod 2 → generatedAxisFirstReturnAxes := fun a =>
    ⟨conwayShortAxis (Sum.inl a.1) a.2,
      ⟨⟨(Sum.inl a.1, a.2), rfl⟩,
        generatedAxis_triality_pair_mem_signed a.1.2 a.1.1 a.2⟩⟩
  have hi : Function.Injective f := by
    intro a b h
    have hv : conwayShortAxis (Sum.inl a.1) a.2 =
        conwayShortAxis (Sum.inl b.1) b.2 := congrArg Subtype.val h
    have hs := @generatedAxis_signed_injective (Sum.inl a.1, a.2)
      (Sum.inl b.1, b.2) hv
    change (Sum.inl a.1, a.2) = (Sum.inl b.1, b.2) at hs
    have hp : a.1 = b.1 ∧ a.2 = b.2 := by
      simpa only [Prod.mk.injEq, Sum.inl.injEq] using hs
    exact Prod.ext hp.1 hp.2
  have hu : Function.Surjective f := by
    rintro ⟨x, ⟨⟨⟨r, c⟩, hx⟩, ht⟩⟩
    change conwayShortAxis r c = x at hx
    rw [← hx] at ht
    obtain ⟨s, p, hr⟩ := (generatedAxis_triality_first_return_iff r c).mp ht
    refine ⟨((s, p), c), Subtype.ext ?_⟩
    change conwayShortAxis (Sum.inl (s, p)) c = x
    rw [← hr, hx]
  have he := Nat.card_congr (Equiv.ofBijective f ⟨hi, hu⟩)
  rw [← he]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
