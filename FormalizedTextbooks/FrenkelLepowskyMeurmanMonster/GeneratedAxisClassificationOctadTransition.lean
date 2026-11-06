/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFirstTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerBlocks

/-! A second explicit triality transition, distinct from the odd-family one.
Octad Fourier coordinates certify separation from the signed-short orbit;
the actual central involution's fixed space separates it from the odd image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fourier transformation of an actual octad axis produces a short
coordinate of magnitude one rather than zero or eight. -/
theorem generatedAxis_triality_octad_coordinate (o : Fin 759) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c))).2.1
      (Sum.inr (Sum.inl (o, 0))) = -qSign c := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c)).2.2.1 o) 0 = _
  have hrow : (trialityBlocksEquiv (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c)).2.2.1 o =
      (-8 * qSign c : ℝ) • Pi.single 0 1 := by
    funext e
    by_cases he : e = 0 <;> simp [conwayShortAxis, griessConwayDecode,
      conwayShortAxisRaw, Pi.single_apply, he]
  rw [hrow, map_smul]
  simp [trialityOctadAction, trialityHadamardEquiv, trialitySignEquiv,
    trialityNormalizedHadamard, trialityHadamard, trialityEvenMask, trialityBitWeight8,
    Matrix.toLin'OfInv_apply]
  ring

/-- This octad image is outside the actual first local orbit. -/
theorem generatedAxis_triality_octad_not_signed (o : Fin 759) (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c) ∉ generatedSignedShortAxes := by
  rintro ⟨⟨r, e⟩, he⟩
  have hc := congrArg (fun x : GriessSpace =>
    (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, 0)))) he
  rw [conwayShortAxis_encode, generatedAxis_triality_octad_coordinate] at hc
  by_cases hr : r = Sum.inr (Sum.inl (o, 0))
  · subst r
    simp only [conwayShortAxisRaw, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      mul_one] at hc
    fin_cases c <;> fin_cases e <;> norm_num [qSign] at hc
  · simp [conwayShortAxisRaw, Ne.symm hr] at hc
    have h1 := qSign_sq c
    nlinarith

/-- The octad image has zero tensor coordinate, proved from the original
dictionary rather than assigned a conjugacy class. -/
theorem generatedAxis_triality_octad_tensor_zero (o : Fin 759) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c))).2.2 = 0 := by
  funext t i
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, trialityCycle]

/-- The odd image has a nonzero tensor coordinate, equivalently it is not
fixed by the actual distinguished central involution. -/
theorem generatedAxis_triality_odd_tensor_ne_zero (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))).2.2 ≠ 0 := by
  intro ht
  have hd := griessConwayDecode_encode
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))
  have hzero := congrArg (fun x : GriessSpace =>
    (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i))) hd
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply] at hzero
  rw [ht] at hzero
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, Nat.reduceMul,
    Equiv.symm_apply_apply, Pi.zero_apply, sub_self, mul_zero, zero_div] at hzero
  have hY := generatedAxis_triality_odd_Y d i c
  rw [← hzero] at hY
  have hs := qSign_sq c
  nlinarith

/-- The actual local action preserves tensor-zero vectors, by its proven
commutation with the distinguished central involution. -/
theorem generatedAxis_local_preserves_tensor_zero (h : H) (x : GriessSpace)
    (hx : (griessConwayEncode x).2.2 = 0) :
    (griessConwayEncode (rhoLocal h x)).2.2 = 0 := by
  let g : generatedCentralizer := ⟨localIntoGenerated h,
    localIntoGenerated_range_le_centralizer ⟨h, rfl⟩⟩
  exact (mem_generatedCentralPlus_iff_tensor_zero _).mp
    (generatedCentralizer_preserves_plus g x
      ((mem_generatedCentralPlus_iff_tensor_zero x).mpr hx))

/-- The octad transition is an actual point of the same global axis orbit. -/
theorem generatedAxis_triality_octad_mem_orbit (r : GriessShortIndex) (c : ZMod 2)
    (o : Fin 759) (e : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) e) ∈
      generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inl (o, 0))) c e
  refine ⟨extraIntoGenerated * localIntoGenerated h, ?_⟩
  change sExtra (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]

/-- The two concrete triality images lie in different actual local orbits. -/
theorem generatedAxis_triality_octad_not_local_odd (o : Fin 759) (c : ZMod 2)
    (d : Fin 2048) (i : Fin 24) (e : ZMod 2) :
    ¬ ∃ h : H, rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) c)) =
      sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) e) := by
  rintro ⟨h, hh⟩
  have hz := generatedAxis_local_preserves_tensor_zero h _
    (generatedAxis_triality_octad_tensor_zero o c)
  rw [hh] at hz
  exact generatedAxis_triality_odd_tensor_ne_zero d i e hz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
