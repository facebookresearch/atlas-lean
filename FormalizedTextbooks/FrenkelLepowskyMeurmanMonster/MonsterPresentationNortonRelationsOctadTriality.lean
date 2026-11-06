/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Triality on one actual octad block, expressed in the original Conway coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalSubgroups

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A short-coordinate vector supported on one genuine octad. -/
def monsterNortonOctadShortCoordinates (d : Fin 759) (v : Fin 64 → ℝ) :
    GriessShortIndex → ℝ
  | Sum.inr (Sum.inl (a, e)) => if a = d then v e else 0
  | _ => 0

/-- Its actual Griess vector under the proved Conway coordinate dictionary. -/
noncomputable def monsterNortonOctadShortVector (d : Fin 759) (v : Fin 64 → ℝ) :
    GriessSpace := griessConwayDecode (0, (monsterNortonOctadShortCoordinates d v, 0))

/-- The vector occupies exactly the indicated original 64-dimensional dictionary block. -/
theorem monsterNortonOctadShortVector_blocks (d : Fin 759) (v : Fin 64 → ℝ) :
    trialityBlocksEquiv (monsterNortonOctadShortVector d v) =
      (0, (0, (Pi.single d v, 0))) := by
  rw [monsterNortonOctadShortVector, griessConwayDecode, LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · funext s p
    fin_cases s <;> simp [monsterNortonOctadShortCoordinates]
  · funext a e
    by_cases h : a = d <;> simp [monsterNortonOctadShortCoordinates, h]
  · funext s k
    fin_cases s <;> simp [monsterNortonOctadShortCoordinates]

/-- A unit vector in one original octad is exactly its actual pure-short Griess vector. -/
theorem monsterNortonOctadShortVector_single (d : Fin 759) (e : Fin 64) (c : ℝ) :
    monsterNortonOctadShortVector d (Pi.single e c) =
      griessConwayDecode (0, (Pi.single (Sum.inr (Sum.inl (d,e))) c, 0)) := by
  have h : monsterNortonOctadShortCoordinates d (Pi.single e c) =
      Pi.single (Sum.inr (Sum.inl (d,e))) c := by
    funext r
    rcases r with ⟨a,p⟩ | (⟨a,b⟩ | ⟨a,b⟩)
    · simp [monsterNortonOctadShortCoordinates]
    · by_cases ha : a = d <;> by_cases hb : b = e <;>
        simp [monsterNortonOctadShortCoordinates, ha, hb]
    · simp [monsterNortonOctadShortCoordinates]
  rw [monsterNortonOctadShortVector, h]

/-- Actual extra acts by the proved 64-dimensional Fourier/sign triality on this octad. -/
theorem monsterNortonOctadShortVector_extra (d : Fin 759) (v : Fin 64 → ℝ) :
    sExtra (monsterNortonOctadShortVector d v) =
      monsterNortonOctadShortVector d (trialityOctadAction v) := by
  apply trialityBlocksEquiv.injective
  change trialityBlocksEquiv (griessTriality (monsterNortonOctadShortVector d v)) = _
  rw [griessTriality, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, monsterNortonOctadShortVector_blocks,
    monsterNortonOctadShortVector_blocks]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · funext a e
    change trialityOctadAction ((Pi.single d v : Fin 759 → Fin 64 → ℝ) a) e =
      (Pi.single d (trialityOctadAction v) : Fin 759 → Fin 64 → ℝ) a e
    by_cases h : a = d
    · subst a
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_apply, h, ite_false, map_zero, Pi.zero_apply]
  · rfl

/-- The actual generated extra has exactly this one-octad coordinate action. -/
theorem monsterNortonOctadShortVector_generated_extra (d : Fin 759) (v : Fin 64 → ℝ) :
    extraIntoGenerated.val (monsterNortonOctadShortVector d v) =
      monsterNortonOctadShortVector d (trialityOctadAction v) :=
  monsterNortonOctadShortVector_extra d v

/-- The exact source Fourier/sign coefficient, with its original denominator eight. -/
noncomputable def monsterNortonOctadTrialityCoefficient (r s : Fin 64) : ℝ :=
  (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    (trialityHadamard r s : ℝ) / 8

/-- A single original octad coordinate has the exact source 64-term Fourier image. -/
theorem monsterNortonOctadTriality_single (e : Fin 64) (c : ℝ) (k : Fin 64) :
    trialityOctadAction (Pi.single e c) k = monsterNortonOctadTrialityCoefficient k e * c := by
  change (if trialityBitWeight8 (trialityEvenMask k) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    (trialityNormalizedHadamard *ᵥ (Pi.single e c)) k = _
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, trialityNormalizedHadamard,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, monsterNortonOctadTrialityCoefficient]
  have hcast : (Int.castRingHom ℝ) (trialityHadamard k e) =
      (trialityHadamard k e : ℝ) := rfl
  rw [hcast]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
