/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete octad basis vectors and their source Fourier triality action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBilinearReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A vector supported on one octad dictionary block. -/
noncomputable def trialityOctadVector (o : Fin 759) (v : Fin 64 → ℝ) : GriessSpace :=
  trialityBlocksEquiv.symm (0, (0, (Pi.single o v, 0)))

/-- The canonical octad source basis is the one-octad vector embedding. -/
theorem trialityOctadBasis_eq_vector (o : Fin 759) (e : Fin 64) :
    trialityOctadBasis o e = trialityOctadVector o (Pi.single e 1) := rfl

@[simp] theorem trialityOctadVector_blocks (o : Fin 759) (v : Fin 64 → ℝ) :
    trialityBlocksEquiv (trialityOctadVector o v) = (0, (0, (Pi.single o v, 0))) := by
  exact trialityBlocksEquiv.apply_symm_apply _

/-- The one-octad embedding is linear. -/
noncomputable def trialityOctadIncl (o : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] GriessSpace where
  toFun := trialityOctadVector o
  map_add' v w := by
    apply trialityBlocksEquiv.injective
    simp only [trialityOctadVector_blocks, map_add, Prod.mk_add_mk, zero_add]
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext
      (Pi.single_add (f := fun _ : Fin 759 => Fin 64 → ℝ) o v w) rfl))
  map_smul' a v := by
    apply trialityBlocksEquiv.injective
    simp only [trialityOctadVector_blocks, map_smul, Prod.smul_mk, smul_zero,
      RingHom.id_apply]
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext
      (Pi.single_smul (f := fun _ : Fin 759 => Fin 64 → ℝ) o a v) rfl))

/-- The source triality applies its actual 64-dimensional Fourier map to each octad. -/
theorem sExtra_octadVector (o : Fin 759) (v : Fin 64 → ℝ) :
    sExtra (trialityOctadVector o v) = trialityOctadVector o (trialityOctadAction v) := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    trialityOctadVector_blocks, LinearEquiv.apply_symm_apply, trialityBlockAction,
    LinearEquiv.prodCongr_apply, map_zero]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  ext p e
  simp only [LinearEquiv.piCongrRight_apply, Pi.single_apply]
  by_cases h : p = o
  · subst p
    simp
  · simp [h]

/-- Encode a single octad block directly into the actual Conway short coordinates. -/
theorem griessConwayEncode_octadVector (o : Fin 759) (v : Fin 64 → ℝ) :
    griessConwayEncode (trialityOctadVector o v) =
      (0, ((fun r => match r with
        | Sum.inr (Sum.inl (p, e)) => if p = o then v e else 0
        | _ => 0), 0)) := by
  simp only [griessConwayEncode, trialityOctadVector_blocks]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · ext i j
    split_ifs <;> rfl
  · funext r
    rcases r with ⟨s,p⟩ | (⟨p,e⟩ | ⟨d,i⟩)
    · simp
    · simp [Pi.single_apply, ite_apply]
    · rfl
  · funext t i
    simp

/-- Octad basis vectors are exactly the raw short basis vectors of Conway's product. -/
theorem griessConwayEncode_octadBasis (o : Fin 759) (e : Fin 64) :
    griessConwayEncode (trialityOctadBasis o e) =
      conwayShortBasis (Sum.inr (Sum.inl (o,e))) := by
  rw [trialityOctadBasis_eq_vector, griessConwayEncode_octadVector]
  dsimp only [conwayShortBasis]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext r
  rcases r with ⟨s,p⟩ | (⟨p,f⟩ | ⟨d,i⟩)
  · simp
  · by_cases hp : p = o <;> by_cases hf : f = e <;> simp [hp, hf]
  · simp

/-- Every octad block is its finite linear combination of signed-octad basis vectors. -/
theorem trialityOctadVector_sum (o : Fin 759) (v : Fin 64 → ℝ) :
    trialityOctadVector o v = ∑ e, v e • trialityOctadBasis o e := by
  have hv : v = ∑ e, v e • (Pi.single e 1 : Fin 64 → ℝ) := by
    ext f
    simp [Finset.sum_apply, Pi.single_apply]
  change trialityOctadIncl o v = _
  conv_lhs => rw [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact (trialityOctadIncl o).map_smul (v e) (Pi.single e 1)

/-- Actual triality on a signed-octad basis vector, with its DH/8 coefficients. -/
theorem sExtra_octadBasis (o : Fin 759) (e : Fin 64) :
    sExtra (trialityOctadBasis o e) =
      ∑ f, trialityRealMatrix f e • trialityOctadBasis o f := by
  exact sExtra_octad_basis o e

/-- Actual multiplication of two octad basis elements is the sparse raw short product. -/
theorem griessProd_octadBasis (o p : Fin 759) (e f : Fin 64) :
    griessProd (trialityOctadBasis o e) (trialityOctadBasis p f) =
      griessConwayDecode
        (conwayRawProduct (conwayShortBasis (Sum.inr (Sum.inl (o,e))))
          (conwayShortBasis (Sum.inr (Sum.inl (p,f))))) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_octadBasis,
    griessConwayEncode_octadBasis]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
