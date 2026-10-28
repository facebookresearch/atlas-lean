/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Basis vectors in the two triples cycled by the source triality operation.
Source: Seysen, arXiv:2002.10921v3, §8.1 and Table 5.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

noncomputable def trialityABCBasis (s : Fin 3) (p : Fin 276) : GriessSpace :=
  trialityBlocksEquiv.symm (0, (Pi.single s (Pi.single p 1), (0, 0)))

noncomputable def trialityXYZBasis (s : Fin 3) (k : Fin 49152) : GriessSpace :=
  trialityBlocksEquiv.symm (0, (0, (0, Pi.single s (Pi.single k 1))))

@[simp] theorem trialityABCBasis_blocks (s : Fin 3) (p : Fin 276) :
    trialityBlocksEquiv (trialityABCBasis s p) = (0, (Pi.single s (Pi.single p 1), (0, 0))) := by
  exact trialityBlocksEquiv.apply_symm_apply _

@[simp] theorem trialityXYZBasis_blocks (s : Fin 3) (k : Fin 49152) :
    trialityBlocksEquiv (trialityXYZBasis s k) = (0, (0, (0, Pi.single s (Pi.single k 1)))) := by
  exact trialityBlocksEquiv.apply_symm_apply _

theorem trialityCycleAction_basis (n : ℕ) (s : Fin 3) (k : Fin n) :
    trialityCycleAction n (Pi.single s (Pi.single k 1)) =
      Pi.single (trialityCycle s) (Pi.single k 1) := by
  ext i j
  change (Pi.single s (Pi.single k 1) : Fin 3 → Fin n → ℝ) (trialityCycle.symm i) j = _
  have he : trialityCycle.symm i = s ↔ i = trialityCycle s := by
    exact trialityCycle.symm_apply_eq
  simp only [Pi.single_apply, he]

set_option backward.isDefEq.respectTransparency false in
theorem sExtra_ABC_basis (s : Fin 3) (p : Fin 276) :
    sExtra (trialityABCBasis s p) = trialityABCBasis (trialityCycle s) p := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, trialityABCBasis, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply,
    map_zero, trialityCycleAction_basis]

set_option backward.isDefEq.respectTransparency false in
theorem sExtra_XYZ_basis (s : Fin 3) (k : Fin 49152) :
    sExtra (trialityXYZBasis s k) = trialityXYZBasis (trialityCycle s) k := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, trialityXYZBasis, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply,
    map_zero, trialityCycleAction_basis]

theorem griessConwayEncode_ABC_basis (s : Fin 3) (p : Fin 276) :
    griessConwayEncode (trialityABCBasis s p) =
      ((fun i j => if h : i = j then 0 else
          (Pi.single s (Pi.single p 1) : Fin 3 → Fin 276 → ℝ) 0 (griessPairIndex i j h)),
        ((fun r => match r with
          | Sum.inl (u, q) => if u = 0 then
              (Pi.single s (Pi.single p 1) : Fin 3 → Fin 276 → ℝ) 1 q +
              (Pi.single s (Pi.single p 1) : Fin 3 → Fin 276 → ℝ) 2 q
            else (Pi.single s (Pi.single p 1) : Fin 3 → Fin 276 → ℝ) 2 q -
              (Pi.single s (Pi.single p 1) : Fin 3 → Fin 276 → ℝ) 1 q
          | Sum.inr _ => 0), 0)) := by
  simp only [griessConwayEncode, trialityABCBasis_blocks]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · rfl
  · funext r
    rcases r with r | (r | r) <;> rfl
  · funext t i
    simp

theorem griessConwayEncode_XYZ_basis (s : Fin 3) (k : Fin 49152) :
    griessConwayEncode (trialityXYZBasis s k) =
      (0, ((fun r => match r with
        | Sum.inr (Sum.inr (d, i)) =>
            (Pi.single s (Pi.single k 1) : Fin 3 → Fin 49152 → ℝ) 0 (finProdFinEquiv (d, i))
        | _ => 0),
      (fun t i =>
        let d := spinDictionaryCode t
        (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
            (Pi.single s (Pi.single k 1) : Fin 3 → Fin 49152 → ℝ) 2 (finProdFinEquiv (d, i)) +
          qSign (t 11) * (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
            (Pi.single s (Pi.single k 1) : Fin 3 → Fin 49152 → ℝ) 1 (finProdFinEquiv (d, i))) /
          Real.sqrt 2))) := by
  simp only [griessConwayEncode, trialityXYZBasis_blocks]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · funext i j
    split_ifs <;> rfl
  · funext r
    rcases r with ⟨u, q⟩ | (r | r)
    · simp
    · rfl
    · rfl
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
