/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationCorrection

/-! Original full-phase spin plans and orthogonality certify all actual tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original full quadratic phase of the compact signed pullback model. -/
def generatedFifthMonomialPermutationModelPhase (k : Fin 6) (t : SpinIndex) : ZMod 2 :=
  monsterMonomialQuadratic (generatedFifthMonomialPermutationSpinModel k).phase t

/-- The original spin label pullback of the compact model. -/
def generatedFifthMonomialPermutationModelLabel (k : Fin 6) (t : SpinIndex) : SpinIndex :=
  (generatedFifthMonomialPermutationSpinModel k).coordinate *ᵥ t

private theorem tensor_model_apply (f : localFiberSubgroup)
    (p : golayAutomorphismSubgroup) (model : RepresentativeSpinModel)
    (hp : f.val.2 = golayPermutationIsometry p)
    (hs : representativeSpinCertificate f.val.1 model.coordinate model.phase)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f T t i = qSign (monsterMonomialQuadratic model.phase t) *
      T (model.coordinate *ᵥ t) (p.val.symm i) := by
  rw [generatedFourth_local_tensor_columns]
  have hs' : ∀ (x : SpinSpace) (u : SpinIndex), f.val.1.val x u =
      qSign (monsterMonomialQuadratic model.phase u) * x (model.coordinate *ᵥ u) := hs
  simp_rw [hs']
  rw [hp]
  change (∑ j : Fin 24, (Pi.single j 1 : Fin 24 → ℝ) (p.val.symm i) *
    (qSign (monsterMonomialQuadratic model.phase t) * T (model.coordinate *ᵥ t) j)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The checked plan binds its compact matrix and original sign to the actual tensor action. -/
theorem generatedFifth_monomial_permutation_tensor_model_apply (k : Fin 6)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k))
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFifthMonomialSpatialFiber k) T t i =
      qSign (generatedFifthMonomialPermutationModelPhase k t) *
        T (generatedFifthMonomialPermutationModelLabel k t)
          ((generatedFifthMonomialSpatialPermutation k).val.symm i) :=
  tensor_model_apply _ _ _ (generatedFifth_monomial_spatial k)
    (generatedFifth_monomial_permutation_spin_plan_sound k hc) T t i

/-- Exact support-address transport and original signs certify the whole corrected tensor. -/
theorem generatedFifth_monomial_permutation_tensor_fixed_of_certificate (k : Fin 6)
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k))
    (r : Fin 64 → Fin 64) (d : Fin 64 → ZMod 2)
    (hc : ∀ j : Fin 64, ∀ b : ZMod 2,
      generatedFifthMonomialPermutationModelLabel k
        (generatedFifthXiTensorAddress j b +
          spinTranslation (generatedFifthMonomialPermutationCorrection k)) =
        generatedFifthXiTensorAddress (r j) (b + d j) ∧
      (generatedFifthMonomialSpatialPermutation k).val.symm
        (generatedFifthOddRootOutputData j).2 = (generatedFifthOddRootOutputData (r j)).2 ∧
      nortonUIntegerSign (spinPhase (generatedFifthMonomialPermutationCorrection k)
        (generatedFifthXiTensorAddress j b) +
        generatedFifthMonomialPermutationModelPhase k
          (generatedFifthXiTensorAddress j b +
            spinTranslation (generatedFifthMonomialPermutationCorrection k))) *
        generatedFifthXiTensorWeight (r j) (b + d j) = generatedFifthXiTensorWeight j b) :
    localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 := by
  classical
  let T := (griessConwayEncode generatedFifthAxis).2.2
  let U := localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber k) T
  have hn := localTensorRepresentation_pairing
    (generatedFifthMonomialPermutationCorrectedFiber k) T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs : ∀ p : SpinIndex × Fin 24, T p.1 p.2 ≠ 0 → U p.1 p.2 = T p.1 p.2 := by
    intro p hne
    obtain ⟨j, hj⟩ := (generatedFifth_tensor_nonzero_iff p.1 p.2).mp hne
    obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition p.1
    have hd := congrArg Prod.fst hj
    have hi := congrArg Prod.snd hj
    have he : p.1 = generatedFifthXiTensorAddress j b := by
      simpa only [generatedFifthXiTensorAddress, hd] using hb
    change localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 p.1 p.2 =
        (griessConwayEncode generatedFifthAxis).2.2 p.1 p.2
    rcases hc j b with ⟨ht, hc', hw⟩
    rw [he, ← hi, generatedFifthMonomialPermutationCorrectedFiber, map_mul,
      LinearEquiv.mul_apply, generatedFourth_lift_q_tensor,
      generatedFifth_monomial_permutation_tensor_model_apply k hp, ht, hc',
      generatedFifth_xi_address_value, generatedFifth_xi_address_value]
    simp only [ite_true]
    rw [← mul_assoc, ← qSign_add]
    simp only [← nortonUIntegerSign_real]
    have hw' := congrArg (fun z : ℤ => (z : ℝ)) hw
    push_cast at hw'
    rw [← mul_div_assoc, hw']
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
