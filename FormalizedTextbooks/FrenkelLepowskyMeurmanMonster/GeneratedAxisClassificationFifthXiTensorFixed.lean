/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction

/-! Soundness of a bounded support certificate for the genuine corrected Xi tensor action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Checking all 128 original support addresses certifies every original tensor coordinate. -/
theorem generatedFifth_xi_tensor_fixed_of_certificate
    (hc : ∀ j : Fin 64, ∀ b : ZMod 2,
      generatedFifthXiCorrectedTensorNumerator (generatedFifthXiTensorAddress j b)
        (generatedFifthOddRootOutputData j).2 = 16 * generatedFifthXiTensorWeight j b) :
    localTensorRepresentation generatedFifthXiCorrectedFiber
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 := by
  classical
  let T := (griessConwayEncode generatedFifthAxis).2.2
  let U := localTensorRepresentation generatedFifthXiCorrectedFiber T
  have hn := localTensorRepresentation_pairing generatedFifthXiCorrectedFiber T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs : ∀ p : SpinIndex × Fin 24, T p.1 p.2 ≠ 0 → U p.1 p.2 = T p.1 p.2 := by
    intro p hp
    obtain ⟨j, hj⟩ := (generatedFifth_tensor_nonzero_iff p.1 p.2).mp hp
    obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition p.1
    have hd := congrArg Prod.fst hj
    have hi := congrArg Prod.snd hj
    have he : p.1 = generatedFifthXiTensorAddress j b := by
      simpa only [generatedFifthXiTensorAddress, hd] using hb
    change localTensorRepresentation generatedFifthXiCorrectedFiber
      (griessConwayEncode generatedFifthAxis).2.2 p.1 p.2 =
        (griessConwayEncode generatedFifthAxis).2.2 p.1 p.2
    rw [he, ← hi, generatedFifth_xi_corrected_tensor_coordinate, hc,
      generatedFifth_xi_address_value]
    simp only [ite_true, Int.cast_mul, Int.cast_ofNat]
    ring
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
