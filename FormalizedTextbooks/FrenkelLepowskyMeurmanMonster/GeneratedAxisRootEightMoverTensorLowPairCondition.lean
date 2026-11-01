/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedLowPairGeneric

/-! Complete original corrected mover low-pair word checks, including every signed slot. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every whole source word, spare-bit guard and signed equation of an actual mover low pair. -/
def generatedRootEightMoverTensorLowPairCondition (s : Fin 3) (k l : Fin 4)
    (j : Fin 24) (a : Fin 256) : Prop :=
  let w := generatedRootEightMoverPackedLowSources
    (generatedRootEightMoverTensorStageWords ⟨s.val, by omega⟩ j
      ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) k l
  let t := generatedRootEightMoverTensorStageWords ⟨s.val + 1, by omega⟩ j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  (∀ z : Fin 7, w z < 65536 ^ 16 ∧ w z &&& generatedRootEightPackedWideUpperMask = 0) ∧
    t < 65536 ^ 16 ∧ t &&& generatedRootEightPackedWideUpperMask = 0 ∧
      (∑ z : Fin 7, generatedRootEightMoverPackedLowCoefficients z *
        generatedRootEightPackedWideBiasedWord (w z)) =
          2 * generatedRootEightPackedWideBiasedWord t

/-- The complete finite guards imply all original4096 low-pair coordinates. -/
theorem generatedRootEight_mover_tensor_low_pair_of_condition
    (s : Fin 3) (k l : Fin 4) (hkl : k ≠ l) (j : Fin 24)
    (h : ∀ a, generatedRootEightMoverTensorLowPairCondition s k l j a) :
    ∀ n : Fin 4096,
      generatedNinthLowerSpinTensorFourierInteger ⟨k.val, by omega⟩
        (generatedNinthLowerSpinTensorFourierInteger ⟨l.val, by omega⟩
          (generatedRootEightMoverTensorSpinInteger ⟨s.val, by omega⟩ j)) n =
            2 * generatedRootEightMoverTensorSpinInteger ⟨s.val + 1, by omega⟩ j n := by
  apply generatedRootEight_mover_packed_low_pair_of_coordinates
    (generatedRootEightMoverTensorStageWords ⟨s.val, by omega⟩ j)
    (generatedRootEightMoverTensorStageWords ⟨s.val + 1, by omega⟩ j) k l hkl
  intro a i
  have hc : (∑ z : Fin 7, |generatedRootEightMoverPackedLowCoefficients z|) + |(2 : ℤ)| < 256 := by
    norm_num [generatedRootEightMoverPackedLowCoefficients, Fin.sum_univ_succ]
  have ha := h a
  unfold generatedRootEightMoverTensorLowPairCondition at ha
  exact generatedRootEight_packed_wide_biased_bounded _ _ _ 2 hc
    (fun z => (ha.1 z).1) ha.2.1 (fun z => (ha.1 z).2) ha.2.2.1 ha.2.2.2 i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
