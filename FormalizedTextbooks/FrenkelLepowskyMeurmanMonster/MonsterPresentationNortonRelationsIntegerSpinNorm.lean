/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact transport of the actual spin norm to its original integer source labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSpinSparsePairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full actual spin squared norm is the exact integer square sum in source coordinates. -/
theorem monsterNortonUIntegerEmbed_spin_norm (v : NortonUIntegerVector) :
    spinPairing (nortonUIntegerEmbed v) (nortonUIntegerEmbed v) =
      ((∑ n : Fin 4096, v n ^ 2 : ℤ) : ℝ) := by
  let e : Fin 4096 ≃ SpinIndex := Equiv.ofBijective golayLabelCoefficients
    golayLabelCoefficients_bijective
  calc
    _ = ∑ n : Fin 4096,
        nortonUIntegerEmbed v (golayLabelCoefficients n) *
          nortonUIntegerEmbed v (golayLabelCoefficients n) :=
      (Equiv.sum_comp e (fun t => nortonUIntegerEmbed v t * nortonUIntegerEmbed v t)).symm
    _ = _ := by
      simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
        Int.cast_sum, pow_two, Int.cast_mul]

/-- The original integer coordinate embedding is injective. -/
theorem monsterNortonUIntegerEmbed_injective : Function.Injective nortonUIntegerEmbed := by
  intro v w h
  funext n
  have hn := congrFun h (golayLabelCoefficients n)
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff] at hn
  exact_mod_cast hn

/-- Finite integer source packets embed as the exact corresponding real spin packets. -/
theorem monsterNortonUIntegerEmbed_packet {I : Type*} [Fintype I]
    (c : I → ℤ) (r : I → Fin 4096) :
    nortonUIntegerEmbed (fun n => ∑ i, c i * (Pi.single (r i) 1 : NortonUIntegerVector) n) =
      ∑ i, (c i : ℝ) • (Pi.single (golayLabelCoefficients (r i)) 1 : SpinSpace) := by
  funext t
  simp only [nortonUIntegerEmbed, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← congrFun (monsterNortonUIntegerDelta_embed (r i)) t]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
