/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact source coefficients and finite concatenation of the reached 240-unit packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthInputIndices

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full integer source coefficient in the sixteen pair and 224 supported-octad slots. -/
def monsterNortonLine01PairEighthCoefficient (k : Fin 240) : ℤ :=
  if hk : k.val < 16 then -1 else
    monsterNortonLine01PairSeventhOctadSupportCoefficient
      (monsterNortonLine01PairEighthInputOctadSlot k hk)
      (monsterNortonLine01PairEighthInputSignSlot k)

/-- All sixteen original pair coefficients are exactly minus one. -/
theorem monsterNortonLine01PairEighthCoefficient_pair (k : Fin 16) :
    monsterNortonLine01PairEighthCoefficient (Fin.castAdd 224 k) = -1 := by
  unfold monsterNortonLine01PairEighthCoefficient
  exact dite_eq_left k.isLt

/-- Every supported-octad slot retains its actual signed source numerator. -/
theorem monsterNortonLine01PairEighthCoefficient_octad (a : Fin 14) (j : Fin 16) :
    monsterNortonLine01PairEighthCoefficient ⟨16 + 16 * a.val + j.val, by omega⟩ =
      monsterNortonLine01PairSeventhOctadSupportCoefficient a j := by
  have hk : ¬16 + 16 * a.val + j.val < 16 := by omega
  unfold monsterNortonLine01PairEighthCoefficient
  rw [dite_eq_right hk]
  have ha : monsterNortonLine01PairEighthInputOctadSlot
      ⟨16 + 16 * a.val + j.val, by omega⟩ hk = a := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputOctadSlot]
    omega
  have hj : monsterNortonLine01PairEighthInputSignSlot
      ⟨16 + 16 * a.val + j.val, by omega⟩ = j := by
    apply Fin.ext
    dsimp [monsterNortonLine01PairEighthInputSignSlot]
    omega
  rw [ha, hj]

/-- The whole finite packet is exactly the concatenation of its original pair and octad pieces. -/
theorem monsterNortonLine01PairEighthCoefficient_sum {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (v : Fin 240 → E) :
    (∑ k : Fin 240, ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) • v k) =
      (∑ k : Fin 8, (-1 / 16 : ℝ) •
        (v ⟨k.val, by omega⟩ + v ⟨8 + k.val, by omega⟩)) +
      ∑ a : Fin 14, ∑ j : Fin 16,
        ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
          v ⟨16 + 16 * a.val + j.val, by omega⟩ := by
  rw [Fin.sum_univ_add (a := 16) (b := 224)]
  congr 1
  · simp only [monsterNortonLine01PairEighthCoefficient_pair, Int.cast_neg, Int.cast_one]
    rw [Fin.sum_univ_add (a := 8) (b := 8)]
    simp only [smul_add, Finset.sum_add_distrib]
    rfl
  · rw [← (finProdFinEquiv : Fin 14 × Fin 16 ≃ Fin 224).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    have hk : Fin.natAdd 16 (finProdFinEquiv (a, j)) =
        (⟨16 + 16 * a.val + j.val, by omega⟩ : Fin 240) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      omega
    rw [hk, monsterNortonLine01PairEighthCoefficient_octad]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
