/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortSupport

/-! Bounded integer addresses enumerate every genuine sparse source without catalogue shortcuts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Consecutive addresses enumerate actual pairs, octad signs and odd coordinates. -/
def generatedSixthXiShortNumberAddress (n : Fin 27624) : GeneratedSixthXiShortAddress :=
  if h : n.val < 552 then Sum.inl ⟨n.val, h⟩
  else if h : n.val < 15336 then
    Sum.inr (Sum.inl (⟨(n.val - 552) / 64, by omega⟩, ⟨(n.val - 552) % 64, by omega⟩))
  else Sum.inr (Sum.inr
    (⟨(n.val - 15336) / 24, by omega⟩, ⟨(n.val - 15336) % 24, by omega⟩))

/-- Every sparse source has an integer address retaining its exact genuine catalogue label. -/
theorem generatedSixth_xi_short_number_surjective :
    Function.Surjective generatedSixthXiShortNumberAddress := by
  intro x
  rcases x with j | (⟨f, e⟩ | ⟨f, j⟩)
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    simp only [generatedSixthXiShortNumberAddress, j.isLt, dite_true]
  · let n : Fin 27624 := ⟨552 + 64 * f.val + e.val, by omega⟩
    refine ⟨n, ?_⟩
    have hn : ¬ n.val < 552 := by dsimp [n]; omega
    have hm : n.val < 15336 := by dsimp [n]; omega
    simp only [generatedSixthXiShortNumberAddress, hn, dite_false, hm, dite_true]
    congr 1
    congr 1
    apply Prod.ext <;> apply Fin.ext <;> dsimp [n] <;> omega
  · let n : Fin 27624 := ⟨15336 + 24 * f.val + j.val, by omega⟩
    refine ⟨n, ?_⟩
    have hn : ¬ n.val < 552 := by dsimp [n]; omega
    have hm : ¬ n.val < 15336 := by dsimp [n]; omega
    simp only [generatedSixthXiShortNumberAddress, hn, dite_false, hm]
    congr 1
    congr 1
    apply Prod.ext <;> apply Fin.ext <;> dsimp [n] <;> omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
