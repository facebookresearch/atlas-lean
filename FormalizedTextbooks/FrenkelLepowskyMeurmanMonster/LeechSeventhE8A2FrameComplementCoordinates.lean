/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2TriangleData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! The intrinsic E8 polar complement of the original anisotropic triangle root plane. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic E8 polar pairing with the first two original integer triangle roots. -/
def leechSeventhE8A2FramePolar (a : Fin 8 → ZMod 2) (j : Fin 2) : ZMod 2 :=
  ∑ i, a i * ∑ k, (generatedAxisE8FrameGram i k : ZMod 2) *
    (leechSeventhE8RootCoefficients
      (leechSeventhE8A2Indices 537 (Fin.castLE (by decide : 2 ≤ 3) j)) k : ZMod 2)

/-- Exact finite Gram rows of the original two triangle roots. -/
theorem leechSeventhE8A2FramePolar_rows : ∀ j : Fin 2, ∀ i : Fin 8,
    (∑ k, (generatedAxisE8FrameGram i k : ZMod 2) *
      (leechSeventhE8RootCoefficients
        (leechSeventhE8A2Indices 537 (Fin.castLE (by decide : 2 ≤ 3) j)) k : ZMod 2)) =
      if j = 0 then (if i = 3 ∨ i = 4 then 1 else 0) else (if i = 3 then 1 else 0) := by
  rw [leechSeventhE8A2_triangle_indices]
  decide +kernel

/-- Orthogonality to both actual triangle root classes means the two stated coordinates vanish. -/
theorem leechSeventhE8A2FramePolar_zero_iff (a : Fin 8 → ZMod 2) :
    (∀ j, leechSeventhE8A2FramePolar a j = 0) ↔ a 3 = 0 ∧ a 4 = 0 := by
  have h0 : leechSeventhE8A2FramePolar a 0 = a 3 + a 4 := by
    simp only [leechSeventhE8A2FramePolar, leechSeventhE8A2FramePolar_rows]
    simp [Fin.sum_univ_succ]
  have h1 : leechSeventhE8A2FramePolar a 1 = a 3 := by
    simp only [leechSeventhE8A2FramePolar, leechSeventhE8A2FramePolar_rows]
    simp
  constructor
  · intro h
    have ha3 : a 3 = 0 := h1.symm.trans (h 1)
    have ha4 : a 4 = 0 := by simpa only [h0, ha3, zero_add] using h 0
    exact ⟨ha3, ha4⟩
  · rintro ⟨ha3, ha4⟩ j
    fin_cases j
    · change leechSeventhE8A2FramePolar a 0 = 0
      rw [h0, ha3, ha4, zero_add]
    · change leechSeventhE8A2FramePolar a 1 = 0
      exact h1.trans ha3

/-- Finite nonzero singular labels in the intrinsic E8 triangle complement. -/
def leechSeventhE8A2FrameComplementLabels : Finset (Fin 256) :=
  Finset.univ.filter (fun x => x ≠ 0 ∧ x.val.testBit 3 = false ∧ x.val.testBit 4 = false ∧
    generatedAxisE8FrameSingularMask.testBit x.val = true)

/-- Exactly 27 intrinsic singular labels lie in the original triangle complement. -/
theorem leechSeventhE8A2FrameComplementLabels_card :
    leechSeventhE8A2FrameComplementLabels.card = 27 := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
