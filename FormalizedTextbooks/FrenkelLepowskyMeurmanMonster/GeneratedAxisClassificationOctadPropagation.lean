/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPropagationData

/-! Additive signs on the 120 checked roots extend to a binary linear functional.
The proof uses the checked acyclic root-addition graph, rather than an assumed
recognition theorem for a root system. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The eight values of a sign assignment on the chosen basis roots. -/
def generatedOctadPropagationValues (f : Fin 120 → ZMod 2) (j : Fin 8) : ZMod 2 :=
  f (generatedOctadPropagationOrder ⟨j.val, by omega⟩)

/-- A root sign assignment respecting every binary root addition is the
restriction of the linear functional with its eight chosen basis values. -/
theorem generatedOctadPropagation_linear (f : Fin 120 → ZMod 2)
    (hadd : ∀ r s t, generatedOctadPatternBits r + generatedOctadPatternBits s =
      generatedOctadPatternBits t → f r + f s = f t) :
    ∀ p, f p = dotProduct (generatedOctadPropagationValues f)
      (generatedOctadPatternBits p) := by
  have hnodes : ∀ n : ℕ, ∀ hn : n < 120,
      f (generatedOctadPropagationOrder ⟨n, hn⟩) =
        dotProduct (generatedOctadPropagationValues f)
          (generatedOctadPatternBits (generatedOctadPropagationOrder ⟨n, hn⟩)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hb : n < 8
      · rw [generatedOctadPropagation_basis ⟨n, hb⟩]
        rw [dotProduct_single_one]
        rfl
      · let j : Fin 112 := ⟨n - 8, by omega⟩
        have hj : 8 + j.val = n := by dsimp [j]; omega
        obtain ⟨hl, hr, he⟩ := generatedOctadPropagation_step j
        rw [hj] at hl hr
        have he' : generatedOctadPatternBits
            (generatedOctadPropagationOrder ⟨n, hn⟩) =
            generatedOctadPatternBits
              (generatedOctadPropagationOrder (generatedOctadPropagationLeft j)) +
            generatedOctadPatternBits
              (generatedOctadPropagationOrder (generatedOctadPropagationRight j)) := by
          have hi : (⟨8 + j.val, by omega⟩ : Fin 120) = ⟨n, hn⟩ := Fin.ext hj
          rwa [hi] at he
        rw [← hadd _ _ _ he'.symm, ih _ hl, ih _ hr, he', dotProduct_add]
  intro p
  obtain ⟨n, rfl⟩ := generatedOctadPropagationOrder_bijective.2 p
  exact hnodes n.val n.isLt

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
