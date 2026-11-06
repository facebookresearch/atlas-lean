/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinaryRootData

/-! Fixing the original eight quotient root classes forces one uniform physical root sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Fixing a genuine short root class leaves exactly its two genuine lattice orientations. -/
theorem generatedNinth_section_binary_root_signs (g : leechIsomSubgroup)
    (hfix : ∀ j : Fin 8,
      leechModTwoAction g (leechReduction (generatedFifthFrameRoot j)) =
        leechReduction (generatedFifthFrameRoot j)) (j : Fin 8) :
    g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j ∨
      g.val (generatedNinthSectionRealRoot j) = -generatedNinthSectionRealRoot j := by
  have h := leechShort_same_class
    (leechIntegralAction g (generatedFifthFrameRoot j)) (generatedFifthFrameRoot j)
    (by rw [leechIntegralAction_squareSum]; exact generatedFifthFrameRoot_square j)
    (generatedFifthFrameRoot_square j) (hfix j)
  rcases h with h | h
  · left
    have he := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) h
    simpa only [leechIntegralAction_embedding, generatedNinthSectionRealRoot] using he
  · right
    have he := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) h
    simpa only [leechIntegralAction_embedding, Submodule.coe_neg, map_neg,
      generatedNinthSectionRealRoot] using he

private theorem positive_roots (g : leechIsomSubgroup)
    (hsign : ∀ j : Fin 8,
      g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j ∨
        g.val (generatedNinthSectionRealRoot j) = -generatedNinthSectionRealRoot j)
    (hzero : g.val (generatedNinthSectionRealRoot 0) = generatedNinthSectionRealRoot 0) :
    ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j := by
  have hc : ∀ n : ℕ, ∀ hn : n < 8,
      g.val (generatedNinthSectionRealRoot ⟨n, hn⟩) =
        generatedNinthSectionRealRoot ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        exact hzero
      let j : Fin 8 := ⟨n, hn⟩
      have hj : j ≠ 0 := fun he => hz (congrArg Fin.val he)
      have hp := ih (generatedNinthSectionRootParent j).val
        (generatedNinth_section_root_parent_lt j hj) (generatedNinthSectionRootParent j).isLt
      rcases hsign j with h | h
      · exact h
      · have he := g.property.1
          (generatedNinthSectionRealRoot (generatedNinthSectionRootParent j))
          (generatedNinthSectionRealRoot j)
        change g.val (generatedNinthSectionRealRoot (generatedNinthSectionRootParent j)) ⬝ᵥ
          g.val (generatedNinthSectionRealRoot j) =
          generatedNinthSectionRealRoot (generatedNinthSectionRootParent j) ⬝ᵥ
            generatedNinthSectionRealRoot j at he
        rw [hp, h, dotProduct_neg] at he
        have hz : generatedNinthSectionRealRoot (generatedNinthSectionRootParent j) ⬝ᵥ
            generatedNinthSectionRealRoot j = 0 := by linarith
        exact (generatedNinth_section_root_pair_ne_zero j hj hz).elim
  intro j
  exact hc j.val j.isLt

private theorem negative_roots (g : leechIsomSubgroup)
    (hsign : ∀ j : Fin 8,
      g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j ∨
        g.val (generatedNinthSectionRealRoot j) = -generatedNinthSectionRealRoot j)
    (hzero : g.val (generatedNinthSectionRealRoot 0) = -generatedNinthSectionRealRoot 0) :
    ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) = -generatedNinthSectionRealRoot j := by
  have hc : ∀ n : ℕ, ∀ hn : n < 8,
      g.val (generatedNinthSectionRealRoot ⟨n, hn⟩) =
        -generatedNinthSectionRealRoot ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        exact hzero
      let j : Fin 8 := ⟨n, hn⟩
      have hj : j ≠ 0 := fun he => hz (congrArg Fin.val he)
      have hp := ih (generatedNinthSectionRootParent j).val
        (generatedNinth_section_root_parent_lt j hj) (generatedNinthSectionRootParent j).isLt
      rcases hsign j with h | h
      · have he := g.property.1
          (generatedNinthSectionRealRoot (generatedNinthSectionRootParent j))
          (generatedNinthSectionRealRoot j)
        change g.val (generatedNinthSectionRealRoot (generatedNinthSectionRootParent j)) ⬝ᵥ
          g.val (generatedNinthSectionRealRoot j) =
          generatedNinthSectionRealRoot (generatedNinthSectionRootParent j) ⬝ᵥ
            generatedNinthSectionRealRoot j at he
        rw [hp, h, neg_dotProduct] at he
        have hz : generatedNinthSectionRealRoot (generatedNinthSectionRootParent j) ⬝ᵥ
            generatedNinthSectionRealRoot j = 0 := by linarith
        exact (generatedNinth_section_root_pair_ne_zero j hj hz).elim
      · exact h
  intro j
  exact hc j.val j.isLt

/-- The entire original root basis has one common genuine orientation under binary fixation. -/
theorem generatedNinth_section_binary_uniform_root_sign (g : leechIsomSubgroup)
    (hfix : ∀ j : Fin 8,
      leechModTwoAction g (leechReduction (generatedFifthFrameRoot j)) =
        leechReduction (generatedFifthFrameRoot j)) :
    (∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) = generatedNinthSectionRealRoot j) ∨
      (∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) =
        -generatedNinthSectionRealRoot j) := by
  have hs := generatedNinth_section_binary_root_signs g hfix
  rcases hs 0 with h | h
  · exact Or.inl (positive_roots g hs h)
  · exact Or.inr (negative_roots g hs h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
