/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ProjectedStrictRetractionReduction

@[expose] public section

set_option autoImplicit false

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber.Shuffle

/-- The distinguished `(p,q)`-shuffle: all left positions precede all right
positions. -/
def blockShuffle (p q : ℕ) : Shuffle p q where
  perm := Equiv.refl _
  isShuffle := ⟨Fin.strictMono_castAdd q, Fin.strictMono_natAdd p⟩

@[simp]
theorem blockShuffle_perm (p q : ℕ) : (blockShuffle p q).perm = Equiv.refl _ := rfl

@[simp]
theorem shuffleSignZ_blockShuffle (p q : ℕ) :
    shuffleSignZ (blockShuffle p q) = 1 := by
  simp [shuffleSignZ, shuffleSign, blockShuffle]

end AlgebraicTopology.EilenbergZilber.Shuffle

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial
open scoped BigOperators MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

open AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

open Classical in
/-- Vanishing away from the distinguished pair and the value at that pair
determine each projected term. -/
theorem projectedShuffleAlexanderWhitneyTermIdentity_of_vanishing
    (p q : ℕ)
    (hvanish : (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
      ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
        r ≠ distinguishedCut ∨ s ≠ Shuffle.blockShuffle p q →
          projectedShuffleAlexanderWhitneyTerm X Y p q s r = 0))
    (hdistinguished : (projectedShuffleAlexanderWhitneyTerm X Y p q
          (Shuffle.blockShuffle p q) ⟨p, by omega⟩ =
        HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            p q (p + q) rfl ≫
          (HomologicalComplex.tensorHom
            (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
            (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))) :
    (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
      ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
        projectedShuffleAlexanderWhitneyTerm X Y p q s r =
          if r = distinguishedCut ∧ s = Shuffle.blockShuffle p q then
            (HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                p q (p + q) rfl ≫
              (HomologicalComplex.tensorHom
                (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))
          else 0) := by
  classical
  dsimp only at hvanish
  dsimp only
  intro r s
  by_cases hr : r = ⟨p, by omega⟩
  · by_cases hs : s = Shuffle.blockShuffle p q
    · subst r
      subst s
      simpa only [true_and, ↓reduceIte] using hdistinguished
    · rw [ite_eq_right]
      · exact hvanish r s (Or.inr hs)
      · exact fun h => hs h.2
  · rw [ite_eq_right]
    · exact hvanish r s (Or.inl hr)
    · exact fun h => hr h.1

open Classical in
/-- The pointwise term identity implies the cutwise identity used by the
categorical reconstruction. -/
theorem projectedShuffleAlexanderWhitneyBidegreeIdentity_of_terms
    (p q : ℕ)
    (hterms : (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
      ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
        projectedShuffleAlexanderWhitneyTerm X Y p q s r =
          if r = distinguishedCut ∧ s = Shuffle.blockShuffle p q then
            (HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                p q (p + q) rfl ≫
              (HomologicalComplex.tensorHom
                (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))
          else 0)) :
    (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
      ∀ r : Fin (p + q + 1),
        (∑ s : Shuffle p q,
          projectedShuffleAlexanderWhitneyTerm X Y p q s r) =
          if r = distinguishedCut then
            (HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                p q (p + q) rfl ≫
              (HomologicalComplex.tensorHom
                (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
                (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))
          else 0) := by
  classical
  dsimp only
  intro r
  dsimp only at hterms
  simp_rw [hterms]
  by_cases hr : r = ⟨p, by omega⟩
  · subst r
    simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · simp [hr]

open Classical in
/-- The pointwise identities in each bidegree give the projector-sandwiched
shuffle/Alexander--Whitney identity. -/
theorem projected_alternatingMap_comp_alexanderWhitney_of_terms
    (hterms : ∀ p q,
      (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
        ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
          projectedShuffleAlexanderWhitneyTerm X Y p q s r =
            if r = distinguishedCut ∧ s = Shuffle.blockShuffle p q then
              (HomologicalComplex.ιTensorObj
                  ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                  ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                  p q (p + q) rfl ≫
                (HomologicalComplex.tensorHom
                  (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                  (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                  (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                  (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                  (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
                  (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))
            else 0)) :
    HomologicalComplex.tensorHom
        (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _) ≫
      alternatingMap X Y ≫
      AlgebraicTopology.AlexanderWhitney.alternatingMap X Y ≫
      HomologicalComplex.tensorHom
        (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _) =
    HomologicalComplex.tensorHom
      (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
      (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _) :=
  projected_alternatingMap_comp_alexanderWhitney_of_bidegrees X Y fun p q =>
    projectedShuffleAlexanderWhitneyBidegreeIdentity_of_terms X Y p q (hterms p q)

end AlgebraicTopology.EilenbergZilber
