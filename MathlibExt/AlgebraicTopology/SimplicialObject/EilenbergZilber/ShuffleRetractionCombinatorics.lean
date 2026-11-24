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

/-- The pointwise term identity, a discharge obligation of the projected
retraction reduction: after the normalization projectors, only the block shuffle
at the cut `p` contributes. It is a proposition; nothing here proves it. -/
noncomputable def ProjectedShuffleAlexanderWhitneyTermIdentity (p q : ℕ) : Prop := by
  classical
  exact
    let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
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
        else 0

/-- Discharge obligation A, a proposition not proved here: every
non-distinguished projected term vanishes. -/
def ProjectedNonDistinguishedTermsVanish (p q : ℕ) : Prop :=
  let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
  ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
    r ≠ distinguishedCut ∨ s ≠ Shuffle.blockShuffle p q →
      projectedShuffleAlexanderWhitneyTerm X Y p q s r = 0

/-- Discharge obligation B, a proposition not proved here: the block shuffle at
the cut `p` contributes the normalization projector on the `(p,q)` summand. -/
def ProjectedDistinguishedTermIdentity (p q : ℕ) : Prop :=
  projectedShuffleAlexanderWhitneyTerm X Y p q
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
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q)

/-- Discharge obligations A and B imply the pointwise term identity. -/
theorem projectedShuffleAlexanderWhitneyTermIdentity_of_vanishing
    (p q : ℕ)
    (hvanish : ProjectedNonDistinguishedTermsVanish X Y p q)
    (hdistinguished : ProjectedDistinguishedTermIdentity X Y p q) :
    ProjectedShuffleAlexanderWhitneyTermIdentity X Y p q := by
  classical
  dsimp [ProjectedNonDistinguishedTermsVanish] at hvanish
  dsimp [ProjectedDistinguishedTermIdentity] at hdistinguished
  dsimp [ProjectedShuffleAlexanderWhitneyTermIdentity]
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

/-- The pointwise term identity implies the cutwise identity used by the
categorical reconstruction. -/
theorem projectedShuffleAlexanderWhitneyBidegreeIdentity_of_terms
    (p q : ℕ)
    (hterms : ProjectedShuffleAlexanderWhitneyTermIdentity X Y p q) :
    ProjectedShuffleAlexanderWhitneyBidegreeIdentity X Y p q := by
  classical
  dsimp [ProjectedShuffleAlexanderWhitneyBidegreeIdentity]
  intro r
  dsimp [ProjectedShuffleAlexanderWhitneyTermIdentity] at hterms
  simp_rw [hterms]
  by_cases hr : r = ⟨p, by omega⟩
  · subst r
    simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · simp [hr]

/-- A conditional reduction: if the pointwise term identities hold for all
`(p,q)`, then the shuffle map followed by the Alexander--Whitney map is the
identity on the image of the normalization projectors. The identities are
hypotheses; this does not prove that the composite restricts to the identity. -/
theorem projected_alternatingMap_comp_alexanderWhitney_of_terms
    (hterms : ∀ p q,
      ProjectedShuffleAlexanderWhitneyTermIdentity X Y p q) :
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
