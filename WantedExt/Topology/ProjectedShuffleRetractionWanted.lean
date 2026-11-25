/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleRetractionCombinatorics

/-! # Projected shuffle and Alexander–Whitney retraction identities -/

set_option autoImplicit false

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

/-- At each bidegree, the projected sum equals the normalized summand at its cut. -/
theorem_wanted ProjectedShuffleAlexanderWhitneyBidegreeIdentity (p q : ℕ) :
  let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
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
      else 0

open Classical in
/-- Only the block shuffle at the distinguished cut contributes to each projected term. -/
theorem_wanted ProjectedShuffleAlexanderWhitneyTermIdentity (p q : ℕ) :
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

/-- Every projected term away from the block shuffle at the distinguished cut vanishes. -/
theorem_wanted ProjectedNonDistinguishedTermsVanish (p q : ℕ) :
  let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
  ∀ (r : Fin (p + q + 1)) (s : Shuffle p q),
    r ≠ distinguishedCut ∨ s ≠ Shuffle.blockShuffle p q →
      projectedShuffleAlexanderWhitneyTerm X Y p q s r = 0

/-- The projected block shuffle at the distinguished cut is the normalized summand. -/
theorem_wanted ProjectedDistinguishedTermIdentity (p q : ℕ) :
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

end AlgebraicTopology.EilenbergZilber
