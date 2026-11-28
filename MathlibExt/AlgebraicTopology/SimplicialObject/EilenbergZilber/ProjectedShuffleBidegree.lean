/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ProjectedDistinguishedTerm
import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.CutMonoClassification
import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBlockClassification

/-!
# The projected shuffle–Alexander–Whitney bidegree identity

Let `X` and `Y` be simplicial objects in a preadditive monoidal category whose tensor
is additive in each variable, and suppose their alternating face map complexes admit
`HomologicalComplex.HasTensor`. For any natural degrees `p` and `q`, the shuffle sum
followed by the Alexander–Whitney cut `r` in degree `p + q`, with normalization
projectors at both ends, is the projected inclusion at `r = p` and zero at every
other cut. This is a cutwise, projector-based form of the classical normalized
shuffle retraction, not the full chain-homotopy statement.

## References

* Samuel Eilenberg and Saunders MacLane, *On the Groups H(Π, n), II: Methods of Computation*,
  Annals of Mathematics (2) 60 (1954), no. 1, 49–139, Theorem 2.1a, for the classical
  normalized retraction.
* `MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ProjectedDistinguishedTerm`,
  `ProjectedDistinguishedTermIdentity`: the computation at the block shuffle supplies the
  surviving value and the proof there shows how to move the target projectors past the inclusion.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial
open scoped BigOperators MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

open AlgebraicTopology.AlexanderWhitney (frontFace backFace frontInclusion backInclusion)
open AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

set_option backward.isDefEq.respectTransparency false in
private theorem projectedTerm_eq_zero (p q : ℕ) (r : Fin (p + q + 1)) (s : Shuffle p q)
    (hoff : r ≠ ⟨p, by omega⟩ ∨ s ≠ Shuffle.blockShuffle p q) :
    projectedShuffleAlexanderWhitneyTerm X Y p q s r = 0 := by
  let t := p + q - r.val
  have hrt : r.val + t = p + q := by dsimp only [t]; omega
  let α := frontInclusion r.val t (p + q) hrt ≫ s.leftHom
  let β := backInclusion r.val t (p + q) hrt ≫ s.rightHom
  have hdeg : ¬ Mono α ∨ ¬ Mono β := by
    by_cases hα : Mono α
    · by_cases hβ : Mono β
      · have hr : r = ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ :=
          Fin.ext (cut_eq_of_both_mono p q r s)
        have : Mono (frontInclusion p q (p + q) rfl ≫ s.leftHom) := by
          -- The front inclusion does not depend on the length of the back face.
          subst r
          exact hα
        have hs := Shuffle.eq_blockShuffle_of_left_mono p q s
        exact (hoff.elim (· hr) (· hs)).elim
      · exact Or.inr hβ
    · exact Or.inl hα
  let K := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let L := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let P : K ⟶ K := PInfty
  let Q : L ⟶ L := PInfty
  let ι := HomologicalComplex.ιTensorObj K L r.val t (p + q) hrt
  have hι : ι ≫ (HomologicalComplex.tensorHom P Q).f (p + q) = (P.f r.val ⊗ₘ Q.f t) ≫ ι := by
    dsimp only [ι]
    rw [HomologicalComplex.tensorHom, HomologicalComplex.ι_mapBifunctorMap]
    exact (tensorHom_def_assoc _ _ _).symm
  have hfaces : (X.map s.leftHom.op ≫ frontFace X hrt ≫ P.f r.val) ⊗ₘ
      (Y.map s.rightHom.op ≫ backFace Y hrt ≫ Q.f t) = 0 := by
    simp only [← Category.assoc]
    change ((X.map s.leftHom.op ≫ X.map (frontInclusion r.val t (p + q) hrt).op) ≫ P.f r.val) ⊗ₘ
      ((Y.map s.rightHom.op ≫ Y.map (backInclusion r.val t (p + q) hrt).op) ≫ Q.f t) = 0
    rw [← X.map_comp, ← Y.map_comp, ← op_comp, ← op_comp]
    rcases hdeg with hα | hβ
    · rw [degeneracy_comp_PInfty X r.val α hα, tensorHom_def]
      change ((curriedTensor C).map (0 : K.X p ⟶ K.X r.val)).app (L.X q) ≫ _ = 0
      rw [Functor.map_zero, zero_app, zero_comp]
    · rw [degeneracy_comp_PInfty Y t β hβ, tensorHom_def]
      change _ ≫ ((curriedTensor C).obj (K.X r.val)).map (0 : L.X q ⟶ L.X t) = 0
      rw [Functor.map_zero, comp_zero]
  change (P.f p ⊗ₘ Q.f q) ≫ shuffleSummand X Y s ≫
    ((frontFace X hrt ⊗ₘ backFace Y hrt) ≫ ι) ≫ (HomologicalComplex.tensorHom P Q).f (p + q) = 0
  simp only [shuffleSummand, Category.assoc, hι, Preadditive.zsmul_comp,
    tensorHom_comp_tensorHom_assoc, hfaces, zero_comp, smul_zero, comp_zero]

/-- At each bidegree, the projected sum equals the normalized summand at its cut. -/
public theorem ProjectedShuffleAlexanderWhitneyBidegreeIdentity (p q : ℕ) :
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
      else 0 := by
  apply projectedShuffleAlexanderWhitneyBidegreeIdentity_of_terms
  exact projectedShuffleAlexanderWhitneyTermIdentity_of_vanishing X Y p q
    (projectedTerm_eq_zero X Y p q) (ProjectedDistinguishedTermIdentity X Y p q)

end AlgebraicTopology.EilenbergZilber
