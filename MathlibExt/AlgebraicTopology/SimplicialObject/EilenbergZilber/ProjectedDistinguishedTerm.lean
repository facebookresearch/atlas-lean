/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.BlockShuffleFaces

/-!
# The distinguished projected shuffle term

At the distinguished cut, the two Alexander–Whitney faces undo the block shuffle.
The two normalization projectors on each factor then reduce to one by idempotence.

## References

For the classical normalized retraction, see Samuel Eilenberg and Saunders Mac Lane,
*On the Groups H(Π, n), II: Methods of Computation*, Annals of Mathematics (2) 60 (1954),
49–139, Theorem 2.1a.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

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
/-- The projected block shuffle at the distinguished cut is the normalized summand. -/
public theorem ProjectedDistinguishedTermIdentity (p q : ℕ) :
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
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q) := by
  let K := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let L := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let P : K ⟶ K := PInfty
  let Q : L ⟶ L := PInfty
  let cut (t : ℕ) (h : p + t = p + q) :=
    (frontFace X h ⊗ₘ backFace Y h) ≫ HomologicalComplex.ιTensorObj K L p t (p + q) h
  -- Change the back-face index and the coproduct inclusion together.
  have hcut (t : ℕ) (h : p + t = p + q) : cut t h = cut q rfl := by
    obtain rfl : t = q := Nat.add_left_cancel h
    rfl
  have hfront : X.map (Shuffle.blockShuffle p q).leftHom.op ≫ frontFace X (p := p) (q := q) rfl =
      𝟙 _ := by
    rw [frontFace, ← X.map_comp, ← op_comp, Shuffle.frontInclusion_comp_blockShuffle_leftHom,
      op_id, X.map_id]
  have hback : Y.map (Shuffle.blockShuffle p q).rightHom.op ≫ backFace Y (p := p) (q := q) rfl =
      𝟙 _ := by
    change Y.map (Shuffle.blockShuffle p q).rightHom.op ≫
      Y.map (backInclusion p q (p + q) rfl).op = 𝟙 _
    rw [← Y.map_comp, ← op_comp, Shuffle.backInclusion_comp_blockShuffle_rightHom,
      op_id, Y.map_id]
  have hfaces : shuffleSummand X Y (Shuffle.blockShuffle p q) ≫
      (frontFace X (p := p) (q := q) rfl ⊗ₘ backFace Y (p := p) (q := q) rfl) =
      𝟙 (K.X p ⊗ L.X q) := by
    simp only [shuffleSummand, Shuffle.shuffleSignZ_blockShuffle, one_smul]
    rw [tensorHom_comp_tensorHom, hfront, hback, tensorHom_id, id_whiskerRight]
    rfl
  -- Evaluate the tensor of the projectors on the selected coproduct summand.
  have hι : HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
      (HomologicalComplex.tensorHom P Q).f (p + q) =
      (P.f p ⊗ₘ Q.f q) ≫ HomologicalComplex.ιTensorObj K L p q (p + q) rfl := by
    rw [HomologicalComplex.tensorHom, HomologicalComplex.ι_mapBifunctorMap]
    exact (tensorHom_def_assoc _ _ _).symm
  change (P.f p ⊗ₘ Q.f q) ≫ shuffleSummand X Y (Shuffle.blockShuffle p q) ≫
      cut (p + q - p) (by omega) ≫ (HomologicalComplex.tensorHom P Q).f (p + q) =
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
      (HomologicalComplex.tensorHom P Q).f (p + q)
  rw [hcut]
  simp only [cut, Category.assoc, hι]
  rw [← Category.assoc (shuffleSummand X Y (Shuffle.blockShuffle p q)), hfaces]
  let ι := HomologicalComplex.ιTensorObj K L p q (p + q) rfl
  change (P.f p ⊗ₘ Q.f q) ≫ 𝟙 (K.X p ⊗ L.X q) ≫ (P.f p ⊗ₘ Q.f q) ≫ ι =
    (P.f p ⊗ₘ Q.f q) ≫ ι
  rw [Category.id_comp, tensorHom_comp_tensorHom_assoc]
  exact congrArg₂ (fun f g => (f ⊗ₘ g) ≫ ι)
    (PInfty_f_idem (X := X) p) (PInfty_f_idem (X := Y) q)

end AlgebraicTopology.EilenbergZilber
