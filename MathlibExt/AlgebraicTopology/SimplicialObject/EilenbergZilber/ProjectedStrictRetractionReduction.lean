/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap
public import Mathlib.AlgebraicTopology.DoldKan.PInfty

@[expose] public section

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

/-- A shuffle/Alexander--Whitney term sandwiched between the Dold--Kan
normalization projectors. -/
noncomputable def projectedShuffleAlexanderWhitneyTerm
    (p q : ℕ) (s : Shuffle p q) (r : Fin (p + q + 1)) :
    X.obj (Opposite.op ⦋p⦌) ⊗ Y.obj (Opposite.op ⦋q⦌) ⟶
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).X (p + q) :=
  let t := p + q - r.val
  have hrt : r.val + t = p + q := by omega
  ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
      (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
    shuffleSummand X Y s ≫
    (((AlgebraicTopology.AlexanderWhitney.frontFace X hrt ⊗ₘ
        AlgebraicTopology.AlexanderWhitney.backFace Y hrt) ≫
      HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        r.val t (p + q) hrt) ≫
      (HomologicalComplex.tensorHom
        (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))

set_option backward.isDefEq.respectTransparency false in
/-- Exact degreewise expansion of the projector-sandwiched composite. -/
theorem projected_shuffleBidegree_comp_alternatingComponent
    (p q : ℕ) :
    ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
      shuffleBidegree X Y p q ≫
      AlgebraicTopology.AlexanderWhitney.alternatingComponent X Y (p + q) ≫
      (HomologicalComplex.tensorHom
        (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q) =
    ∑ r : Fin (p + q + 1), ∑ s : Shuffle p q,
      projectedShuffleAlexanderWhitneyTerm X Y p q s r := by
  rw [AlgebraicTopology.AlexanderWhitney.alternatingComponent_eq_sum]
  unfold shuffleBidegree projectedShuffleAlexanderWhitneyTerm
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
/-- Cutwise projected identities imply the fixed-bidegree projected identity. -/
theorem projected_shuffleBidegree_identity_of_cuts
    (p q : ℕ)
    (hcuts : (let distinguishedCut : Fin (p + q + 1) := ⟨p, by omega⟩
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
          else 0)) :
    ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
      shuffleBidegree X Y p q ≫
      AlgebraicTopology.AlexanderWhitney.alternatingComponent X Y (p + q) ≫
      (HomologicalComplex.tensorHom
        (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
        (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q) =
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
  rw [projected_shuffleBidegree_comp_alternatingComponent]
  dsimp only at hcuts
  simp_rw [hcuts]
  rw [Finset.sum_ite_eq']
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The cutwise identities in each bidegree give the projector-sandwiched
shuffle/Alexander--Whitney identity on the alternating complex. -/
theorem projected_alternatingMap_comp_alexanderWhitney_of_bidegrees
    (hbidegree : ∀ p q,
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
      (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  simp only [HomologicalComplex.comp_f, alternatingMap_f,
    AlgebraicTopology.AlexanderWhitney.alternatingMap_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  dsimp only [curriedTensor]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  have hShuffle :
      ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q (p + q) rfl ≫
        shuffleComponent X Y (p + q) ≫
        AlgebraicTopology.AlexanderWhitney.alternatingComponent X Y (p + q) ≫
        (HomologicalComplex.tensorHom
          (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q) =
      ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
        shuffleBidegree X Y p q ≫
        AlgebraicTopology.AlexanderWhitney.alternatingComponent X Y (p + q) ≫
        (HomologicalComplex.tensorHom
          (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
          (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q) := by
    simpa only [Category.assoc, eqToHom_refl, Category.comp_id] using congrArg
      (fun t =>
        ((PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _).f p ⊗ₘ
            (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _).f q) ≫
          t ≫ AlgebraicTopology.AlexanderWhitney.alternatingComponent X Y (p + q) ≫
          (HomologicalComplex.tensorHom
            (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            (L₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            (L₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj X ⟶ _)
            (PInfty : (AlgebraicTopology.alternatingFaceMapComplex C).obj Y ⟶ _)).f (p + q))
      (ιTensorObj_comp_shuffleComponent X Y p q (p + q) rfl)
  exact hShuffle.trans
    (projected_shuffleBidegree_identity_of_cuts X Y p q (hbidegree p q))

end AlgebraicTopology.EilenbergZilber
