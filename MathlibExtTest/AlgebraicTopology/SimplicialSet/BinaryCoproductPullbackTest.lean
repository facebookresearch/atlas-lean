/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.BinaryCoproductPullback
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SSet.BinaryCoproductPullback.Tests

/-- The occupied identity component retains the original non-Kan two-simplex as base. -/
def occupiedLeft : (Δ[2] : SSet.{u}) ⟶ Δ[2] := 𝟙 _

/-- The second original cofan leg is a constant, nonmonic interval attachment. -/
def occupiedRight : (Δ[1] : SSet.{u}) ⟶ Δ[2] :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3))

/-- The actual degree-zero pullback cofan has all four original projection equations. -/
theorem degreeZeroFourLegs :
    let t : (Δ[0] : SSet.{u}) ⟶ Δ[2] := SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 1)
    (coprod.inl : pullback occupiedLeft.{u} t ⟶ pullback occupiedLeft.{u} t ⨿ pullback occupiedRight.{u} t) ≫
      (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).hom ≫
      pullback.fst (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t =
      pullback.fst occupiedLeft.{u} t ≫ coprod.inl ∧
    (coprod.inl : pullback occupiedLeft.{u} t ⟶ pullback occupiedLeft.{u} t ⨿ pullback occupiedRight.{u} t) ≫
      (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).hom ≫
      pullback.snd (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t = pullback.snd occupiedLeft.{u} t ∧
    (coprod.inr : pullback occupiedRight.{u} t ⟶ pullback occupiedLeft.{u} t ⨿ pullback occupiedRight.{u} t) ≫
      (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).hom ≫
      pullback.fst (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t =
      pullback.fst occupiedRight.{u} t ≫ coprod.inr ∧
    (coprod.inr : pullback occupiedRight.{u} t ⟶ pullback occupiedLeft.{u} t ⨿ pullback occupiedRight.{u} t) ≫
      (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).hom ≫
      pullback.snd (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t = pullback.snd occupiedRight.{u} t := by
  dsimp only
  exact binaryPullbackIso_hom_legs _ _ _

/-- Both original inverse aggregate projections remain visible on the same occupied cofan. -/
theorem originalInverseAggregate (t : (Δ[2] : SSet.{u}) ⟶ Δ[2]) :
    (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).inv ≫
      coprod.desc (pullback.fst occupiedLeft.{u} t ≫ coprod.inl)
        (pullback.fst occupiedRight.{u} t ≫ coprod.inr) =
      pullback.fst (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t ∧
    (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} t).inv ≫
      coprod.desc (pullback.snd occupiedLeft.{u} t) (pullback.snd occupiedRight.{u} t) =
      pullback.snd (coprod.desc occupiedLeft.{u} occupiedRight.{u}) t :=
  binaryPullbackIso_inv_legs _ _ _

/-- A genuine degeneracy preserves both ordinary operator equations without a weak-map premise. -/
theorem originalDegeneracyLaws :
    let w : (Δ[2] : SSet.{u}) ⟶ Δ[1] := SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2))
    let v : (Δ[1] : SSet.{u}) ⟶ Δ[2] := SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3))
    let c₁ := pullback.map occupiedLeft.{u} (w ≫ v) occupiedLeft.{u} v
      (𝟙 _) w (𝟙 _) (by simp) (by simp)
    let c₂ := pullback.map occupiedRight.{u} (w ≫ v) occupiedRight.{u} v
      (𝟙 _) w (𝟙 _) (by simp) (by simp)
    let c := pullback.map (coprod.desc occupiedLeft.{u} occupiedRight.{u}) (w ≫ v)
      (coprod.desc occupiedLeft.{u} occupiedRight.{u}) v (𝟙 _) w (𝟙 _) (by simp) (by simp)
    coprod.map c₁ c₂ ≫ (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} v).hom =
      (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} (w ≫ v)).hom ≫ c ∧
    (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} (w ≫ v)).inv ≫ coprod.map c₁ c₂ =
      c ≫ (binaryPullbackIso occupiedLeft.{u} occupiedRight.{u} v).inv := by
  dsimp only
  exact binaryPullbackIso_operator _ _ _ _

/-- Both distinct-base component squares retain their actual original maps. -/
theorem allOriginalBinarySquares {X₁ X₂ Y₁ Y₂ : SSet.{u}}
    (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) :
    IsPullback coprod.inl p₁ (coprod.map p₁ p₂) coprod.inl ∧
    IsPullback coprod.inr p₂ (coprod.map p₁ p₂) coprod.inr := binaryCoproductSquares _ _

end SSet.BinaryCoproductPullback.Tests
