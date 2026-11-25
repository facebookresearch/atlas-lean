/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing

/-!
# Right-proper gluing for actual maps of chosen pullback squares

Objectwise weak maps of two cospans induce a weak map of their actual chosen
pullbacks when the same designated cospan leg in both is a fibration. The
proof uses the existing chosen-span gluing theorem in the opposite model.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsRightProper C]

/-- Right properness gives left properness in the actual opposite model, for use in chosen-square
gluing. -/
private theorem opposite_leftProper : IsLeftProper Cᵒᵖ where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro X Y i hi
    constructor
    intro A B g' f' f sq hf
    let : Fibration i.unop := (fibration_iff _).mpr hi
    let : WeakEquivalence f.unop := (weakEquivalence_iff _).mpr hf
    have h := IsRightProper.weakEquivalence_of_isPullback sq.unop
    rw [weakEquivalence_iff] at h
    change weakEquivalences C f'.unop
    exact h

/-- Whole maps of chosen pullbacks are weak when both designated right cospan legs are genuine
fibrations. -/
theorem IsRightProper.weakEquivalence_map_of_isPullbacks_of_snd
    {P X Y Z P' X' Y' Z' : C}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a' : P' ⟶ X'} {b' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (sq : IsPullback a b f g) (sq' : IsPullback a' b' f' g')
    {p : P ⟶ P'} {x : X ⟶ X'} {y : Y ⟶ Y'} {z : Z ⟶ Z'}
    (hx : f ≫ z = x ≫ f') (hy : g ≫ z = y ≫ g')
    (ha : a ≫ x = p ≫ a') (hb : b ≫ y = p ≫ b')
    [Fibration g] [Fibration g'] [WeakEquivalence x] [WeakEquivalence y] [WeakEquivalence z] :
    WeakEquivalence p := by
  let : IsLeftProper Cᵒᵖ := opposite_leftProper
  let : WeakEquivalence x.op := by
    rw [weakEquivalence_iff, weakEquivalences_op]
    exact mem_weakEquivalences x
  let : WeakEquivalence y.op := by
    rw [weakEquivalence_iff, weakEquivalences_op]
    exact mem_weakEquivalences y
  let : WeakEquivalence z.op := by
    rw [weakEquivalence_iff, weakEquivalences_op]
    exact mem_weakEquivalences z
  have h : WeakEquivalence p.op :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst sq'.op sq.op
      (a := z.op) (b := y.op) (c := x.op) (d := p.op)
      (congrArg Quiver.Hom.op hy).symm (congrArg Quiver.Hom.op hx).symm
      (congrArg Quiver.Hom.op hb).symm (congrArg Quiver.Hom.op ha).symm
  rw [weakEquivalence_iff, weakEquivalences_op] at h
  exact (weakEquivalence_iff _).mpr h

/-- Whole maps of chosen pullbacks are weak when both designated left cospan legs are genuine
fibrations. -/
theorem IsRightProper.weakEquivalence_map_of_isPullbacks_of_fst
    {P X Y Z P' X' Y' Z' : C}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a' : P' ⟶ X'} {b' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (sq : IsPullback a b f g) (sq' : IsPullback a' b' f' g')
    {p : P ⟶ P'} {x : X ⟶ X'} {y : Y ⟶ Y'} {z : Z ⟶ Z'}
    (hx : f ≫ z = x ≫ f') (hy : g ≫ z = y ≫ g')
    (ha : a ≫ x = p ≫ a') (hb : b ≫ y = p ≫ b')
    [Fibration f] [Fibration f'] [WeakEquivalence x] [WeakEquivalence y] [WeakEquivalence z] :
    WeakEquivalence p :=
  IsRightProper.weakEquivalence_map_of_isPullbacks_of_snd sq.flip sq'.flip hy hx hb ha

end HomotopicalAlgebra
