/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import MathlibExtTest.AlgebraicGeometry.EtaleSpacePresentations
import Mathlib.CategoryTheory.SingleObj

/-! # Tests for 2-fibre products, algebraic spaces and stacks

The 2-fibre product of two points in the one-object groupoid of `ℤ` retains a different object
for each comparison automorphism: equal first and second projections do not identify different
comparisons, which probes the data lost by replacing a 2-fibre product with an ordinary product of
point sets. The remaining checks cover invertible modifications, the comparison functor of a
2-commutative square of stacks, atlases, and a scheme as an algebraic space over itself (smooth,
étale and surjective, via the identity chart).
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.GeneralStackGeometry

open CategoryTheory _root_.AlgebraicGeometry.GeneralStackGeometry

abbrev G := Multiplicative ℤ

def pointFunctor : Discrete Unit ⥤ SingleObj G :=
  (Functor.const (Discrete Unit)).obj (SingleObj.star G)

/-- The automorphism `n` of the unique object of the one-object groupoid of `ℤ`. -/
def comparisonIso (n : ℤ) :
    pointFunctor.obj (Discrete.mk ()) ≅ pointFunctor.obj (Discrete.mk ()) where
  hom := Multiplicative.ofAdd n
  inv := Multiplicative.ofAdd (-n)
  hom_inv_id := by
    change Multiplicative.ofAdd (-n) * Multiplicative.ofAdd n = 1
    rw [← ofAdd_add, neg_add_cancel, ofAdd_zero]
  inv_hom_id := by
    change Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1
    rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]

def comparisonPoint (n : ℤ) : IsoFibre pointFunctor pointFunctor :=
  ⟨Discrete.mk (), Discrete.mk (), comparisonIso n⟩

example : IsGroupoid (IsoFibre pointFunctor pointFunctor) := inferInstance

example : (Limits.CategoricalPullback.π₁ pointFunctor pointFunctor).obj (comparisonPoint 0) =
    (Limits.CategoricalPullback.π₁ pointFunctor pointFunctor).obj (comparisonPoint 1) := rfl

example : (Limits.CategoricalPullback.π₂ pointFunctor pointFunctor).obj (comparisonPoint 0) =
    (Limits.CategoricalPullback.π₂ pointFunctor pointFunctor).obj (comparisonPoint 1) := rfl

example : (CatCommSq.iso (Limits.CategoricalPullback.π₁ pointFunctor pointFunctor)
      (Limits.CategoricalPullback.π₂ pointFunctor pointFunctor) pointFunctor pointFunctor).hom.app
        (comparisonPoint 1) = Multiplicative.ofAdd (1 : ℤ) := rfl

example : ¬ Nonempty (comparisonPoint 0 ⟶ comparisonPoint 1) := by
  rintro ⟨h⟩
  have hc := h.w
  change Multiplicative.ofAdd (1 : ℤ) * 1 = 1 * Multiplicative.ofAdd (0 : ℤ) at hc
  simp only [mul_one, one_mul] at hc
  have heq : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd hc
  exact Int.one_ne_zero heq

universe u

example (X : AlgebraicGeometry.FppfStacks.StackInGroupoids.{u})
    {T : AlgebraicGeometry.Scheme.{u}} (x y : Fibre X T) (V : Over T)
    (e : ULift.{u + 1} ((reindex X V.hom).obj x ≅ (reindex X V.hom).obj y)) :
    ((isomPresheafObjEquiv X x y V) e).down = e.down.hom := rfl

example (S : AlgebraicGeometry.Scheme.{u})
    (F : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1})
    (groupoids : ∀ T : Over S, IsGroupoid (F.obj (.mk (Opposite.op T))))
    (stack : F.IsStack (AlgebraicGeometry.Scheme.fppfTopology.over S)) :
    (RelativeStack.of S F groupoids stack).toPseudofunctor = F := rfl

example {S : AlgebraicGeometry.Scheme.{u}} (T : Over S)
    (A : AlgebraicSpaceOver T.left) (V : Over T) :
    (relativeSpacePresheaf T A).obj (Opposite.op V) =
      {x : A.sheaf.obj.obj (Opposite.op V.left.left) //
        A.structural.hom.app (Opposite.op V.left.left) x = ULift.up V.hom.left} := rfl

example {S : AlgebraicGeometry.Scheme.{u}} (X : RelativeStack S)
    {U T : Over S} (x : X.Fibre U) (y : X.Fibre T) (V : Over T)
    (z : (pointComparisonPresheaf X.toPseudofunctor x y).obj (Opposite.op V)) :
    z.1.left ≫ U.hom = V.left.hom := Over.w z.1

section Stacks

open scoped Pseudofunctor.StrongTrans

variable {X Y Z : AlgebraicGeometry.FppfStacks.StackInGroupoids.{u}}

/-- The components of the identity invertible modification are identities. -/
example (p : AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom X Y) (T : AlgebraicGeometry.Scheme.{u})
    (x : Fibre X T) :
    (componentIso (Iso.refl _ : TwoIso p p) T).hom.app x =
      𝟙 _ := rfl

/-- The comparison functor of a 2-commutative square recovers both legs and the 2-cell. -/
example {f : AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom X Z}
    {g : AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom Y Z} (P : TwoFibreSquare f g)
    (T : AlgebraicGeometry.Scheme.{u}) (w : Fibre P.apex T) :
    ((P.comparisonFunctor T).obj w).fst = (component P.fst T).obj w ∧
      ((P.comparisonFunctor T).obj w).snd = (component P.snd T).obj w ∧
      ((P.comparisonFunctor T).obj w).iso = (componentIso P.commutes T).app w :=
  ⟨rfl, rfl, rfl⟩

example {f : AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom X Z}
    {g : AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom Y Z} (P : TwoFibreSquare f g)
    (T : AlgebraicGeometry.Scheme.{u}) :
    P.comparisonFunctor T ⋙ Limits.CategoricalPullback.π₁ (component f T) (component g T) =
      component P.fst T :=
  P.comparison_fst T

/-- An étale atlas gives a smooth atlas with the same underlying atlas. -/
example (a : EtaleAtlas X) : a.toSmoothAtlas.toAtlas = a.toAtlas := rfl

example (h : IsDeligneMumfordStack X) : IsArtinStack X :=
  isArtinStack_of_isDeligneMumfordStack h

/-- Charts of an algebraic space are unique: the represented-sheaf functor is faithful. -/
example {T : AlgebraicGeometry.Scheme.{u}} (A : AlgebraicSpaceOver T) (c c' : A.Chart) :
    c.map = c'.map :=
  AlgebraicGeometry.EtaleSpacePresentations.represented.map_injective
    (c.normalization.symm.trans c'.normalization)

end Stacks

section Presentations

variable {S : AlgebraicGeometry.Scheme.{u}} (X : RelativeStack S) {U T : Over S}
  (x : X.Fibre U) (y : X.Fibre T)

/-- Restriction along `f` of a comparison arrow precomposes its map to `U` with `f`. -/
example {V W : (Over T)ᵒᵖ} (f : V ⟶ W)
    (z : (pointComparisonPresheaf X.toPseudofunctor x y).obj V) :
    ((pointComparisonPresheaf X.toPseudofunctor x y).map f z).1 = f.unop.left ≫ z.1 :=
  rfl

/-- Restriction of comparison arrows is functorial: identities act trivially and composites act
in order. -/
example (V : (Over T)ᵒᵖ) (z : (pointComparisonPresheaf X.toPseudofunctor x y).obj V) :
    (pointComparisonPresheaf X.toPseudofunctor x y).map (𝟙 V) z = z :=
  Functor.map_id_apply _ _ _

example {V W Z : (Over T)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z)
    (z : (pointComparisonPresheaf X.toPseudofunctor x y).obj V) :
    (pointComparisonPresheaf X.toPseudofunctor x y).map (f ≫ g) z =
      (pointComparisonPresheaf X.toPseudofunctor x y).map g
        ((pointComparisonPresheaf X.toPseudofunctor x y).map f z) :=
  Functor.map_comp_apply _ _ _ _

/-- For a stack in groupoids the comparison arrows are isomorphisms, so the presheaf is the
2-fibre product. -/
example (Y : AlgebraicGeometry.FppfStacks.StackInGroupoids.{u}) {U T : AlgebraicGeometry.Scheme.{u}}
    (x : Fibre Y U) (y : Fibre Y T) (V : (Over T)ᵒᵖ) (z : (schemePointFibrePresheaf Y x y).obj V) :
    IsIso z.2 :=
  IsGroupoid.all_isIso _

/-- A point of an algebraic space over `V ⟶ T` is a point of the quotient sheaf over `V` whose
image under the structure map is `V ⟶ T`; restriction is restriction in the quotient sheaf. -/
example {T : AlgebraicGeometry.Scheme.{u}} (A : AlgebraicSpaceOver T) (V : (Over T)ᵒᵖ)
    (p : A.relativePresheaf.obj V) :
    A.structural.hom.app (Opposite.op V.unop.left) p.val = ULift.up V.unop.hom :=
  p.property

example {T : AlgebraicGeometry.Scheme.{u}} (A : AlgebraicSpaceOver T) {V W : (Over T)ᵒᵖ}
    (a : V ⟶ W) (p : A.relativePresheaf.obj V) :
    (A.relativePresheaf.map a p).val = A.sheaf.obj.map a.unop.left.op p.val :=
  rfl

/-- The comparison of an atlas is natural in the scheme over `T`: restricting a point of the base
change along `f` precomposes the corresponding map to the atlas with `f`. -/
example (Y : AlgebraicGeometry.FppfStacks.StackInGroupoids.{u}) (a : Atlas Y)
    (T : AlgebraicGeometry.Scheme.{u}) (y : Fibre Y T) {V W : (Over T)ᵒᵖ} (f : V ⟶ W)
    (p : (a.baseChange T y).relativePresheaf.obj V) :
    ((a.comparison T y).hom.app W ((a.baseChange T y).relativePresheaf.map f p)).down.1 =
      f.unop.left ≫ ((a.comparison T y).hom.app V p).down.1 := by
  rw [NatTrans.naturality_apply]
  rfl

end Presentations

section Spaces

open MathlibExtTest.AlgebraicGeometry.EtaleSpacePresentations

/-- A scheme `U` as an algebraic space over itself, presented by the trivial relation. -/
def selfSpace (U : AlgebraicGeometry.Scheme.{u}) : AlgebraicSpaceOver (trivialPresentation U).U :=
  ⟨trivialPresentation U, trivialRetraction U⟩

/-- Its chart is the identity of `U`. -/
def selfChart (U : AlgebraicGeometry.Scheme.{u}) : (selfSpace U).Chart :=
  ⟨𝟙 _, (atlas_trivialRetraction U).trans
    (AlgebraicGeometry.EtaleSpacePresentations.represented.map_id _).symm⟩

example (U : AlgebraicGeometry.Scheme.{u}) :
    (selfSpace U).IsSurjective ∧ (selfSpace U).IsSmooth ∧ (selfSpace U).IsEtale :=
  ⟨⟨selfChart U, (inferInstance : AlgebraicGeometry.Surjective (𝟙 (trivialPresentation U).U))⟩,
    ⟨selfChart U, (inferInstance : AlgebraicGeometry.Smooth (𝟙 (trivialPresentation U).U))⟩,
    ⟨selfChart U, (inferInstance : AlgebraicGeometry.Etale (𝟙 (trivialPresentation U).U))⟩⟩

end Spaces

end MathlibExtTest.AlgebraicGeometry.GeneralStackGeometry
