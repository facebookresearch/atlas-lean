/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.LiftingTest

/-!
# Semantic colimit owners for the original tagged lifting tests

Every original diagonal and every whole native square factors through an
actual stage of the given filtered colimit. Equal whole tagged values
become equal at a later actual stage. Original diagram evaluations retain
the original object and both full native square maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w s u v uD vD uA vA

open CategoryTheory Limits TypeCat
open CategoryTheory.MorphismProperty.LiftingTest
open CategoryTheory.Presentable.LiftingTest

namespace CategoryTheory.Presentable.LiftingTestSemantic

section Scalar

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} C] {I : Type s} [Small.{w} I] (f : I → Arrow C)
  (χ : Cardinal.{w}) [Fact χ.IsRegular]
  [∀ k, IsCardinalPresentable (f k).left χ]
  [∀ k, IsCardinalPresentable (f k).right χ]
  {J : Type w} [SmallCategory J] [IsCardinalFiltered J χ]
  {X : J ⥤ Arrow C} {c : Cocone X}

include χ

/-- The actual normalized source cocone is colimiting at the same endpoint rank. -/
def scalarLeftColimit (hc : IsColimit c) :
    IsColimit ((smallFunctor.{w} f ⋙ Arrow.leftFunc).mapCocone c) := by
  let _ : (smallFunctor.{w} f).IsCardinalAccessible χ :=
    smallFunctor_isCardinalAccessible f χ
  let _ : PreservesColimitsOfShape J (smallFunctor.{w} f) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ J
  let _ : PreservesColimitsOfShape J (Arrow.leftFunc : Arrow (Type w) ⥤ Type w) :=
    inferInstanceAs (PreservesColimitsOfShape J (Comma.fst (𝟭 (Type w)) (𝟭 (Type w))))
  exact isColimitOfPreserves _ hc

/-- The actual normalized target cocone retains all original native squares. -/
def scalarRightColimit (hc : IsColimit c) :
    IsColimit ((smallFunctor.{w} f ⋙ Arrow.rightFunc).mapCocone c) := by
  let _ : (smallFunctor.{w} f).IsCardinalAccessible χ :=
    smallFunctor_isCardinalAccessible f χ
  let _ : PreservesColimitsOfShape J (smallFunctor.{w} f) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ J
  let _ : PreservesColimitsOfShape J (Arrow.rightFunc : Arrow (Type w) ⥤ Type w) :=
    inferInstanceAs (PreservesColimitsOfShape J (Comma.snd (𝟭 (Type w)) (𝟭 (Type w))))
  exact isColimitOfPreserves _ hc

/-- Every whole ORIGINAL tagged diagonal factors through an actual original stage. -/
theorem rawLifts_factor (hc : IsColimit c) (z : RawLifts f c.pt) :
    ∃ (j : J) (b : RawLifts f (X.obj j)), rawLiftMap f (c.ι.app j) b = z := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (scalarLeftColimit f χ hc) (liftsEquiv.{w} f c.pt z)
  let b : RawLifts f (X.obj j) := (liftsEquiv.{w} f (X.obj j)).symm x
  refine ⟨j, b, (liftsEquiv.{w} f c.pt).injective ?_⟩
  have hm := congrFun (smallFunctor_map_left_function.{w} f (c.ι.app j)) b
  change ((smallFunctor.{w} f).map (c.ι.app j)).left
      (liftsEquiv.{w} f (X.obj j) b) =
    liftsEquiv.{w} f c.pt (rawLiftMap f (c.ι.app j) b) at hm
  rw [show liftsEquiv.{w} f (X.obj j) b = x from
    (liftsEquiv.{w} f (X.obj j)).apply_symm_apply x] at hm
  exact hm.symm.trans hx

/-- Every whole ORIGINAL tagged native square factors with its original tag unchanged. -/
theorem rawSquares_factor (hc : IsColimit c) (z : RawSquares f c.pt) :
    ∃ (j : J) (b : RawSquares f (X.obj j)), rawSquareMap f (c.ι.app j) b = z := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (scalarRightColimit f χ hc) (squaresEquiv.{w} f c.pt z)
  let b : RawSquares f (X.obj j) := (squaresEquiv.{w} f (X.obj j)).symm x
  refine ⟨j, b, (squaresEquiv.{w} f c.pt).injective ?_⟩
  have hm := congrFun (smallFunctor_map_right_function.{w} f (c.ι.app j)) b
  change ((smallFunctor.{w} f).map (c.ι.app j)).right
      (squaresEquiv.{w} f (X.obj j) b) =
    squaresEquiv.{w} f c.pt (rawSquareMap f (c.ι.app j) b) at hm
  rw [show squaresEquiv.{w} f (X.obj j) b = x from
    (squaresEquiv.{w} f (X.obj j)).apply_symm_apply x] at hm
  exact hm.symm.trans hx

/-- The same ORIGINAL generator and its full original diagonal equation are retained. -/
theorem nativeDiagonal_factor (hc : IsColimit c) (k : I) (l : (f k).right ⟶ c.pt.left) :
    ∃ (j : J) (b : (f k).right ⟶ (X.obj j).left), b ≫ (c.ι.app j).left = l := by
  obtain ⟨j, ⟨k', b⟩, hb⟩ := rawLifts_factor f χ hc ⟨k, l⟩
  have hk : k' = k := congrArg Sigma.fst hb
  subst k'
  change (⟨k, b ≫ (c.ι.app j).left⟩ : RawLifts f c.pt) = ⟨k, l⟩ at hb
  have hab := sigma_mk_injective hb
  exact ⟨j, b, hab⟩

/-- The entire ORIGINAL square factors, including BOTH original map fields. -/
theorem nativeSquare_factor (hc : IsColimit c) (k : I) (a : f k ⟶ c.pt) :
    ∃ (j : J) (b : f k ⟶ X.obj j), b ≫ c.ι.app j = a := by
  obtain ⟨j, ⟨k', b⟩, hb⟩ := rawSquares_factor f χ hc ⟨k, a⟩
  have hk : k' = k := congrArg Sigma.fst hb
  subst k'
  change (⟨k, b ≫ c.ι.app j⟩ : RawSquares f c.pt) = ⟨k, a⟩ at hb
  have hab := sigma_mk_injective hb
  exact ⟨j, b, hab⟩

/-- All three original square equations are retained at the actual factor stage. -/
theorem nativeSquare_factor_fields (hc : IsColimit c) (k : I) (a : f k ⟶ c.pt) :
    ∃ (j : J) (top : (f k).left ⟶ (X.obj j).left)
      (bottom : (f k).right ⟶ (X.obj j).right),
      top ≫ (X.obj j).hom = (f k).hom ≫ bottom ∧
      top ≫ (c.ι.app j).left = a.left ∧
      bottom ≫ (c.ι.app j).right = a.right := by
  obtain ⟨j, b, hb⟩ := nativeSquare_factor f χ hc k a
  exact ⟨j, b.left, b.right, b.w,
    congrArg (fun z : f k ⟶ c.pt => z.left) hb,
    congrArg (fun z : f k ⟶ c.pt => z.right) hb⟩

/-- Equal ORIGINAL tagged diagonal images coequalize at a later actual stage. -/
theorem rawLifts_eventually_equal (hc : IsColimit c) {j : J}
    (a b : RawLifts f (X.obj j))
    (h : rawLiftMap f (c.ι.app j) a = rawLiftMap f (c.ι.app j) b) :
    ∃ (j' : J) (t : j ⟶ j'), rawLiftMap f (X.map t) a = rawLiftMap f (X.map t) b := by
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J χ
  have hn : ((smallFunctor.{w} f).map (c.ι.app j)).left (liftsEquiv.{w} f (X.obj j) a) =
      ((smallFunctor.{w} f).map (c.ι.app j)).left (liftsEquiv.{w} f (X.obj j) b) := by
    have ha := congrFun (smallFunctor_map_left_function.{w} f (c.ι.app j)) a
    have hb := congrFun (smallFunctor_map_left_function.{w} f (c.ι.app j)) b
    exact ha.trans ((congrArg (liftsEquiv.{w} f c.pt) h).trans hb.symm)
  obtain ⟨j', t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (scalarLeftColimit f χ hc) (liftsEquiv.{w} f (X.obj j) a)
      (liftsEquiv.{w} f (X.obj j) b)).mp hn
  refine ⟨j', t, (liftsEquiv.{w} f (X.obj j')).injective ?_⟩
  have ha := congrFun (smallFunctor_map_left_function.{w} f (X.map t)) a
  have hb := congrFun (smallFunctor_map_left_function.{w} f (X.map t)) b
  exact ha.symm.trans (ht.trans hb)

/-- Equal whole ORIGINAL native square images coequalize without dropping a field or tag. -/
theorem rawSquares_eventually_equal (hc : IsColimit c) {j : J}
    (a b : RawSquares f (X.obj j))
    (h : rawSquareMap f (c.ι.app j) a = rawSquareMap f (c.ι.app j) b) :
    ∃ (j' : J) (t : j ⟶ j'), rawSquareMap f (X.map t) a = rawSquareMap f (X.map t) b := by
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J χ
  have hn : ((smallFunctor.{w} f).map (c.ι.app j)).right (squaresEquiv.{w} f (X.obj j) a) =
      ((smallFunctor.{w} f).map (c.ι.app j)).right (squaresEquiv.{w} f (X.obj j) b) := by
    have ha := congrFun (smallFunctor_map_right_function.{w} f (c.ι.app j)) a
    have hb := congrFun (smallFunctor_map_right_function.{w} f (c.ι.app j)) b
    exact ha.trans ((congrArg (squaresEquiv.{w} f c.pt) h).trans hb.symm)
  obtain ⟨j', t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (scalarRightColimit f χ hc) (squaresEquiv.{w} f (X.obj j) a)
      (squaresEquiv.{w} f (X.obj j) b)).mp hn
  refine ⟨j', t, (squaresEquiv.{w} f (X.obj j')).injective ?_⟩
  have ha := congrFun (smallFunctor_map_right_function.{w} f (X.map t)) a
  have hb := congrFun (smallFunctor_map_right_function.{w} f (X.map t)) b
  exact ha.symm.trans (ht.trans hb)

end Scalar

/-- Every ORIGINAL diagram object retains its whole native coefficient square at a factor stage. -/
theorem original_component_square_factor
    {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w, w} C] {J : Type w} [SmallCategory J]
    (χ : Cardinal.{w}) [Fact χ.IsRegular] [IsCardinalFiltered J χ]
    {X : J ⥤ Arrow (D ⥤ C)} {c : Cocone X} (hc : IsColimit c)
    (d : D) (g : Arrow C) [IsCardinalPresentable g.left χ]
    [IsCardinalPresentable g.right χ]
    (a : g ⟶ (Functor.mapArrow ((evaluation D C).obj d)).obj c.pt) :
    ∃ (j : J) (b : g ⟶ (Functor.mapArrow ((evaluation D C).obj d)).obj (X.obj j)),
      b ≫ (Functor.mapArrow ((evaluation D C).obj d)).map (c.ι.app j) = a := by
  let _ : (Functor.mapArrow ((evaluation D C).obj d)).IsCardinalAccessible χ :=
    evaluationArrow_isCardinalAccessible d χ
  let _ : IsCardinalPresentable g χ := generator_isCardinalPresentable g χ
  let _ : PreservesColimitsOfShape J (Functor.mapArrow ((evaluation D C).obj d)) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ J
  exact IsCardinalPresentable.exists_hom_of_isColimit χ
    (isColimitOfPreserves (Functor.mapArrow ((evaluation D C).obj d)) hc) a

section FixedTags

variable (A : Type uA) [Category.{vA} A]

local instance regularAleph0 : Fact (Cardinal.aleph0 : Cardinal.{w}).IsRegular :=
  Cardinal.fact_isRegular_aleph0

/-- An actual empty fixed family has no tag, object or surjectivity assumption. -/
def emptyFamily : PEmpty → A ⥤ Type w := fun k => nomatch k

/-- The empty fixed coproduct preserves the same filtered colimits. -/
theorem emptyFixedSum (χ : Cardinal.{w}) [Fact χ.IsRegular] :
    (fixedSumFunctor (emptyFamily.{w} A)).IsCardinalAccessible χ := by
  let (k : PEmpty) : (emptyFamily.{w} A k).IsCardinalAccessible χ := nomatch k
  exact fixedSumFunctor_isCardinalAccessible _ χ

/-- A genuinely infinite fixed family with literal varying finite component values. -/
def infiniteFamily (n : ℕ) : Type w ⥤ Type w :=
  (Functor.const (Type w)).obj (ULift.{w} (Fin (n + 1)))

/-- An infinite fixed tag family preserves at aleph0 without imposing a finite-tag bound. -/
theorem infiniteFixedSum :
    (fixedSumFunctor (infiniteFamily.{w})).IsCardinalAccessible
      (Cardinal.aleph0 : Cardinal.{w}) := by
  let (n : ℕ) : (infiniteFamily.{w} n).IsCardinalAccessible
      (Cardinal.aleph0 : Cardinal.{w}) := by
    change ((Functor.const (Type w)).obj (ULift.{w} (Fin (n + 1)))).IsCardinalAccessible
      (Cardinal.aleph0 : Cardinal.{w})
    infer_instance
  exact fixedSumFunctor_isCardinalAccessible _ _

end FixedTags

end CategoryTheory.Presentable.LiftingTestSemantic
