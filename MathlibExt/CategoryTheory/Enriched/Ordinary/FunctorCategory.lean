/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Underlying ordinary functors of genuine enriched functors

The usual enrichment-forgetting operations turn every genuine unit graded
transformation into its actual ordinary natural transformation. Objects and
all morphism components remain the original values, with identity and
composition inherited from the genuine transformation category.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]

/-- The ordinary natural transformation obtained from a genuine unit graded transformation. -/
def ordinaryNatTrans {F G : EnrichedFunctorCat V I} (q : F ⟶ G) :
    F.toEnrichedFunctor.toOrdinaryFunctor ⟶ G.toEnrichedFunctor.toOrdinaryFunctor :=
  Functor.whiskerRight
    (Functor.whiskerLeft (ForgetEnrichment.equiv (D := I) V).inverse q.toEnrichedNatTrans.out)
    (ForgetEnrichment.equivFunctor V V)

/-- Forgetting enrichment retains every original ordinary component. -/
@[simp]
theorem ordinaryNatTrans_app {F G : EnrichedFunctorCat V I} (q : F ⟶ G) (i : I) :
    (ordinaryNatTrans q).app i = component q i := rfl

/-- The genuine forgetful functor on enriched functors and all unit graded transformations. -/
def forgetOrdinary : EnrichedFunctorCat V I ⥤ (I ⥤ V) where
  obj F := F.toEnrichedFunctor.toOrdinaryFunctor
  map q := ordinaryNatTrans q
  map_id F := by
    ext i
    exact (ordinaryNatTrans_app (𝟙 F) i).trans (component_id F i)
  map_comp q r := by
    ext i
    have h₀ := ordinaryNatTrans_app (q ≫ r) i
    have h₁ := component_comp q r i
    have h₂ := congrArg₂ (fun f g => f ≫ g) (ordinaryNatTrans_app q i)
      (ordinaryNatTrans_app r i)
    exact h₀.trans (h₁.trans h₂.symm)

/-- The underlying functor has exactly the original enriched functor values and actions. -/
@[simp]
theorem forgetOrdinary_obj (F : EnrichedFunctorCat V I) :
    (forgetOrdinary (V := V) (I := I)).obj F = F.toEnrichedFunctor.toOrdinaryFunctor := rfl

/-- Every forgotten morphism keeps its entire original component. -/
@[simp]
theorem forgetOrdinary_map_app {F G : EnrichedFunctorCat V I} (q : F ⟶ G) (i : I) :
    ((forgetOrdinary (V := V) (I := I)).map q).app i = component q i :=
  ordinaryNatTrans_app q i

end CategoryTheory.EnrichedFunctorCat
