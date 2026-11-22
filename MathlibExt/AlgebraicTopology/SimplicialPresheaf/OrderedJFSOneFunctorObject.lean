/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneRecognition
import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer
import MathlibExt.AlgebraicTopology.SimplicialSpace.WholePowerZeroOriginalMappingIso
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Actual functor objects on the original one-fold carrier

The object is the specified inverse image of the actual Cartesian Rezk power.
The existing monoidal equivalence transports its Cartesian adjunction, and the
proved Rezk power closure gives original local fibrancy. All original coefficient
universes are retained. The named closed structure is activated locally only.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian SimplicialSpace.Inner

namespace SimplicialPresheaf.OrderedJFS.OneFunctor

open SimplicialPresheaf.InjectiveKan

/-- The existing closed-category transport through the fixed one-fold equivalence.
This is a named value, with no global instance registration. -/
@[instance_reducible] def closed : MonoidalClosed (Original.{u} 1) := by
  let _ : oneDesignatedEquivalence.{u}.functor.Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact MonoidalClosed.ofEquiv oneDesignatedEquivalence.{u}.functor
    oneDesignatedEquivalence.{u}.toAdjunction

/-- The target functor of the specified inverse Cartesian power. -/
@[implicit_reducible] def objectFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ Original.{u} 1 :=
  oneDesignatedEquivalence.functor ⋙
    ihom (oneDesignatedEquivalence.functor.obj A) ⋙
      oneDesignatedEquivalence.inverse

/-- The full one-fold functor object, before any outer-zero or scalar evaluation. -/
@[implicit_reducible] def object (A Z : Original.{u} 1) : Original.{u} 1 := (objectFunctor A).obj Z

/-- Its original Cartesian tensor adjunction is the existing transported adjunction. -/
@[implicit_reducible] def adjunction (A : Original.{u} 1) : tensorLeft A ⊣ objectFunctor A :=
  (closed.closed A).adj

/-- The image is the actual Rezk power through the specified inverse counit. -/
def imageIso (A Z : Original.{u} 1) :
    oneDesignatedEquivalence.functor.obj (object A Z) ≅
      (ihom (oneDesignatedEquivalence.functor.obj A)).obj
        (oneDesignatedEquivalence.functor.obj Z) :=
  oneDesignatedEquivalence.counitIso.app _

/-- Actual evaluation is the Cartesian counit of this fixed adjunction. -/
@[implicit_reducible] def evaluation (A Z : Original.{u} 1) : A ⊗ object A Z ⟶ Z :=
  (adjunction A).counit.app Z

/-- The actual original Cartesian transpose into the full functor object. -/
@[implicit_reducible] def curry {A B Z : Original.{u} 1} (f : A ⊗ B ⟶ Z) : B ⟶ object A Z :=
  (adjunction A).homEquiv B Z f

/-- The inverse transpose uses the same Cartesian counit. -/
@[implicit_reducible] def uncurry {A B Z : Original.{u} 1} (f : B ⟶ object A Z) : A ⊗ B ⟶ Z :=
  ((adjunction A).homEquiv B Z).symm f

@[simp] theorem uncurry_curry {A B Z : Original.{u} 1} (f : A ⊗ B ⟶ Z) :
    uncurry (curry f) = f := ((adjunction A).homEquiv B Z).symm_apply_apply f

@[simp] theorem curry_uncurry {A B Z : Original.{u} 1} (f : B ⟶ object A Z) :
    curry (uncurry f) = f := ((adjunction A).homEquiv B Z).apply_symm_apply f

/-- The inverse transpose is the actual evaluation composite. -/
theorem uncurry_eq {A B Z : Original.{u} 1} (f : B ⟶ object A Z) :
    uncurry f = A ◁ f ≫ evaluation A Z :=
  Adjunction.homEquiv_counit (adjunction A) B Z f

@[reassoc (attr := simp)] theorem evaluation_curry {A B Z : Original.{u} 1}
    (f : A ⊗ B ⟶ Z) : A ◁ curry f ≫ evaluation A Z = f := by
  rw [← uncurry_eq, uncurry_curry]

/-- A target map acts through the same full Cartesian power. -/
@[implicit_reducible] def targetMap (A : Original.{u} 1) {Z V : Original.{u} 1} (g : Z ⟶ V) :
    object A Z ⟶ object A V := (objectFunctor A).map g

/-- Precomposition is preserved by the same inverse Cartesian transpose. -/
theorem uncurry_natural_left {A B C Z : Original.{u} 1}
    (f : B ⟶ C) (g : C ⟶ object A Z) :
    uncurry (f ≫ g) = A ◁ f ≫ uncurry g :=
  (adjunction A).homEquiv_naturality_left_symm f g

/-- Target maps are preserved by the same inverse Cartesian transpose. -/
theorem uncurry_natural_right {A B Z V : Original.{u} 1}
    (f : B ⟶ object A Z) (g : Z ⟶ V) :
    uncurry (f ≫ targetMap A g) = uncurry f ≫ g :=
  (adjunction A).homEquiv_naturality_right_symm f g

/-- A source map acts contravariantly through the same Cartesian adjunction. -/
@[implicit_reducible] def sourceMap {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    object B Z ⟶ object A Z := by
  let _ : MonoidalClosed (Original.{u} 1) := closed
  exact (MonoidalClosed.pre f).app Z

@[reassoc] theorem evaluation_source {A B : Original.{u} 1} (f : A ⟶ B)
    (Z : Original.{u} 1) :
    A ◁ sourceMap f Z ≫ evaluation A Z = f ▷ object B Z ≫ evaluation B Z := by
  let _ : MonoidalClosed (Original.{u} 1) := closed
  exact MonoidalClosed.id_tensor_pre_app_comp_ev f Z

@[simp] theorem sourceMap_id (A Z : Original.{u} 1) : sourceMap (𝟙 A) Z = 𝟙 _ := by
  let _ : MonoidalClosed (Original.{u} 1) := closed
  change (MonoidalClosed.pre (𝟙 A)).app Z = 𝟙 _
  simp

@[simp] theorem sourceMap_comp {A B C : Original.{u} 1} (f : A ⟶ B) (g : B ⟶ C)
    (Z : Original.{u} 1) : sourceMap (f ≫ g) Z = sourceMap g Z ≫ sourceMap f Z := by
  let _ : MonoidalClosed (Original.{u} 1) := closed
  exact congrArg (fun t => t.app Z) (MonoidalClosed.pre_map f g)

@[reassoc] theorem sourceMap_target {A B Z V : Original.{u} 1}
    (f : A ⟶ B) (g : Z ⟶ V) :
    sourceMap f Z ≫ targetMap A g = targetMap B g ≫ sourceMap f V := by
  let _ : MonoidalClosed (Original.{u} 1) := closed
  exact MonoidalClosed.pre_comm_ihom_map f g

/-- Precomposition in the source is the original evaluation transpose. -/
theorem uncurry_source {A B C Z : Original.{u} 1}
    (f : A ⟶ B) (g : C ⟶ object B Z) :
    uncurry (g ≫ sourceMap f Z) = f ▷ C ≫ uncurry g := by
  rw [uncurry_eq, uncurry_eq, whiskerLeft_comp, Category.assoc,
    evaluation_source, whisker_exchange_assoc]

/-- The forward Cartesian transpose has the same source-map law. -/
theorem curry_source {A B C Z : Original.{u} 1} (f : A ⟶ B) (g : B ⊗ C ⟶ Z) :
    curry (f ▷ C ≫ g) = curry g ≫ sourceMap f Z := by
  apply ((adjunction A).homEquiv C Z).symm.injective
  change uncurry (curry (f ▷ C ≫ g)) = uncurry (curry g ≫ sourceMap f Z)
  rw [uncurry_curry, uncurry_source, uncurry_curry]

@[reassoc] theorem evaluation_target (A : Original.{u} 1)
    {Z V : Original.{u} 1} (g : Z ⟶ V) :
    A ◁ targetMap A g ≫ evaluation A V = evaluation A Z ≫ g :=
  (adjunction A).counit.naturality g

@[reassoc] theorem imageIso_target (A : Original.{u} 1)
    {Z V : Original.{u} 1} (g : Z ⟶ V) :
    oneDesignatedEquivalence.functor.map (targetMap A g) ≫ (imageIso A V).hom =
      (imageIso A Z).hom ≫
        (ihom (oneDesignatedEquivalence.functor.obj A)).map
          (oneDesignatedEquivalence.functor.map g) :=
  oneDesignatedEquivalence.counitIso.hom.naturality _

/-- The proved Rezk power closure gives global original normalized local fibrancy. -/
theorem object_localFibrant (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant (originalFamily.{u} 1) Z) :
    isOriginalLocalFibrant (originalFamily.{u} 1) (object A Z) := by
  have hImage := TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal
    (oneDesignatedEquivalence.functor.obj A) (oneDesignatedEquivalence.functor.obj Z)
    ((one_locality_recognition Z).2.2.mp hZ)
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.RezkModel.modelCategory
  let _ : IsFibrant
      ((ihom (oneDesignatedEquivalence.functor.obj A)).obj
        (oneDesignatedEquivalence.functor.obj Z)) :=
    (SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces _).mpr hImage
  let _ : Fibration (imageIso A Z).hom := inferInstance
  exact (one_locality_recognition (object A Z)).2.2.mpr
    ((SimplicialSpace.RezkModel.isFibrant_iff_completeSegalSpaces _).mp
      (isFibrant_of_fibration (imageIso A Z).hom))

/-- The same object preserves the literal full original family as well. -/
theorem object_fullLocalFibrant (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant (fullOriginalFamily.{u} 1) Z) :
    isOriginalLocalFibrant (fullOriginalFamily.{u} 1) (object A Z) :=
  (one_locality_recognition (object A Z)).2.1.mpr
    ((one_locality_recognition (object A Z)).1.mp
      (object_localFibrant A Z ((one_locality_recognition Z).1.mpr
        ((one_locality_recognition Z).2.1.mp hZ))))

/-- A terminal source recovers the entire original target functor object. -/
def unitSourceNatIso : objectFunctor (𝟙_ (Original.{u} 1)) ≅ 𝟭 (Original.{u} 1) :=
  (adjunction (𝟙_ (Original.{u} 1))).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso (Original.{u} 1)).symm)

/-- The unit-source counit comparison holds on the same actual evaluation. -/
@[reassoc] theorem unitSource_evaluation (Z : Original.{u} 1) :
    (𝟙_ (Original.{u} 1)) ◁ unitSourceNatIso.hom.app Z ≫ (λ_ Z).hom =
      evaluation (𝟙_ (Original.{u} 1)) Z := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (adjunction (𝟙_ (Original.{u} 1)))
    (Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso (Original.{u} 1)).symm) Z
  change (𝟙_ (Original.{u} 1)) ◁ unitSourceNatIso.hom.app Z ≫
    ((λ_ Z).hom ≫ 𝟙 Z) = evaluation (𝟙_ (Original.{u} 1)) Z at h
  simpa only [Category.comp_id] using h

end SimplicialPresheaf.OrderedJFS.OneFunctor
