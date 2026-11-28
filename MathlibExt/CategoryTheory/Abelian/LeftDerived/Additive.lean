/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of projective resolutions and left-derived functors

The functor `projectiveResolutions C`, sending an object to (a choice of) its
projective resolution in the homotopy category, is additive. As a consequence,
the left-derived functors `F.leftDerived n` of an additive functor `F` are
additive.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v u

section

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

/-- The functor sending an object to a choice of projective resolution is
additive: the lift of a sum of morphisms is homotopic to the sum of the lifts. -/
instance projectiveResolutions_additive : Functor.Additive (projectiveResolutions C) where
  map_add {X Y f g} := by
    dsimp [projectiveResolutions]
    suffices h : (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (f + g) (projectiveResolution X)
          (projectiveResolution Y)) =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
         ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) by
      rw [h]
      exact (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map_add
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftHomotopy (f + g)
    · exact ProjectiveResolution.lift_commutes (f + g) _ _
    · rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes f,
          ProjectiveResolution.lift_commutes g,
          ← Preadditive.comp_add, ← Functor.map_add]

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type*} [Category* D] [Abelian D]

/-- The left-derived functors of an additive functor are additive. -/
instance leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

end

end CategoryTheory

noncomputable section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [HasProjectiveResolutions C]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Left derivation preserves sums of natural transformations. -/
@[simp]
theorem leftDerived_add (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n =
      NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  let P := projectiveResolution X
  rw [NatTrans.app_add, ProjectiveResolution.leftDerived_app_eq (α + β) P n,
    ProjectiveResolution.leftDerived_app_eq α P n,
    ProjectiveResolution.leftDerived_app_eq β P n]
  have h : (NatTrans.mapHomologicalComplex (α + β) (ComplexShape.down ℕ)).app
        P.complex =
      (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex +
        (NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app P.complex := by
    ext i
    rfl
  rw [h, Functor.map_add]
  rw [Preadditive.add_comp, Preadditive.comp_add]

/-- Left derivation preserves the zero natural transformation. -/
@[simp]
theorem leftDerived_zero (n : ℕ) :
    NatTrans.leftDerived (0 : F ⟶ G) n = 0 := by
  have h := leftDerived_add (0 : F ⟶ G) 0 n
  simpa only [zero_add, add_eq_left] using h.symm

end CategoryTheory.NatTrans

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable (D : Type u₃) [Category.{v₃} D] [Abelian D]

/-- Left derivation in degree `n`, functorial in the additive input functor. -/
def leftDerivedDegreeFunctor (n : ℕ) : (C ⥤+ D) ⥤ (C ⥤ D) where
  obj F := F.obj.leftDerived n
  map α := NatTrans.leftDerived α.hom n
  map_id F := by
    change NatTrans.leftDerived (𝟙 F.obj) n = 𝟙 (F.obj.leftDerived n)
    exact NatTrans.leftDerived_id F.obj n
  map_comp α β := by
    change NatTrans.leftDerived (α.hom ≫ β.hom) n =
      NatTrans.leftDerived α.hom n ≫ NatTrans.leftDerived β.hom n
    exact NatTrans.leftDerived_comp α.hom β.hom n

/-- The parameter functor sends an additive functor to its degree-`n` left-derived functor. -/
@[simp]
theorem leftDerivedDegreeFunctor_obj (n : ℕ) (F : C ⥤+ D) :
    (leftDerivedDegreeFunctor C D n).obj F = F.obj.leftDerived n := rfl

/-- The parameter functor sends natural transformations to their degree-`n` derived transformations. -/
@[simp]
theorem leftDerivedDegreeFunctor_map (n : ℕ) {F G : C ⥤+ D} (α : F ⟶ G) :
    (leftDerivedDegreeFunctor C D n).map α = NatTrans.leftDerived α.hom n := rfl

/-- Derivation in one degree is additive on the category of additive functors. -/
instance leftDerivedDegreeFunctor_additive (n : ℕ) :
    (leftDerivedDegreeFunctor C D n).Additive where
  map_add {F G} α β := by
    change NatTrans.leftDerived (α.hom + β.hom) n =
      NatTrans.leftDerived α.hom n + NatTrans.leftDerived β.hom n
    exact NatTrans.leftDerived_add (F := F.obj) (G := G.obj) α.hom β.hom n

end CategoryTheory

end
