/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.EssentialIndex
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Fixed original-index model, generation and chosen-factor contracts -/
set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.FunctorProjective

namespace MathlibExtTest.EssentialProjectiveIndex

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S] [LocallySmall.{w} S]
  (e : D ≌ S) (d : CofibrantGenerationData M κ)

example : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D :=
  EssentialIndex.weakEquivalences_eq e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    fibrations (D ⥤ M) = (fibrations M).functorCategory D :=
  EssentialIndex.fibrations_eq e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D :=
  EssentialIndex.trivialFibrations_eq e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp :=
  EssentialIndex.cofibrations_eq e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  EssentialIndex.trivialCofibrations_eq e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  EssentialIndex.five_classes e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    CofibrantGenerationData (D ⥤ M) κ :=
  EssentialIndex.generationData e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).I = Representatives.family e d d.I :=
  EssentialIndex.generationData_I e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).J = Representatives.family e d d.J :=
  EssentialIndex.generationData_J e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).I_smallObject = Representatives.familyI_eligible e d :=
  EssentialIndex.generationData_I_smallObject e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).J_smallObject = Representatives.familyJ_eligible e d :=
  EssentialIndex.generationData_J_smallObject e d

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).I.isoClosure = (freeGenerators d d.I).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact EssentialIndex.generationData_I_isoClosure e d

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).J.isoClosure = (freeGenerators d d.J).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact EssentialIndex.generationData_J_isoClosure e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).I.rlp.llp = cofibrations (D ⥤ M) :=
  EssentialIndex.generationData_I_left e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.generationData e d).J.rlp.llp = trivialCofibrations (D ⥤ M) :=
  EssentialIndex.generationData_J_left e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  EssentialIndex.cofibrantFactorizationData e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  EssentialIndex.fibrantFactorizationData e d

example (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    ((EssentialIndex.cofibrantFactorizationData e d).i.app f).app x ≫
      ((EssentialIndex.cofibrantFactorizationData e d).p.app f).app x = f.hom.app x :=
  EssentialIndex.cofibrantFactorizationData_fac_app e d f x

example (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    ((EssentialIndex.fibrantFactorizationData e d).i.app f).app x ≫
      ((EssentialIndex.fibrantFactorizationData e d).p.app f).app x = f.hom.app x :=
  EssentialIndex.fibrantFactorizationData_fac_app e d f x

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.cofibrantFactorizationData e d).Z =
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.cofibrantFactorizationData (D := S) d).Z ⋙
          (e.congrLeft (E := M)).inverse :=
  EssentialIndex.cofibrantFactorizationData_Z e d

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.fibrantFactorizationData e d).Z =
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.fibrantFactorizationData (D := S) d).Z ⋙
          (e.congrLeft (E := M)).inverse :=
  EssentialIndex.fibrantFactorizationData_Z e d

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    EssentialIndex.cofibrantFactorizationData e d =
      (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalence
        (e.congrLeft (E := M)) :=
  EssentialIndex.cofibrantFactorizationData_eq_transport e d

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    EssentialIndex.fibrantFactorizationData e d =
      (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalence
        (e.congrLeft (E := M)) :=
  EssentialIndex.fibrantFactorizationData_eq_transport e d

example :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    IsWeakFactorizationSystem (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) ∧
      IsWeakFactorizationSystem (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  EssentialIndex.weakFactorizationSystems e d

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.cofibrantFactorizationData e d).i.app f =
      (e.congrLeft (E := M)).unit.app f.left ≫
        (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) :=
  EssentialIndex.cofibrantFactorizationData_i e d f

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.fibrantFactorizationData e d).p.app f =
      (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.fibrantFactorizationData (D := S) d).p.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
        (e.congrLeft (E := M)).unitInv.app f.right :=
  EssentialIndex.fibrantFactorizationData_p e d f

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (fun f : Arrow (D ⥤ M) => (EssentialIndex.cofibrantFactorizationData e d).i.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).unit.app f.left ≫
          (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) :=
  EssentialIndex.cofibrantFactorizationData_i_function e d

example :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (fun f : Arrow (D ⥤ M) => (EssentialIndex.fibrantFactorizationData e d).p.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.fibrantFactorizationData (D := S) d).p.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
          (e.congrLeft (E := M)).unitInv.app f.right :=
  EssentialIndex.fibrantFactorizationData_p_function e d

example {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    a.left ≫ (EssentialIndex.cofibrantFactorizationData e d).i.app g =
      (EssentialIndex.cofibrantFactorizationData e d).i.app f ≫
        (EssentialIndex.cofibrantFactorizationData e d).Z.map a :=
  EssentialIndex.cofibrantFactorizationData_i_naturality e d a

example {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    a.left.app x ≫ ((EssentialIndex.cofibrantFactorizationData e d).i.app g).app x =
      ((EssentialIndex.cofibrantFactorizationData e d).i.app f).app x ≫
        ((EssentialIndex.cofibrantFactorizationData e d).Z.map a).app x :=
  EssentialIndex.cofibrantFactorizationData_i_naturality_app e d a x

example {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    ((EssentialIndex.fibrantFactorizationData e d).Z.map a).app x ≫
        ((EssentialIndex.fibrantFactorizationData e d).p.app g).app x =
      ((EssentialIndex.fibrantFactorizationData e d).p.app f).app x ≫ a.right.app x :=
  EssentialIndex.fibrantFactorizationData_p_naturality_app e d a x

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.cofibrantFactorizationData e d).Z.map (𝟙 f) =
      𝟙 ((EssentialIndex.cofibrantFactorizationData e d).Z.obj f) :=
  EssentialIndex.cofibrantFactorizationData_map_id e d f

example {f g k : Arrow (D ⥤ M)} (a : f ⟶ g) (b : g ⟶ k) :
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.fibrantFactorizationData e d).Z.map (a ≫ b) =
      (EssentialIndex.fibrantFactorizationData e d).Z.map a ≫
        (EssentialIndex.fibrantFactorizationData e d).Z.map b :=
  EssentialIndex.fibrantFactorizationData_map_comp e d a b

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (e.congrLeft (E := M)).functor.map ((EssentialIndex.cofibrantFactorizationData e d).i.app f) ≫
        (EssentialIndex.cofibrantZComparisonIso e d).hom.app f =
      (FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
        ((e.congrLeft (E := M)).functor.mapArrow.obj f) :=
  EssentialIndex.cofibrantFactorizationData_mapped_i e d f

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.fibrantZComparisonIso e d).hom.app f ≫
        (FunctorProjective.fibrantFactorizationData (D := S) d).p.app
          ((e.congrLeft (E := M)).functor.mapArrow.obj f) =
      (e.congrLeft (E := M)).functor.map ((EssentialIndex.fibrantFactorizationData e d).p.app f) :=
  EssentialIndex.fibrantFactorizationData_mapped_p e d f

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (EssentialIndex.cofibrantZComparisonIso e d).hom.app f ≫
        (FunctorProjective.cofibrantFactorizationData (D := S) d).p.app
          ((e.congrLeft (E := M)).functor.mapArrow.obj f) =
      (e.congrLeft (E := M)).functor.map
        ((EssentialIndex.cofibrantFactorizationData e d).p.app f) :=
  EssentialIndex.cofibrantFactorizationData_mapped_p e d f

example (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := EssentialIndex.modelCategory e d
    (e.congrLeft (E := M)).functor.map ((EssentialIndex.fibrantFactorizationData e d).i.app f) ≫
        (EssentialIndex.fibrantZComparisonIso e d).hom.app f =
      (FunctorProjective.fibrantFactorizationData (D := S) d).i.app
        ((e.congrLeft (E := M)).functor.mapArrow.obj f) :=
  EssentialIndex.fibrantFactorizationData_mapped_i e d f

/-- The stock original index category is used after raising its object universe. -/
local instance raisedObjectCategory : Category.{vS} (ULift.{uS + 1} S) := uliftCategory S
/-- The stock original Hom category is used after an independent Hom universe raise. -/
local instance raisedHomCategory :
    Category.{max (vS + 1) vS} (ULiftHom.{vS + 1} (ULift.{uS + 1} S)) :=
  @ULiftHom.category (ULift.{uS + 1} S) (inferInstance : Category.{vS} (ULift.{uS + 1} S))

example :
    let raised := (ULiftHomULiftCategory.equiv.{vS + 1, uS + 1} S).symm
    letI : ModelCategory (ULiftHom.{vS + 1} (ULift.{uS + 1} S) ⥤ M) :=
      EssentialIndex.modelCategory raised d
    CofibrantGenerationData (ULiftHom.{vS + 1} (ULift.{uS + 1} S) ⥤ M) κ := by
  let raised := (ULiftHomULiftCategory.equiv.{vS + 1, uS + 1} S).symm
  exact EssentialIndex.generationData raised d

example :
    ModelCategory (Discrete PEmpty.{w + 1} ⥤ M) :=
  EssentialIndex.modelCategory (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{w + 1})) d

example : ModelCategory (Discrete ℕ ⥤ M) :=
  EssentialIndex.modelCategory (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) d

example : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
  EssentialIndex.modelCategory (κ := κ)
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) d

end MathlibExtTest.EssentialProjectiveIndex
