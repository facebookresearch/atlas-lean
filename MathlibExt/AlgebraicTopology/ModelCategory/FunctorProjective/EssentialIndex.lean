/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Representatives
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# The original projective package through a genuine small index

The input is the actual original-index equivalence and one supplied base
generation datum. The small-side model is the existing projective construction.
Its inverse-image classes are transported with the stock model transport.
The original category receives small representative generators and the same
actual small-side factor values, preserving every original Arrow and component.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective.EssentialIndex

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} S] [LocallySmall.{w} S]

/-- The weak class is the literal inverse image of the actual original small-side model. -/
def weakProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    MorphismProperty (D ⥤ M) :=
  MorphismProperty.inverseImage
    (FunctorProjective.modelCategory (J := S) d).categoryWithWeakEquivalences.weakEquivalences
     (e.congrLeft (E := M)).functor

/-- The cofibration class is the literal inverse image of the same small-side model. -/
def cofibrationProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    MorphismProperty (D ⥤ M) :=
  (FunctorProjective.modelCategory (J := S) d).categoryWithCofibrations.cofibrations.inverseImage
     (e.congrLeft (E := M)).functor

/-- The fibration class is the literal inverse image of that same actual small-side model. -/
def fibrationProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    MorphismProperty (D ⥤ M) :=
  (FunctorProjective.modelCategory (J := S) d).categoryWithFibrations.fibrations.inverseImage
     (e.congrLeft (E := M)).functor

/-- Construct the original-index model using only the existing stock equivalence transport. -/
@[instance_reducible]
def modelCategory (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    ModelCategory (D ⥤ M) := by
  letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  letI : CategoryWithCofibrations (D ⥤ M) := ⟨cofibrationProperty e d⟩
  letI : CategoryWithFibrations (D ⥤ M) := ⟨fibrationProperty e d⟩
  letI : CategoryWithWeakEquivalences (D ⥤ M) := ⟨weakProperty e d⟩
  exact ModelCategory.transport (e.congrLeft (E := M)) rfl rfl rfl

/-- The constructed weak class retains the entire original inverse-image field. -/
theorem modelCategory_weakProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    (modelCategory e d).categoryWithWeakEquivalences.weakEquivalences = weakProperty e d := rfl

/-- The constructed cofibrations retain the entire original inverse-image field. -/
theorem modelCategory_cofibrationProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    (modelCategory e d).categoryWithCofibrations.cofibrations = cofibrationProperty e d := rfl

/-- The constructed fibrations retain the entire original inverse-image field. -/
theorem modelCategory_fibrationProperty (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    (modelCategory e d).categoryWithFibrations.fibrations = fibrationProperty e d := rfl

/-- Original weak equivalences are detected on every original object. -/
theorem weakEquivalences_eq (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  change (weakEquivalences (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor = _
  exact (congrArg (fun P : MorphismProperty (S ⥤ M) =>
    P.inverseImage (e.congrLeft (E := M)).functor)
    (FunctorProjective.weakEquivalences_eq d)).trans
      (functorCategory_inverseImage_congrLeft e (weakEquivalences M))

/-- Original fibrations are detected on every original object. -/
theorem fibrations_eq (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    fibrations (D ⥤ M) = (fibrations M).functorCategory D := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  change (fibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor = _
  exact (congrArg (fun P : MorphismProperty (S ⥤ M) =>
    P.inverseImage (e.congrLeft (E := M)).functor)
    (FunctorProjective.fibrations_eq d)).trans
      (functorCategory_inverseImage_congrLeft e (fibrations M))

/-- Original trivial fibrations retain the exact transported intersection class. -/
theorem trivialFibrations_inverseImage (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    trivialFibrations (D ⥤ M) =
      (trivialFibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor := rfl

/-- Original trivial fibrations are exactly all-original objectwise base trivial fibrations. -/
theorem trivialFibrations_eq (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  change (trivialFibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor = _
  exact (congrArg (fun P : MorphismProperty (S ⥤ M) =>
    P.inverseImage (e.congrLeft (E := M)).functor)
    (FunctorProjective.trivialFibrations_eq d)).trans
      (functorCategory_inverseImage_congrLeft e (trivialFibrations M))

/-- Original cofibrations are the complete left lifting class of original objectwise TFibs. -/
theorem cofibrations_eq (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  change (cofibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor = _
  exact (congrArg (fun P : MorphismProperty (S ⥤ M) =>
    P.inverseImage (e.congrLeft (E := M)).functor)
    (FunctorProjective.cofibrations_eq_objectwise_llp d)).trans
      (functorCategory_llp_inverseImage_congrLeft e (trivialFibrations M))

/-- Original trivial cofibrations retain the exact transported intersection class. -/
theorem trivialCofibrations_inverseImage (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    trivialCofibrations (D ⥤ M) =
      (trivialCofibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor := rfl

/-- Original trivial cofibrations are the complete left lifting class of objectwise Fib. -/
theorem trivialCofibrations_eq (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  change (trivialCofibrations (S ⥤ M)).inverseImage (e.congrLeft (E := M)).functor = _
  exact (congrArg (fun P : MorphismProperty (S ⥤ M) =>
    P.inverseImage (e.congrLeft (E := M)).functor)
    (FunctorProjective.trivialCofibrations_eq_objectwise_llp d)).trans
      (functorCategory_llp_inverseImage_congrLeft e (fibrations M))

/-- All five classes belong to the same constructed original-index projective model. -/
theorem five_classes (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  ⟨weakEquivalences_eq e d, fibrations_eq e d, trivialFibrations_eq e d,
    cofibrations_eq e d, trivialCofibrations_eq e d⟩


/-- The actual representative I right class is the same constructed model's TFib class. -/
theorem representativeI_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (Representatives.family e d d.I).rlp = trivialFibrations (D ⥤ M) := by
  rw [Representatives.family_rlp, d.I_rlp, trivialFibrations_eq e d]

/-- The actual representative J right class is the same constructed model's Fib class. -/
theorem representativeJ_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (Representatives.family e d d.J).rlp = fibrations (D ⥤ M) := by
  rw [Representatives.family_rlp, d.J_rlp, fibrations_eq e d]

/-- The original projective generation data uses the actual small representative families. -/
def generationData (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    CofibrantGenerationData (D ⥤ M) κ := by
  letI : ModelCategory (D ⥤ M) := modelCategory e d
  exact
    { I := Representatives.family e d d.I
      J := Representatives.family e d d.J
      I_smallObject := Representatives.familyI_eligible e d
      J_smallObject := Representatives.familyJ_eligible e d
      I_rlp := representativeI_rlp e d
      J_rlp := representativeJ_rlp e d }

/-- The returned I family retains the actual representative labels and original base I. -/
theorem generationData_I (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).I = Representatives.family e d d.I := rfl

/-- The returned J family retains the actual representative labels and original base J. -/
theorem generationData_J (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).J = Representatives.family e d d.J := rfl

/-- The returned I eligibility is the same actual original representative dictionary. -/
theorem generationData_I_smallObject (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).I_smallObject = Representatives.familyI_eligible e d := rfl

/-- The returned J eligibility is the same actual original representative dictionary. -/
theorem generationData_J_smallObject (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).J_smallObject = Representatives.familyJ_eligible e d := rfl

/-- Returned I retains the entire original free-image isomorphism saturation. -/
theorem generationData_I_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).I.isoClosure = (freeGenerators d d.I).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact Representatives.family_isoClosure e d d.I

/-- Returned J retains the entire original free-image isomorphism saturation. -/
theorem generationData_J_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).J.isoClosure = (freeGenerators d d.J).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact Representatives.family_isoClosure e d d.J

/-- Every original free-I lifting test is the returned model's full trivial-fibration class. -/
theorem allOriginalI_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (freeGenerators d d.I).rlp = trivialFibrations (D ⥤ M) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [freeGenerators_rlp, d.I_rlp, trivialFibrations_eq e d]

/-- Every original free-J lifting test is the returned model's full fibration class. -/
theorem allOriginalJ_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (freeGenerators d d.J).rlp = fibrations (D ⥤ M) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [freeGenerators_rlp, d.J_rlp, fibrations_eq e d]

/-- The returned I left class is the complete original projective cofibration class. -/
theorem generationData_I_left (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).I.rlp.llp = cofibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  rw [generationData_I, representativeI_rlp e d, trivialFibrations_llp]

/-- The returned J left class is the complete original projective trivial-cofibration class. -/
theorem generationData_J_left (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (generationData e d).J.rlp.llp = trivialCofibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  rw [generationData_J, representativeJ_rlp e d, fibrations_llp]


/-- Pull back the existing small-side cofibrant factor value with the same original equivalence. -/
def cofibrantFactorizationData (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) := by
  letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  letI : ModelCategory (D ⥤ M) := modelCategory e d
  exact (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalence
     (e.congrLeft (E := M))

/-- Pull back the existing small-side fibrant factor value with that same κ and datum. -/
def fibrantFactorizationData (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  letI : ModelCategory (D ⥤ M) := modelCategory e d
  exact (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalence
     (e.congrLeft (E := M))

/-- The entire cofibrant middle functor is the actual original inverse of the same small value. -/
theorem cofibrantFactorizationData_Z (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z =
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.cofibrantFactorizationData (D := S) d).Z ⋙
          (e.congrLeft (E := M)).inverse := rfl

/-- The entire fibrant middle functor is the actual original inverse of the same small value. -/
theorem fibrantFactorizationData_Z (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z =
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.fibrantFactorizationData (D := S) d).Z ⋙
          (e.congrLeft (E := M)).inverse := rfl

/-- Every original cofibrant Arrow factors at every original object. -/
theorem cofibrantFactorizationData_fac_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    ((cofibrantFactorizationData e d).i.app f).app x ≫
      ((cofibrantFactorizationData e d).p.app f).app x = f.hom.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  have h : (cofibrantFactorizationData e d).i.app f ≫
      (cofibrantFactorizationData e d).p.app f = f.hom :=
    (cofibrantFactorizationData e d).fac_app
  exact congrArg (fun a : f.left ⟶ f.right => a.app x) h

/-- Every original fibrant Arrow factors at every original object. -/
theorem fibrantFactorizationData_fac_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    ((fibrantFactorizationData e d).i.app f).app x ≫
      ((fibrantFactorizationData e d).p.app f).app x = f.hom.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  have h : (fibrantFactorizationData e d).i.app f ≫
      (fibrantFactorizationData e d).p.app f = f.hom :=
    (fibrantFactorizationData e d).fac_app
  exact congrArg (fun a : f.left ⟶ f.right => a.app x) h

/-- Every original cofibrant intermediate object is the same inverse small-side object. -/
theorem cofibrantFactorizationData_obj (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z.obj f =
      (e.congrLeft (E := M)).inverse.obj
        ((FunctorProjective.cofibrantFactorizationData (D := S) d).Z.obj
          ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- Every original fibrant intermediate object is the same inverse small-side object. -/
theorem fibrantFactorizationData_obj (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z.obj f =
      (e.congrLeft (E := M)).inverse.obj
        ((FunctorProjective.fibrantFactorizationData (D := S) d).Z.obj
          ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- The whole cofibrant left transformation retains its original unit and small-side value. -/
theorem cofibrantFactorizationData_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).i.app f =
      (e.congrLeft (E := M)).unit.app f.left ≫
        (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- The whole cofibrant right transformation retains its original inverse unit and small value. -/
theorem cofibrantFactorizationData_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).p.app f =
      (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.cofibrantFactorizationData (D := S) d).p.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
        (e.congrLeft (E := M)).unitInv.app f.right := rfl

/-- The whole fibrant left transformation retains its original unit and small-side value. -/
theorem fibrantFactorizationData_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).i.app f =
      (e.congrLeft (E := M)).unit.app f.left ≫
        (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.fibrantFactorizationData (D := S) d).i.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- The whole fibrant right transformation retains its original inverse unit and small value. -/
theorem fibrantFactorizationData_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).p.app f =
      (e.congrLeft (E := M)).inverse.map
          ((FunctorProjective.fibrantFactorizationData (D := S) d).p.app
            ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
        (e.congrLeft (E := M)).unitInv.app f.right := rfl

/-- Every original cofibrant Arrow-square map is the exact inverse of the same small-side map. -/
theorem cofibrantFactorizationData_map (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z.map a =
      (e.congrLeft (E := M)).inverse.map
        ((FunctorProjective.cofibrantFactorizationData (D := S) d).Z.map
          ((e.congrLeft (E := M)).functor.mapArrow.map a)) := rfl

/-- Every original fibrant Arrow-square map is the exact inverse of the same small-side map. -/
theorem fibrantFactorizationData_map (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z.map a =
      (e.congrLeft (E := M)).inverse.map
        ((FunctorProjective.fibrantFactorizationData (D := S) d).Z.map
          ((e.congrLeft (E := M)).functor.mapArrow.map a)) := rfl

/-- The original cofibrant i-leg retains every actual Arrow square. -/
theorem cofibrantFactorizationData_i_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    a.left ≫ (cofibrantFactorizationData e d).i.app g =
      (cofibrantFactorizationData e d).i.app f ≫ (cofibrantFactorizationData e d).Z.map a :=
  (cofibrantFactorizationData e d).i.naturality a

/-- The original cofibrant p-leg retains every actual Arrow square. -/
theorem cofibrantFactorizationData_p_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z.map a ≫ (cofibrantFactorizationData e d).p.app g =
      (cofibrantFactorizationData e d).p.app f ≫ a.right :=
  (cofibrantFactorizationData e d).p.naturality a

/-- The original fibrant i-leg retains every actual Arrow square. -/
theorem fibrantFactorizationData_i_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    a.left ≫ (fibrantFactorizationData e d).i.app g =
      (fibrantFactorizationData e d).i.app f ≫ (fibrantFactorizationData e d).Z.map a :=
  (fibrantFactorizationData e d).i.naturality a

/-- The original fibrant p-leg retains every actual Arrow square. -/
theorem fibrantFactorizationData_p_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z.map a ≫ (fibrantFactorizationData e d).p.app g =
      (fibrantFactorizationData e d).p.app f ≫ a.right :=
  (fibrantFactorizationData e d).p.naturality a

/-- The original cofibrant middle functor retains every identity Arrow. -/
theorem cofibrantFactorizationData_map_id (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z.map (𝟙 f) = 𝟙 ((cofibrantFactorizationData e d).Z.obj f) :=
  (cofibrantFactorizationData e d).Z.map_id f

/-- The original fibrant middle functor retains every identity Arrow. -/
theorem fibrantFactorizationData_map_id (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z.map (𝟙 f) = 𝟙 ((fibrantFactorizationData e d).Z.obj f) :=
  (fibrantFactorizationData e d).Z.map_id f

/-- The original cofibrant middle functor retains every composed Arrow square. -/
theorem cofibrantFactorizationData_map_comp (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g k : Arrow (D ⥤ M)} (a : f ⟶ g) (b : g ⟶ k) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z.map (a ≫ b) =
      (cofibrantFactorizationData e d).Z.map a ≫ (cofibrantFactorizationData e d).Z.map b :=
  (cofibrantFactorizationData e d).Z.map_comp a b

/-- The original fibrant middle functor retains every composed Arrow square. -/
theorem fibrantFactorizationData_map_comp (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g k : Arrow (D ⥤ M)} (a : f ⟶ g) (b : g ⟶ k) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z.map (a ≫ b) =
      (fibrantFactorizationData e d).Z.map a ≫ (fibrantFactorizationData e d).Z.map b :=
  (fibrantFactorizationData e d).Z.map_comp a b

/-- Every original source component retains the actual cofibrant i-leg naturality. -/
theorem cofibrantFactorizationData_i_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    a.left.app x ≫ ((cofibrantFactorizationData e d).i.app g).app x =
      ((cofibrantFactorizationData e d).i.app f).app x ≫
        ((cofibrantFactorizationData e d).Z.map a).app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  exact congrArg (fun h : f.left ⟶ (cofibrantFactorizationData e d).Z.obj g => h.app x)
    (cofibrantFactorizationData_i_naturality e d a)

/-- Every original source component retains the actual cofibrant p-leg naturality. -/
theorem cofibrantFactorizationData_p_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    ((cofibrantFactorizationData e d).Z.map a).app x ≫
        ((cofibrantFactorizationData e d).p.app g).app x =
      ((cofibrantFactorizationData e d).p.app f).app x ≫ a.right.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  exact congrArg (fun h : (cofibrantFactorizationData e d).Z.obj f ⟶ g.right => h.app x)
    (cofibrantFactorizationData_p_naturality e d a)

/-- Every original source component retains the actual fibrant i-leg naturality. -/
theorem fibrantFactorizationData_i_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    a.left.app x ≫ ((fibrantFactorizationData e d).i.app g).app x =
      ((fibrantFactorizationData e d).i.app f).app x ≫
        ((fibrantFactorizationData e d).Z.map a).app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  exact congrArg (fun h : f.left ⟶ (fibrantFactorizationData e d).Z.obj g => h.app x)
    (fibrantFactorizationData_i_naturality e d a)

/-- Every original source component retains the actual fibrant p-leg naturality. -/
theorem fibrantFactorizationData_p_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    ((fibrantFactorizationData e d).Z.map a).app x ≫
        ((fibrantFactorizationData e d).p.app g).app x =
      ((fibrantFactorizationData e d).p.app f).app x ≫ a.right.app x := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  exact congrArg (fun h : (fibrantFactorizationData e d).Z.obj f ⟶ g.right => h.app x)
    (fibrantFactorizationData_p_naturality e d a)

/-- The entire cofibrant record is exactly the existing transported small-side factor value. -/
theorem cofibrantFactorizationData_eq_transport (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    cofibrantFactorizationData e d =
      (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalence
        (e.congrLeft (E := M)) := rfl

/-- The entire fibrant record is exactly the existing transported small-side factor value. -/
theorem fibrantFactorizationData_eq_transport (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    fibrantFactorizationData e d =
      (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalence
        (e.congrLeft (E := M)) := rfl

/-- The whole cofibrant left function retains every actual original Arrow input. -/
theorem cofibrantFactorizationData_i_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fun f : Arrow (D ⥤ M) => (cofibrantFactorizationData e d).i.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).unit.app f.left ≫
          (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- The whole cofibrant right function retains every actual original Arrow input. -/
theorem cofibrantFactorizationData_p_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fun f : Arrow (D ⥤ M) => (cofibrantFactorizationData e d).p.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.cofibrantFactorizationData (D := S) d).p.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
          (e.congrLeft (E := M)).unitInv.app f.right := rfl

/-- The whole fibrant left function retains every actual original Arrow input. -/
theorem fibrantFactorizationData_i_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fun f : Arrow (D ⥤ M) => (fibrantFactorizationData e d).i.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).unit.app f.left ≫
          (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.fibrantFactorizationData (D := S) d).i.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) := rfl

/-- The whole fibrant right function retains every actual original Arrow input. -/
theorem fibrantFactorizationData_p_function (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fun f : Arrow (D ⥤ M) => (fibrantFactorizationData e d).p.app f) =
      fun f : Arrow (D ⥤ M) =>
        (e.congrLeft (E := M)).inverse.map
            ((FunctorProjective.fibrantFactorizationData (D := S) d).p.app
              ((e.congrLeft (E := M)).functor.mapArrow.obj f)) ≫
          (e.congrLeft (E := M)).unitInv.app f.right := rfl

/-- The actual small-side counit compares the whole original cofibrant middle functor. -/
def cofibrantZComparisonIso (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantFactorizationData e d).Z ⋙ (e.congrLeft (E := M)).functor ≅
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.cofibrantFactorizationData (D := S) d).Z := by
  letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalenceZComparisonIso
     (e.congrLeft (E := M))

/-- The same actual counit compares the whole original fibrant middle functor. -/
def fibrantZComparisonIso (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantFactorizationData e d).Z ⋙ (e.congrLeft (E := M)).functor ≅
      (e.congrLeft (E := M)).functor.mapArrow ⋙
        (FunctorProjective.fibrantFactorizationData (D := S) d).Z := by
  letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalenceZComparisonIso
     (e.congrLeft (E := M))

/-- The actual cofibrant left component recovers the same small-side value under its counit. -/
theorem cofibrantFactorizationData_mapped_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (e.congrLeft (E := M)).functor.map ((cofibrantFactorizationData e d).i.app f) ≫
        (cofibrantZComparisonIso e d).hom.app f =
      (FunctorProjective.cofibrantFactorizationData (D := S) d).i.app
        ((e.congrLeft (E := M)).functor.mapArrow.obj f) := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalence_mapped_i
     (e.congrLeft (E := M)) f

/-- The actual cofibrant right component recovers the same small-side value under its counit. -/
theorem cofibrantFactorizationData_mapped_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (cofibrantZComparisonIso e d).hom.app f ≫
        (FunctorProjective.cofibrantFactorizationData (D := S) d).p.app
          ((e.congrLeft (E := M)).functor.mapArrow.obj f) =
      (e.congrLeft (E := M)).functor.map ((cofibrantFactorizationData e d).p.app f) := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.cofibrantFactorizationData (D := S) d).ofEquivalence_mapped_p
     (e.congrLeft (E := M)) f

/-- The actual fibrant left component recovers the same small-side value under its counit. -/
theorem fibrantFactorizationData_mapped_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (e.congrLeft (E := M)).functor.map ((fibrantFactorizationData e d).i.app f) ≫
        (fibrantZComparisonIso e d).hom.app f =
      (FunctorProjective.fibrantFactorizationData (D := S) d).i.app
        ((e.congrLeft (E := M)).functor.mapArrow.obj f) := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalence_mapped_i
     (e.congrLeft (E := M)) f

/-- The actual fibrant right component recovers the same small-side value under its counit. -/
theorem fibrantFactorizationData_mapped_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    (fibrantZComparisonIso e d).hom.app f ≫
        (FunctorProjective.fibrantFactorizationData (D := S) d).p.app
          ((e.congrLeft (E := M)).functor.mapArrow.obj f) =
      (e.congrLeft (E := M)).functor.map ((fibrantFactorizationData e d).p.app f) := by
  let _ : ModelCategory (S ⥤ M) := FunctorProjective.modelCategory (J := S) d
  exact (FunctorProjective.fibrantFactorizationData (D := S) d).ofEquivalence_mapped_p
     (e.congrLeft (E := M)) f

/-- Both WFSs belong to the actual constructed original model, without an incoming WFS tuple. -/
theorem weakFactorizationSystems (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : ModelCategory (D ⥤ M) := modelCategory e d
    IsWeakFactorizationSystem (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) ∧
      IsWeakFactorizationSystem (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory e d
  exact ⟨inferInstance, inferInstance⟩

end HomotopicalAlgebra.FunctorProjective.EssentialIndex
