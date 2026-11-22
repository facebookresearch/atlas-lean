/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveBasedNative.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.OriginalClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Generators
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Quillen

/-!
# Full classes and free adjunctions of strict chosen-base native diagrams

Use the exact strict restriction/extension equivalence. Every class is on
the literal original mapped arrow. Both original-cardinal systems retain
the full non-base free families and their actual Hom adjunctions.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The entire strict source free functor at the original native label. -/
def strictFreeAt (a : A) : PointedCGWH.{u, v} ⥤ StrictCarrier (A := A) :=
  NativePresentation.transportedFree strictEquivalence a

/-- The exact original non-base evaluation of a literal strict diagram. -/
def strictEvaluation (a : A) : StrictCarrier (A := A) ⥤ PointedCGWH.{u, v} :=
  NativePresentation.transportedEvaluation strictEquivalence a

/-- The real native free adjunction through the proved strict source equivalence. -/
def strictFreeAdjunction (a : A) : strictFreeAt a ⊣ strictEvaluation a :=
  NativePresentation.transportedAdjunction strictEquivalence a

/-- Literal full source I-family labels and their original base arrows. -/
def strictBoundaryGenerators : MorphismProperty (StrictCarrier (A := A)) :=
  MorphismProperty.adjointFamilyGenerators strictFreeAt
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- Literal full source J-family labels and their original base arrows. -/
def strictHornGenerators : MorphismProperty (StrictCarrier (A := A)) :=
  MorphismProperty.adjointFamilyGenerators strictFreeAt
    PointedCGWH.realizedHornInclusions.{u, v}

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Actual strict source weak equivalences are detected on all original non-base components. -/
theorem strict_weakEquivalences_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    weakEquivalences (StrictCarrier (A := A)) f ↔
      ∀ a : A, weakEquivalences PointedCGWH.{u, v} ((strictEvaluation a).map f) :=
  NativePresentation.weakEquivalences_iff_original strictEquivalence
    id Function.surjective_id strictEvaluation (fun _ => Iso.refl _) f

/-- Actual strict source fibrations are detected on all original non-base components. -/
theorem strict_fibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    fibrations (StrictCarrier (A := A)) f ↔
      ∀ a : A, fibrations PointedCGWH.{u, v} ((strictEvaluation a).map f) :=
  NativePresentation.fibrations_iff_original strictEquivalence
    id Function.surjective_id strictEvaluation (fun _ => Iso.refl _) f

/-- The complete source intersection class is detected on all original non-base components. -/
theorem strict_trivialFibrations_iff {F G : StrictCarrier (A := A)} (f : F ⟶ G) :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    trivialFibrations (StrictCarrier (A := A)) f ↔
      ∀ a : A, trivialFibrations PointedCGWH.{u, v} ((strictEvaluation a).map f) :=
  NativePresentation.trivialFibrations_iff_original strictEquivalence
    id Function.surjective_id strictEvaluation (fun _ => Iso.refl _) f

/-- Actual strict source cofibrations use the whole original free-I lifting class. -/
theorem strict_cofibrations_eq :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    cofibrations (StrictCarrier (A := A)) = strictBoundaryGenerators.rlp.llp :=
  NativePresentation.cofibrations_eq_originalGenerators strictEquivalence
    id Function.surjective_id strictFreeAt strictEvaluation strictFreeAdjunction
    (fun _ => Iso.refl _)

/-- Actual strict source trivial cofibrations use the whole original free-J lifting class. -/
theorem strict_trivialCofibrations_eq :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    trivialCofibrations (StrictCarrier (A := A)) = strictHornGenerators.rlp.llp :=
  NativePresentation.trivialCofibrations_eq_originalGenerators strictEquivalence
    id Function.surjective_id strictFreeAt strictEvaluation strictFreeAdjunction
    (fun _ => Iso.refl _)

/-- The actual source free adjunction is Quillen without a source model as an input. -/
theorem strict_freeAdjunction_isQuillen (a : A) :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    (strictFreeAdjunction a).IsQuillenAdjunction :=
  NativePresentation.originalFreeEvaluation_isQuillenAdjunction strictEquivalence
    a (strictFreeAt a) (strictEvaluation a) (strictFreeAdjunction a) (Iso.refl _)

/-- The actual κ/I source class and all original right-map components are retained. -/
theorem strictCofibrantFactorizationData_classes
    (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    strictBoundaryGenerators.rlp.llp ((strictCofibrantFactorizationData (A := A)).i.app f) ∧
      ∀ a : A, trivialFibrations PointedCGWH.{u, v}
        ((strictEvaluation a).map ((strictCofibrantFactorizationData (A := A)).p.app f)) := by
  let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty (StrictCarrier (A := A)) =>
    P ((strictCofibrantFactorizationData (A := A)).i.app f)) strict_cofibrations_eq)
      ((strictCofibrantFactorizationData (A := A)).hi f),
    (strict_trivialFibrations_iff _).mp ((strictCofibrantFactorizationData (A := A)).hp f)⟩

/-- The actual κ/J source class and all original right-map components are retained. -/
theorem strictFibrantFactorizationData_classes
    (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    strictHornGenerators.rlp.llp ((strictFibrantFactorizationData (A := A)).i.app f) ∧
      ∀ a : A, fibrations PointedCGWH.{u, v}
        ((strictEvaluation a).map ((strictFibrantFactorizationData (A := A)).p.app f)) := by
  let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty (StrictCarrier (A := A)) =>
    P ((strictFibrantFactorizationData (A := A)).i.app f)) strict_trivialCofibrations_eq)
      ((strictFibrantFactorizationData (A := A)).hi f),
    (strict_fibrations_iff _).mp ((strictFibrantFactorizationData (A := A)).hp f)⟩

end HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation
