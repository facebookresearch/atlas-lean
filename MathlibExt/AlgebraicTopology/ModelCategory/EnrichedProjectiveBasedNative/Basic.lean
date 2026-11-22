/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.FreeEvaluation
import MathlibExt.CategoryTheory.Enriched.ZeroCompletionBasedDiagram
import MathlibExt.Topology.Category.PointedCGWH.Zero

/-!
# Native models on complete and strict chosen-base diagrams

The actual restriction/extension and strict-normalization equivalences
construct these models and their original-cardinal data. A strict diagram
has literal equality at the chosen zero object; a complete diagram is kept
as its separate carrier. No source-model or desired equivalence is an input.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- Genuine native diagrams on the actual completed enriched index. -/
abbrev CompletedCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} (EnrichedZeroCompletion PointedCGWH.{u, v} A)

/-- The literal chosen-zero full subcategory of completed native diagrams. -/
abbrev StrictCarrier := EnrichedZeroCompletion.BasedDiagram (V := PointedCGWH.{u, v}) (A := A)

/-- The entire actual completed-diagram restriction/extension equivalence. -/
def completedEquivalence : CompletedCarrier (A := A) ≌ EnrichedFunctorCat PointedCGWH.{u, v} A :=
  EnrichedZeroCompletion.diagramEquivalence.symm

/-- The entire actual strict chosen-base restriction/extension equivalence. -/
def strictEquivalence : StrictCarrier (A := A) ≌ EnrichedFunctorCat PointedCGWH.{u, v} A :=
  EnrichedZeroCompletion.basedDiagramEquivalence.symm

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual native model on completed diagrams through its proved complete equivalence. -/
@[instance_reducible]
def completedModelCategory : ModelCategory (CompletedCarrier (A := A)) :=
  NativePresentation.modelCategory completedEquivalence

/-- The actual native model on literal strict chosen-base diagrams. -/
@[instance_reducible]
def strictModelCategory : ModelCategory (StrictCarrier (A := A)) :=
  NativePresentation.modelCategory strictEquivalence

/-- The original κ/I data on the entire completed-diagram carrier. -/
def completedCofibrantFactorizationData :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    FunctorialFactorizationData (cofibrations (CompletedCarrier (A := A)))
      (trivialFibrations (CompletedCarrier (A := A))) :=
  NativePresentation.cofibrantFactorizationData completedEquivalence

/-- The original κ/J data on the entire completed-diagram carrier. -/
def completedFibrantFactorizationData :
    let _ : ModelCategory (CompletedCarrier (A := A)) := completedModelCategory
    FunctorialFactorizationData (trivialCofibrations (CompletedCarrier (A := A)))
      (fibrations (CompletedCarrier (A := A))) :=
  NativePresentation.fibrantFactorizationData completedEquivalence

/-- The original κ/I data on the literal strict chosen-base carrier. -/
def strictCofibrantFactorizationData :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    FunctorialFactorizationData (cofibrations (StrictCarrier (A := A)))
      (trivialFibrations (StrictCarrier (A := A))) :=
  NativePresentation.cofibrantFactorizationData strictEquivalence

/-- The original κ/J data on the literal strict chosen-base carrier. -/
def strictFibrantFactorizationData :
    let _ : ModelCategory (StrictCarrier (A := A)) := strictModelCategory
    FunctorialFactorizationData (trivialCofibrations (StrictCarrier (A := A)))
      (fibrations (StrictCarrier (A := A))) :=
  NativePresentation.fibrantFactorizationData strictEquivalence

/-- The whole strict I middle functor uses actual restriction, original κ and strict extension. -/
theorem strictCofibrantFactorizationData_Z :
    (strictCofibrantFactorizationData (A := A)).Z =
      EnrichedZeroCompletion.strictRestriction.mapArrow ⋙
        (Native.cofibrantFactorizationData (A := A)).Z ⋙
          EnrichedZeroCompletion.strictExtension := rfl

/-- The whole strict J middle functor uses actual restriction, original κ and strict extension. -/
theorem strictFibrantFactorizationData_Z :
    (strictFibrantFactorizationData (A := A)).Z =
      EnrichedZeroCompletion.strictRestriction.mapArrow ⋙
        (Native.fibrantFactorizationData (A := A)).Z ⋙
          EnrichedZeroCompletion.strictExtension := rfl

/-- Every computed strict I middle diagram preserves the chosen base literally. -/
theorem strictCofibrantFactorizationData_base (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    ((strictCofibrantFactorizationData (A := A)).Z.obj f).obj.toEnrichedFunctor.obj
      EnrichedZeroCompletion.zero = (0 : PointedCGWH.{u, v}) :=
  ((strictCofibrantFactorizationData (A := A)).Z.obj f).property

/-- Every computed strict J middle diagram preserves the chosen base literally. -/
theorem strictFibrantFactorizationData_base (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    ((strictFibrantFactorizationData (A := A)).Z.obj f).obj.toEnrichedFunctor.obj
      EnrichedZeroCompletion.zero = (0 : PointedCGWH.{u, v}) :=
  ((strictFibrantFactorizationData (A := A)).Z.obj f).property

/-- The strict I data factor the same caller's entire original diagram arrow. -/
theorem strictCofibrantFactorizationData_fac (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    (strictCofibrantFactorizationData (A := A)).i.app f ≫
      (strictCofibrantFactorizationData (A := A)).p.app f = f.hom :=
  NativePresentation.cofibrantFactorizationData_fac strictEquivalence f

/-- The strict J data factor the same caller's entire original diagram arrow. -/
theorem strictFibrantFactorizationData_fac (f : CategoryTheory.Arrow (StrictCarrier (A := A))) :
    (strictFibrantFactorizationData (A := A)).i.app f ≫
      (strictFibrantFactorizationData (A := A)).p.app f = f.hom :=
  NativePresentation.fibrantFactorizationData_fac strictEquivalence f

end HomotopicalAlgebra.EnrichedProjective.BasedNativePresentation
