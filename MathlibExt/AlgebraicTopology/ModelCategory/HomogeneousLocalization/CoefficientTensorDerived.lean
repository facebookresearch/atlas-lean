/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.HomogeneousLocalization.CoefficientTensorQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.HomogeneousLocalization.DerivedAdjointTelescope
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.ScalarChange

/-!
# The original coefficient beta adjunction and its actual derived diagram

The original full module transfer supplies the model, generating rank and
both complete chosen replacement factories.  The actual ambient coefficient
tensor-Hom adjunction is Quillen for cofibrant U.  These original constructors
produce the full derived adjunction, the original derived beta action, and
the natural comparison of the whole fibrant point-set beta diagram with the
derived diagram.  All ordinary source maps, Q/R maps and transitions remain
the actual maps of the original coefficient action.

The source does not assert a tensor inverse, beta locality, a relative
derived tensor formula or a Kan localization universal property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

open CategoryTheory Limits MorphismProperty MonoidalCategory
open CategoryTheory.HomogeneousLocalization
open CategoryTheory.SmallObject
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.CoefficientTensorDerived

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [MonoidAxiom.{w} C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [HasEqualizers C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (R : CommMon C) (U : C) [IsCofibrant U]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (sI : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators R.toMon I))
  (sJ : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators R.toMon J))

/-- The ordinary module model is the actual output of the original full transfer. -/
abbrev moduleModel : ModelCategory (Mod C R.X) :=
  (CoefficientTensorQuillen.transfer R I J hI hJ sI sJ).model

/-- The original transfer rank and both original generating families construct these same Q/R factors. -/
def replacements :
    letI := moduleModel R I J hI hJ sI sJ
    GeneratedFunctorialReplacements.Data (C := Mod C R.X) := by
  letI := moduleModel R I J hI hJ sI sJ
  exact ModuleTransfer.ScalarChange.replacementsOfTransfer
    (CoefficientTensorQuillen.transfer R I J hI hJ sI sJ)

/-- The full actual derived adjunction retains all four original derived conditions and comparisons. -/
def derivedAdjunctionData :
    letI := moduleModel R I J hI hJ sI sJ
    QuillenDerivedAdjunctionData (CoefficientTensorHom.adjunction R U) := by
  letI := moduleModel R I J hI hJ sI sJ
  letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
  exact DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (CoefficientTensorHom.adjunction R U)
    (replacements R I J hI hJ sI sJ) (replacements R I J hI hJ sI sJ)

variable (b : U ⟶ R.X)

/-- The original central beta action derives through the same source-ranked Q. -/
def beta :
    letI := moduleModel R I J hI hJ sI sJ
    letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
    DerivedFunctorCoherence.left (CoefficientTensorHom.adjunction R U) (replacements R I J hI hJ sI sJ) ⟶
      𝟭 (weakEquivalences (Mod C R.X)).Localization := by
  letI := moduleModel R I J hI hJ sI sJ
  letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
  exact HomogeneousDerivedAdjointTelescope.beta (CoefficientTensorHom.adjunction R U)
    (replacements R I J hI hJ sI sJ) (CoefficientTensorHom.betaAction R U b)

/-- The whole beta adjunct is derived using the actual chosen Q/R adjunction. -/
def coaugmentation :
    letI := moduleModel R I J hI hJ sI sJ
    letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
    𝟭 (weakEquivalences (Mod C R.X)).Localization ⟶
      DerivedFunctorCoherence.right (CoefficientTensorHom.adjunction R U) (replacements R I J hI hJ sI sJ) := by
  letI := moduleModel R I J hI hJ sI sJ
  letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
  exact HomogeneousDerivedAdjointTelescope.coaugmentation (CoefficientTensorHom.adjunction R U)
    (replacements R I J hI hJ sI sJ) (replacements R I J hI hJ sI sJ) (CoefficientTensorHom.betaAction R U b)

/-- Every represented transition is the original coefficient adjunct followed by the actual right comparison. -/
theorem coaugmentation_projection (M : Mod C R.X) :
    letI := moduleModel R I J hI hJ sI sJ
    letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
    (coaugmentation R U I J hI hJ sI sJ b).app ((weakEquivalences (Mod C R.X)).Q.obj M) =
      (weakEquivalences (Mod C R.X)).Q.map ((CoefficientTensorHom.coaugmentation R U b).app M) ≫
        (DerivedFunctorCoherence.rightComparison (CoefficientTensorHom.adjunction R U)
          (replacements R I J hI hJ sI sJ)).app M := by
  let _ := moduleModel R I J hI hJ sI sJ
  let _ := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
  exact HomogeneousDerivedAdjointTelescope.coaugmentation_projection (CoefficientTensorHom.adjunction R U)
    (replacements R I J hI hJ sI sJ) (replacements R I J hI hJ sI sJ) (CoefficientTensorHom.betaAction R U b) M

/-- The actual fibrant starting module uses the original J replacement and every original input map. -/
def nativeDiagramFunctor :
    letI := moduleModel R I J hI hJ sI sJ
    Mod C R.X ⥤ (ℕ ⥤ Mod C R.X) := by
  letI := moduleModel R I J hI hJ sI sJ
  exact (replacements R I J hI hJ sI sJ).R ⋙ CoefficientTensorHom.betaDiagramFunctor R U b

/-- The actual derived diagram keeps each current-stage derived beta adjunct. -/
def derivedDiagramFunctor :
    letI := moduleModel R I J hI hJ sI sJ
    (weakEquivalences (Mod C R.X)).Localization ⥤ (ℕ ⥤ (weakEquivalences (Mod C R.X)).Localization) := by
  letI := moduleModel R I J hI hJ sI sJ
  exact AdjointTelescope.diagramFunctor (coaugmentation R U I J hI hJ sI sJ b)

/-- The complete original fibrant beta diagram agrees naturally with the full derived beta diagram. -/
def diagramComparison :
    letI := moduleModel R I J hI hJ sI sJ
    nativeDiagramFunctor R U I J hI hJ sI sJ b ⋙
        (Functor.whiskeringRight ℕ (Mod C R.X) (weakEquivalences (Mod C R.X)).Localization).obj
          (weakEquivalences (Mod C R.X)).Q ≅
      (weakEquivalences (Mod C R.X)).Q ⋙ derivedDiagramFunctor R U I J hI hJ sI sJ b := by
  letI := moduleModel R I J hI hJ sI sJ
  letI := CoefficientTensorQuillen.isQuillenAdjunction R U I J hI hJ sI sJ
  exact HomogeneousDerivedAdjointTelescope.diagramComparison (CoefficientTensorHom.adjunction R U)
    (replacements R I J hI hJ sI sJ) (replacements R I J hI hJ sI sJ) (CoefficientTensorHom.betaAction R U b)

end HomotopicalAlgebra.CoefficientTensorDerived
