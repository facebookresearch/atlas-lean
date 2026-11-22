/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerCombinedSmallObject
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerGeneratingFibrations

/-!
# The same original countable Bergner factorization

The intermediate object, inclusion, projection and every functorial
map are literally the original native small-object construction for
the full original A1/A2 family. Its actual full relative cell complex
is genuinely acyclic, and its exact right class is the original
full-Hom Kan/component-isofibration class.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
namespace NativeFactorization

/-- The original native combined-generator inclusion is genuinely C0 cofibrant and DK weak. -/
theorem left_cofibration_weak {C D : Carrier.{u}} (f : C ⟶ D) :
    (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences)
      (SmallObject.ιObj generatingTrivialCofibrations Cardinal.aleph0 f) :=
  relativeCellComplex_cofibration_weak.{u, u, u, u + 1} _
    (SmallObject.relativeCellComplexιObj generatingTrivialCofibrations Cardinal.aleph0 f)
      (fun s => s.i.2)

/-- The original native combined-generator projection is in the full original canonical Bergner fibration class. -/
theorem right_localFibration {C D : Carrier.{u}} (f : C ⟶ D) :
    Bergner.localFibrations
      (SmallObject.πObj generatingTrivialCofibrations Cardinal.aleph0 f) :=
  (generatingTrivialCofibrations_rlp_iff _).mp
    (SmallObject.rlp_πObj generatingTrivialCofibrations Cardinal.aleph0 f)

/-- The complete original native factorization has its genuinely proved original weak/cofibration and fibration classes.
-/
def data {C D : Carrier.{u}} (f : C ⟶ D) :
    MorphismProperty.MapFactorizationData
      (Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) Bergner.localFibrations f where
  Z := SmallObject.obj generatingTrivialCofibrations Cardinal.aleph0 f
  i := SmallObject.ιObj generatingTrivialCofibrations Cardinal.aleph0 f
  p := SmallObject.πObj generatingTrivialCofibrations Cardinal.aleph0 f
  fac := SmallObject.ιObj_πObj generatingTrivialCofibrations Cardinal.aleph0 f
  hi := left_cofibration_weak f
  hp := right_localFibration f

/-- Read back the same entire original native intermediate enrichment. -/
theorem object_original {C D : Carrier.{u}} (f : C ⟶ D) :
    (data f).Z = SmallObject.obj generatingTrivialCofibrations Cardinal.aleph0 f := rfl

/-- Read back the same entire original native inclusion functor. -/
theorem left_original {C D : Carrier.{u}} (f : C ⟶ D) :
    (data f).i = SmallObject.ιObj generatingTrivialCofibrations Cardinal.aleph0 f := rfl

/-- Read back the same entire original native projection functor. -/
theorem right_original {C D : Carrier.{u}} (f : C ⟶ D) :
    (data f).p = SmallObject.πObj generatingTrivialCofibrations Cardinal.aleph0 f := rfl

/-- Both entire original native factor maps compose to the same input functor. -/
theorem fac {C D : Carrier.{u}} (f : C ⟶ D) : (data f).i ≫ (data f).p = f := (data f).fac

/-- The same complete original native inclusion is in the original combined-generator left class. -/
theorem left_mem {C D : Carrier.{u}} (f : C ⟶ D) :
    generatingTrivialCofibrations.rlp.llp (data f).i :=
  SmallObject.llp_rlp_ιObj generatingTrivialCofibrations Cardinal.aleph0 f

/-- The same complete original native projection is in the original combined-generator right class. -/
theorem right_mem {C D : Carrier.{u}} (f : C ⟶ D) :
    generatingTrivialCofibrations.rlp (data f).p :=
  SmallObject.rlp_πObj generatingTrivialCofibrations Cardinal.aleph0 f

end NativeFactorization
end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
