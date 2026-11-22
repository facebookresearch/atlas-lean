/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.TensorFlatnessOfReplacementCounits
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeAllObjectSpectrumMonoidAxiom

/-!
# Cofibrant tensor flatness in the symmetric stable model

In the specified symmetric stable model, smashing an arbitrary stable weak equivalence with
a cofibrant spectrum preserves stable weakness. The result holds for both left and right
smash factors, with the right-factor formula obtained through the braiding. The same
conclusion is expressed by the original Ω-test class, and the replacement functor and counit
remain the specified ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.OriginalCofibrantTensorFlatness

private abbrev C := Actual.SymmetricCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

private abbrev Q := StableModelConstruction.symmetricCofibrantReplacement (B := B)
private abbrev ε := StableModelConstruction.symmetricCofibrantReplacementCounit (B := B)

/-- The original symmetric stable model on the actual native carrier. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.symmetricModelCategory (B := B)

local instance originalStableMonoidal : IsClosedSymmetricMonoidalModelCategory C.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableSmashMonoidalModel (B := B)

/-- Both entire replacement functors and natural arrows remain the original chosen values. -/
theorem replacement_values :
    Q (B := B) = StableModelConstruction.symmetricCofibrantReplacement (B := B) ∧
      ε (B := B) = StableModelConstruction.symmetricCofibrantReplacementCounit (B := B) := ⟨rfl, rfl⟩

/-- Every original weak map, with arbitrary endpoints, remains weak under any original cofibrant left factor. -/
theorem originalStableCofibrantSmash_weak {Y Z : C.{u, v}} (f : Y ⟶ Z) (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := StableModelConstruction.symmetricModelCategory (B := B)
    weakEquivalences C.{u, v} f → IsCofibrant X → weakEquivalences C.{u, v} (X ◁ f) :=
  PointedCGWH.Spectra.Symmetric.OriginalCofibrantFlatness.originalStableCofibrantSmash_weak f X

/-- The full Omega-test formulation uses the literal original five-class equality. -/
theorem originalStableCofibrantSmash_omegaTests {Y Z : C.{u, v}} (f : Y ⟶ Z)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v} f) (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := StableModelConstruction.symmetricModelCategory (B := B)
    IsCofibrant X → NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v} (X ◁ f) := by
  change IsCofibrant X → NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v} (X ◁ f)
  intro hX
  have hf' : weakEquivalences C.{u, v} f := by
    rw [(StableModelConstruction.symmetric_five_classes (B := B)).1]
    exact hf
  have h := originalStableCofibrantSmash_weak f X hf' hX
  rw [(StableModelConstruction.symmetric_five_classes (B := B)).1] at h
  exact h

/-- The original whole Arrow braid gives the right coefficient order required by free-I module tensors. -/
theorem originalStableCofibrantRightTensor_weak {Y Z : C.{u, v}} (f : Y ⟶ Z) (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := StableModelConstruction.symmetricModelCategory (B := B)
    weakEquivalences C.{u, v} f → IsCofibrant X → weakEquivalences C.{u, v} (f ▷ X) := by
  change weakEquivalences C.{u, v} f → IsCofibrant X → weakEquivalences C.{u, v} (f ▷ X)
  intro hf hX
  exact HomotopicalAlgebra.TensorFlatnessOfReplacementCounits.rightTensor_weak_of_leftTensor f X
    (originalStableCofibrantSmash_weak f X hf hX)

end PointedCGWH.Spectra.Symmetric.OriginalCofibrantTensorFlatness
