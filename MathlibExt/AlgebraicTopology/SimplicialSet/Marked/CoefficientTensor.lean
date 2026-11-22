/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientModel
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ScalarQuillen

/-!
# Original maximal scalar tensors in the actual marked coefficient model

The point-slice equivalence changes only the unique base projection.
Both tensor arrows have the same full marked product and component map;
the identity total-carrier isomorphism identifies their original point
projections. The proved native scalar Quillen restriction over the point
therefore gives genuine coefficient cofibration and weak-mono
preservation for every scalar, with no Kan-source assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] coefficientMarkedModelCategory

/-- The actual point-slice scalar tensor retains the same whole marked product and original arrow. -/
def coefficientTensorArrowIso (K : SSet.{u}) {A D : Marked.{u}} (f : A ⟶ D) :
    Arrow.mk (coefficientPointEquivalence.functor.map (prodMap (𝟙 (max K)) f)) ≅
      Arrow.mk ((overScalarTensor (max (Δ[0] : SSet.{u})) K).map
        (coefficientPointEquivalence.functor.map f)) :=
  Arrow.isoMk
    (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
    (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
    (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)

/-- The genuine original coefficient cofibration class is exactly marked monomorphisms. -/
theorem coefficientMarkedCofibrations_eq : cofibrations Marked.{u} = monomorphisms Marked.{u} := by
  ext A D f
  change Mono (coefficientPointEquivalence.functor.map f) ↔ Mono f
  constructor
  · intro h
    exact coefficientPointEquivalence.functor.mono_of_mono_map h
  · intro h
    let _ : Mono f := h
    infer_instance

/-- Every original coefficient cofibration remains a cofibration under its same maximal scalar tensor,
  without any scalar fibrancy hypothesis. -/
theorem coefficientMaxTensor_preserves_cofibrations {A D : Marked.{u}} (f : A ⟶ D)
    (hf : cofibrations Marked.{u} f) (K : SSet.{u}) :
    cofibrations Marked.{u} (prodMap (𝟙 (max K)) f) := by
  let _ := markedCofibrationStructure (max (Δ[0] : SSet.{u}))
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedWeakStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedModelCategory (Δ[0] : SSet.{u})
  change cofibrations (Over (max (Δ[0] : SSet.{u}))) (coefficientPointEquivalence.functor.map f) at hf
  let _ : Mono (coefficientPointEquivalence.functor.map f) := hf
  have ht : cofibrations (Over (max (Δ[0] : SSet.{u})))
      ((overScalarTensor (max (Δ[0] : SSet.{u})) K).map (coefficientPointEquivalence.functor.map f)) :=
    overScalarTensorMap_mono _ K
  exact ((cofibrations (Over (max (Δ[0] : SSet.{u})))).arrow_mk_iso_iff
    (coefficientTensorArrowIso K f)).mpr ht

/-- The same original full marked weak-mono class is preserved by every maximal scalar tensor, retaining the
  actual complete coefficient arrow. -/
theorem coefficientMaxTensor_preserves_trivialCofibrations {A D : Marked.{u}} (f : A ⟶ D)
    (hf : trivialCofibrations Marked.{u} f) (K : SSet.{u}) :
    trivialCofibrations Marked.{u} (prodMap (𝟙 (max K)) f) := by
  let _ := markedCofibrationStructure (max (Δ[0] : SSet.{u}))
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedWeakStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedModelCategory (Δ[0] : SSet.{u})
  change cartesianTestingTrivialCofibrations (Δ[0] : SSet.{u})
    (coefficientPointEquivalence.functor.map f) at hf
  have ht := overScalarTensor_cartesian_weakMono (coefficientPointEquivalence.functor.map f) hf K
  change trivialCofibrations (Over (max (Δ[0] : SSet.{u})))
      ((overScalarTensor (max (Δ[0] : SSet.{u})) K).map (coefficientPointEquivalence.functor.map f)) at ht
  exact ((trivialCofibrations (Over (max (Δ[0] : SSet.{u})))).arrow_mk_iso_iff
    (coefficientTensorArrowIso K f)).mpr ht

end SSet.Marked
