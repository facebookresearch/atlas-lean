/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Basic
public import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
public import MathlibExt.Topology.Category.CGWH.Limits

/-!
# Canonical free spectra and evaluated colimits

The suspension coordinate is arbitrary. Free generation and its adjunction
are the actual enriched free/evaluation pair. Colimits and evaluation
preservation are the existing genuine pointwise construction at the same
native size. No spectrum-model or Day-convolution data is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CGWH.limits MonoidalClosed

namespace PointedCGWH.SequentialSpectrum

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Free native spectra over an arbitrary coordinate use the actual enriched free functor. -/
noncomputable def freeAt (K : PointedCGWH.{u, v}) (n : ℕ) :
    PointedCGWH.{u, v} ⥤ CategoryTheory.Spectra.Sequential.Spectrum K :=
  CategoryTheory.Spectra.Sequential.freeAt K n

/-- Native free generation is left adjoint to the actual canonical level evaluation. -/
noncomputable def freeAtEvaluationAdjunction (K : PointedCGWH.{u, v}) (n : ℕ) :
    freeAt K n ⊣ CategoryTheory.Spectra.Sequential.evaluation K n :=
  CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction K n

/-- The whole constructed free/evaluation pair retains its actual left triangle. -/
theorem freeAtEvaluationAdjunction_left_triangle_components
    (K : PointedCGWH.{u, v}) (n : ℕ) (A : PointedCGWH.{u, v}) :
    (freeAt K n).map ((freeAtEvaluationAdjunction K n).unit.app A) ≫
      (freeAtEvaluationAdjunction K n).counit.app ((freeAt K n).obj A) =
      𝟙 ((freeAt K n).obj A) :=
  (freeAtEvaluationAdjunction K n).left_triangle_components A

/-- The actual functor carrier has native colimits of size `(v, v)` for every coordinate. -/
theorem hasColimitsOfSize (K : PointedCGWH.{u, v}) :
    HasColimitsOfSize.{v, v} (CategoryTheory.Spectra.Sequential.Spectrum K) :=
  inferInstance

/-- Every actual canonical degree evaluation preserves native colimits of the same size. -/
theorem evaluation_preservesColimitsOfSize (K : PointedCGWH.{u, v}) (n : ℕ) :
    PreservesColimitsOfSize.{v, v}
      (CategoryTheory.Spectra.Sequential.evaluation K n) :=
  inferInstance

end PointedCGWH.SequentialSpectrum
