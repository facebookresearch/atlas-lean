/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.Monoidal.ModLimits
import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SymmetricSpectrum

/-!
# Tests for limits of module objects

Symmetric spectra, the modules over the sphere symmetric sequence, have all limits, in
particular the products and equalizers used for spectral ends. The projections of the limit
of module objects are module maps over the limit projections of the underlying objects.
-/

open CategoryTheory Limits MonoidalCategory MathlibExt.CategoryTheory.ModLimits

/-- Symmetric spectra have all limits. -/
example : HasLimits MathlibExt.SpectraSource.SymmetricSpectrum := inferInstance

/-- In particular they have equalizers and products. -/
example : HasEqualizers MathlibExt.SpectraSource.SymmetricSpectrum := inferInstance

example : HasProducts.{0} MathlibExt.SpectraSource.SymmetricSpectrum := inferInstance

/-- The limit projections of module objects are the underlying limit projections. -/
example {C : Type*} [Category C] [MonoidalCategory C] {A : C} [MonObj A] {J : Type*}
    [Category J] (F : J ⥤ Mod C A) [HasLimit (F ⋙ Mod.forget (D := C) A)] (j : J) :
    ((limitCone F).π.app j).hom = limit.π (F ⋙ Mod.forget (D := C) A) j :=
  rfl
