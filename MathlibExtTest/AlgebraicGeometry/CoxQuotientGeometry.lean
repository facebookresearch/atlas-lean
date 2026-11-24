/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

/-!
# Tests for the localization charts of the Cox open

Every point of the Cox open lies in the localization chart of some cone, and
each chart composed with the inclusion is the localization map of spectra.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.CoxGradedSheaves
open MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

/-- The charts cover the Cox open. -/
example {n : ℕ} {F : FiniteFan n} (R : Rays F) (x : (openScheme R).left) :
    ∃ σ : F.Face, x ∈ Set.range ((localCover R).map σ).left :=
  (localCover R).cover x

/-- Each chart is the localization at the denominator of its cone. -/
example {n : ℕ} {F : FiniteFan n} (R : Rays F) (σ : F.Face) :
    ((localCover R).map σ).left ≫ (inclusion R).left =
      Spec.map (CommRingCat.ofHom (algebraMap (CoxRing R) (LocalRing R σ.val))) :=
  (localCover R).normalized σ
