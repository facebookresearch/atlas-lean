/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModels

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.NativeKummerFlatModels` -/

noncomputable section

open CategoryTheory
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogStructures
open MathlibExt.AlgebraicGeometry.NativeKummerFlatModels
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes

namespace MathlibExtTest.AlgebraicGeometry.NativeKummerFlatModels

/-- A chart in the units, `ℕ → 0`, does not have a Kummer chart map. Such a chart makes the
chart comparison of a nonflat strict closed immersion (`Spec 𝔽₂ → Spec ℤ`, generator `-1`) an
isomorphism, so log-flat atlases exclude it. -/
example : ¬ IsKummerMonoidMap
    (CommMonCat.ofHom (1 : Multiplicative ℕ →* Multiplicative Unit)) := by
  intro h
  have e := h.1 (a₁ := (Multiplicative.ofAdd (0 : ℕ) : Multiplicative ℕ))
    (a₂ := (Multiplicative.ofAdd (1 : ℕ) : Multiplicative ℕ)) (Subsingleton.elim _ _)
  exact absurd (congrArg Multiplicative.toAdd e) (by decide)

/-- Log-flat atlases carry Kummer chart maps. -/
example [InverseImageTheory.{0}] (D : RegularSectionComparisons)
    {X Y : LogScheme.{0}} {f : EtaleLogSchemes.Hom X Y} (A : LogFlatAtlas D f) (i : A.index) :
    IsKummerMonoidMap (CommMonCat.ofHom (A.chartMap i).monoidMap) :=
  A.chart_kummer i

end MathlibExtTest.AlgebraicGeometry.NativeKummerFlatModels

end
