/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FlatBundleMonodromyModels

/-!
# Wanted actual local-system and flat-bundle monodromy constructions

The stalk transport and fibre evaluation are fixed on every actual
local section and path. The fundamental groupoid and its path classes
are native. This supplies the monodromy operation of the same actual
flat connection used by the compact Kähler Higgs comparison.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
open MathlibExt.AlgebraicGeometry.FlatBundleMonodromyModels
open scoped Manifold ContDiff

variable {M : Type} [TopologicalSpace M]

/-- Local coefficient-frame sections give the actual normalized stalk coordinates. -/
def_wanted native_local_system_stalk_coordinates (G : CoefficientSheaf (M := M))
    (U : Opens M) (r : ℕ) (F : LocalCoefficientFrame G U r) (x : M) (hx : x ∈ U) :
  LocalStalkCoordinates F x hx

/-- The same actual locally constant sheaf has native path-groupoid transport fixed on every local path. -/
def_wanted native_local_system_monodromy (G : CoefficientSheaf (M := M))
    (h : LocallyConstantFinite G) : StalkMonodromySource G

/-- Actual flat horizontal sections form the same finite locally constant coefficient sheaf. -/
theorem_wanted native_flat_horizontal_locally_constant (n : ℕ) [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (r : ℕ) (B : SmoothComplexBundle n M r) (A : SmoothConnection B)
    [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    (hA : IsFlat B A) : LocallyConstantFinite (horizontalSheaf B A.value)

/-- The actual horizontal germ is evaluated in the actual native bundle fibre. -/
def_wanted native_flat_horizontal_stalk_realization (n : ℕ) [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (r : ℕ) (B : SmoothComplexBundle n M r) (A : SmoothConnection B)
    [SectionCalculus B A.value] [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    (hA : IsFlat B A) (x : M) : FlatStalkRealization B A x
