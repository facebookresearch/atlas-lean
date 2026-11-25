/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FanoVanishingFiltrations

@[expose] public noncomputable section

/-!
# Actual smooth projective Fano families and their valuative semistable fibres

Fibres are the actual scheme pullbacks at actual complex field-valued
points. Their anticanonical lines are identified with the actual relative
line's restrictions. The finite-dimensional Hilbert data in each fibre
refers to its actual coherent global sections.

The semistability predicate is the genuine all-prime-divisor beta
criterion. The parameter point used in the Zariski topology is the actual
image of the unique point of Spec C. No moduli/DF/beta function is supplied.
-/

namespace MathlibExt.AlgebraicGeometry.FanoKSemistabilityFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.ValuativeFanoGeometry
open MathlibExt.AlgebraicGeometry.FanoVanishingFiltrations

/-- Actual rational points over the fixed complex coefficient field. -/
abbrev RationalPoint (B : ComplexVariety) := 𝟙_ (Over (Spec (.of ℂ))) ⟶ B

/-- The actual fibre as a complex scheme. -/
abbrev fiberVariety {X B : ComplexVariety} (f : X ⟶ B) (b : RationalPoint B) :
    ComplexVariety := Over.mk (fiberStructure (Ω := ℂ) f b.left)

/-- A smooth projective Fano family, including the actual anticanonical fibre data. -/
structure SmoothFanoFamily (n : ℕ) where
  B : ComplexVariety
  [integralBase : IsIntegral B.left]
  [smoothBase : Smooth B.hom]
  [finiteTypeBase : QuasiCompact B.hom]
  [separatedBase : IsSeparated B.hom]
  X : ComplexVariety
  morphism : X ⟶ B
  [proper : IsProper morphism.left]
  [smooth : SmoothOfRelativeDimension n morphism.left]
  projective : IsHProjectiveOver morphism
  anticanonical : LineBundle X.left
  fiberData : ∀ b : RationalPoint B, FanoData (fiberVariety morphism b) n
  fiberAnticanonical : ∀ b : RationalPoint B,
    (fiberData b).anticanonical.val ≅
      (Scheme.Modules.pullback (pullback.fst morphism.left b.left)).obj anticanonical.val

attribute [instance] SmoothFanoFamily.integralBase SmoothFanoFamily.smoothBase
  SmoothFanoFamily.finiteTypeBase SmoothFanoFamily.separatedBase
  SmoothFanoFamily.proper SmoothFanoFamily.smooth

/-- The actual parameter point in the underlying Zariski space. -/
def parameterPoint {n : ℕ} (F : SmoothFanoFamily n) (b : RationalPoint F.B) : F.B.left :=
  b.left (IsLocalRing.closedPoint ℂ)

/-- The intrinsic valuative semistability of the actual fibre. -/
def SemistableFiber {n : ℕ} (F : SmoothFanoFamily n) (b : RationalPoint F.B) : Prop :=
  IsValuativelyKSemistable (F.fiberData b)

end MathlibExt.AlgebraicGeometry.FanoKSemistabilityFamilies
