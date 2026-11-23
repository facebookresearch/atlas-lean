/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass
import Mathlib.Algebra.Field.ZMod

noncomputable section
open CategoryTheory
open MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe
open MathlibExt.AlgebraicGeometry.GeometricChow

/-- The zero section comes from the global section universal property and
has the required base identity; it is not an unrelated chosen map. -/
example {X : ComplexScheme} {E : X.left.Modules} {r : ℕ}
    (B : VectorBundleModel X E r) : zeroSection B ≫ B.projection = 𝟙 X :=
  zeroSection_projection B

/-- The actual negative-dual bundle also fixes the zero form over the base. -/
example {X : ComplexScheme} {E : X.left.Modules} {r : ℕ}
    (B : MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass.DualBundleModel X E r) :
    B.zeroSection ≫ B.projection = 𝟙 X := B.zeroSection_projection

section LaurentAmbient

variable (k : Type) [Field k]

/-- A smooth Laurent ambient is allowed by the general contract. -/
private abbrev LaurentAmbient := Localization.Away (Polynomial.X : Polynomial k)

private instance : Algebra.Smooth k (Polynomial k) where

private instance : Algebra.Smooth (Polynomial k) (LaurentAmbient k) :=
  Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial k)

private instance : Algebra.Smooth k (LaurentAmbient k) :=
  Algebra.Smooth.comp k (Polynomial k) (LaurentAmbient k)

private def laurentPresentation : Algebra.Extension.{0} k (LaurentAmbient k) :=
  Algebra.Extension.self k (LaurentAmbient k)

/-- The identity Laurent presentation has a smooth ambient and zero conormal
kernel; it is compatible with the canonical smooth rank-zero-negative scope. -/
example : Algebra.Smooth k (laurentPresentation k).Ring := by
  change Algebra.Smooth k (LaurentAmbient k)
  infer_instance

/-- The coordinate is actually inverted in this localization ambient. -/
example : IsUnit (algebraMap (Polynomial k) (LaurentAmbient k) Polynomial.X) :=
  IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)

example : (laurentPresentation k).ker = ⊥ := by
  change RingHom.ker (RingHom.id (LaurentAmbient k)) = ⊥
  ext x
  rfl

end LaurentAmbient

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Smooth Laurent ambients are admitted in characteristic two as well. -/
example : Algebra.Smooth (ZMod 2) (LaurentAmbient (ZMod 2)) := inferInstance

/-- The actual dual-bundle model is available over a positive-characteristic
base; its zero map is still fixed by the same form universal property. -/
example {X : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.SchemeOver (ZMod 2)}
    {E : X.left.Modules} {r : ℕ}
    (B : MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass.DualBundleModel X E r) :
    B.zeroSection ≫ B.projection = 𝟙 X := B.zeroSection_projection

/-- Negative Chow degree stays zero in positive characteristic. -/
example (X : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.SchemeOver (ZMod 2))
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] [AlgebraicGeometry.IsNoetherian X.left] :
    Subsingleton (MathlibExt.AlgebraicGeometry.FieldChowOperators.gradedChow X (-1)) := by
  dsimp [MathlibExt.AlgebraicGeometry.FieldChowOperators.gradedChow]
  infer_instance

/-- Complex specialization identifies the actual quotient representatives,
without freely choosing an unrelated Chow comparison. -/
example (X : ComplexScheme) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] (d : ℕ) (c : CycleGroup X.left d) :
    MathlibExt.AlgebraicGeometry.FieldChowOperators.complexChowEquiv X d
      ((MathlibExt.AlgebraicGeometry.RelativeCurveClasses.relations X d).mkQ c) =
      (rationalEquivalences X d).mkQ c :=
  MathlibExt.AlgebraicGeometry.FieldChowOperators.complexChowEquiv_mk X d c
