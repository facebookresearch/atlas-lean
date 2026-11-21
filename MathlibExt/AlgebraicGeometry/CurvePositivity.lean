/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Curve line-bundle positivity

Tensor powers use actual presheaf tensor followed by sheafification.
Semiampleness means a positive power has a finite global generating
family. Bigness is positive linear asymptotic section growth, the
dimension-one definition. These are curve predicates, rather than a
substitute for higher-dimensional numerical positivity.

Reference: Lazarsfeld, *Positivity in Algebraic Geometry I*, Chapter 1,
https://doi.org/10.1007/978-3-642-18808-4.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CurvePositivity

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u

/-- Ordinary tensor of the actual module sheaves, with sheafification. -/
def moduleTensor (X : Scheme.{u}) (L M : X.Modules) : X.Modules :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((curriedTensor P).obj (U.obj L) |>.obj (U.obj M))

def power {X : Scheme.{u}} (L : X.Modules) : ℕ → X.Modules
  | 0 => structureModule X
  | n + 1 => moduleTensor X (power L n) L

def IsTorsion {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (power L n ≅ structureModule X)

def IsSemiample {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∃ n : ℕ, 0 < n ∧ GloballyGenerated (power L n)

/-- Positive asymptotic linear section growth on a proper curve. -/
def IsBigOnCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * n ≤ (Module.finrank k (cohomology f (power L n) 0) : ℚ)

/-- Numerical nefness in dimension one is nonnegative line-bundle degree. -/
def IsNefOnCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) : Prop :=
  0 ≤ degree f L

end MathlibExt.AlgebraicGeometry.CurvePositivity
