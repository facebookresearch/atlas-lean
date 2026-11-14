/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual vector bundles, degrees and slopes on curves

Local trivializations use finite coproducts of the structure sheaf. Degree
is the actual Euler characteristic minus rank times the Euler
characteristic of the structure sheaf. Global generation is an actual
epimorphism from a finite trivial bundle.

Reference: Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Chapter 1, https://doi.org/10.1017/CBO9780511711985.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CurveVectorBundles

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

def trivialBundle (X : Scheme.{u}) (r : ℕ) : X.Modules :=
  ∐ fun _ : Fin r ↦ structureModule X

def IsVectorBundle {X : Scheme.{u}} (E : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅ trivialBundle U r)

def bundleDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) : ℤ :=
  (Module.finrank k (cohomology f E 0) : ℤ) -
    Module.finrank k (cohomology f E 1) - (r : ℤ) *
      ((Module.finrank k (cohomology f (structureModule X) 0) : ℤ) -
        Module.finrank k (cohomology f (structureModule X) 1))

def slope {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) : ℚ :=
  (bundleDegree f E r : ℚ) / r

/-- A finite family of actual global sections generates the sheaf. -/
def GloballyGenerated {X : Scheme.{u}} (E : X.Modules) : Prop :=
  ∃ b : ℕ, ∃ e : trivialBundle X b ⟶ E, Epi e

end MathlibExt.AlgebraicGeometry.CurveVectorBundles
