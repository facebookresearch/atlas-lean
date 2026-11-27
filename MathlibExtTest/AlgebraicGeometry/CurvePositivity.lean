/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import MathlibExt.AlgebraicGeometry.LineBundleTensor

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.CurvePositivity

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

-- The tensor product and powers re-exported here are the single definitions of
-- `SchemeModulesTensor`, not parallel copies.
example : @CurvePositivity.moduleTensor = @SchemeModulesTensor.moduleTensor := rfl
example : @CurvePositivity.power = @SchemeModulesTensor.power := rfl

-- Semiampleness and torsion are predicates on line bundles, witnessed by a positive power.
example (L : X.Modules) (hL : IsLineBundle L) (h : GloballyGenerated (power L 1)) :
    IsSemiample L hL :=
  ⟨1, one_pos, h⟩

example (L : X.Modules) (hL : IsLineBundle L) (e : power L 2 ≅ structureModule X) :
    IsTorsion L hL :=
  ⟨2, two_pos, ⟨e⟩⟩

-- The structure sheaf is a torsion line bundle.
example : IsTorsion (structureModule X) (isLineBundle_structureModule X) :=
  ⟨1, one_pos, ⟨LineBundleTensor.unitTensorUnitIso X⟩⟩

-- The zeroth power is the structure sheaf, so the zeroth power never witnesses torsion or
-- semiampleness: both definitions require a positive exponent.
example (L : X.Modules) : power L 0 = structureModule X := rfl

-- On an integral proper curve the structure sheaf is nef: its degree is zero.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] [IsIntegral X] :
    IsNefOnCurve f (structureModule X) (isLineBundle_structureModule X) := by
  simp [IsNefOnCurve]

-- Nefness is nonnegativity of the line-bundle degree of `CoherentCurveLinearSeries`.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] [IsIntegral X] (L : X.Modules)
    (hL : IsLineBundle L) :
    IsNefOnCurve f L hL ↔ 0 ≤ degree f L hL := Iff.rfl

-- Bigness asks for linear growth of `h⁰` of the powers, with a positive constant.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] (L : X.Modules) (hL : IsLineBundle L)
    (h : ∀ n : ℕ, (n : ℚ) ≤ Module.finrank k (cohomology f (power L n) 0)) :
    IsBigOnCurve f L hL :=
  ⟨1, one_pos, 0, fun n _ ↦ by simpa using h n⟩
