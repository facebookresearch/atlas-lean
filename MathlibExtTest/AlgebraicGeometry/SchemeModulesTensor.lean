/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LineBundleTensor
import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-!
# Tests for the sheaf tensor product and tensor powers

`power L 0` is the structure sheaf and `power L (n + 1) = power L n ⊗ L`. The structure sheaf is
a unit for `moduleTensor` on both sides, so `power L 1 ≅ L`, and the left unit at the structure
sheaf is the isomorphism `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X` used to trivialise tensor products of line bundles.
Restriction to an open subscheme commutes with `moduleTensor`, and tensor products and powers of
line bundles are line bundles.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor
open MathlibExt.AlgebraicGeometry.LineBundleTensor
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons

universe u

variable {X : Scheme.{u}}

-- The zeroth power is the structure sheaf, and powers multiply on the right.
example (L : X.Modules) : power L 0 = structureModule X := rfl

example (L : X.Modules) (n : ℕ) : power L (n + 1) = moduleTensor X (power L n) L := rfl

/-- The structure sheaf is a left unit. -/
noncomputable example (L : X.Modules) : moduleTensor X (structureModule X) L ≅ L :=
  tensorLeftUnit X L

/-- The structure sheaf is a right unit. -/
noncomputable example (L : X.Modules) : moduleTensor X L (structureModule X) ≅ L :=
  tensorRightUnit X L

/-- The first power is the sheaf itself. -/
noncomputable example (L : X.Modules) : power L 1 ≅ L :=
  tensorLeftUnit X L

/-- At the structure sheaf the left unit is the trivialisation of `𝒪_X ⊗ 𝒪_X`. -/
example : tensorLeftUnit X (structureModule X) = unitTensorUnitIso X :=
  Iso.ext rfl

/-- Restriction to an open subscheme commutes with the tensor product. -/
noncomputable example {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (L M : X.Modules) :
    (moduleTensor X L M).restrict f ≅ moduleTensor U (L.restrict f) (M.restrict f) :=
  restrictModuleTensorIso f L M

/-- Tensor products of line bundles are line bundles. -/
example {L M : X.Modules} (hL : IsLineBundle L) (hM : IsLineBundle M) :
    IsLineBundle (moduleTensor X L M) :=
  hL.moduleTensor hM

/-- Tensor powers of line bundles are line bundles. -/
example {L : X.Modules} (hL : IsLineBundle L) (n : ℕ) : IsLineBundle (power L n) :=
  hL.power n
