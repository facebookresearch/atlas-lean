/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpace

/-!
# TopCat bundle of the Quillen K-space carrier

For an exact category `C`, `NQKSpaceTop C` bundles the loop-space carrier
`NQKSpace C` as a `TopCat`, with the constant loop at the realized
zero-object basepoint as `NQKSpaceTop.basepoint C`.

This is a thin bundle for the later Q/S comparison. It provides no maps,
functoriality laws, homotopy groups, equivalence invariance, `π₀`/`K₀`
comparison, or spectra.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

/-- TopCat bundle of the Quillen loop-space carrier. -/
noncomputable abbrev NQKSpaceTop (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    TopCat.{max u v} :=
  TopCat.of (NQKSpace C)

/-- The constant loop at the realized zero-object basepoint. -/
noncomputable def NQKSpaceTop.basepoint (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] : NQKSpaceTop C :=
  Path.refl (NQReal.basepoint C)

/-- The bundled basepoint is the constant loop. -/
@[simp]
theorem NQKSpaceTop.basepoint_eq (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    NQKSpaceTop.basepoint C = Path.refl (NQReal.basepoint C) :=
  rfl

end AlgebraicKTheory
