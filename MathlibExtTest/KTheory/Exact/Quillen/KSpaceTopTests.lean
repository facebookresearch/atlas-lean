/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Quillen.KSpaceTop

/-!
# TopCat bundle of the Quillen K-space carrier: tests

Focused public-API checks for `NQKSpaceTop`: the bundle elaborates as a
`TopCat` over `NQKSpace C`, the basepoint inhabits the bundle and is the
constant loop, and the loop-space carrier has its path-space topology.

No maps, functoriality laws, homotopy groups, equivalence invariance,
`π₀`/`K₀` comparison, Q/S comparison, or spectra are added or tested.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.KTheory.Exact.Quillen.KSpaceTopTests

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The Quillen K-space bundle elaborates as a `TopCat`. -/
noncomputable example : TopCat.{max u v} :=
  AlgebraicKTheory.NQKSpaceTop C

/-- The bundle carrier is the loop-space carrier. -/
noncomputable example : ↥(AlgebraicKTheory.NQKSpaceTop C) = AlgebraicKTheory.NQKSpace C :=
  rfl

/-- The constant loop inhabits the bundle. -/
noncomputable example : AlgebraicKTheory.NQKSpaceTop C :=
  AlgebraicKTheory.NQKSpaceTop.basepoint C

/-- The bundled basepoint is the constant loop. -/
example :
    AlgebraicKTheory.NQKSpaceTop.basepoint C =
      Path.refl (AlgebraicKTheory.NQReal.basepoint C) :=
  AlgebraicKTheory.NQKSpaceTop.basepoint_eq C

/-- The loop-space carrier has its path-space topology. -/
noncomputable example : TopologicalSpace (AlgebraicKTheory.NQKSpace C) :=
  inferInstance

section TypeZero

variable {C₀ : Type 0} [Category.{0} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

/-- The bundle and basepoint elaborate at `Type 0`. -/
noncomputable example : TopCat.{0} :=
  AlgebraicKTheory.NQKSpaceTop C₀

noncomputable example : AlgebraicKTheory.NQKSpaceTop C₀ :=
  AlgebraicKTheory.NQKSpaceTop.basepoint C₀

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

/-- The bundle and basepoint elaborate at `Type 1`. -/
noncomputable example : TopCat.{1} :=
  AlgebraicKTheory.NQKSpaceTop C₁

noncomputable example : AlgebraicKTheory.NQKSpaceTop C₁ :=
  AlgebraicKTheory.NQKSpaceTop.basepoint C₁

end TypeOne

section Nonclaims

#check_failure AlgebraicKTheory.NQKSpaceTop.toPointed

#check_failure AlgebraicKTheory.NQKSpaceTop.map

#check_failure AlgebraicKTheory.NQKSpaceTop.basepointMap

#check_failure AlgebraicKTheory.NQKSpacePiZeroEquivK0

#check_failure AlgebraicKTheory.quillenQSContinuousMap

end Nonclaims

#print axioms AlgebraicKTheory.NQKSpaceTop.basepoint
#print axioms AlgebraicKTheory.NQKSpaceTop.basepoint_eq

end MathlibExtTest.KTheory.Exact.Quillen.KSpaceTopTests
