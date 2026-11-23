/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Quillen.KSpaceHomotopyGroups

/-!
# Quillen K-space homotopy groups for projective modules: tests

Focused public-API checks for `NQKSpaceHomotopyGroup`: the carrier
elaborates in `Type (u + 1)` as the cube-based group at the constant loop,
and positive degrees have their group structure.

Carrier only: no functorial transport, identity or composition laws, no
`π₀`/`K₀` comparison, no Q/S comparison, and no spectra are added
or tested.
-/

universe u

namespace MathlibExtTest.KTheory.Exact.Quillen.KSpaceHomotopyGroupsTests

variable {R : Type u} [Ring R]

/-- The carrier elaborates in `Type (u + 1)`. -/
noncomputable example (n : ℕ) : Type (u + 1) :=
  AlgebraicKTheory.NQKSpaceHomotopyGroup R n

/-- The carrier is the cube-based group at the constant loop. -/
noncomputable example (n : ℕ) :
    AlgebraicKTheory.NQKSpaceHomotopyGroup R n =
      HomotopyGroup.Pi n
        (AlgebraicKTheory.NQKSpace (FGProjectiveCat.{u} R))
        (AlgebraicKTheory.NQKSpaceTop.basepoint
          (FGProjectiveCat.{u} R)) :=
  rfl

/-- Positive degrees have their cube-based group structure. -/
noncomputable example (n : ℕ) :
    Group (AlgebraicKTheory.NQKSpaceHomotopyGroup R (n + 1)) :=
  inferInstance

section TypeZero

variable {R₀ : Type 0} [Ring R₀]

/-- The carrier elaborates at `Type 0`. -/
noncomputable example (n : ℕ) : Type 1 :=
  AlgebraicKTheory.NQKSpaceHomotopyGroup R₀ n

end TypeZero

section Nonclaims

#check_failure AlgebraicKTheory.NQKSpaceHomotopyGroupMap

#check_failure AlgebraicKTheory.NQKSpaceHomotopyGroupMapHom

#check_failure AlgebraicKTheory.NQKSpacePiZeroEquivK0

#check_failure AlgebraicKTheory.quillenQStageKSpacePiZeroEquiv

#check_failure AlgebraicKTheory.quillenQSContinuousMap

end Nonclaims

#print axioms AlgebraicKTheory.NQKSpaceHomotopyGroup

end MathlibExtTest.KTheory.Exact.Quillen.KSpaceHomotopyGroupsTests
