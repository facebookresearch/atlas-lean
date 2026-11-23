/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceTop
public import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-!
# Homotopy groups of the Quillen K-space for projective modules

For a ring `R`, `NQKSpaceHomotopyGroup R n` is the degree-`n` cube-based
homotopy group of `NQKSpace (FGProjectiveCat R)` at the constant loop, with
the module universe fixed to the ring universe (`FGProjectiveCat.{u} R` for
`R : Type u`).

This source-facing name delegates to the canonical generic raw connective
carrier with exactly the same constant-loop point. The original cube
carrier and the fixed module/ring universe convention are retained in every
degree. This facade reexports only the basic raw-carrier interface. Group
conventions, chosen-root exact-functor maps, the next-BQ shift and K-zero
dictionaries require an explicit import of the full `ConnectiveKGroups`
API; the degree-zero cube carrier remains distinct from its group convention.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory

/-- Degree-`n` homotopy group of the Quillen K-space at the constant loop,
for finitely generated projective modules. -/
noncomputable abbrev NQKSpaceHomotopyGroup (R : Type u) [Ring R] (n : ℕ) :
    Type (u + 1) :=
  ConnectiveKGroups.rawCarrier (FGProjectiveCat.{u} R) n

end AlgebraicKTheory
