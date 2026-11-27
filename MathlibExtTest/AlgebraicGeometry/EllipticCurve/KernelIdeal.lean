/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.KernelIdeal

open WeierstrassCurve

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
  [IsAlgClosed k]

example (W : WeierstrassCurve F) :
    (1 : rationalEndSubring k W) ∈ kernelIdealSet k W W (AddMonoidHom.id _) :=
  one_mem_kernelIdealSet_id k W

example (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    (0 : rationalEndSubring k W₀) ∈ kernelIdealSet k W₀ W χ :=
  zero_mem_kernelIdealSet k W₀ W χ

/-- Membership in `kernelIdealSet` is factorization through `χ` by a map that is zero or rationally
represented. -/
example (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (a : rationalEndSubring k W₀) :
    a ∈ kernelIdealSet k W₀ W χ ↔
      ∃ ρ, (ρ = 0 ∨ IsRationallyRepresented k W W₀ ρ) ∧
        (a : AddMonoid.End (W₀.baseChange k).toAffine.Point) = ρ.comp χ :=
  Iff.rfl
