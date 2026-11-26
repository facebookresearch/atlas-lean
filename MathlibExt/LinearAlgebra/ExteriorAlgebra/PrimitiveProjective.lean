/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraMap
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveFree
public import Mathlib.Algebra.Module.Projective

/-!
# Homogeneous exterior primitives over projective modules

Let R be a commutative ring and M a projective R-module. A split linear embedding into a free
module carries a homogeneous exterior primitive to a primitive of the same degree in the free
exterior coalgebra. For every degree n≠1 that image is zero, and the split exterior map
reflects zero.

Thus a projective module has no nonzero homogeneous exterior primitive outside degree one.
This uses module projectivity over R and holds in every characteristic, without finite
generation or invertibility of the degree.
-/

@[expose] public section

noncomputable section

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Let R be a commutative ring, M an R-module with Module.Projective R M, and n ∈ ℕ with n≠1. If
a ∈ Λ^n_R M becomes a (1,1)-skew primitive element of ExteriorAlgebra R M, then a=0. A split
embedding of M into a free R-module transports primitivity through the exterior coalgebra map
and preserves degree; split injectivity then reflects the free-module vanishing. The ring and
module carrier universes are independent, and no finite-generation or characteristic condition
is required. -/
theorem primitive_homogeneous_eq_zero_of_projective [Module.Projective R M]
    (n : ℕ) (hn : n ≠ 1) (a : ⋀[R]^n M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R M) 1
      (a : ExteriorAlgebra R M)) : a = 0 := by
  obtain ⟨N, hNadd, hNmodule, hNfree, i, s, hsi⟩ := Module.Projective.iff_split.mp
    (inferInstance : Module.Projective R M)
  letI : AddCommMonoid N := hNadd
  letI : Module R N := hNmodule
  letI : Module.Free R N := hNfree
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  have hi : Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R N) 1
      (exteriorPower.map n i a : ExteriorAlgebra R N) := by
    rw [exteriorPower.coe_map]
    exact map_isPrimitive R M i a ha
  have hz : exteriorPower.map n i a = 0 :=
    primitive_homogeneous_eq_zero R N n hn _ hi
  apply exteriorPower.map_injective (n := n) (f := i) s hsi
  simpa only [map_zero] using hz

end ExteriorAlgebra
