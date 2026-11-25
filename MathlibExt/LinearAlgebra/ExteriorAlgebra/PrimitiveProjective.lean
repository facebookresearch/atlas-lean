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
# Homogeneous exterior primitives on projective modules

A projective module admits a split embedding into a free module. The
exterior coalgebra map preserves primitives, and the free-module theorem
forces every homogeneous degree other than one to vanish. Split
injectivity reflects zero back to the given module, over any commutative
ring and in every characteristic.
-/

@[expose] public section

noncomputable section

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Every homogeneous exterior primitive outside degree one vanishes on a projective module,
over any commutative ring and in every characteristic. -/
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
