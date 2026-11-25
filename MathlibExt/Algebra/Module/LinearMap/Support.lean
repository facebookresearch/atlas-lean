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

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# The vector range of a possibly nonunital operator representation

For a multiplicative operator representation of a unital semiring, every
represented vector lies in the range of the image of the source unit.
Conversely that unit range is already one of the represented vector ranges.
Thus their union is the actual linear range of that single endomorphism.

No unit-preservation, topology, norm, star or nontriviality is assumed.
-/

public section

namespace NonUnitalRingHom

universe uR uA uH

variable {R : Type uR} [Semiring R]
variable {A : Type uA} [Semiring A]
variable {H : Type uH} [AddCommMonoid H] [Module R H]

/-- The represented vector ranges of a possibly nonunital operator homomorphism
have union equal to the actual range of the image of the source unit. -/
theorem iUnion_range_apply_eq_range_one (ρ : A →ₙ+* Module.End R H) :
    (⋃ a : A, Set.range (ρ a : H → H)) = Set.range (ρ 1 : H → H) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, rfl⟩ := ha
    refine ⟨ρ a x, ?_⟩
    have hUnit : ρ (1 : A) * ρ a = ρ a := by
      rw [← map_mul ρ (1 : A) a, one_mul]
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End R H => T x) hUnit
  · intro hy
    obtain ⟨x, rfl⟩ := hy
    exact Set.mem_iUnion.mpr ⟨(1 : A), ⟨x, rfl⟩⟩

end NonUnitalRingHom
