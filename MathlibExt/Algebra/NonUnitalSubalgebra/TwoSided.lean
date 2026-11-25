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

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# Two-sided nonunital subalgebras

This algebraic owner records ambient left and right absorption together with
the canonical bottom and top dictionaries. It has no topological, normed,
star, or quotient dependency.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace NonUnitalSubalgebra

variable {𝕜 A : Type*} [CommSemiring 𝕜] [NonUnitalNonAssocSemiring A] [Module 𝕜 A]

/-- Let `𝕜` be a commutative semiring and let `A` be a possibly nonunital, nonassociative semiring with
a `𝕜`-module structure. A nonunital subalgebra `S` is two-sided if `a*x` and `x*a` belong to `S`
whenever `x ∈ S` and `a ∈ A`.
-/
class IsTwoSided (S : NonUnitalSubalgebra 𝕜 A) : Prop where
  mul_mem_left (a : A) {x : A} : x ∈ S → a * x ∈ S
  mul_mem_right {x : A} : x ∈ S → (a : A) → x * a ∈ S

section Bounds

variable {𝕜 A : Type*} [CommRing 𝕜] [NonUnitalRing A] [Module 𝕜 A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The zero nonunital subalgebra is two-sided. -/
instance instIsTwoSidedBot : IsTwoSided (⊥ : NonUnitalSubalgebra 𝕜 A) where
  mul_mem_left a {x} hx := by
    rw [NonUnitalAlgebra.mem_bot] at hx ⊢
    simp [hx]
  mul_mem_right {x} hx a := by
    rw [NonUnitalAlgebra.mem_bot] at hx ⊢
    simp [hx]

/-- The full nonunital subalgebra is two-sided. -/
instance instIsTwoSidedTop : IsTwoSided (⊤ : NonUnitalSubalgebra 𝕜 A) where
  mul_mem_left _ _ := by simp
  mul_mem_right _ _ := by simp

end Bounds

end NonUnitalSubalgebra
