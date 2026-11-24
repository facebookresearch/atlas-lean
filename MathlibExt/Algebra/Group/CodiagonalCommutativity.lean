/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Prod

/-!
# Commutativity from the original two-factor codiagonal

A monoid homomorphism from two copies of a monoid whose restrictions to
both original factors are identities forces the original multiplication
to commute. The resulting commutative structure keeps every old operation.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

namespace MonoidHom.CodiagonalCommutativity

section Monoid
variable {A : Type u} [Monoid A] (m : A × A →* A)
  (hl : ∀ a, m (a, 1) = a) (hr : ∀ a, m (1, a) = a)

include hl hr

/-- The original multiplication commutes through the actual cross factors of the product. -/
theorem mul_comm (a b : A) : a * b = b * a := by
  calc
    a * b = m (a, 1) * m (1, b) := congrArg₂ (fun x y => x * y) (hl a).symm (hr b).symm
    _ = m ((a, 1) * (1, b)) := (map_mul m _ _).symm
    _ = m ((1, b) * (a, 1)) := congrArg m (by apply Prod.ext <;> simp)
    _ = m (1, b) * m (a, 1) := map_mul m _ _
    _ = b * a := congrArg₂ (fun x y => x * y) (hr b) (hl a)

/-- The original monoid operations have the proved commutative structure. -/
@[instance_reducible]
def commMonoid : CommMonoid A := { ‹Monoid A› with mul_comm := mul_comm m hl hr }

/-- The commutative structure retains the whole original monoid record. -/
theorem commMonoid_toMonoid : (commMonoid m hl hr).toMonoid = ‹Monoid A› := rfl

end Monoid

section Group
variable {A : Type u} [Group A] (m : A × A →* A)
  (hl : ∀ a, m (a, 1) = a) (hr : ∀ a, m (1, a) = a)

/-- The original group operations have the proved commutative structure. -/
@[instance_reducible]
def commGroup : CommGroup A := { ‹Group A› with mul_comm := mul_comm m hl hr }

/-- The commutative structure retains the whole original group record. -/
theorem commGroup_toGroup : (commGroup m hl hr).toGroup = ‹Group A› := rfl

end Group
end MonoidHom.CodiagonalCommutativity
