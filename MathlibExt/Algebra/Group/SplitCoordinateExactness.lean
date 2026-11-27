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
# A whole two-coordinate group map from a split exact sequence

The original two projection homomorphisms are bijective together when
the second projection kernel is the first inclusion image and both
original inclusions split the prescribed projections with zero cross
terms. No commutativity of the groups is needed for the actual map.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

namespace MonoidHom.SplitCoordinateExactness

variable {A : Type u} {B : Type v} {D : Type w} [Group A] [Group B] [Group D]
  (i : A →* B) (p : B →* A) (j : D →* B) (q : B →* D)
  (hpi : ∀ a, p (i a) = a) (hqj : ∀ d, q (j d) = d)
  (hqi : ∀ a, q (i a) = 1) (hpj : ∀ d, p (j d) = 1)
  (hexact : ∀ b, q b = 1 ↔ ∃ a, i a = b)

/-- The actual whole two-coordinate homomorphism retains the supplied original projections. -/
def comparison : B →* A × D := p.prod q

include hpi hexact in
/-- Both full original coordinates detect equality through the exact original kernel/image law. -/
theorem comparison_injective : Function.Injective (comparison p q) := by
  intro b c h
  have hp : p b = p c := congrArg Prod.fst h
  have hq : q b = q c := congrArg Prod.snd h
  have hker : q (b * c⁻¹) = 1 := by rw [map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨a, ha⟩ := (hexact (b * c⁻¹)).mp hker
  have hpker : p (b * c⁻¹) = 1 := by rw [map_mul, map_inv, hp, mul_inv_cancel]
  have ha1 : a = 1 := (hpi a).symm.trans ((congrArg p ha).trans hpker)
  have hb : b * c⁻¹ = 1 := ha.symm.trans ((congrArg i ha1).trans (map_one i))
  exact mul_inv_eq_one.mp hb

include hpi hqj hqi hpj in
/-- Every entire pair of original coordinates is realized by the product of the two original
sections. -/
theorem comparison_surjective : Function.Surjective (comparison p q) := by
  rintro ⟨a, d⟩
  refine ⟨i a * j d, Prod.ext ?_ ?_⟩
  · exact (map_mul p _ _).trans ((congrArg₂ (fun x y => x * y) (hpi a) (hpj d)).trans (mul_one a))
  · exact (map_mul q _ _).trans ((congrArg₂ (fun x y => x * y) (hqi a) (hqj d)).trans (one_mul d))

/-- The original coordinate hom is a genuine multiplicative equivalence from the proved
split sequence. -/
def equiv : B ≃* A × D :=
  MulEquiv.ofBijective (comparison p q)
    ⟨comparison_injective i p q hpi hexact,
      comparison_surjective i p j q hpi hqj hqi hpj⟩

end MonoidHom.SplitCoordinateExactness
