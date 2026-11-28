/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Multiplication coordinates for a regular principal ideal

For a commutative ring B and an element g, multiplication b ↦ b g gives a B-linear surjection
from B to the principal ideal (g). If g is a non-zero-divisor, the coefficients are unique and
this map is a linear equivalence.

Under this equivalence, 1 maps to g as an element of (g). The construction applies to
arbitrary commutative rings, including the zero ring when the stated regularity condition
holds.
-/

@[expose] public section
noncomputable section
universe u
namespace Ideal
variable (B : Type u) [CommRing B] (g : B)

/-- For a commutative ring B and g : B, define principalIdealMultiplier B g : B →ₗ[B] Ideal.span
{g} by b ↦ b * g, with the product viewed as an element of the principal ideal. -/
def principalIdealMultiplier : B →ₗ[B] (Ideal.span ({g} : Set B)) where
  toFun b := ⟨b * g, Ideal.mem_span_singleton.mpr ⟨b, mul_comm b g⟩⟩
  map_add' b c := by
    apply Subtype.ext
    exact add_mul b c g
  map_smul' r b := by
    apply Subtype.ext
    exact mul_assoc r b g

/-- For a commutative ring B, g : B and b : B, the underlying value of principalIdealMultiplier B
g b in B is b * g. -/
theorem principalIdealMultiplier_apply (b : B) :
    (principalIdealMultiplier B g b).val = b * g := rfl

/-- For a commutative ring B and any g : B, principalIdealMultiplier B g : B →ₗ[B] Ideal.span {g}
is surjective. Thus every element of (g) has the form b * g for some b : B. -/
theorem principalIdealMultiplier_surjective : Function.Surjective (principalIdealMultiplier B g) :=
  by
  intro x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp x.property
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact (mul_comm b g).trans hb.symm

/-- For a commutative ring B and g ∈ nonZeroDivisors B, the map b ↦ b * g into the principal ideal
(g) is injective. If two products b * g and c * g are equal, then b = c. -/
theorem principalIdealMultiplier_injective (hg : g ∈ nonZeroDivisors B) :
    Function.Injective (principalIdealMultiplier B g) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h : b * g = 0 := congrArg Subtype.val hb
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp h

/-- For a commutative ring B and g ∈ nonZeroDivisors B, multiplication by g defines a B-linear
equivalence principalIdealEquiv B g hg : B ≃ₗ[B] Ideal.span {g}. Its forward map is b ↦ b * g,
and its inverse is the unique multiplication coefficient. -/
def principalIdealEquiv (hg : g ∈ nonZeroDivisors B) : B ≃ₗ[B] (Ideal.span ({g} : Set B)) :=
  LinearEquiv.ofBijective (principalIdealMultiplier B g)
    ⟨principalIdealMultiplier_injective B g hg, principalIdealMultiplier_surjective B g⟩

/-- For a commutative ring B and g ∈ nonZeroDivisors B, principalIdealEquiv B g hg sends 1 to g
viewed as an element of Ideal.span {g}. -/
theorem principalIdealEquiv_one (hg : g ∈ nonZeroDivisors B) :
    principalIdealEquiv B g hg 1 = (⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ : (Ideal.span ({g}
      : Set B))) := by
  apply Subtype.ext
  exact one_mul g

end Ideal
