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
# The original regular principal ideal and its equation generator

Multiplication by the actual regular equation identifies the ambient
coefficient module with its actual principal ideal. No line or basis is
supplied. The coefficient ring may be a zero ring.
-/

@[expose] public section
noncomputable section
universe u
namespace Ideal
variable (B : Type u) [CommRing B] (g : B)
local notation "𝓘" => Ideal.span (Set.singleton g)

/-- The original equation multiplier as a map into its actual ideal. -/
def principalIdealMultiplier : B →ₗ[B] 𝓘 where
  toFun b := ⟨b * g, Ideal.mem_span_singleton.mpr ⟨b, mul_comm b g⟩⟩
  map_add' b c := by
    apply Subtype.ext
    exact add_mul b c g
  map_smul' r b := by
    apply Subtype.ext
    exact mul_assoc r b g

/-- The actual ideal multiplier retains the original equation product. -/
theorem principalIdealMultiplier_apply (b : B) :
    (principalIdealMultiplier B g b).val = b * g := rfl

/-- Every element of the actual principal ideal has an original equation coefficient. -/
theorem principalIdealMultiplier_surjective : Function.Surjective (principalIdealMultiplier B g) := by
  intro x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp x.property
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact (mul_comm b g).trans hb.symm

/-- The original regular equation has unique ideal coefficients. -/
theorem principalIdealMultiplier_injective (hg : g ∈ nonZeroDivisors B) :
    Function.Injective (principalIdealMultiplier B g) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h : b * g = 0 := congrArg Subtype.val hb
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp h

/-- A regular equation earns the actual principal-ideal linear equivalence. -/
def principalIdealEquiv (hg : g ∈ nonZeroDivisors B) : B ≃ₗ[B] 𝓘 :=
  LinearEquiv.ofBijective (principalIdealMultiplier B g)
    ⟨principalIdealMultiplier_injective B g hg, principalIdealMultiplier_surjective B g⟩

/-- One is carried to the original actual defining-equation ideal element. -/
theorem principalIdealEquiv_one (hg : g ∈ nonZeroDivisors B) :
    principalIdealEquiv B g hg 1 = (⟨g, Ideal.subset_span (Set.mem_singleton g)⟩ : 𝓘) := by
  apply Subtype.ext
  exact one_mul g

end Ideal
