/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.DiamondEtaleCoefficientOperations
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Geometric-point data of diamond étale coefficient operations

The original Huber ring of an `IntegralGeometricInclusion` is a field with its own ring operations,
so it has no nontrivial idempotents (a product of two fields is excluded), and its algebraic
closedness refers to that field structure. Its plus ring is a valuation subring, and the map
identifies the two rings as topological spaces (a bijective continuous map would not suffice).
-/

namespace MathlibExtTest.DiamondEtaleCoefficientOperations

open MathlibExt.Condensed.DiamondEtaleCoefficientOperations

variable {p : ℕ} [Fact p.Prime]

/-- The original ring of a geometric inclusion has no nontrivial idempotent. -/
theorem idempotent_eq_zero_or_one (T : IntegralGeometricInclusion p) (e : T.original.pair.ring)
    (he : e * e = e) : e = 0 ∨ e = 1 := by
  letI := T.isField.toField
  exact IsIdempotentElem.iff_eq_zero_or_one.mp he

/-- Algebraic closedness is stated for the field structure of the original ring operations. -/
example (T : IntegralGeometricInclusion p) :
    letI := T.isField.toField; IsAlgClosed T.original.pair.ring := T.closed

/-- The plus ring of the original field is a valuation subring. -/
theorem mem_or_inv_mem (T : IntegralGeometricInclusion p) (a : T.original.pair.ring) :
    letI := T.isField.toField
    a ∈ T.original.pair.plus ∨ a⁻¹ ∈ T.original.pair.plus := by
  letI := T.isField.toField
  rcases T.plus_valuation a with h | ⟨b, hb, hab⟩
  · exact Or.inl h
  · exact Or.inr ((inv_eq_of_mul_eq_one_right hab).symm ▸ hb)

/-- The plus ring of the original field, as a valuation subring. -/
def plusValuationSubring (T : IntegralGeometricInclusion p) :
    letI := T.isField.toField; ValuationSubring T.original.pair.ring :=
  letI := T.isField.toField
  { toSubring := T.original.pair.plus
    mem_or_inv_mem' := mem_or_inv_mem T }

/-- The two rings are identified as topological spaces. -/
noncomputable def fieldHomeomorph (T : IntegralGeometricInclusion p) :
    T.original.pair.ring ≃ₜ T.maximal.pair.ring :=
  IsHomeomorph.homeomorph _ T.same_field

example (T : IntegralGeometricInclusion p) (a : T.original.pair.ring) :
    fieldHomeomorph T a = T.map.original.hom a := rfl

end MathlibExtTest.DiamondEtaleCoefficientOperations
