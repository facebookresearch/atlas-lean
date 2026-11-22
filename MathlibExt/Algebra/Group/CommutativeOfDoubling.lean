/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public meta import Mathlib.Tactic.FastInstance

/-!
# Commutativity from the original double-product identity

Group cancellation turns the double-product identity into commutativity.
The resulting structure keeps every original group operation and field.
-/

@[expose] public section

universe u

namespace GroupDoubling

/-- The original two double products force the original two factors to commute. -/
theorem commute {A : Type u} [Group A] (a b : A)
    (h : (a * b) * (a * b) = (a * a) * (b * b)) : a * b = b * a := by
  have hc : (b * a) * b = (a * b) * b :=
    mul_left_cancel (by simpa only [mul_assoc] using h)
  exact (mul_right_cancel hc).symm

/-- The proved commuting law adds commutativity to the SAME original group structure. -/
@[instance_reducible]
def commGroup {A : Type u} (g : Group A) (h : letI := g; ∀ a b : A, a * b = b * a) : CommGroup A :=
  fast_instance% { g with mul_comm := h }

end GroupDoubling
