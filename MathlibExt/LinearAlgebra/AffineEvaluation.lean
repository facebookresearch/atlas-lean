/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/variables/VariableBound/Family/Pairwise.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
extract the source's finite-field bijection as a linear equivalence over any field.
-/
module

public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Evaluation of an affine function at two points

The slope and intercept of an affine function over a field are linearly equivalent to its values
at two distinct points. The inverse is the usual two-point interpolation formula.
-/

@[expose] public section

namespace LinearEquiv

variable {F : Type*} [Field F]

/-- Evaluation of the affine function `x ↦ slope * x + intercept` at two distinct points. -/
def affineEvaluation (theta theta' : F) (h : theta ≠ theta') : (F × F) ≃ₗ[F] (F × F) where
  toFun p := (p.1 * theta + p.2, p.1 * theta' + p.2)
  invFun p := ((p.1 - p.2) / (theta - theta'),
    p.1 - (p.1 - p.2) / (theta - theta') * theta)
  map_add' p q := by
    ext <;> dsimp <;> ring
  map_smul' c p := by
    ext <;> dsimp <;> ring
  left_inv p := by
    ext <;> dsimp <;> field_simp [sub_ne_zero.mpr h] <;> ring
  right_inv p := by
    ext <;> dsimp <;> field_simp [sub_ne_zero.mpr h] <;> ring

@[simp]
theorem affineEvaluation_apply (theta theta' : F) (h : theta ≠ theta') (p : F × F) :
    affineEvaluation theta theta' h p =
      (p.1 * theta + p.2, p.1 * theta' + p.2) :=
  rfl

@[simp]
theorem affineEvaluation_symm_apply (theta theta' : F) (h : theta ≠ theta') (p : F × F) :
    (affineEvaluation theta theta' h).symm p =
      ((p.1 - p.2) / (theta - theta'),
        p.1 - (p.1 - p.2) / (theta - theta') * theta) :=
  rfl

end LinearEquiv
