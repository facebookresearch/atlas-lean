/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Cap-ladder evaluation recurrence

This file isolates the algebraic induction underlying cup-power evaluations.
A ladder consists of cohomology and homology modules, cup and cap step maps,
chosen cohomology powers and homology elements, scalar cap incidences, and a
compatible evaluation pairing.  Cup--cap compatibility and the normalized bottom
evaluation force the evaluation on every rung to be the product of the
successive incidence scalars.

The theorem is conditional: it does not identify a topological incidence
scalar with a cap scalar, nor does it assert a projective-space cohomology-ring
presentation.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

/-- Algebraic data for a cap-ladder evaluation.  The scalar at index `j`
belongs to the transition from rung `j + 1` to rung `j`. -/
@[ext]
structure CapLadderEvaluationData (R : Type u) [CommRing R] where
  /-- Cohomology modules on the successive rungs. -/
  cohomology : ℕ → ModuleCat.{u} R
  /-- Homology modules on the successive rungs. -/
  homology : ℕ → ModuleCat.{u} R
  /-- Cup product on the left by the fixed class. -/
  cupStep : ∀ j, cohomology j ⟶ cohomology (j + 1)
  /-- Cap product by the fixed class. -/
  capStep : ∀ j, homology (j + 1) ⟶ homology j
  /-- Evaluation on each rung. -/
  pairing : ∀ j,
    MonoidalCategory.tensorObj (cohomology j) (homology j) ⟶ ModuleCat.of R R
  /-- The chosen successive cup powers. -/
  power : ∀ j, cohomology j
  /-- The chosen homology elements. -/
  homologyElement : ∀ j, homology j
  /-- The scalar attached to each cap transition. -/
  scalar : ℕ → R
  /-- The chosen powers advance by the cup-step map. -/
  power_succ : ∀ j, power (j + 1) = (cupStep j).hom (power j)
  /-- Pointwise cup--cap compatibility. -/
  pairing_step : ∀ j (a : cohomology j) (b : homology (j + 1)),
    (pairing (j + 1)).hom ((cupStep j).hom a ⊗ₜ[R] b) =
      (pairing j).hom (a ⊗ₜ[R] (capStep j).hom b)
  /-- Cap sends each chosen homology element to the scalar multiple of its
  predecessor. -/
  cap_homologyElement : ∀ j,
    (capStep j).hom (homologyElement (j + 1)) = scalar j • homologyElement j
  /-- The bottom chosen elements evaluate to one. -/
  pairing_zero : (pairing 0).hom (power 0 ⊗ₜ[R] homologyElement 0) = 1

namespace CapLadderEvaluationData

variable {R : Type u} [CommRing R]

/-- Evaluation of the chosen power on the chosen homology element is the
product of the preceding cap-incidence scalars. -/
theorem pairing_power_homologyElement (L : CapLadderEvaluationData R) (j : ℕ) :
    (L.pairing j).hom (L.power j ⊗ₜ[R] L.homologyElement j) =
      ∏ i ∈ Finset.range j, L.scalar i := by
  induction j with
  | zero => simpa using L.pairing_zero
  | succ j ih =>
      rw [L.power_succ j, L.pairing_step j, L.cap_homologyElement j,
        TensorProduct.tmul_smul, map_smul, ih, smul_eq_mul,
        Finset.prod_range_succ, mul_comm]

/-- If every incidence scalar occurring below a rung is a unit, then the
chosen-element evaluation on that rung is a unit. -/
theorem isUnit_pairing_power_homologyElement
    (L : CapLadderEvaluationData R) (j : ℕ)
    (hscalar : ∀ i < j, IsUnit (L.scalar i)) :
    IsUnit ((L.pairing j).hom (L.power j ⊗ₜ[R] L.homologyElement j)) := by
  rw [L.pairing_power_homologyElement]
  exact IsUnit.prod_iff.mpr fun i hi ↦ hscalar i (Finset.mem_range.mp hi)

end CapLadderEvaluationData

end ModuleCat

end
