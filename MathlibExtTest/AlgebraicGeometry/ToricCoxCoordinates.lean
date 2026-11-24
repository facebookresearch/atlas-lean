/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

/-!
# Tests for analytic Cox coordinates

The zero tuple lies outside the Cox open when every cone misses a ray, as for
the projective line; a tuple with no zero coordinate lies in it; a diagonal
scalar lies in the Cox group when the ray generators sum to zero, as for the
rays `1` and `-1`; and the group acts coordinatewise.
-/

noncomputable section

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.CoxGradedSheaves
open MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

/-- If every cone misses some ray, the zero tuple is excluded. -/
example (h : ∀ σ ∈ F.cones, ∃ i, ¬rayInCone R σ i) :
    (fun _ : Fin R.count ↦ (0 : ℂ)) ∉ coxLocus R := by
  rintro ⟨σ, hσ, hz⟩
  obtain ⟨i, hi⟩ := h σ hσ
  exact hz i hi rfl

/-- A tuple with no zero coordinate lies in the Cox open. -/
example (σ : F.Face) (z : Fin R.count → ℂ) (hz : ∀ i, z i ≠ 0) : z ∈ coxLocus R :=
  ⟨σ.val, σ.property, fun i _ ↦ hz i⟩

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) (u : ℂˣ) :
    ∏ i ∈ s, u ^ f i = u ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- A diagonal scalar is in the Cox group when the ray generators sum to zero. -/
example (u : ℂˣ) (h : ∀ j, ∑ i, R.generator i j = 0) :
    characterHom R (fun _ ↦ u) = 1 := by
  funext j
  change ∏ i, u ^ (R.generator i j) = 1
  rw [prod_zpow_eq_zpow_sum, h j, zpow_zero]

/-- The Cox group acts coordinatewise. -/
example (g : CoxGroup R) (z : CoxOpen R) (i : Fin R.count) :
    (g • z).val i = (g.val i : ℂ) * z.val i :=
  rfl
