/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the exponent type and bundle the coefficientwise operator as an additive homomorphism,
with reusable support and simplification lemmas.
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-! # Exponent-indexed coefficient maps on Hahn series

An exponent-indexed family of additive maps acts coefficientwise on Hahn series. If the family
satisfies the graded Leibniz identity, the induced additive map satisfies the product rule.

Adapted from `eth/proof/rates/GeneralPieces/Series/Deriv.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- Apply the map indexed by each exponent to the coefficient at that exponent. -/
noncomputable def gradedCoefficientMap (D : Γ → R →+ R) :
    HahnSeries Γ R →+ HahnSeries Γ R where
  toFun f :=
    { coeff := fun y => D y (f.coeff y)
      isPWO_support' := f.isPWO_support.mono fun y hy h => hy (by simp [h]) }
  map_zero' := by
    ext y
    simp
  map_add' f g := by
    ext y
    simp

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The coefficient formula for an exponent-indexed coefficient map. -/
@[simp] theorem coeff_gradedCoefficientMap (D : Γ → R →+ R) (f : HahnSeries Γ R) (y : Γ) :
    (gradedCoefficientMap D f).coeff y = D y (f.coeff y) := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Acting coefficientwise cannot introduce new exponents into the support. -/
theorem support_gradedCoefficientMap (D : Γ → R →+ R) (f : HahnSeries Γ R) :
    (gradedCoefficientMap D f).support ⊆ f.support :=
  fun y hy h => hy (by simp [h])

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The family consisting of zero maps induces the zero additive map. -/
@[simp] theorem gradedCoefficientMap_zero_family :
    gradedCoefficientMap (Γ := Γ) (fun _ => (0 : R →+ R)) = 0 := by
  ext f y
  simp

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- A one-term series keeps its exponent and applies the map indexed by that exponent. -/
@[simp] theorem gradedCoefficientMap_single (D : Γ → R →+ R) (y : Γ) (a : R) :
    gradedCoefficientMap D (single y a) = single y (D y a) := by
  ext z
  by_cases h : z = y
  · subst z
    simp
  · simp [h]

/-- On a constant series, the map indexed by zero acts on the constant coefficient. -/
@[simp] theorem gradedCoefficientMap_C (D : Γ → R →+ R) (a : R) :
    gradedCoefficientMap D (HahnSeries.C a) = HahnSeries.C (D 0 a) :=
  gradedCoefficientMap_single D 0 a

/-- An exponent-indexed coefficient map satisfying the graded Leibniz identity obeys the product
rule on Hahn series. -/
theorem gradedCoefficientMap_mul (D : Γ → R →+ R)
    (hD : ∀ i j a b, D (i + j) (a * b) = D i a * b + a * D j b)
    (f g : HahnSeries Γ R) :
    gradedCoefficientMap D (f * g) =
      gradedCoefficientMap D f * g + f * gradedCoefficientMap D g := by
  ext y
  rw [coeff_add, coeff_mul_left' f.isPWO_support (support_gradedCoefficientMap D f),
    coeff_mul_right' g.isPWO_support (support_gradedCoefficientMap D g),
    ← Finset.sum_add_distrib]
  change D y ((f * g).coeff y) = _
  rw [coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h : ij.1 + ij.2 = y := (Finset.mem_antidiagonal.1 hij).2.2
  rw [← h, hD]
  rfl

end HahnSeries
