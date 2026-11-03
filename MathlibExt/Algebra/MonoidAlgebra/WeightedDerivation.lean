/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the source operator to arbitrary commutative rings and additive exponent monoids,
and package it as a Mathlib derivation.
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-! # Weighted derivations of additive monoid algebras

An additive weight on the exponents of an additive monoid algebra determines a derivation:
the coefficient at `g` is multiplied by the weight of `g`.

Adapted from `eth/proof/rates/GeneralPieces/Series/Deriv.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace AddMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommMonoid Γ]

/-- Multiply the coefficient at each exponent by an additive weight of that exponent. -/
noncomputable def weightedDerivation (w : Γ →+ R) :
    Derivation R (AddMonoidAlgebra R Γ) (AddMonoidAlgebra R Γ) :=
  let D : AddMonoidAlgebra R Γ →ₗ[R] AddMonoidAlgebra R Γ :=
    (coeffLinearEquiv R).symm.toLinearMap ∘ₗ
      Finsupp.lsum R (fun g ↦ (Finsupp.lsingle g).comp (LinearMap.mulLeft R (w g))) ∘ₗ
      (coeffLinearEquiv R).toLinearMap
  Derivation.mk' D fun f h ↦ by
    simp only [smul_eq_mul]
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [add_mul, map_add, hf, hg, map_add]
      ring
    | single g r =>
      induction h using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add f h hf hh =>
        rw [mul_add, map_add, hf, hh, map_add]
        ring
      | single k s =>
        ext x
        by_cases hx : x = g + k
        · simp [D, w.map_add, single_mul_single, add_comm, add_mul, hx]
          ring
        · simp [D, w.map_add, single_mul_single, add_comm, add_mul, hx]

/-- The coefficient at `g` is multiplied by the weight of `g`. -/
@[simp] theorem coeff_weightedDerivation (w : Γ →+ R)
    (f : AddMonoidAlgebra R Γ) (g : Γ) :
    (weightedDerivation w f).coeff g = w g * f.coeff g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp [hf, hh, mul_add]
  | single h r =>
    by_cases e : g = h
    · subst g
      simp [weightedDerivation]
    · simp [weightedDerivation, e]

/-- A basis term keeps its exponent and has its coefficient multiplied by the weight. -/
@[simp] theorem weightedDerivation_single (w : Γ →+ R) (g : Γ) (r : R) :
    weightedDerivation w (single g r) = single g (w g * r) := by
  ext h
  by_cases e : h = g
  · subst h
    simp
  · simp [e]

/-- The zero weight determines the zero derivation. -/
@[simp] theorem weightedDerivation_zero :
    weightedDerivation (0 : Γ →+ R) = 0 := by
  ext f g
  simp

end AddMonoidAlgebra
