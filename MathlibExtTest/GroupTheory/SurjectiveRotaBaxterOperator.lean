/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SurjectiveRotaBaxterOperator
import Mathlib.Data.Fintype.Basic

/-!
# Tests for `MathlibExt.GroupTheory.SurjectiveRotaBaxterOperator`

Examples and non-examples of Rota–Baxter operators on groups, the left shift on `ℤ^ℕ` on explicit
sequences, and the surjective non-injective operator `(σ, f) ↦ (σ⁻¹, s f)` on `S₃ × ℤ^ℕ`.
-/

namespace MathlibExtTest.GroupTheory.SurjectiveRotaBaxterOperator

open MathlibExt.GroupTheory.SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted

-- Test section: examples and non-examples of Rota–Baxter operators.

-- The constant map to `1` is a Rota–Baxter operator on every group.
example {G : Type} [Group G] : IsRotaBaxterOperator fun _ : G => (1 : G) :=
  fun _ _ => by simp

-- Inversion on `S₃`.
example : IsRotaBaxterOperator fun σ : Equiv.Perm (Fin 3) => σ⁻¹ :=
  isRotaBaxterOperator_inv

-- The identity of `S₃` is multiplicative but not a Rota–Baxter operator: for `g = (0 1)` and
-- `h = (1 2)` the identity would force `g * h = g * g * h * g⁻¹ = h * g`. So the commutativity
-- assumption of `isRotaBaxterOperator_iff_map_mul` cannot be dropped.
example : ¬ IsRotaBaxterOperator (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) := fun h =>
  absurd (h (Equiv.swap 0 1) (Equiv.swap 1 2)) (by decide)

-- On a commutative group the identity and squaring are endomorphisms, hence Rota–Baxter operators.
example : IsRotaBaxterOperator (id : Multiplicative ℤ → Multiplicative ℤ) :=
  isRotaBaxterOperator_monoidHom (MonoidHom.id _)

example : IsRotaBaxterOperator fun g : Multiplicative ℤ => g ^ 2 :=
  isRotaBaxterOperator_iff_map_mul.2 fun g h => (mul_pow g h 2).symm

-- A translation of `ℤ` is not multiplicative, so it is not a Rota–Baxter operator.
example : ¬ IsRotaBaxterOperator fun g : Multiplicative ℤ => g * Multiplicative.ofAdd 1 :=
  fun h => absurd (isRotaBaxterOperator_iff_map_mul.1 h 1 1) (by decide)

-- Products: inversion on `S₃` times the identity of `ℤ`.
example : IsRotaBaxterOperator
    (Prod.map (fun σ : Equiv.Perm (Fin 3) => σ⁻¹) (id : Multiplicative ℤ → Multiplicative ℤ)) :=
  isRotaBaxterOperator_inv.prodMap (isRotaBaxterOperator_monoidHom (MonoidHom.id _))

-- Test section: the left shift on `ℤ^ℕ`.

-- The shift of `0, 1, 2, …` is `1, 2, 3, …`.
example : leftShift (Multiplicative.ofAdd fun n : ℕ => (n : ℤ)) =
    Multiplicative.ofAdd fun n : ℕ => (n : ℤ) + 1 :=
  congrArg Multiplicative.ofAdd (funext fun n => by simp)

-- The sequence `1, 0, 0, …` and the zero sequence (the identity `1` of the multiplicative group)
-- are distinct and have the same shift.
example : leftShift (Multiplicative.ofAdd fun n => if n = 0 then 1 else 0) = leftShift 1 :=
  congrArg Multiplicative.ofAdd (funext fun n => by simp)

example : (Multiplicative.ofAdd fun n : ℕ => if n = 0 then (1 : ℤ) else 0) ≠ 1 := fun h => by
  simpa using congrFun (congrArg Multiplicative.toAdd h) 0

-- Test section: the operator `(σ, f) ↦ (σ⁻¹, s f)` on `S₃ × ℤ^ℕ`.

example (σ : Equiv.Perm (Fin 3)) (f : Multiplicative (ℕ → ℤ)) :
    rotaBaxterExample (σ, f) = (σ⁻¹, leftShift f) :=
  rfl

-- The image of `((0 1 2), 0, 1, 2, …)` is `((0 2 1), 1, 2, 3, …)`, with `(0 1 2) = (0 1) * (1 2)`
-- and `(0 2 1) = (1 2) * (0 1)` (permutations compose right to left).
example : rotaBaxterExample (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2,
    Multiplicative.ofAdd fun n : ℕ => (n : ℤ)) =
    (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1, Multiplicative.ofAdd fun n : ℕ => (n : ℤ) + 1) :=
  Prod.ext (by decide) (congrArg Multiplicative.ofAdd (funext fun n => by simp))

-- The Rota–Baxter identity at `g = ((0 1), 0, 1, 2, …)` and `h = ((1 2), 1, 0, 0, …)`.
example :
    let g : Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ) :=
      (Equiv.swap 0 1, Multiplicative.ofAdd fun n : ℕ => (n : ℤ))
    let h : Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ) :=
      (Equiv.swap 1 2, Multiplicative.ofAdd fun n => if n = 0 then 1 else 0)
    rotaBaxterExample g * rotaBaxterExample h =
      rotaBaxterExample (g * rotaBaxterExample g * h * (rotaBaxterExample g)⁻¹) :=
  isRotaBaxterOperator_rotaBaxterExample _ _

-- Every element has a preimage.
example (x : Equiv.Perm (Fin 3) × Multiplicative (ℕ → ℤ)) : ∃ y, rotaBaxterExample y = x :=
  rotaBaxterExample_surjective x

-- The elements `(1, (1, 0, 0, …))` and `(1, (0, 0, 0, …))`, distinct by the test above, have the
-- same image, so the operator is not injective.
example : rotaBaxterExample (1, Multiplicative.ofAdd fun n => if n = 0 then 1 else 0) =
    rotaBaxterExample (1, 1) :=
  Prod.ext rfl (congrArg Multiplicative.ofAdd (funext fun n => by simp))

example : ¬ Function.Injective rotaBaxterExample :=
  rotaBaxterExample_not_injective

-- Test section: the main theorem.

example : surjectiveNonInjectiveRotaBaxterOperatorExists :=
  surjectiveNonInjectiveRotaBaxterOperatorExists_holds

end MathlibExtTest.GroupTheory.SurjectiveRotaBaxterOperator
