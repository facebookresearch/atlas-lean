/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

import MathlibExt.Algebra.TensorProduct.PointSeparation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option autoImplicit false
open scoped TensorProduct

namespace TensorPointSeparationTest

-- Preserve the historical Pi.algHom spelling and redundant finiteness premise.
set_option linter.deprecated false in
set_option linter.unusedSectionVars false in
theorem exactSource
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} (pt : P → (A →ₐ[K] L))
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (x : A ⊗[K] A)
    (hx : ∀ p q : P, Algebra.TensorProduct.lift (pt p) (pt q)
      (fun _ _ => Commute.all _ _) x = 0) : x = 0 :=
  Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero pt hinj x hx

-- The second coordinate is redundant, making the point type genuinely infinite.
def coordinatePoint (K : Type*) [Field K] (p : Bool × ℕ) : K × K →ₐ[K] K :=
  if p.1 then AlgHom.snd K K K else AlgHom.fst K K K

theorem coordinateEvaluation_injective (K : Type*) [Field K] :
    Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId K ((Bool × ℕ) → K))
        (AlgHom.pi (coordinatePoint K)) (fun _ _ => Commute.all _ _) :
          K ⊗[K] (K × K) →ₐ[K] ((Bool × ℕ) → K)) := by
  let ev := Algebra.TensorProduct.lift (Algebra.ofId K ((Bool × ℕ) → K))
    (AlgHom.pi (coordinatePoint K)) (fun _ _ => Commute.all _ _)
  have he (x : K ⊗[K] (K × K)) (p : Bool × ℕ) :
      ev x p = coordinatePoint K p (Algebra.TensorProduct.lid K (K × K) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r a => simp [ev]
    | add x y hx hy => simp [map_add, hx, hy]
  intro x y h
  change ev x = ev y at h
  apply (Algebra.TensorProduct.lid K (K × K)).injective
  apply Prod.ext
  · simpa [he, coordinatePoint] using congrFun h (false, 0)
  · simpa [he, coordinatePoint] using congrFun h (true, 0)

theorem tensorMaps_ext
    {K L A P M : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (pt : P → A →ₐ[K] L)
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi pt)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (f g : M → A ⊗[K] A)
    (h : ∀ m p q, Algebra.TensorProduct.lift (pt p) (pt q)
      (fun _ _ => Commute.all _ _) (f m) =
        Algebra.TensorProduct.lift (pt p) (pt q) (fun _ _ => Commute.all _ _) (g m)) :
    f = g := by
  funext m
  apply sub_eq_zero.mp
  apply Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero pt hinj
  intro p q
  rw [map_sub, h, sub_self]

-- A non-field algebra over the non-algebraically-closed field of rationals.
theorem rationalProduct_separation (x : (ℚ × ℚ) ⊗[ℚ] (ℚ × ℚ))
    (hx : ∀ p q : Bool × ℕ, Algebra.TensorProduct.lift
      (coordinatePoint ℚ p) (coordinatePoint ℚ q) (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 :=
  exactSource (coordinatePoint ℚ) (coordinateEvaluation_injective ℚ) x hx

-- Independent pairs are essential: this tensor is invisible on the diagonal.
theorem offDiagonal_nonzero :
    ((1, 0) : ℚ × ℚ) ⊗ₜ[ℚ] ((0, 1) : ℚ × ℚ) ≠ 0 := by
  intro h
  have := congrArg (Algebra.TensorProduct.lift (coordinatePoint ℚ (false, 0))
    (coordinatePoint ℚ (true, 0)) (fun _ _ => Commute.all _ _)) h
  norm_num [coordinatePoint] at this

theorem offDiagonal_vanishes_on_diagonal (p : Bool × ℕ) :
    Algebra.TensorProduct.lift (coordinatePoint ℚ p) (coordinatePoint ℚ p)
      (fun _ _ => Commute.all _ _) (((1, 0) : ℚ × ℚ) ⊗ₜ[ℚ] ((0, 1) : ℚ × ℚ)) = 0 := by
  rcases p with ⟨b, n⟩
  cases b <;> simp [coordinatePoint]

-- Dropping scalar-extended injectivity fails for the dual-number algebra.
theorem nilpotentTensor_nonzero :
    (TrivSqZeroExt.inr (1 : ℚ) : TrivSqZeroExt ℚ ℚ) ⊗ₜ[ℚ]
      (1 : TrivSqZeroExt ℚ ℚ) ≠ 0 := by
  intro h
  have he := congrArg (Algebra.TensorProduct.lift
    (AlgHom.id ℚ (TrivSqZeroExt ℚ ℚ)) (AlgHom.id ℚ (TrivSqZeroExt ℚ ℚ))
    (fun _ _ => Commute.all _ _)) h
  have := congrArg TrivSqZeroExt.snd he
  simp at this

theorem nilpotentTensor_vanishes
    (p q : TrivSqZeroExt ℚ ℚ →ₐ[ℚ] ℚ) :
    Algebra.TensorProduct.lift p q (fun _ _ => Commute.all _ _)
      ((TrivSqZeroExt.inr (1 : ℚ) : TrivSqZeroExt ℚ ℚ) ⊗ₜ[ℚ]
        (1 : TrivSqZeroExt ℚ ℚ)) = 0 := by
  have hp : p (TrivSqZeroExt.inr (1 : ℚ)) = 0 := by
    apply mul_self_eq_zero.mp
    rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  simp [hp]

end TensorPointSeparationTest
