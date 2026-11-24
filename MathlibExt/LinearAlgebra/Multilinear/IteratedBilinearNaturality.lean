/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Multilinear.IteratedBilinear

/-! # Naturality of actual ordered bilinear iteration -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe r a a' b b'
namespace MultilinearMap
variable {R : Type r} [CommRing R] [TopologicalSpace R]

/-- A genuine map of bilinear steps and their starting vectors preserves
all ordered iterations, including the empty tuple. -/
theorem iterateCupMultilinear_naturality
    (V : Type a) [AddCommGroup V] [Module R V]
    (V' : Type a') [AddCommGroup V'] [Module R V']
    (A : TopModuleCat.{b} R) (C : ℕ → TopModuleCat.{b} R)
    (A' : TopModuleCat.{b'} R) (C' : ℕ → TopModuleCat.{b'} R)
    (kappa : V →ₗ[R] A) (kappa' : V' →ₗ[R] A')
    (unit : C 0) (unit' : C' 0)
    (step : (n : ℕ) → A →ₗ[R] C n →ₗ[R] C (n+1))
    (step' : (n : ℕ) → A' →ₗ[R] C' n →ₗ[R] C' (n+1))
    (j : V →ₗ[R] V') (f : A →ₗ[R] A')
    (g : (n : ℕ) → C n →ₗ[R] C' n)
    (hkappa : ∀ x, f (kappa x) = kappa' (j x))
    (hunit : g 0 unit = unit')
    (hstep : ∀ (n : ℕ) (x : A) (y : C n),
      g (n+1) (step n x y) = step' n (f x) (g n y)) :
    ∀ (n : ℕ) (x : Fin n → V),
      g n (iterateCupMultilinear (R := R) V A C kappa unit step n x) =
      iterateCupMultilinear (R := R) V' A' C' kappa' unit' step' n
        (fun i => j (x i)) := by
  intro n
  induction n with
  | zero => intro x; exact hunit
  | succ n ih =>
    intro x
    have hs := hstep n (kappa (x 0))
      (iterateCupMultilinear (R := R) V A C kappa unit step n (fun i => x i.succ))
    have ht := ih (fun i => x i.succ)
    change g (n+1) (step n (kappa (x 0))
      (iterateCupMultilinear (R := R) V A C kappa unit step n (fun i => x i.succ))) =
      step' n (kappa' (j (x 0)))
        (iterateCupMultilinear (R := R) V' A' C' kappa' unit' step' n
          (fun i => j (x i.succ)))
    exact hs.trans (congrArg₂ (fun (z : A') (w : C' n) => step' n z w) (hkappa (x 0)) ht)

end MultilinearMap
