/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions are adapted from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2:
Theorems/Thm_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.lean
(exact source consumer) and
P2M/Sol/S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.lean
(homogeneous-support scaling argument).
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
The frozen files name no individual authors; copyright is from their NOTICE.
-/

import MathlibExt.Algebra.MvPolynomial.IntegerHomogeneity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Importing applications and boundaries for integer-grid recognition -/

namespace IntegerHomogeneityTest

open MvPolynomial

universe u v w

/-- The exact source-shaped consumer, with independent universes. -/
theorem sourceExact {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {ι : Type v} (P : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ),
      MvPolynomial.eval (fun i => ((n * c i : ℤ) : R)) P =
        (n : R) ^ d * MvPolynomial.eval (fun i => (c i : R)) P) :
    P.IsHomogeneous d :=
  MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul P d h

/-- The determinant form is recognized from its integer-lattice scaling. -/
theorem determinantForm {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type v) [Fintype ι] [DecidableEq ι] :
    (Matrix.det (Matrix.of fun i j : ι =>
      (X (i, j) : MvPolynomial (ι × ι) R))).IsHomogeneous
      (Fintype.card ι) := by
  apply isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
  intro n c
  rw [(eval (fun i => ((n * c i : ℤ) : R))).map_det,
    (eval (fun i => (c i : R))).map_det]
  have he (x : ι × ι → R) :
      (eval x).mapMatrix (Matrix.of fun i j : ι => X (i, j)) =
        Matrix.of (fun i j : ι => x (i, j)) := by
    ext i j
    simp
  rw [he, he]
  have hs : Matrix.of (fun i j : ι => ((n * c (i, j) : ℤ) : R)) =
      (n : R) • Matrix.of (fun i j : ι => (c (i, j) : R)) := by
    ext i j
    simp [Int.cast_mul]
  rw [hs, Matrix.det_smul]

/-- Empty determinants remain one, and recognition gives degree zero. -/
theorem emptyDeterminant {R : Type u} [CommRing R] [IsDomain R] [CharZero R] :
    let p := Matrix.det (Matrix.of fun i j : Fin 0 =>
      (X (i, j) : MvPolynomial (Fin 0 × Fin 0) R))
    p = 1 ∧ p.IsHomogeneous 0 := by
  dsimp only
  exact ⟨Matrix.det_isEmpty, by simpa using determinantForm (R := R) (Fin 0)⟩

/-- A cubic over a nonfield, with an infinite ambient variable type. -/
noncomputable def cubic : MvPolynomial ℕ (Polynomial ℤ) :=
  X 0 ^ 3 + C Polynomial.X * X 1 * X 2 * X 3

/-- Its integer-grid scaling is an algebraic identity, not an assumption. -/
theorem cubicHomogeneous : cubic.IsHomogeneous 3 := by
  apply isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
  intro n c
  simp only [cubic, map_add, map_pow, map_mul, eval_X, eval_C, Int.cast_mul]
  ring

private lemma supportScaling {S : Type w} [CommSemiring S] {ι : Type v}
    {p : MvPolynomial ι S} {d : ℕ} (hp : p.IsHomogeneous d)
    (t : S) (x : ι → S) :
    eval (fun i => t * x i) p = t ^ d * eval x p := by
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hm]
  ac_rfl

/-- Transport needs no characteristic or domain assumption on the target. -/
theorem cubicTransport {S : Type w} [CommSemiring S]
    (f : Polynomial ℤ →+* S) :
    (map f cubic).IsHomogeneous 3 ∧
      ∀ (t : S) (x : ℕ → S),
        eval (fun i => t * x i) (map f cubic) =
          t ^ 3 * eval x (map f cubic) := by
  have hc := cubicHomogeneous.map f
  exact ⟨hc, supportScaling hc⟩

/-- The example is nonzero, its variables are infinite, and its coefficient
ring has a nonzero element without a multiplicative inverse. -/
theorem nonfieldWitness : cubic ≠ 0 ∧ Infinite ℕ ∧
    (Polynomial.X : Polynomial ℤ) ≠ 0 ∧
      ∀ q : Polynomial ℤ, Polynomial.X * q ≠ 1 := by
  refine ⟨?_, inferInstance, by simp, ?_⟩
  · intro h
    have h0 := congrArg (eval (fun i : ℕ => if i = 0 then 1 else 0)) h
    norm_num [cubic] at h0
  · intro q h
    have h0 := congrArg (Polynomial.eval (0 : ℤ)) h
    simp at h0

/-- Zero is recognized at positive degree, but its total degree stays zero. -/
theorem zeroBoundary {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type v) :
    (0 : MvPolynomial ι R).IsHomogeneous 5 ∧
      (0 : MvPolynomial ι R).totalDegree = 0 := by
  constructor
  · apply isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    intro n c
    simp
  · simp

/-- A nonzero constant on an empty variable type is recognized at degree
zero. -/
theorem emptyConstant {R : Type u} [CommRing R] [IsDomain R] [CharZero R] :
    (C (1 : R) : MvPolynomial (PEmpty.{v + 1}) R).IsHomogeneous 0 ∧
      (C (1 : R) : MvPolynomial (PEmpty.{v + 1}) R) ≠ 0 := by
  constructor
  · apply isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    intro n c
    simp
  · simp

private lemma f2Square (x : ZMod 2) : x ^ 2 = x :=
  (by decide : ∀ a : ZMod 2, a ^ 2 = a) x

/-- The finite-characteristic evaluation function loses formal coefficients. -/
theorem finiteCharBoundary :
    (∀ c : Unit → ℤ, eval (fun i => (c i : ZMod 2))
      ((X () : MvPolynomial Unit (ZMod 2)) ^ 2 - X ()) = 0) ∧
    ¬ ((X () : MvPolynomial Unit (ZMod 2)) ^ 2 - X ()).IsHomogeneous 3 := by
  constructor
  · intro c
    simp only [map_sub, map_pow, eval_X, f2Square, sub_self]
  · intro h
    have hc := h.coeff_eq_zero (d := Finsupp.single () 2) (by simp)
    rw [coeff_sub, X_pow_eq_monomial] at hc
    norm_num [X, coeff_monomial] at hc

/-- Characteristic zero alone does not prevent a polynomial from vanishing
on the integer grid without being formally homogeneous. -/
theorem zeroDivisorBoundary :
    let p := C (0, 1) *
      ((X () : MvPolynomial Unit (ℤ × ZMod 2)) ^ 2 - X ())
    (∀ c : Unit → ℤ, eval (fun i => (c i : ℤ × ZMod 2)) p = 0) ∧
      ¬ p.IsHomogeneous 3 := by
  dsimp only
  constructor
  · intro c
    simp only [map_mul, eval_C, map_sub, map_pow, eval_X]
    apply Prod.ext
    · simp
    · simp [f2Square]
  · intro h
    have hc := h.coeff_eq_zero (d := Finsupp.single () 2) (by simp)
    rw [coeff_C_mul, coeff_sub, X_pow_eq_monomial] at hc
    norm_num [X, coeff_monomial] at hc

/-- Explicit characteristic-zero and zero-divisor witnesses in the product. -/
theorem productRingWitness : CharZero (ℤ × ZMod 2) ∧
    ((1, 0) : ℤ × ZMod 2) ≠ 0 ∧ ((0, 1) : ℤ × ZMod 2) ≠ 0 ∧
      ((1, 0) : ℤ × ZMod 2) * (0, 1) = 0 := by
  exact ⟨inferInstance, by decide, by decide, by decide⟩

/-- Both counterexamples satisfy the literal integer-scaling premise. -/
theorem counterexampleScaling :
    let p := (X () : MvPolynomial Unit (ZMod 2)) ^ 2 - X ()
    let q := C (0, 1) *
      ((X () : MvPolynomial Unit (ℤ × ZMod 2)) ^ 2 - X ())
    (∀ (n : ℤ) (c : Unit → ℤ),
      eval (fun i => ((n * c i : ℤ) : ZMod 2)) p =
        (n : ZMod 2) ^ 3 * eval (fun i => (c i : ZMod 2)) p) ∧
    (∀ (n : ℤ) (c : Unit → ℤ),
      eval (fun i => ((n * c i : ℤ) : ℤ × ZMod 2)) q =
        (n : ℤ × ZMod 2) ^ 3 * eval (fun i => (c i : ℤ × ZMod 2)) q) := by
  dsimp only
  constructor
  · intro n c
    rw [finiteCharBoundary.1 (fun i => n * c i), finiteCharBoundary.1 c,
      mul_zero]
  · intro n c
    rw [zeroDivisorBoundary.1 (fun i => n * c i), zeroDivisorBoundary.1 c,
      mul_zero]

end IntegerHomogeneityTest
