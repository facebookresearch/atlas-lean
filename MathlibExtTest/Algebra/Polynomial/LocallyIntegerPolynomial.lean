/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial

/-! # Tests for locally integer polynomial functions -/

open MetaMathlibExt Polynomial

-- On an infinite domain a single exceptional input must also be a zero.
example {U : Set ℤ} (hU : U.Infinite) {f : U → ℤ} (hf : f ∈ lipSubring U)
    (a : U) (ha : ∀ x ≠ a, f x = 0) : f a = 0 := by
  have := hU.to_subtype
  have hinf := Set.infinite_univ.sdiff (Set.finite_singleton a)
  have hz := lip_eq_zero_of_infinite_zeros hf
    (hinf.mono fun x (hx : x ∈ (Set.univ : Set U) \ {a}) => ha x hx.2)
  exact congrFun hz a

-- A single zero is possible for a nonzero locally integer polynomial function.
example (a : ℤ) :
    {x : (Set.univ : Set ℤ) | (polynomialToLIP Set.univ (X - C a) : _ → ℤ) x = 0} =
      {⟨a, Set.mem_univ a⟩} := by
  ext x
  simp [Subtype.ext_iff, sub_eq_zero]

-- Interpolation at a single node gives a constant polynomial, even away from the node.
example (a b : ℤ) (f : ℤ → ℤ) : (interpolationPoly {a} f).eval (b : ℚ) = f a := by
  simp [interpolationPoly]

-- The coordinate function can be cancelled even though it vanishes at zero.
example (f g : lipSubring Set.univ)
    (h : polynomialToLIP Set.univ X * f = polynomialToLIP Set.univ X * g) : f = g := by
  have := lipSubring_isDomain (Set.infinite_univ (α := ℤ))
  apply mul_left_cancel₀ _ h
  intro hX
  have h1 := congrArg (fun p : lipSubring Set.univ => p.val ⟨1, Set.mem_univ 1⟩) hX
  simp at h1

-- The backward difference of the square function is 2x - 1 on all integers.
example : (fun x : (Set.univ : Set ℤ) => 2 * (x : ℤ) - 1) ∈ lipSubring Set.univ := by
  have h := lip_univ_sub_shift (polynomialToLIP Set.univ (X ^ 2)).property
  convert h using 1
  funext x
  simp only [polynomialToLIP_apply, eval_pow, eval_X]
  ring

-- A single negative prime value repeated on an infinite domain suffices.
example {U : Set ℤ} (hU : U.Infinite) : Irreducible (polynomialToLIP U (C (-2))) := by
  have := hU.to_subtype
  apply irreducible_of_infinite_prime_values
  simpa [Nat.prime_two] using (Set.infinite_univ (α := U))

-- A unit taking the value -1 at the origin is -1 everywhere.
example (u : (lipSubring Set.univ)ˣ) (h : (u : lipSubring Set.univ).val ⟨0, trivial⟩ = -1) :
    u = -1 := by
  obtain rfl | hneg := lipSubring_units_eq Set.infinite_univ u
  · change (1 : ℤ) = -1 at h
    norm_num at h
  · exact hneg
