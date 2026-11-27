/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ConsecutiveSquares
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# No finitely many planes contain all consecutive-squares solutions

This module proves that for every finite collection of affine planes in ℝ³ with nonzero
normal vectors, some solution of the sum of consecutive squares problem lies on none of them.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2.
-/

namespace MetaMathlibExt

@[expose] public section

private def curveA {R : Type*} [CommRing R] (x : R) : R :=
  96 * x ^ 6 + 816 * x ^ 5 + 2808 * x ^ 4 + 4992 * x ^ 3 +
    4820 * x ^ 2 + 2389 * x + 473

private def curveB {R : Type*} [CommRing R] (x : R) : R :=
  96 * x ^ 6 + 864 * x ^ 5 + 3192 * x ^ 4 + 6192 * x ^ 3 +
    6644 * x ^ 2 + 3732 * x + 855

private def curveC {R : Type*} [CommRing R] (x : R) : R :=
  96 * x ^ 6 + 912 * x ^ 5 + 3528 * x ^ 4 + 7104 * x ^ 3 +
    7844 * x ^ 2 + 4499 * x + 1046

private theorem curve_solution (n : ℕ) :
    IsSoCSSolution (curveA (n : ℤ)) (curveB (n : ℤ)) (curveC (n : ℤ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [curveA]
    positivity
  · have h : 0 < (48 * (n : ℤ) ^ 5 + 384 * (n : ℤ) ^ 4 +
        1200 * (n : ℤ) ^ 3 + 1824 * (n : ℤ) ^ 2 + 1343 * (n : ℤ) + 381) := by
      positivity
    dsimp [curveA, curveB]
    linear_combination h
  · have h : 0 < (48 * (n : ℤ) ^ 5 + 336 * (n : ℤ) ^ 4 +
        912 * (n : ℤ) ^ 3 + 1200 * (n : ℤ) ^ 2 + 767 * (n : ℤ) + 191) := by
      positivity
    dsimp [curveB, curveC]
    linear_combination h
  · dsimp [SoCSEq, curveA, curveB, curveC]
    ring

private noncomputable def planePolynomial (p : ℝ × ℝ × ℝ × ℝ) : Polynomial ℝ :=
  Polynomial.C p.1 * curveA Polynomial.X +
    Polynomial.C p.2.1 * curveB Polynomial.X +
    Polynomial.C p.2.2.1 * curveC Polynomial.X - Polynomial.C p.2.2.2

private theorem planePolynomial_ne_zero (p : ℝ × ℝ × ℝ × ℝ)
    (hp : (p.1, p.2.1, p.2.2.1) ≠ 0) : planePolynomial p ≠ 0 := by
  intro h
  have h6 := congrArg (fun q : Polynomial ℝ => q.coeff 6) h
  have h5 := congrArg (fun q : Polynomial ℝ => q.coeff 5) h
  have h4 := congrArg (fun q : Polynomial ℝ => q.coeff 4) h
  norm_num [planePolynomial, curveA, curveB, curveC, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X] at h6 h5 h4
  have hu : p.1 = 0 := by linarith
  have hv : p.2.1 = 0 := by linarith
  have hw : p.2.2.1 = 0 := by linarith
  exact hp (by simp [hu, hv, hw])

private theorem finite_plane_parameters (p : ℝ × ℝ × ℝ × ℝ)
    (hp : (p.1, p.2.1, p.2.2.1) ≠ 0) :
    {n : ℕ | p.1 * curveA (n : ℝ) + p.2.1 * curveB (n : ℝ) +
      p.2.2.1 * curveC (n : ℝ) = p.2.2.2}.Finite := by
  have h := (Polynomial.finite_setOfPred_isRoot (planePolynomial_ne_zero p hp)).preimage
    (Nat.cast_injective (R := ℝ)).injOn
  convert h using 1
  ext n
  simp [Polynomial.IsRoot, planePolynomial, curveA, curveB, curveC, sub_eq_zero]

/-- **No finitely many planes contain all solutions.** Let $S$ be a finite set of affine planes
$ux + vy + wz = t$ in $\mathbb{R}^3$, with $u, v, w, t$ real and $(u, v, w) \ne (0, 0, 0)$. Then
some solution $(a, b, c)$ of the sum of consecutive squares problem lies on none of the planes in
$S$, that is, $ua + vb + wc \ne t$ for every plane in $S$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2
(`integers-2026-A1-cor-2`); the proof text appended to the extracted
statement is not part of the claim. -/
public theorem soCS_not_finite_planes
    (S : Finset (ℝ × ℝ × ℝ × ℝ))
    (hS : ∀ p ∈ S, (p.1, p.2.1, p.2.2.1) ≠ 0) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      ∀ p ∈ S, p.1 * (a : ℝ) + p.2.1 * (b : ℝ) + p.2.2.1 * (c : ℝ) ≠ p.2.2.2
    := by
  classical
  let E (p : ℝ × ℝ × ℝ × ℝ) : Set ℕ :=
    {n | p.1 * curveA (n : ℝ) + p.2.1 * curveB (n : ℝ) +
      p.2.2.1 * curveC (n : ℝ) = p.2.2.2}
  have hE : (⋃ p ∈ S, E p).Finite :=
    S.finite_toSet.biUnion fun p hp => finite_plane_parameters p (hS p hp)
  obtain ⟨n, hn⟩ := hE.exists_notMem
  refine ⟨curveA (n : ℤ), curveB (n : ℤ), curveC (n : ℤ), curve_solution n, ?_⟩
  intro p hp h
  apply hn
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ?_⟩⟩
  simpa [E, curveA, curveB, curveC] using h

end

end MetaMathlibExt
