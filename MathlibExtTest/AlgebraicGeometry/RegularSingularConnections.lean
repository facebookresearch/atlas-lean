/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RegularSingularConnections
import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves

/-!
# Rational connections, solution sections and compact-support sheaves

Focused checks of the regular-singular connection API on concrete data:

* the connection of the zero matrix is the normalized derivation, so it sends the coordinate
  vector to the constant vector `1`, while a constant scalar matrix shifts constants;
* the Leibniz rule against the coordinate `t` produces exactly one extra copy of the vector;
* constant matrices have no poles and evaluate to themselves;
* the finite place at `a` contains `t - a`;
* the solution sections of the zero connection contain the constant vector functions
  extended by zero, and nonzero values off the open are excluded;
* the abelian structure of compact-support sheaves uses the hom-groups inherited from all
  sheaves (no second preadditive structure).
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RegularSingularConnections

open MathlibExt.AlgebraicGeometry.RegularSingularConnections

variable (δ : RationalDerivative)

/-- The zero connection is the normalized derivation, coordinatewise. -/
example (v : Fin 2 → RationalFunctions) :
    connection δ (0 : Matrix (Fin 2) (Fin 2) RationalFunctions) v = fun i ↦ δ.derivation (v i) := by
  ext i
  simp [connection]

/-- On the coordinate vector, the zero connection gives the constant vector `1`. -/
example :
    connection δ (0 : Matrix (Fin 2) (Fin 2) RationalFunctions) (fun _ ↦ RatFunc.X) =
      fun _ ↦ 1 := by
  ext i
  simp [connection, δ.coordinate]

/-- The connection of the scalar matrix `c • 1` sends the constant vector `1` to `-c`. -/
example (c : ℂ) :
    connection δ ((RatFunc.C (K := ℂ) c : RationalFunctions) •
        (1 : Matrix (Fin 2) (Fin 2) RationalFunctions)) (fun _ ↦ 1) =
      fun _ ↦ -(RatFunc.C (K := ℂ) c : RationalFunctions) := by
  ext i
  simp [connection, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Leibniz against the coordinate `t`, using the normalization `δ t = 1`. -/
example {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions) (v : Fin r → RationalFunctions) :
    connection δ A ((RatFunc.X : RationalFunctions) • v) =
      (RatFunc.X : RationalFunctions) • connection δ A v + v := by
  rw [connection_leibniz, δ.coordinate, one_smul]

/-- Constant matrices have no poles anywhere. -/
example (S : Finset ℂ) : PolesWithin S (1 : Matrix (Fin 2) (Fin 2) RationalFunctions) := by
  intro z _ i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/-- The zero matrix has no poles anywhere. -/
theorem polesWithin_zero (S : Finset ℂ) {r : ℕ} :
    PolesWithin S (0 : Matrix (Fin r) (Fin r) RationalFunctions) := by
  intro z _ i j
  simp

/-- The coefficient `1/t` has its pole at `0`. -/
abbrev inverseCoordinate : Matrix (Fin 1) (Fin 1) RationalFunctions :=
  Matrix.of fun _ _ ↦ algebraMap (Polynomial ℂ) RationalFunctions 1 /
    algebraMap (Polynomial ℂ) RationalFunctions Polynomial.X

theorem inverseCoordinate_denom :
    (algebraMap (Polynomial ℂ) RationalFunctions 1 /
      algebraMap (Polynomial ℂ) RationalFunctions Polynomial.X).denom = Polynomial.X := by
  rw [RatFunc.denom_div _ Polynomial.X_ne_zero]
  simp

theorem inverseCoordinate_num :
    (algebraMap (Polynomial ℂ) RationalFunctions 1 /
      algebraMap (Polynomial ℂ) RationalFunctions Polynomial.X).num = 1 := by
  rw [RatFunc.num_div]
  simp

/-- Hidden-pole regression: `1/t` does not have its poles in `∅`, so no solution sheaf of
`d/dt - 1/t` on the whole line `ℂ` can be formed (the evaluated coefficient at `0` would be the
totalized `1/0 = 0`). -/
example : ¬ PolesWithin (∅ : Finset ℂ) inverseCoordinate := by
  intro h
  have h0 := h 0 (Finset.notMem_empty 0) 0 0
  simp only [inverseCoordinate, Matrix.of_apply] at h0
  rw [inverseCoordinate_denom, Polynomial.eval_X] at h0
  exact h0 rfl

/-- Removing the pole: `1/t` has its poles in `{0}`, so its solution sections on `ℂ \ {0}` are
defined, and there its evaluated coefficient is the actual value `1/z`. -/
theorem inverseCoordinate_poles : PolesWithin ({0} : Finset ℂ) inverseCoordinate := by
  intro z hz i j
  simp only [inverseCoordinate, Matrix.of_apply]
  rw [inverseCoordinate_denom, Polynomial.eval_X]
  simpa using hz

example (z : ℂ) : evaluatedAt inverseCoordinate_poles z 0 0 = 1 / z := by
  rw [evaluatedAt_apply]
  simp only [inverseCoordinate, Matrix.of_apply]
  rw [RatFunc.eval, inverseCoordinate_num, inverseCoordinate_denom]
  simp

/-- Evaluation of a constant matrix is the matrix itself. -/
example (z : ℂ) (c : ℂ) :
    evaluated (Matrix.of fun _ _ : Fin 2 ↦ (RatFunc.C c : RationalFunctions)) z =
      Matrix.of fun _ _ ↦ c := by
  ext i j
  simp [evaluated]

/-- The finite place at `a` is the ideal of `t - a`. -/
example (a : ℂ) : Polynomial.X - Polynomial.C a ∈ (finitePlace a).asIdeal :=
  Ideal.subset_span rfl

open Classical in
/-- A constant vector function, extended by zero off the open, solves the zero connection. -/
example (S : Finset ℂ) (U : TopologicalSpace.Opens (puncturedLine S))
    (w : EuclideanSpace ℂ (Fin 2)) :
    (fun z ↦ if z ∈ ambientOpen S U then w else 0) ∈
      solutionSections S (0 : Matrix (Fin 2) (Fin 2) RationalFunctions) (polesWithin_zero S) U := by
  refine ⟨fun z hz ↦ by simp [hz], fun z hz i ↦ ?_⟩
  have hev : ∀ v : Fin 2 → ℂ,
      (evaluatedAt (polesWithin_zero (r := 2) S) z).mulVec v i = 0 := by
    intro v
    simp [evaluatedAt, evaluated, Matrix.mulVec, dotProduct]
  simp only [hev]
  exact (hasDerivWithinAt_const z (ambientOpen S U) (w i)).congr
    (fun t ht ↦ by simp [ht]) (by simp [hz])

/-- Solution sections vanish off the open: a nonzero value at an omitted point is excluded. -/
example (S : Finset ℂ) {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions)
    (hA : PolesWithin S A)
    (U : TopologicalSpace.Opens (puncturedLine S)) (s : ℂ → EuclideanSpace ℂ (Fin r))
    (z : ℂ) (hz : z ∉ ambientOpen S U) (hs : s z ≠ 0) : s ∉ solutionSections S A hA U :=
  fun h ↦ hs (h.1 z hz)

end MathlibExtTest.AlgebraicGeometry.RegularSingularConnections

namespace MathlibExtTest.AlgebraicGeometry.CompactSupportIndSheaves

open CategoryTheory MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves

/-- The abelian structure of compact-support sheaves is built on the inherited hom-groups. -/
example (k : Type) [Field k] (X : TopCat.{0}) [CompactSheafSource k X] :
    (inferInstance : Abelian (CompactSheaf k X)).toPreadditive =
      Preadditive.fullSubcategory (IsCompactSupported k X) :=
  rfl

/-- Ind-sheaf presentations have small (`Type 0`) index categories. -/
example (k : Type) [Field k] (X : TopCat.{0}) (F : IndSheaf k X) : Type 0 :=
  (indPresentation k X F).I

end MathlibExtTest.AlgebraicGeometry.CompactSupportIndSheaves
