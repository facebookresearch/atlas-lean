/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.TropicalTorIntersection
import MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections

/-!
# Tests for Tor intersection coefficients

A vanishing Tor module has length zero, and an intersection with the unit ideal is empty, so its
length coefficient is zero. Relative genericity only constrains a displacement by pairs of cells
whose direction sum misses part of the ambient direction: a padding cell of full dimension, even
of weight zero, imposes no condition.
-/

open MathlibExt.AlgebraicGeometry.TropicalTorIntersection
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
open MathlibExt.AlgebraicGeometry.GeneralAmbientTropicalIntersections
open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates

/-- Vanishing Tor modules have length zero. -/
example (I J : Ideal ℤ) (q : ℕ) (h : CategoryTheory.Limits.IsZero (torModule ℤ I J q)) :
    Module.length ℤ (torModule ℤ I J q) = 0 :=
  torLength_zero ℤ h

/-- An intersection with the unit ideal has length coefficient zero. -/
example (J : Ideal ℤ) : schemeCoefficient ℤ ⊤ J = 0 := by
  rw [schemeCoefficient, top_sup_eq, Module.length_eq_zero_iff]
  exact Ideal.Quotient.subsingleton_iff.mpr rfl

/-- Pairs of cells whose direction sum contains the ambient direction impose no genericity
condition: every ambient vector is then relatively generic. -/
example {n : ℕ} {Y A B : WeightedComplex n} {w : RealSpace n} (S : SimplePoint Y w)
    (v : RealSpace n) (hv : v ∈ ambientDirection S)
    (h : ∀ i j, w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      ambientDirection S ≤ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction) :
    RelativeGeneric S A B v :=
  ⟨hv, fun i j _ _ hi hj hle ↦ (hle (h i j hi hj)).elim⟩

/-- Cells outside the weighted supports, such as padding cells of weight zero, never constrain the
displacement: only cells inside the supports are tested. -/
example {n : ℕ} {Y A B : WeightedComplex n} {w : RealSpace n} (S : SimplePoint Y w)
    (v : RealSpace n) (hv : v ∈ ambientDirection S)
    (h : ∀ i j, (A.complex.cell i).carrier ⊆ A.support → (B.complex.cell j).carrier ⊆ B.support →
      w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      ¬ ambientDirection S ≤ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction →
      v ∉ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction) :
    RelativeGeneric S A B v :=
  ⟨hv, h⟩

/-- The same holds for the generic displacements of stable products. -/
example {n : ℕ} {A B : WeightedComplex n} {w v : RealSpace n}
    (h : ∀ i j, (A.complex.cell i).carrier ⊆ A.support → (B.complex.cell j).carrier ⊆ B.support →
      w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
      v ∉ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
        (affineSpan ℝ (B.complex.cell j).carrier).direction) :
    GenericDisplacement A B w v :=
  fun i j hA hB hi hj _ ↦ h i j hA hB hi hj

/-- A cell of full dimension through `w`, for instance a weight-zero padding half-plane, never
constrains the displacement. -/
example {n : ℕ} {Y A B : WeightedComplex n} {w : RealSpace n} (S : SimplePoint Y w)
    (i : Fin A.complex.count) (j : Fin B.complex.count)
    (hfull : (affineSpan ℝ (A.complex.cell i).carrier).direction = ⊤) :
    ambientDirection S ≤ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
      (affineSpan ℝ (B.complex.cell j).carrier).direction := by
  rw [hfull, top_sup_eq]
  exact le_top
