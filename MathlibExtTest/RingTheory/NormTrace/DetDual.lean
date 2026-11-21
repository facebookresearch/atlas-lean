/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.NormTrace.DetDual

/-- Consumer with the original binders. -/
theorem exactSource (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det =
      Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det :=
  Algebra.det_dual_mul_mul_eq_norm_mul_det R A b τ c

universe u

/-- The statement also applies with the coefficient ring in a higher
universe. -/
example (R : Type (u + 1)) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det =
      Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det :=
  Algebra.det_dual_mul_mul_eq_norm_mul_det R A b τ c

/-- Scaling by `1` leaves the determinant unchanged, as its norm is `1`. -/
example (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    (τ : Module.Dual R A) :
    (Matrix.of fun i j => τ (1 * b i * b j)).det =
      (Matrix.of fun i j => τ (b i * b j)).det := by
  rw [Algebra.det_dual_mul_mul_eq_norm_mul_det R A b τ 1, map_one, one_mul]
