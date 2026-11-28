/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public noncomputable section

/-!
# Absolute irreducibility and arithmetic determinant for actual lisse coefficients

A continuous representation of the actual arithmetic finite étale fibre
automorphism group is the lisse rational coefficient datum. Absolute
irreducibility is tested after the actual scalar extension to Mathlib's
algebraic closure of Q_ell. Finite determinant is imposed on the entire
arithmetic group. Frobenius polynomials use the actual geometric element
defined by field automorphisms and fibre paths.
-/

namespace MathlibExt.AlgebraicGeometry.AbsoluteLissePurity

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius

universe u

variable (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} {K : Type u}
  [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ X) (r : ℕ)

/-- Lisse rational coefficients: continuous representations of the arithmetic fundamental group
(with its profinite topology) in `GL_r(ℚ_ell)` (with its `ell`-adic topology). -/
abbrev LisseRepresentation := ContinuousMonoidHom (ArithmeticFundamentalGroup x)
  (Matrix.GeneralLinearGroup (Fin r) ℚ_[ell])

/-- Absolute irreducibility after actual coefficient extension. -/
def AbsolutelyIrreducible (ρ : LisseRepresentation ell x r) : Prop :=
  0 < r ∧
  ∀ W : Submodule (AlgebraicClosure ℚ_[ell]) (Fin r → AlgebraicClosure ℚ_[ell]),
    (∀ g : ArithmeticFundamentalGroup x, ∀ v ∈ W,
      ((ρ g).val.map (algebraMap ℚ_[ell] (AlgebraicClosure ℚ_[ell]))).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- Finite order on the entire arithmetic group, not just its geometric kernel. -/
def FiniteArithmeticDeterminant (ρ : LisseRepresentation ell x r) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ g : ArithmeticFundamentalGroup x, (ρ g).val.det ^ N = 1

/-- The characteristic polynomial of geometric Frobenius at the `κ`-valued point `y`, for a finite
field `κ`, mapped to `ℂ` by a coefficient embedding. -/
def frobeniusPolynomial {κ : Type u} [Field κ] [Fintype κ] [Algebra κ K]
    (ρ : LisseRepresentation ell x r) (y : Spec (.of κ) ⟶ X)
    (σ : ArithmeticFrobenius κ K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y))
    (ι : ℚ_[ell] →+* ℂ) : Polynomial ℂ :=
  ((ρ (geometricFrobeniusElement x y σ path)).val.charpoly).map ι

end MathlibExt.AlgebraicGeometry.AbsoluteLissePurity
