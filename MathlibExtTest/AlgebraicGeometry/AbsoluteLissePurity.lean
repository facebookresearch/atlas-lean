/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AbsoluteLissePurity

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius
open MathlibExt.AlgebraicGeometry.AbsoluteLissePurity

namespace MathlibExtTest.AlgebraicGeometry.AbsoluteLissePurity

universe u

variable (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
  (x : Spec (.of K) ⟶ X)

-- The trivial representation has determinant of finite order.
example (r : ℕ) : FiniteArithmeticDeterminant ell x r 1 :=
  ⟨1, one_pos, fun _ ↦ by simp⟩

-- Absolute irreducibility excludes the zero representation.
example (ρ : LisseRepresentation ell x 0) : ¬ AbsolutelyIrreducible ell x 0 ρ :=
  fun h ↦ (lt_irrefl 0) h.1

-- The trivial rank-two representation is not absolutely irreducible: the first coordinate
-- line is a proper nonzero invariant subspace.
example : ¬ AbsolutelyIrreducible ell x 2 1 := by
  rintro ⟨-, h⟩
  let W : Submodule (AlgebraicClosure ℚ_[ell]) (Fin 2 → AlgebraicClosure ℚ_[ell]) :=
    Submodule.span _ {Pi.single 0 1}
  have hinv : ∀ g : ArithmeticFundamentalGroup x, ∀ v ∈ W,
      (((1 : LisseRepresentation ell x 2) g).val.map
        (algebraMap ℚ_[ell] (AlgebraicClosure ℚ_[ell]))).mulVec v ∈ W := by
    intro g v hv
    simpa using hv
  rcases h W hinv with hW | hW
  · have : (Pi.single 0 1 : Fin 2 → AlgebraicClosure ℚ_[ell]) ∈ W := Submodule.subset_span rfl
    rw [hW, Submodule.mem_bot] at this
    simpa using congr_fun this 0
  · have : (Pi.single 1 1 : Fin 2 → AlgebraicClosure ℚ_[ell]) ∈ W := hW ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    simpa using congr_fun hc 1

-- Lisse coefficients are continuous by construction.
example (r : ℕ) (ρ : LisseRepresentation ell x r) : Continuous ρ :=
  ρ.continuous_toFun

-- The Frobenius polynomial of the trivial representation is `(X - 1) ^ r` under every
-- coefficient embedding.
example {κ : Type u} [Field κ] [Fintype κ] [Algebra κ K] (r : ℕ) (y : Spec (.of κ) ⟶ X)
    (σ : ArithmeticFrobenius κ K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y))
    (ι : ℚ_[ell] →+* ℂ) :
    frobeniusPolynomial ell x r 1 y σ path ι = (Polynomial.X - 1) ^ r := by
  simp [frobeniusPolynomial, Matrix.charpoly_one]

end MathlibExtTest.AlgebraicGeometry.AbsoluteLissePurity
