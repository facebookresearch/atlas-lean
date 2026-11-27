/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.K3IntegralLattice
public import Mathlib.GroupTheory.Coxeter.Matrix

@[expose] public section

/-!
# Tests for the K3 Gram matrix

The Gram matrix is symmetric and even. Its first six indices form three
hyperbolic planes `U`, orthogonal to everything else; the remaining two
blocks of eight are orthogonal to each other, and each is the negative of the
`E₈` Cartan matrix: `-2` on the diagonal and `1` exactly on the edges of the
`E₈` diagram, read off Mathlib's Coxeter matrix `CoxeterMatrix.E₈` (entry `3`
on an edge). A connected space is nonempty, so the K3 request does not apply to
the empty surface.
-/

open MathlibExt.AlgebraicGeometry.K3IntegralLattice

namespace MathlibExtTest.AlgebraicGeometry.K3IntegralLattice

example : gram.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : ∀ i, gram i i % 2 = 0 := by decide

/-- The first six indices form three mutually orthogonal hyperbolic planes. -/
example : ∀ a b : Fin 2, ∀ k l : Fin 3,
    gram ⟨2 * k + a, by omega⟩ ⟨2 * l + b, by omega⟩ =
      if k = l ∧ a ≠ b then 1 else 0 := by
  decide

/-- The hyperbolic planes are orthogonal to the `E₈` blocks. -/
example : ∀ (i : Fin 6) (j : Fin 16), gram ⟨i, by omega⟩ ⟨6 + j, by omega⟩ = 0 := by
  decide

/-- Both `E₈` blocks are the negative `E₈` Cartan matrix, in Bourbaki's
labelling shared with Mathlib's Coxeter matrix. -/
example : ∀ (b : Fin 2) (i j : Fin 8),
    gram ⟨6 + 8 * b + i, by omega⟩ ⟨6 + 8 * b + j, by omega⟩ =
      if i = j then -2 else if CoxeterMatrix.E₈ i j = 3 then 1 else 0 := by
  decide

/-- The two `E₈` blocks are orthogonal. -/
example : ∀ i j : Fin 8, gram ⟨6 + i, by omega⟩ ⟨14 + j, by omega⟩ = 0 := by
  decide

example : latticePairing (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp [latticePairing, Pi.single_apply, Finset.sum_ite_eq']
  decide

example (Z : Type) [TopologicalSpace Z] [ConnectedSpace Z] : Nonempty Z := inferInstance

end MathlibExtTest.AlgebraicGeometry.K3IntegralLattice
