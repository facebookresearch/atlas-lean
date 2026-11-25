/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @vonbo, Avocado
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

/-!
# Entry formula for permutation matrices

`Matrix.permMatrix_entry_eq` gives the entries of `Equiv.Perm.permMatrix`:
`(σ.permMatrix R) i j = if σ i = j then 1 else 0`, requiring only
`[Zero R] [One R]`.

This lives in its own lightweight module — rather than alongside the
monomial-matrix / general-linear-group theory — so that basic results about
permutation matrices (e.g. the Birkhoff–von Neumann 2×2 classification) do
not pull in the permutation-cocycle, determinant, special-linear-group, and
semidirect-product dependencies. It is stated in the `Matrix` namespace,
matching Mathlib's existing permutation-matrix API (`Matrix.permMatrix_one`,
`Matrix.det_permutation`), not the `GeneralLinearGroup` namespace.
-/

open Matrix

namespace Matrix

universe uR uι

variable {R : Type uR} [Zero R] [One R] {ι : Type uι} [DecidableEq ι]

/-- Entry formula for permutation matrices: `(σ.permMatrix R) i j` is `1` if
`σ i = j` and `0` otherwise. Registered as a `simp` lemma. -/
@[simp]
theorem permMatrix_entry_eq (σ : Equiv.Perm ι) (i j : ι) :
    (σ.permMatrix R : Matrix ι ι R) i j = if σ i = j then 1 else 0 := by
  classical
  have h1 : (σ.permMatrix R) i j =
      if j ∈ (Equiv.toPEquiv σ) i then (1 : R) else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  have hmem : (j ∈ (Equiv.toPEquiv σ) i) ↔ σ i = j := by
    rw [Equiv.toPEquiv_apply]
    simp
  calc (σ.permMatrix R) i j
      = if j ∈ (Equiv.toPEquiv σ) i then (1 : R) else 0 := h1
    _ = if σ i = j then 1 else 0 := if_congr hmem rfl rfl

end Matrix
