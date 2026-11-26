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
# Permutation matrix entry formula

Let I be any index type, σ:I≃I a permutation, and R a type with zero and one. The permutation
matrix Pσ has entry Pσ(i,j)=1 when σ(i)=j and 0 otherwise. No finiteness or ring structure is
needed for this entry formula.
-/

open Matrix

namespace Matrix

universe uR uι

variable {R : Type uR} [Zero R] [One R] {ι : Type uι} [DecidableEq ι]

/-- **Entries of a permutation matrix.**

Let I be any index type, R a type with zero and one and σ a permutation of I. For i,j∈I,
(σ.permMatrix R)_(i,j)=if σ(i)=j then 1 else 0.
-/
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
