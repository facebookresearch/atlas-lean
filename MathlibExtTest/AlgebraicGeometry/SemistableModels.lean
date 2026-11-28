/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SemistableModels

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SemistableModels

open _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (π : R)

-- `r = 1`: the chart `x₀ = π` is smooth over the base.
example (d : ℕ) : crossingEquation R π d 1 = MvPolynomial.X 0 - MvPolynomial.C π := by
  have h : Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [Nat.lt_one_iff, Fin.ext_iff, Fin.val_zero]
  rw [crossingEquation, h, Finset.prod_singleton]

-- `r = d + 1`: every coordinate is a crossing coordinate, `x₀ ⋯ x_d = π`.
example (d : ℕ) : crossingEquation R π d (d + 1) =
    (∏ i : Fin (d + 1), MvPolynomial.X i) - MvPolynomial.C π := by
  have h : Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < d + 1) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦ i.isLt
  rw [crossingEquation, h]

-- In the chart ring the crossing coordinates multiply to the uniformizer.
example (d r : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (d + 1) ↦ i.val < r),
      crossingCoordinate R π d r i) = algebraMap R (crossingRing R π d r) π :=
  crossingCoordinate_product R π d r

end MathlibExt.AlgebraicGeometry.SemistableModels
