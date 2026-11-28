/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.Basis
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Stock ℓ² bases in the completed Hilbert tensor product

The stock default Hilbert basis of ℓ²(ℕ,ℂ) has the ordinary coordinate
representation. Its completed tensor basis therefore has coordinate
`x i * y j` on a pure tensor, and its basis vectors are completed pairs
of coordinate unit vectors. The nonreal values `1+i` and `2-i` give
coordinate `3+i`, so this completed tensor is nonzero. An empty-index
factor gives an actual subsingleton tensor completion.
-/

noncomputable section

open UniformSpace
open scoped TensorProduct Classical

namespace MathlibExtTest.CompletedTensorBasis

private abbrev L2 (I : Type) := lp (fun _ : I => ℂ) 2
private abbrev basisN : HilbertBasis ℕ ℂ (L2 ℕ) := default
private abbrev productBasis := basisN.completedTensorProduct basisN
private abbrev TensorHilbert := Completion (L2 ℕ ⊗[ℂ] L2 ℕ)

private theorem coordinate_product (x y : L2 ℕ) (i j : ℕ) :
    productBasis.repr (x ⊗ₜ[ℂ] y : TensorHilbert) (i, j) = x i * y j := by
  rw [HilbertBasis.completedTensorProduct_repr_tmul]
  rfl

example (x y : L2 ℕ) (i j : ℕ) :
    productBasis.repr (x ⊗ₜ[ℂ] y : TensorHilbert) (i, j) = x i * y j :=
  coordinate_product x y i j

example (i j : ℕ) :
    productBasis (i, j) =
      (((lp.single 2 i (1 : ℂ) : L2 ℕ) ⊗ₜ[ℂ]
        (lp.single 2 j (1 : ℂ) : L2 ℕ) : L2 ℕ ⊗[ℂ] L2 ℕ) : TensorHilbert) := by
  rw [HilbertBasis.completedTensorProduct_apply,
    ← basisN.repr_symm_single i, ← basisN.repr_symm_single j]
  rfl

private def x : L2 ℕ := lp.single 2 0 (1 + Complex.I)
private def y : L2 ℕ := lp.single 2 1 (2 - Complex.I)
private def nonrealTensor : TensorHilbert := (x ⊗ₜ[ℂ] y : TensorHilbert)

private theorem nonreal_coordinate : productBasis.repr nonrealTensor (0, 1) = 3 + Complex.I := by
  exact (coordinate_product x y 0 1).trans (by
    norm_num [x, y, mul_add, add_mul, Complex.I_mul_I];
    ring_nf; norm_num [pow_two, Complex.I_mul_I]; ring)

example : productBasis.repr nonrealTensor (0, 1) = 3 + Complex.I ∧ nonrealTensor ≠ 0 := by
  refine ⟨nonreal_coordinate, ?_⟩
  intro h
  have hc := nonreal_coordinate
  rw [h, map_zero] at hc
  have hre := congrArg Complex.re hc
  norm_num at hre

private abbrev EmptyHilbert := L2 (Fin 0)
private abbrev EmptyTensor := Completion (EmptyHilbert ⊗[ℂ] L2 ℕ)
private abbrev emptyBasis : HilbertBasis (Fin 0) ℂ EmptyHilbert := default
private abbrev emptyProductBasis := emptyBasis.completedTensorProduct basisN

example : Subsingleton EmptyTensor := by
  constructor
  intro a b
  apply emptyProductBasis.repr.injective
  apply lp.ext
  funext ij
  exact Fin.elim0 ij.1

example (z : EmptyTensor) : z = 0 := by
  apply emptyProductBasis.repr.injective
  apply lp.ext
  funext ij
  exact Fin.elim0 ij.1

end MathlibExtTest.CompletedTensorBasis
