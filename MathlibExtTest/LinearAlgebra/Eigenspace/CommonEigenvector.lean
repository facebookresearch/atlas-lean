/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector

@[expose] public section

-- Consumer with the original binders.
example {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v :=
  Module.End.exists_common_eigenvector_of_commute T hcomm

-- Higher-universe consumer.
example {K : Type 1} [Field K] [IsAlgClosed K] {V : Type 1} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type 1} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v :=
  Module.End.exists_common_eigenvector_of_commute T hcomm

-- Concrete consumer: the two commuting diagonal matrices `diag(1, 2)` and `diag(3, 4)` over `ℂ`.
example :
    ∃ (χ : Fin 2 → ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      ∀ i, Matrix.toLinAlgEquiv' (Matrix.diagonal (![![1, 2], ![3, 4]] i)) v = χ i • v :=
  Module.End.exists_common_eigenvector_of_commute _ fun _ _ =>
    (Matrix.commute_diagonal _ _).map Matrix.toLinAlgEquiv'
