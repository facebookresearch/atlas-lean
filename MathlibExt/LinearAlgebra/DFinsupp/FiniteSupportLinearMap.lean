/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Linear maps into dependent finitely supported functions

A family of linear maps f i : M →ₗ[R] N i determines a linear map into the
dependent direct sum whenever its value on every input has finite support.
This file packages that standard construction and exposes its coordinate
formula.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uR uι uM uN

namespace DFinsupp

variable {R : Type uR} [Semiring R]
variable {ι : Type uι}
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : ι → Type uN}
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Assemble a pointwise finitely supported family of linear maps into one
linear map with dependent direct-sum target. -/
noncomputable def linearMapOfFiniteSupport
    (f : ∀ i, M →ₗ[R] N i)
    (hf : ∀ x, {i | f i x ≠ 0}.Finite) :
    M →ₗ[R] Π₀ i, N i := by
  classical
  let toFunImpl (x : M) : Π₀ i, N i :=
    DFinsupp.mk (hf x).toFinset fun i => f i.1 x
  have applyImpl (x : M) (i : ι) : toFunImpl x i = f i x := by
    by_cases hi : i ∈ (hf x).toFinset
    · exact DFinsupp.mk_of_mem hi
    · rw [DFinsupp.mk_of_notMem hi]
      by_contra h
      exact hi ((hf x).mem_toFinset.mpr (Ne.symm h))
  exact
    { toFun := toFunImpl
      map_add' := by
        intro x y
        apply DFinsupp.ext
        intro i
        calc
          toFunImpl (x + y) i = f i (x + y) := applyImpl _ _
          _ = f i x + f i y := map_add _ _ _
          _ = toFunImpl x i + toFunImpl y i := by
            rw [applyImpl, applyImpl]
          _ = (toFunImpl x + toFunImpl y) i := rfl
      map_smul' := by
        intro c x
        apply DFinsupp.ext
        intro i
        calc
          toFunImpl (c • x) i = f i (c • x) := applyImpl _ _
          _ = c • f i x := map_smul _ _ _
          _ = c • toFunImpl x i := by rw [applyImpl]
          _ = (c • toFunImpl x) i := rfl }

/-- Coordinate evaluation of the finite-support linear-map constructor. -/
@[simp]
theorem linearMapOfFiniteSupport_apply
    (f : ∀ i, M →ₗ[R] N i)
    (hf : ∀ x, {i | f i x ≠ 0}.Finite)
    (x : M) (i : ι) :
    linearMapOfFiniteSupport f hf x i = f i x := by
  classical
  unfold linearMapOfFiniteSupport
  dsimp only
  change (DFinsupp.mk (hf x).toFinset
    (fun j => f j.1 x)) i = f i x
  by_cases hi : i ∈ (hf x).toFinset
  · exact DFinsupp.mk_of_mem hi
  · rw [DFinsupp.mk_of_notMem hi]
    by_contra h
    exact hi ((hf x).mem_toFinset.mpr (Ne.symm h))

end DFinsupp

end
