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
# Linear maps into a dependent direct sum

Let R be a semiring, M an R-semimodule, I arbitrary and N_i R-semimodules. A family f_i:M→N_i
of linear maps defines F:M→⊕iN_i when {i:f_i(x)≠0} is finite for each x, with F(x)_i=f_i(x).
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

/-- **Direct-sum linear map from a pointwise finite-support family.**

Let R be a semiring, M,N_i R-semimodules and f_i:M→N_i linear. If each x∈M has only finitely
many nonzero values f_i(x), linearMapOfFiniteSupport f hf:M→⊕iN_i is x↦(f_i(x))_i.
-/
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

/-- **Coordinate of the finite-support linear-map construction.**

For R-semimodules M,N_i and a linear family f_i with finite support on each input,
linearMapOfFiniteSupport f hf x i=f_i(x).
-/
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
