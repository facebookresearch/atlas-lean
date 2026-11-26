/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.StableModule
public import Mathlib.LinearAlgebra.Pi

/-!
# Retractions to finite stable matrix stages

For a semiring `k` and a `k`-semimodule `M`, restriction of stable entry coordinates to the
first `r` rows and columns defines a `k`-linear map to `r × r` matrices. Its composite with
the stage-`r` inclusion is the identity, including at `r = 0`.

Thus each finite matrix stage has a linear retraction from the stable matrix semimodule, with
the retraction computed by coordinate evaluation.
-/

@[expose] public section

noncomputable section

universe u v

namespace Matrix.StableModule

variable (k : Type u) [Semiring k] (M : Type v) [AddCommMonoid M] [Module k M]

/-- Restriction of stable matrix entries to a finite square.

For natural `r`, the linear map `Matrix.StableModule.truncate k M r` sends a stable matrix
semimodule element to the matrix of its entries at pairs `(i.val, j.val)` for `i, j : Fin r`. -/
def truncate (r : ℕ) : Matrix.StableModule k M →ₗ[k] Matrix (Fin r) (Fin r) M :=
  (LinearMap.pi fun i : Fin r => LinearMap.pi fun j : Fin r =>
    Finsupp.lapply (i.val, j.val)).comp (finsuppEquiv k M).toLinearMap

/-- Entry formula for finite-square restriction.

For `i, j : Fin r`, the `(i, j)` entry of `truncate k M r X` equals the stable entry `entries
k M X i.val j.val`. -/
@[simp]
theorem truncate_apply (r : ℕ) (X : Matrix.StableModule k M) (i j : Fin r) :
    truncate k M r X i j = entries k M X i.val j.val := rfl

/-- Finite-square restriction retracts the matching stage inclusion.

For an `r × r` matrix `X`, restricting the stable class `ofFinite k M r X` to the first `r`
rows and columns gives `X`. -/
@[simp]
theorem truncate_ofFinite (r : ℕ) (X : Matrix (Fin r) (Fin r) M) :
    truncate k M r (ofFinite k M r X) = X := by
  ext i j
  exact entries_ofFinite_fin k M r X i j

/-- Linear retraction identity for a finite stable matrix stage.

The composite of the stage-`r` inclusion with the linear finite-square restriction is the
identity on `Matrix (Fin r) (Fin r) M`. -/
theorem truncate_comp_ofFinite (r : ℕ) :
    (truncate k M r).comp (ofFinite k M r) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact truncate_ofFinite k M r X

end Matrix.StableModule
