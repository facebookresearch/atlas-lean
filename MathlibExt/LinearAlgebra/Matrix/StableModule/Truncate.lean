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
# Finite-square retractions of stable matrix modules

For a semiring `k` and a `k`-semimodule `M`, restriction of stable matrix
entries to an `r × r` square is k-linear and is a left inverse to the
inclusion of the `r`th finite matrix stage.
-/

@[expose] public section

noncomputable section

universe u v

namespace Matrix.StableModule

variable (k : Type u) [Semiring k] (M : Type v) [AddCommMonoid M] [Module k M]

/-- Restrict stable matrix entries to the first `r` rows and columns. -/
def truncate (r : ℕ) : Matrix.StableModule k M →ₗ[k] Matrix (Fin r) (Fin r) M :=
  (LinearMap.pi fun i : Fin r => LinearMap.pi fun j : Fin r =>
    Finsupp.lapply (i.val, j.val)).comp (finsuppEquiv k M).toLinearMap

@[simp]
theorem truncate_apply (r : ℕ) (X : Matrix.StableModule k M) (i j : Fin r) :
    truncate k M r X i j = entries k M X i.val j.val := rfl

/-- Finite-square restriction is a left inverse to the finite-stage inclusion. -/
@[simp]
theorem truncate_ofFinite (r : ℕ) (X : Matrix (Fin r) (Fin r) M) :
    truncate k M r (ofFinite k M r X) = X := by
  ext i j
  exact entries_ofFinite_fin k M r X i j

theorem truncate_comp_ofFinite (r : ℕ) :
    (truncate k M r).comp (ofFinite k M r) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact truncate_ofFinite k M r X

end Matrix.StableModule
