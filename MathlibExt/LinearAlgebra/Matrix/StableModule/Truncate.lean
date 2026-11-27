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
# Truncation of stable coefficient matrices

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. Restricting natural-number entries to an r × r square defines a k-linear
map Tᵣ : S → Mat(r,r;A). It retracts the inclusion iᵣ: Tᵣ(iᵣ(B)) = B, including r = 0.
-/

@[expose] public section

noncomputable section

universe u v

namespace Matrix.StableModule

variable (k : Type u) [Semiring k] (M : Type v) [AddCommMonoid M] [Module k M]

/-- **The finite-square truncation map.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For r ∈ ℕ, define the k-linear map Tᵣ : S → Mat(r,r;A) by Tᵣ(x)ᵢⱼ = E(x)ᵢⱼ
for i,j < r, where E(x) is the natural-number entry matrix of x.
-/
def truncate (r : ℕ) : Matrix.StableModule k M →ₗ[k] Matrix (Fin r) (Fin r) M :=
  (LinearMap.pi fun i : Fin r => LinearMap.pi fun j : Fin r =>
    Finsupp.lapply (i.val, j.val)).comp (finsuppEquiv k M).toLinearMap

@[simp]
theorem truncate_apply (r : ℕ) (X : Matrix.StableModule k M) (i j : Fin r) :
    truncate k M r X i j = entries k M X i.val j.val := rfl

/-- **Truncation retracts the finite-stage inclusion.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For the inclusion iᵣ : Mat(r,r;A) → S and entry restriction Tᵣ : S →
Mat(r,r;A), one has Tᵣ(iᵣ(B)) = B for every B, including the empty matrix when r = 0.
-/
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
