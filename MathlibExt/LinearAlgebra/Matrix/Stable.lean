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

/-!
# Stable matrix rings and finite entry coordinates

Let `k` be a commutative ring and `A` a nonunital ring with a `k`-module structure, in
independent universes. Finite square matrices over `A` form a direct system under top-left
zero extension. Its direct limit is the stable matrix ring, and each finite-stage inclusion
preserves addition, multiplication, and the `k`-action.

The underlying `k`-module is equivalent to the stable matrix module and to finitely supported
`A`-valued functions on `ℕ × ℕ`. Every stable matrix has bounded entry support. Products of
representatives in a common size `n` have entries `∑ p : Fin n, B i p * C p j`, with
coefficient multiplication in that order.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe u v

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]

local instance : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) :=
  zeroExtend_directedSystem (k := k) (A := A)

local instance : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) (A := A) h) :=
  zeroExtendLinear_directedSystem (k := k) (A := A)

/-- Stable matrix ring as a direct limit.

For a commutative ring `k` and a nonunital ring `A` with a `k`-module structure,
`Matrix.Stable k A` is the direct limit of the finite square matrix rings under top-left zero
extension. Its carrier lies in the universe of `A`. -/
abbrev Stable : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) :=
    zeroExtend_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)

namespace Stable

/-- Finite-stage inclusion in the stable matrix ring.

For natural `n`, the map from `n × n` matrices over `A` to `Matrix.Stable k A` preserves
addition, multiplication, and `k`-scalars. It sends a finite matrix to its stable class. -/
def ofFinite (n : ℕ) : Matrix (Fin n) (Fin n) A →ₙₐ[k] Stable k A :=
  DirectLimit.NonUnitalAlgebra.of (R := k)
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) n

/-- Stable ring class is unchanged by zero extension.

If `n ≤ m`, the class of the top-left zero extension of an `n × n` matrix in stage `m` equals
its class in stage `n`. -/
@[simp]
theorem ofFinite_zeroExtend {n m : ℕ} (h : n ≤ m) (B : Matrix (Fin n) (Fin n) A) :
    ofFinite k A m (zeroExtend h B) = ofFinite k A n B :=
  DirectLimit.NonUnitalAlgebra.of_f (R := k)
    (G := fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (f := fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) h B

/-- Finite representative of every stable matrix ring element.

Every `x : Matrix.Stable k A` equals the image of some `n × n` matrix under the stage-`n`
inclusion. -/
theorem exists_ofFinite (x : Stable k A) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) A), x = ofFinite k A n B :=
  DirectLimit.exists_eq_mk (f := fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) x

/-- Positive-size representative of every stable matrix ring element.

Every stable matrix has a representative of size `n + 1` for some natural `n`. A size-zero
representative may be extended by zero to a positive stage. -/
theorem exists_positive_ofFinite (x : Stable k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- Stable ring carrier maps to the stable matrix module.

The `k`-linear map from `Matrix.Stable k A` to `Matrix.StableModule k A` is induced by the
identity on each finite matrix stage. -/
def toModule : Stable k A →ₗ[k] StableModule k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)
    (fun n => StableModule.ofFinite k A n)
    (fun _ _ h B => StableModule.ofFinite_zeroExtend k A h B)

/-- Stable matrix module maps to the ring carrier.

The `k`-linear map from `Matrix.StableModule k A` to `Matrix.Stable k A` sends each finite-
stage module class to the same finite-stage ring class. -/
def fromModule : StableModule k A →ₗ[k] Stable k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) (A := A) h)
    (fun n => (ofFinite k A n : _ →ₗ[k] _))
    (fun _ _ h B => ofFinite_zeroExtend k A h B)

/-- Ring-to-module comparison on finite matrices.

The map `Matrix.Stable.toModule k A` sends the ring class of an `n × n` matrix `B` to
`Matrix.StableModule.ofFinite k A n B`. -/
@[simp]
theorem toModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    toModule k A (ofFinite k A n B) = StableModule.ofFinite k A n B := rfl

/-- Module-to-ring comparison on finite matrices.

The map `Matrix.Stable.fromModule k A` sends the module class of an `n × n` matrix `B` to
`Matrix.Stable.ofFinite k A n B`. -/
@[simp]
theorem fromModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    fromModule k A (StableModule.ofFinite k A n B) = ofFinite k A n B := rfl

/-- Stable matrix ring carrier and stable matrix module are equivalent.

The identity maps on finite stages induce mutually inverse `k`-linear maps between
`Matrix.Stable k A` and `Matrix.StableModule k A`. -/
def moduleEquiv : Stable k A ≃ₗ[k] StableModule k A :=
  { toModule k A with
    invFun := fromModule k A
    left_inv x := by
      refine DirectLimit.induction _ (fun n B => ?_) x
      rfl
    right_inv x := by
      refine DirectLimit.induction _ (fun n B => ?_) x
      rfl }

/-- Forward stable module equivalence preserves finite classes.

The forward map of `Matrix.Stable.moduleEquiv k A` sends a finite matrix ring class to its
finite matrix module class in the same stage. -/
@[simp]
theorem moduleEquiv_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    moduleEquiv k A (ofFinite k A n B) = StableModule.ofFinite k A n B := rfl

/-- Inverse stable module equivalence preserves finite classes.

The inverse of `Matrix.Stable.moduleEquiv k A` sends a finite matrix module class to its
finite matrix ring class in the same stage. -/
@[simp]
theorem moduleEquiv_symm_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    (moduleEquiv k A).symm (StableModule.ofFinite k A n B) = ofFinite k A n B := rfl

/-- Natural-number entry coordinates of stable matrix ring elements.

For `x : Matrix.Stable k A`, its entry function on `ℕ × ℕ` is obtained through the linear
equivalence with the stable matrix module. A finite representative is extended by zero outside
its square. -/
def entries (x : Stable k A) : Matrix ℕ ℕ A := StableModule.entries k A (moduleEquiv k A x)

/-- Entry formula for a finite matrix ring class.

The `(i, j)` entry of the stage-`n` class of `B` is `B ⟨i, hi⟩ ⟨j, hj⟩` when `i < n` and `j <
n`, and is zero if either index lies outside the square. -/
@[simp]
theorem entries_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : ℕ) :
    entries k A (ofFinite k A n B) i j =
      if hi : i < n then if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

/-- Stable ring entries agree with the finite matrix inside its square.

For `i, j : Fin n`, the stable entries of the stage-`n` class of `B` at `(i.val, j.val)` equal
`B i j`. -/
theorem entries_ofFinite_fin (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B) i.val j.val = B i j :=
  StableModule.entries_ofFinite_fin k A n B i j

/-- Entry coordinates determine a stable matrix ring element.

Two elements of `Matrix.Stable k A` with equal natural-number entry functions are equal. -/
theorem entries_injective : Function.Injective (entries k A) :=
  (StableModule.entries_injective k A).comp (moduleEquiv k A).injective

/-- Each finite matrix ring stage embeds injectively.

For each natural `n`, `Matrix.Stable.ofFinite k A n` is injective. -/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite k A n) :=
  DirectLimit.mk_injective
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)
    (fun _ _ h => zeroExtend_injective (A := A) h) n

/-- Stable matrix ring entries vanish outside a finite square.

For every stable matrix `x`, there is a natural `n` such that its `(i, j)` entry is zero
whenever `n ≤ i` or `n ≤ j`. -/
theorem entries_bounded (x : Stable k A) :
    ∃ n, ∀ i j : ℕ, n ≤ i ∨ n ≤ j → entries k A x i j = 0 :=
  StableModule.entries_bounded k A (moduleEquiv k A x)

/-- Stable matrix ring entry functions have finite support.

The support of the function `(i, j) ↦ Matrix.Stable.entries k A x i j` is finite for every
stable matrix ring element `x`. -/
theorem entries_finiteSupport (x : Stable k A) :
    (Function.support (fun p : ℕ × ℕ => entries k A x p.1 p.2)).Finite :=
  StableModule.entries_finiteSupport k A (moduleEquiv k A x)

/-- Stable matrix ring carrier as finitely supported entries.

The underlying `k`-module of `Matrix.Stable k A` is linearly equivalent to `(ℕ × ℕ) →₀ A`,
through the stable module equivalence and its entry-coordinate equivalence. -/
def finsuppEquiv : Stable k A ≃ₗ[k] (ℕ × ℕ) →₀ A :=
  (moduleEquiv k A).trans (StableModule.finsuppEquiv k A)

/-- Finitely supported coordinate of a stable matrix ring element.

Evaluating `Matrix.Stable.finsuppEquiv k A x` at `(i, j)` gives the stable matrix entry at row
`i` and column `j`. -/
@[simp]
theorem finsuppEquiv_apply (x : Stable k A) (p : ℕ × ℕ) :
    finsuppEquiv k A x p = entries k A x p.1 p.2 := rfl

/-- Stable multiplication in a common finite matrix stage.

For `n × n` matrices `B` and `C`, the product of their stable classes is the stable class of
their matrix product `B * C` in the same stage. -/
theorem mul_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) :
    ofFinite k A n B * ofFinite k A n C = ofFinite k A n (B * C) :=
  (map_mul (ofFinite k A n) B C).symm

/-- Entry formula for a product of finite stable ring classes.

For `i, j : Fin n`, the `(i.val, j.val)` entry of the product of the stable classes of `B` and
`C` is `∑ p : Fin n, B i p * C p j`. The factor order is retained for noncommutative `A`. -/
theorem mul_entries_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B * ofFinite k A n C) i.val j.val =
      ∑ p : Fin n, B i p * C p j := by
  rw [mul_ofFinite, entries_ofFinite_fin, Matrix.mul_apply]

end Stable

end Matrix
