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
# Stable nonunital matrix algebras

The algebra is the native `DirectLimit` of finite square matrix algebras under
top-left zero extension. Its nonunital ring and ground module are native
direct-limit structures. The actual identity-on-stages module comparison
identifies it with the coefficient matrix direct limit and hence with literal
finite-support matrix coordinates. No equality of chosen colimit carriers is
assumed, and multiplication always comes from a common finite stage.
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

/-- The actual stable nonunital algebra, with native direct-limit multiplication. -/
abbrev Stable : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) :=
    zeroExtend_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)

namespace Stable

/-- The actual native nonunital algebra inclusion of a finite stage. -/
def ofFinite (n : ℕ) : Matrix (Fin n) (Fin n) A →ₙₐ[k] Stable k A :=
  DirectLimit.NonUnitalAlgebra.of (R := k)
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) n

@[simp]
theorem ofFinite_zeroExtend {n m : ℕ} (h : n ≤ m) (B : Matrix (Fin n) (Fin n) A) :
    ofFinite k A m (zeroExtend h B) = ofFinite k A n B :=
  DirectLimit.NonUnitalAlgebra.of_f (R := k)
    (G := fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (f := fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) h B

theorem exists_ofFinite (x : Stable k A) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) A), x = ofFinite k A n B :=
  DirectLimit.exists_eq_mk (f := fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) x

/-- Positive finite stages suffice, including for an element from the size-zero stage. -/
theorem exists_positive_ofFinite (x : Stable k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- The identity-on-stages ground-linear map from the stable algebra to the stable module. -/
def toModule : Stable k A →ₗ[k] StableModule k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)
    (fun n => StableModule.ofFinite k A n)
    (fun _ _ h B => StableModule.ofFinite_zeroExtend k A h B)

/-- The identity-on-stages ground-linear map from the stable module to the stable algebra. -/
def fromModule : StableModule k A →ₗ[k] Stable k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) (A := A) h)
    (fun n => (ofFinite k A n : _ →ₗ[k] _))
    (fun _ _ h B => ofFinite_zeroExtend k A h B)

/-- The forward native colimit map retains its actual finite-stage values. -/
@[simp]
theorem toModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    toModule k A (ofFinite k A n B) = StableModule.ofFinite k A n B := rfl

/-- The reverse native colimit map retains its actual finite-stage values. -/
@[simp]
theorem fromModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    fromModule k A (StableModule.ofFinite k A n B) = ofFinite k A n B := rfl

/-- The actual identity-on-stages comparison of the native algebra and module colimits. -/
def moduleEquiv : Stable k A ≃ₗ[k] StableModule k A :=
  { toModule k A with
    invFun := fromModule k A
    left_inv x := by
      refine DirectLimit.induction _ (fun n B => ?_) x
      rfl
    right_inv x := by
      refine DirectLimit.induction _ (fun n B => ?_) x
      rfl }

@[simp]
theorem moduleEquiv_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    moduleEquiv k A (ofFinite k A n B) = StableModule.ofFinite k A n B := rfl

@[simp]
theorem moduleEquiv_symm_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    (moduleEquiv k A).symm (StableModule.ofFinite k A n B) = ofFinite k A n B := rfl

/-- Actual entries of the stable algebra, obtained by the earned module comparison. -/
def entries (x : Stable k A) : Matrix ℕ ℕ A := StableModule.entries k A (moduleEquiv k A x)

@[simp]
theorem entries_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : ℕ) :
    entries k A (ofFinite k A n B) i j =
      if hi : i < n then if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

theorem entries_ofFinite_fin (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B) i.val j.val = B i j :=
  StableModule.entries_ofFinite_fin k A n B i j

theorem entries_injective : Function.Injective (entries k A) :=
  (StableModule.entries_injective k A).comp (moduleEquiv k A).injective

/-- Injectivity of finite inclusions is the native direct-limit injectivity criterion. -/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite k A n) :=
  DirectLimit.mk_injective
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)
    (fun _ _ h => zeroExtend_injective (A := A) h) n

theorem entries_bounded (x : Stable k A) :
    ∃ n, ∀ i j : ℕ, n ≤ i ∨ n ≤ j → entries k A x i j = 0 :=
  StableModule.entries_bounded k A (moduleEquiv k A x)

theorem entries_finiteSupport (x : Stable k A) :
    (Function.support (fun p : ℕ × ℕ => entries k A x p.1 p.2)).Finite :=
  StableModule.entries_finiteSupport k A (moduleEquiv k A x)

/-- The actual stable algebra has all, and only, finite-support matrix coordinates. -/
def finsuppEquiv : Stable k A ≃ₗ[k] (ℕ × ℕ) →₀ A :=
  (moduleEquiv k A).trans (StableModule.finsuppEquiv k A)

@[simp]
theorem finsuppEquiv_apply (x : Stable k A) (p : ℕ × ℕ) :
    finsuppEquiv k A x p = entries k A x p.1 p.2 := rfl

/-- Multiplication is computed in a genuine common finite stage. -/
theorem mul_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) :
    ofFinite k A n B * ofFinite k A n C = ofFinite k A n (B * C) :=
  (map_mul (ofFinite k A n) B C).symm

theorem mul_entries_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B * ofFinite k A n C) i.val j.val =
      ∑ p : Fin n, B i p * C p j := by
  rw [mul_ofFinite, entries_ofFinite_fin, Matrix.mul_apply]

end Stable

end Matrix
