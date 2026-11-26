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
# Stable nonunital matrix rings

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. Matrix multiplication at a common finite stage equips S with its nonunital ring
structure. Its underlying k-module is equivalent to the corresponding module colimit and hence
to (ℕ × ℕ) →₀ A; every finite-stage inclusion is injective.
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

/-- **The stable nonunital matrix ring.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. The finite-stage nonunital ring operations and k-module operations induce the stable
nonunital matrix structure on S.
-/
abbrev Stable : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h) :=
    zeroExtend_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)

namespace Stable

/-- **Inclusion of a finite matrix ring.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. For every n, the map iₙ : Mat(n,n;A) → S preserves addition, multiplication and
k-scalars. It takes B to its finite-stage colimit class.
-/
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

/-- **Positive finite-stage representatives.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. For every x ∈ S there exist n ≥ 0 and B ∈ Mat(n+1,n+1;A) with x = iₙ₊₁(B), including x
represented at size zero.
-/
theorem exists_positive_ofFinite (x : Stable k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- **From the stable ring to its coefficient module.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Let S_alg be the
colimit of Mat(n,n;A) as nonunital matrix rings and S_mod the colimit as k-modules, both under
zero extension. The k-linear map S_alg → S_mod sends each finite-stage class iₙ(B) to the same
matrix class in S_mod.
-/
def toModule : Stable k A →ₗ[k] StableModule k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendAlgHom (k := k) (A := A) h)
    (fun n => StableModule.ofFinite k A n)
    (fun _ _ h B => StableModule.ofFinite_zeroExtend k A h B)

/-- **From the coefficient module to the stable ring.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. For the
matrix-ring colimit S_alg and matrix-module colimit S_mod under zero extension, the k-linear
map S_mod → S_alg sends each finite-stage matrix class to its class in S_alg.
-/
def fromModule : StableModule k A →ₗ[k] Stable k A :=
  DirectLimit.Module.lift k ℕ
    (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) (A := A) h)
    (fun n => (ofFinite k A n : _ →ₗ[k] _))
    (fun _ _ h B => ofFinite_zeroExtend k A h B)

/-- **The forward comparison on a finite stage.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. For the
zero-extension colimits S_alg and S_mod, their k-linear comparison T : S_alg → S_mod satisfies
T(iₙ(B)) = iₙ^mod(B) for every finite matrix B.
-/
@[simp]
theorem toModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    toModule k A (ofFinite k A n B) = StableModule.ofFinite k A n B := rfl

/-- **The reverse comparison on a finite stage.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. For the
zero-extension colimits S_alg and S_mod, their reverse k-linear comparison U : S_mod → S_alg
satisfies U(iₙ^mod(B)) = iₙ(B) for every finite matrix B.
-/
@[simp]
theorem fromModule_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) :
    fromModule k A (StableModule.ofFinite k A n B) = ofFinite k A n B := rfl

/-- **The stable ring and module colimits agree linearly.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. The colimit
S_alg of finite matrix rings and the colimit S_mod of their underlying k-modules, both under
zero extension, are k-linearly equivalent by the map preserving each finite-stage matrix.
-/
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

/-- **Natural-number entries of the stable ring.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. For x = iₙ(B), its entry matrix E(x) on ℕ × ℕ equals B on the n × n square and is zero
outside that square.
-/
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

/-- **Injectivity of finite matrix-ring inclusions.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. For every n, the map iₙ : Mat(n,n;A) → S is injective.
-/
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

/-- **Finite-support coordinates of the stable ring.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. Taking natural-number entries gives a k-linear equivalence S ≃ (ℕ × ℕ) →₀ A.
-/
def finsuppEquiv : Stable k A ≃ₗ[k] (ℕ × ℕ) →₀ A :=
  (moduleEquiv k A).trans (StableModule.finsuppEquiv k A)

@[simp]
theorem finsuppEquiv_apply (x : Stable k A) (p : ℕ × ℕ) :
    finsuppEquiv k A x p = entries k A x p.1 p.2 := rfl

/-- **Multiplication at a common finite stage.**

Let k be a commutative ring and A a nonunital ring with a k-module structure. Write S = colimₙ
Mat(n,n;A), with transition maps extending each finite matrix by zero outside its upper-left
square. For B,C ∈ Mat(n,n;A), one has iₙ(B)iₙ(C) = iₙ(BC). Thus multiplication of stable
matrices can be evaluated after putting both representatives in a common finite square.
-/
theorem mul_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) :
    ofFinite k A n B * ofFinite k A n C = ofFinite k A n (B * C) :=
  (map_mul (ofFinite k A n) B C).symm

theorem mul_entries_ofFinite (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B * ofFinite k A n C) i.val j.val =
      ∑ p : Fin n, B i p * C p j := by
  rw [mul_ofFinite, entries_ofFinite_fin, Matrix.mul_apply]

end Stable

end Matrix
