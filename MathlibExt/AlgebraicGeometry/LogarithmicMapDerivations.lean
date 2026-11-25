/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Module.Hom

/-!
# Actual logarithmic map derivations

The local Li modules retain the logarithmic value eta in addition to the
ordinary derivation. At a boundary the equation is d(z)=f(z)*eta. At a
node it is d(w_i)=f(w_i)*eta_i, with eta_0+eta_1 in the actual base
coefficient image. Smoothing-parameter derivatives also lie in that image.
These are literal submodules, including when a normal coordinate vanishes.

The geometric coefficient map below is the actual 1-tensor map into
R tensor_A I. It does not choose an arbitrary coefficient subspace.
Source: Jun Li arXiv:math/0110113v1, Definitions1.9/1.12,
equations1.18--1.20 and the relative boundary formula on printed p21.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LogarithmicMapDerivations

open scoped TensorProduct

section
variable {k A B M I : Type} [CommRing k] [CommRing A] [CommRing B]
  [AddCommGroup M] [AddCommGroup I] [Algebra k B]
  [Module k M] [Module B M] [Module A M] [Module A I]
  [SMulCommClass k A M] [SMulCommClass A B M]

def derivationLinear : Derivation k B M →ₗ[A] (B →ₗ[k] M) where
  toFun := Derivation.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- For commutative rings `k`, `A`, `B` with `B` a `k`-algebra, and a module `M` over `k`, `A` and
`B` whose `A`-action commutes with the `k`- and `B`-actions: the `A`-submodule of `k`-linear maps
`B → M` formed by the `k`-derivations, the maps `d` with `d (b * c) = b • d c + c • d b` (the image
of `Derivation k B M` in `B →ₗ[k] M`). -/
def derivationSubmodule : Submodule A (B →ₗ[k] M) := LinearMap.range (derivationLinear (k := k))

def parameterCondition {m : ℕ} (t : Fin m → B) (base : I →ₗ[A] M)
    (d : B →ₗ[k] M) : Prop := ∀ i, d (t i) ∈ LinearMap.range base

def ordinaryEquations {m : ℕ} (t : Fin m → B) (base : I →ₗ[A] M) :
    Submodule A (B →ₗ[k] M) where
  carrier := {d | parameterCondition t base d}
  zero_mem' := by intro i; exact ⟨0, map_zero base⟩
  add_mem' := by
    intro d e hd he i
    exact (LinearMap.range base).add_mem (hd i) (he i)
  smul_mem' := by
    intro a d hd i
    exact (LinearMap.range base).smul_mem a (hd i)

def boundaryEquations {m : ℕ} (z : B) (t : Fin m → B) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × M) where
  carrier := {x | x.1 z = z • x.2 ∧ parameterCondition t base x.1}
  zero_mem' := by
    constructor
    · simp
    · intro i; exact ⟨0, map_zero base⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · change x.1 z + y.1 z = z • (x.2 + y.2)
      rw [hx.1, hy.1, smul_add]
    · intro i; exact (LinearMap.range base).add_mem (hx.2 i) (hy.2 i)
  smul_mem' := by
    intro a x hx
    constructor
    · change a • x.1 z = z • (a • x.2)
      rw [hx.1, smul_comm]
    · intro i; exact (LinearMap.range base).smul_mem a (hx.2 i)

def nodeEquations {m : ℕ} (w : Fin 2 → B) (t : Fin m → B) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × (Fin 2 → M)) where
  carrier := {x | (∀ i, x.1 (w i) = w i • x.2 i) ∧
    x.2 0 + x.2 1 ∈ LinearMap.range base ∧ parameterCondition t base x.1}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i; simp
    · simp
    · intro i; exact (LinearMap.range base).zero_mem
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change x.1 (w i) + y.1 (w i) = w i • (x.2 i + y.2 i)
      rw [hx.1 i, hy.1 i, smul_add]
    · change (x.2 0 + y.2 0) + (x.2 1 + y.2 1) ∈ LinearMap.range base
      rw [add_add_add_comm]
      exact (LinearMap.range base).add_mem hx.2.1 hy.2.1
    · intro i; exact (LinearMap.range base).add_mem (hx.2.2 i) (hy.2.2 i)
  smul_mem' := by
    intro a x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change a • x.1 (w i) = w i • (a • x.2 i)
      rw [hx.1 i, smul_comm]
    · change a • x.2 0 + a • x.2 1 ∈ LinearMap.range base
      rw [← smul_add]
      exact (LinearMap.range base).smul_mem a hx.2.1
    · intro i; exact (LinearMap.range base).smul_mem a (hx.2.2 i)

/-- Basis-free local log values. The additive homomorphism is evaluated
on the actual multiplicative log monoid, including all units. Thus unit
coordinate changes impose eta'=eta+d(u)/u automatically. -/
def logarithmicEquations {P : Type} [CommMonoid P] (alpha : P →* B) {m : ℕ}
    (parameter : Fin m → P) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × (Additive P →+ M)) where
  carrier := {x | (∀ p, x.1 (alpha p) = alpha p • x.2 (Additive.ofMul p)) ∧
    (∀ i, x.1 (alpha (parameter i)) ∈ LinearMap.range base) ∧
    (∀ i, x.2 (Additive.ofMul (parameter i)) ∈ LinearMap.range base)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro p; simp
    · intro i; exact (LinearMap.range base).zero_mem
    · intro i; exact (LinearMap.range base).zero_mem
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro p
      change x.1 (alpha p) + y.1 (alpha p) =
        alpha p • (x.2 (Additive.ofMul p) + y.2 (Additive.ofMul p))
      rw [hx.1 p, hy.1 p, smul_add]
    · intro i; exact (LinearMap.range base).add_mem (hx.2.1 i) (hy.2.1 i)
    · intro i; exact (LinearMap.range base).add_mem (hx.2.2 i) (hy.2.2 i)
  smul_mem' := by
    intro a x hx
    refine ⟨?_, ?_, ?_⟩
    · intro p
      change a • x.1 (alpha p) = alpha p • (a • x.2 (Additive.ofMul p))
      rw [hx.1 p, smul_comm]
    · intro i; exact (LinearMap.range base).smul_mem a (hx.2.1 i)
    · intro i; exact (LinearMap.range base).smul_mem a (hx.2.2 i)

def ordinary {m : ℕ} (t : Fin m → B) (base : I →ₗ[A] M) : Submodule A (B →ₗ[k] M) :=
  derivationSubmodule ⊓ ordinaryEquations t base

def boundary {m : ℕ} (z : B) (t : Fin m → B) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × M) :=
  derivationSubmodule.comap (LinearMap.fst A (B →ₗ[k] M) M) ⊓ boundaryEquations z t base

def node {m : ℕ} (w : Fin 2 → B) (t : Fin m → B) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × (Fin 2 → M)) :=
  derivationSubmodule.comap (LinearMap.fst A (B →ₗ[k] M) (Fin 2 → M)) ⊓ nodeEquations w t base

def logarithmic {P : Type} [CommMonoid P] (alpha : P →* B) {m : ℕ}
    (parameter : Fin m → P) (base : I →ₗ[A] M) :
    Submodule A ((B →ₗ[k] M) × (Additive P →+ M)) :=
  derivationSubmodule.comap (LinearMap.fst A (B →ₗ[k] M) (Additive P →+ M)) ⊓
    logarithmicEquations alpha parameter base

end

/-- Literal regular functions that become units on the specified interior.
In a geometric chart the map is actual restriction to that open scheme. -/
def interiorMonoid {B E : Type} [CommRing B] [CommRing E] (restriction : B →+* E) :
    Submonoid B where
  carrier := {b | IsUnit (restriction b)}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using ha.mul hb

variable (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (I : Type)
  [AddCommGroup I] [Module A I]

def coefficientUnit : I →ₗ[A] R ⊗[A] I :=
  TensorProduct.mk A R I 1

@[simp] theorem coefficientUnit_apply (x : I) : coefficientUnit A R I x = 1 ⊗ₜ[A] x := rfl

end MathlibExt.AlgebraicGeometry.LogarithmicMapDerivations
