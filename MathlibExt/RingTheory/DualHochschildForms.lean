/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.HochschildCochains
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.RingTheory.Smooth.Basic

/-!
# The actual generator-normalized dual HKR map

The source is the k-linear dual of the native exterior Kähler module
Ω^n_(A/k), and the target is the already constructed Hochschild cochain
complex in n+1 arguments, with dual coefficient bimodule Hom_k(A,k).
Its value is exactly 1/n! times ψ(a0 da1∧…∧dan). This completed
multilinear construction assumes neither cocycle closure nor an HKR
isomorphism. The conditional cohomology map uses the actual cocycle
inclusion and the actual cohomology projection, never a free map.

Sources: Hochschild--Kostant--Rosenberg, *Differential forms on regular
affine algebras*, Trans. AMS102(1962)383–408; Loday, *Cyclic Homology*,
Section3.4. Tau's Dual.lean proves the dual-bimodule interpretation of
these cochains; its normalization/tensor coordinates concern universal
noncommutative forms and do not assert this native Kähler comparison.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.DualHochschildForms

open CategoryTheory
open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]

/-- Native differential forms, not a freely named graded object. -/
abbrev Forms (n : ℕ) := ⋀[A]^n (KaehlerDifferential k A)

/-- The alternating product of actual Kähler differentials. -/
def differentialWedge (n : ℕ) :
    MultilinearMap (RingHom.id k) (fun _ : Fin n ↦ A) (Forms k A n) :=
  ((exteriorPower.ιMulti A n).toMultilinearMap.restrictScalars k).compLinearMap
    (fun _ ↦ (KaehlerDifferential.D k A).toLinearMap)

/-- The actual multilinear form a0 da1∧…∧dan, with the zeroth coordinate retained. -/
def formGenerator (n : ℕ) : MultilinearMap (RingHom.id k) (fun _ : Fin (n + 1) ↦ A) (Forms k A n) :=
  LinearMap.uncurryLeft
    { toFun := fun a ↦ a • differentialWedge k A n
      map_add' a b := add_smul a b _
      map_smul' c a := by
        apply MultilinearMap.ext
        intro x
        change (c • a) • differentialWedge k A n x = c • (a • differentialWedge k A n x)
        exact smul_assoc c a (differentialWedge k A n x) }

@[simp] theorem formGenerator_apply (n : ℕ) (a : Fin (n + 1) → A) :
    formGenerator k A n a = a 0 •
      exteriorPower.ιMulti A n (fun i : Fin n ↦ KaehlerDifferential.D k A (a i.succ)) := by
  simp only [formGenerator, LinearMap.uncurryLeft_apply, differentialWedge]
  rfl

/-- The actual k-linear normalized HKR cochain map before imposing cocycle closure. -/
def hkrCochain (n : ℕ) : (Forms k A n →ₗ[k] k) →ₗ[k]
    MultilinearMap (RingHom.id k) (fun _ : Fin (n + 1) ↦ A) k where
  toFun ψ := ((n.factorial : k)⁻¹) • ψ.compMultilinearMap (formGenerator k A n)
  map_add' ψ χ := by
    apply MultilinearMap.ext
    intro a
    change (n.factorial : k)⁻¹ * ((ψ + χ) (formGenerator k A n a)) =
      (n.factorial : k)⁻¹ * ψ (formGenerator k A n a) +
        (n.factorial : k)⁻¹ * χ (formGenerator k A n a)
    rw [LinearMap.add_apply, mul_add]
  map_smul' c ψ := by
    apply MultilinearMap.ext
    intro a
    change (n.factorial : k)⁻¹ * (c * ψ (formGenerator k A n a)) =
      c * ((n.factorial : k)⁻¹ * ψ (formGenerator k A n a))
    exact mul_left_comm _ _ _

@[simp] theorem hkrCochain_apply (n : ℕ) (ψ : Forms k A n →ₗ[k] k)
    (a : Fin (n + 1) → A) :
    hkrCochain k A n ψ a = (n.factorial : k)⁻¹ *
      ψ (a 0 • exteriorPower.ιMulti A n
        (fun i : Fin n ↦ KaehlerDifferential.D k A (a i.succ))) := by
  change (n.factorial : k)⁻¹ * ψ (formGenerator k A n a) = _
  rw [formGenerator_apply]

/-- The canonical map on cohomology, under the literal native-form cocycle condition. -/
def hkrOnCohomology (n : ℕ)
    (h : ∀ ψ : Forms k A n →ₗ[k] k,
      hkrCochain k A n ψ ∈ TauCeti.hochschildCocycles k A k n) :
    (Forms k A n →ₗ[k] k) →ₗ[k] TauCeti.hochschildCohomology k A k n :=
  (TauCeti.hochschildCohomology.mk k A k n).comp
    (LinearMap.codRestrict _ (hkrCochain k A n) h)

@[simp] theorem hkrOnCohomology_apply (n : ℕ)
    (h : ∀ ψ : Forms k A n →ₗ[k] k,
      hkrCochain k A n ψ ∈ TauCeti.hochschildCocycles k A k n)
    (ψ : Forms k A n →ₗ[k] k) :
    hkrOnCohomology k A n h ψ =
      TauCeti.hochschildCohomology.mk k A k n ⟨hkrCochain k A n ψ, h ψ⟩ := rfl

end MathlibExt.RingTheory.DualHochschildForms
