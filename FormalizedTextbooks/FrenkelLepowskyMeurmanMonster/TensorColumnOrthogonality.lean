/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonality of a tensor-column operator is orthogonality of its common factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TensorMatrixCommutant
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The unscaled ordinary dot product of tensor coordinates. -/
def tensorColumnPairing {I : Type*} [Fintype I]
    (T U : I → Fin 24 → ℝ) : ℝ := ∑ t, ∑ i, T t i * U t i

private theorem tensorColumnInsert_pairing {I : Type*} [Fintype I] (x y : I → ℝ) :
    tensorColumnPairing (tensorColumnInsert 0 x) (tensorColumnInsert 0 y) = dotProduct x y := by
  simp [tensorColumnPairing, tensorColumnInsert, dotProduct, ite_mul, mul_ite]

private theorem tensorColumnwise_insert {I : Type*}
    (L : Module.End ℝ (I → Fin 24 → ℝ)) (S : Module.End ℝ (I → ℝ))
    (hL : ∀ T t i, L T t i = S (fun u => T u i) t) (x : I → ℝ) :
    L (tensorColumnInsert 0 x) = tensorColumnInsert 0 (S x) := by
  ext t i
  rw [hL]
  by_cases hi : i = 0
  · subst i
    simp [tensorColumnInsert]
  · simp only [tensorColumnInsert, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false]
    change S 0 t = 0
    rw [map_zero]
    rfl

/-- Orthogonality on tensor coordinates implies orthogonality of the common column operator. -/
theorem tensorColumnwise_preserves_pairing {I : Type*} [Fintype I]
    (L : Module.End ℝ (I → Fin 24 → ℝ)) (S : Module.End ℝ (I → ℝ))
    (hL : ∀ T t i, L T t i = S (fun u => T u i) t)
    (hpair : ∀ T U, tensorColumnPairing (L T) (L U) = tensorColumnPairing T U) :
    ∀ x y : I → ℝ, dotProduct (S x) (S y) = dotProduct x y := by
  intro x y
  have h := hpair (tensorColumnInsert 0 x) (tensorColumnInsert 0 y)
  rw [tensorColumnwise_insert L S hL, tensorColumnwise_insert L S hL,
    tensorColumnInsert_pairing, tensorColumnInsert_pairing] at h
  exact h

/-- A dot-product-preserving endomorphism of a finite real coordinate space is bijective. -/
theorem tensorColumnFactor_bijective {I : Type*} [Fintype I]
    (S : Module.End ℝ (I → ℝ))
    (hpair : ∀ x y : I → ℝ, dotProduct (S x) (S y) = dotProduct x y) :
    Function.Bijective S := by
  have hinj : Function.Injective S := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply dotProduct_self_eq_zero.mp
    have h := hpair (x - y) (x - y)
    rw [map_sub, hxy, sub_self, dotProduct_zero] at h
    exact h.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- The recovered spin factor preserves the actual spin pairing. -/
theorem tensorColumnwise_spin_pairing
    (L : Module.End ℝ (SpinIndex → Fin 24 → ℝ)) (S : Module.End ℝ SpinSpace)
    (hL : ∀ T t i, L T t i = S (fun u => T u i) t)
    (hpair : ∀ T U, tensorColumnPairing (L T) (L U) = tensorColumnPairing T U) :
    ∀ x y, spinPairing (S x) (S y) = spinPairing x y :=
  tensorColumnwise_preserves_pairing L S hL hpair

/-- The actual spin column factor is an orthogonal equivalence, with its action unchanged. -/
theorem tensorColumnwise_spin_equiv
    (L : Module.End ℝ (SpinIndex → Fin 24 → ℝ)) (S : Module.End ℝ SpinSpace)
    (hL : ∀ T t i, L T t i = S (fun u => T u i) t)
    (hpair : ∀ T U, tensorColumnPairing (L T) (L U) = tensorColumnPairing T U) :
    ∃ e : SpinSpace ≃ₗ[ℝ] SpinSpace, e.toLinearMap = S ∧ e ∈ spinOrthogonalSubgroup := by
  have hs := tensorColumnwise_spin_pairing L S hL hpair
  let e := LinearEquiv.ofBijective S (tensorColumnFactor_bijective S hs)
  exact ⟨e, rfl, hs⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
