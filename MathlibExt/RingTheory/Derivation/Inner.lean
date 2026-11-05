/-
Copyright 2026 Anthropic, PBC

Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0

Adapted from the following Fermat's Last Theorem in Lean 4 files at
6e837e75355538c7f80bab5b956861e86c4eacc2:
Theorems/Thm_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.lean
P2M/Sol/S_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.lean
Authors: no individual authors are supplied for these files upstream.
The scalar-extension and tensor-contraction argument is adapted here;
P2M extraction machinery is not retained.
-/
module

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Inner derivations from a separability element

The separability element lies in an ordinary tensor product. The right action
is a homomorphism from the opposite ring. No field structure is needed.
-/

open scoped TensorProduct

universe u v w

namespace Algebra

private theorem liftBaseChange_op_mul
    {k : Type u} [CommRing k] {Λ : Type v} [Ring Λ]
    {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : Λᵐᵒᵖ →+* Module.End k M) (a b : k ⊗[ℤ] Λ) :
    let R := LinearMap.liftBaseChange k
      (ρ.toAddMonoidHom.comp
        (MulOpposite.opAddEquiv : Λ ≃+ Λᵐᵒᵖ).toAddMonoidHom).toIntLinearMap
    R (a * b) = R b * R a := by
  dsimp only
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, mul_add]
  | tmul c x =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_mul]
    | tmul d y =>
      simp only [TensorProduct.tmul_mul_tmul, LinearMap.liftBaseChange_tmul]
      change (c * d) • ρ (MulOpposite.op (x * y)) =
        (d • ρ (MulOpposite.op y)) * (c • ρ (MulOpposite.op x))
      rw [MulOpposite.op_mul, map_mul, smul_mul_smul_comm, mul_comm d c]

/-- Every additive bimodule derivation is inner if the scalar extension has
an ordinary separability tensor. The witness has the convention
`o x + θ x ξ - ρ (op x) ξ = 0`; existence does not imply uniqueness.

This is the exact three-universe statement of the frozen FLT separability
source. The base ring is any commutative ring, and `Λ` need not commute. -/
public theorem exists_inner_of_separabilityElement
    (k : Type u) [CommRing k] (Λ : Type v) [Ring Λ]
    (e : (k ⊗[ℤ] Λ) ⊗[k] (k ⊗[ℤ] Λ))
    (he₁ : LinearMap.mul' k (k ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : k ⊗[ℤ] Λ,
      _root_.TensorProduct.map (LinearMap.mulLeft k x) LinearMap.id e =
      _root_.TensorProduct.map LinearMap.id (LinearMap.mulRight k x) e)
    (M : Type w) [AddCommGroup M] [Module k M]
    (θ : Λ →+* Module.End k M) (ρ : Λᵐᵒᵖ →+* Module.End k M)
    (hθρ : ∀ (x : Λ) (y : Λᵐᵒᵖ),
      (θ x).comp (ρ y) = (ρ y).comp (θ x))
    (o : Λ →+ M)
    (ho : ∀ x y : Λ, o (x * y) = θ x (o y) + ρ (MulOpposite.op y) (o x)) :
    ∃ ξ : M, ∀ x : Λ, o x + θ x ξ - ρ (MulOpposite.op x) ξ = 0 := by
  classical
  let δ := o.toIntLinearMap.liftBaseChange k
  let Θ := θ.toAddMonoidHom.toIntLinearMap.liftBaseChange k
  let Ρ := LinearMap.liftBaseChange k
    (ρ.toAddMonoidHom.comp
      (MulOpposite.opAddEquiv : Λ ≃+ Λᵐᵒᵖ).toAddMonoidHom).toIntLinearMap
  have hδ (c : k) (x : Λ) : δ (c ⊗ₜ[ℤ] x) = c • o x := rfl
  have hΘ (c : k) (x : Λ) : Θ (c ⊗ₜ[ℤ] x) = c • θ x := rfl
  have hΡ (c : k) (x : Λ) :
      Ρ (c ⊗ₜ[ℤ] x) = c • ρ (MulOpposite.op x) := rfl
  have hΡmul (a b : k ⊗[ℤ] Λ) : Ρ (a * b) = Ρ b * Ρ a :=
    liftBaseChange_op_mul ρ a b
  have hΡone : Ρ 1 = 1 := by
    rw [TensorProduct.one_def, hΡ, one_smul, MulOpposite.op_one, map_one]
  have hcomm (a b : k ⊗[ℤ] Λ) : Θ a * Ρ b = Ρ b * Θ a := by
    induction a using TensorProduct.inductionOn with
    | add a₁ a₂ h₁ h₂ => simp only [map_add, add_mul, mul_add, h₁, h₂]
    | tmul c x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ h₁ h₂ => simp only [map_add, add_mul, mul_add, h₁, h₂]
      | tmul d y =>
        rw [hΘ, hΡ, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c d]
        exact congrArg ((d * c) • ·) (hθρ x (MulOpposite.op y))
  have hcoc (a b : k ⊗[ℤ] Λ) :
      δ (a * b) = Θ a (δ b) + Ρ b (δ a) := by
    induction a using TensorProduct.inductionOn with
    | add a₁ a₂ h₁ h₂ =>
      simp only [add_mul, map_add, h₁, h₂, LinearMap.add_apply]
      abel
    | tmul c x =>
      induction b using TensorProduct.inductionOn with
      | add b₁ b₂ h₁ h₂ =>
        simp only [mul_add, map_add, h₁, h₂, LinearMap.add_apply]
        abel
      | tmul d y =>
        rw [TensorProduct.tmul_mul_tmul, hδ, hδ, hδ, hΘ, hΡ, ho,
          smul_add, LinearMap.smul_apply, LinearMap.smul_apply,
          map_smul, map_smul, smul_smul, smul_smul, mul_comm d c]
  let B : (k ⊗[ℤ] Λ) →ₗ[k] (k ⊗[ℤ] Λ) →ₗ[k] M :=
    LinearMap.mk₂ k (fun a b => Ρ b (δ a))
      (fun a₁ a₂ b => by rw [map_add, map_add])
      (fun c a b => by rw [map_smul, map_smul])
      (fun a b₁ b₂ => by rw [map_add, LinearMap.add_apply])
      (fun c a b => by rw [map_smul, LinearMap.smul_apply])
  let Φ := _root_.TensorProduct.lift B
  have hΦ (a b : k ⊗[ℤ] Λ) : Φ (a ⊗ₜ[k] b) = Ρ b (δ a) :=
    _root_.TensorProduct.lift.tmul a b
  obtain ⟨T, hT⟩ := _root_.TensorProduct.exists_finset e
  set m : M := ∑ p ∈ T, Ρ p.2 (δ p.1) with hm
  have hsum : ∑ p ∈ T, p.1 * p.2 = 1 := by
    have h := he₁
    rw [hT, map_sum] at h
    simpa only [LinearMap.mul'_apply] using h
  have key (a : k ⊗[ℤ] Λ) : Θ a m + δ a = Ρ a m := by
    have hL : Φ (_root_.TensorProduct.map
        (LinearMap.mulLeft k a) LinearMap.id e) = Θ a m + δ a := by
      rw [hT, map_sum, map_sum]
      simp only [_root_.TensorProduct.map_tmul, LinearMap.mulLeft_apply,
        LinearMap.id_apply, hΦ, hcoc, map_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [hm, map_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]
      · have h1 (p) (_ : p ∈ T) :
            Ρ p.2 (Ρ p.1 (δ a)) = Ρ (p.1 * p.2) (δ a) := by
          rw [hΡmul, Module.End.mul_apply]
        rw [Finset.sum_congr rfl h1, ← LinearMap.sum_apply,
          ← map_sum, hsum, hΡone, Module.End.one_apply]
    have hR : Φ (_root_.TensorProduct.map LinearMap.id
        (LinearMap.mulRight k a) e) = Ρ a m := by
      rw [hT, map_sum, map_sum]
      simp only [_root_.TensorProduct.map_tmul, LinearMap.mulRight_apply,
        LinearMap.id_apply, hΦ]
      rw [hm, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hΡmul, Module.End.mul_apply]
    rw [← hL, ← hR, he₂ a]
  refine ⟨m, fun x => ?_⟩
  have hx := key ((1 : k) ⊗ₜ[ℤ] x)
  rw [hΘ, hδ, hΡ, one_smul, one_smul, one_smul] at hx
  rw [← hx]
  abel

end Algebra
