/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois.lean`
and
`P2M/Sol/S_Algebra_bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.TensorProduct.GaloisDescentAux

variable {𝒪 : Type u} [CommRing 𝒪] {B : Type u} [CommRing B] [Algebra 𝒪 B]
  {G : Type v} [Group G] (τ : G →* (B ≃ₐ[𝒪] B))

private noncomputable def galComp (σ : G) : B ⊗[𝒪] B →ₗ[B] B :=
  (Algebra.TensorProduct.lmul'' (S := B) 𝒪).toLinearMap ∘ₗ
    (Algebra.TensorProduct.map (AlgHom.id B B)
      ((τ σ : B ≃ₐ[𝒪] B) : B →ₐ[𝒪] B)).toLinearMap

private noncomputable def galLin : B ⊗[𝒪] B →ₗ[B] (G → B) :=
  LinearMap.pi fun σ => galComp τ σ

private theorem galLin_tmul (a b : B) (σ : G) :
    galLin τ (a ⊗ₜ b) σ = a * τ σ b := by
  simp only [galLin, galComp, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq]
  rfl

private theorem galLin_eq (x : B ⊗[𝒪] B) (σ : G) :
    galLin τ x σ = Algebra.TensorProduct.lmul' (S := B) 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 B)
          ((τ σ : B ≃ₐ[𝒪] B) : B →ₐ[𝒪] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [galLin_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul]
    rfl
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add, map_add]

end Algebra.TensorProduct.GaloisDescentAux

open Algebra.TensorProduct.GaloisDescentAux in
/-- Galois-ring descent: if `𝒪' ⊗[𝒪] 𝒪'` is identified with functions on `G`
via the supplied semilinear action, and `C` is exactly the fixed-point ring
of the action on `A`, then the canonical map `C ⊗[𝒪] 𝒪' →ₐ[𝒪] A` is
bijective. -/
public theorem Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois
    (𝒪 : Type u) [CommRing 𝒪] (𝒪' : Type u) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    [Module.Flat 𝒪 𝒪']
    (G : Type v) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪')
          ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (A : Type u) [CommRing A] [Algebra 𝒪' A] [Algebra 𝒪 A] [IsScalarTower 𝒪 𝒪' A]
    (θ : G → (A ≃+* A)) (hθ1 : θ 1 = RingEquiv.refl A)
    (hθmul : ∀ σ σ' : G, θ (σ * σ') = (θ σ').trans (θ σ))
    (hθτ : ∀ (σ : G) (l : 𝒪') (a : A),
      θ σ (algebraMap 𝒪' A l * a) = algebraMap 𝒪' A (τ σ l) * θ σ a)
    (C : Type u) [CommRing C] [Algebra 𝒪 C] (ι : C →ₐ[𝒪] A)
    (hι : Function.Injective ι)
    (hιG : ∀ a : A, (∀ σ : G, θ σ a = a) ↔ a ∈ Set.range ι) :
    Function.Bijective (Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A)
      (IsScalarTower.toAlgHom 𝒪 𝒪' A)
      (fun c l => Commute.all _ _) : C ⊗[𝒪] 𝒪' →ₐ[𝒪] A) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hgal' : Function.Bijective (galLin τ) := by
    have hfun : (⇑(galLin τ) : 𝒪' ⊗[𝒪] 𝒪' → G → 𝒪') = fun x σ =>
        Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
          (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪')
            ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x) := by
      funext x; funext σ; exact galLin_eq τ x σ
    rw [hfun]; exact hgal
  let galE : 𝒪' ⊗[𝒪] 𝒪' ≃ₗ[𝒪'] (G → 𝒪') :=
    LinearEquiv.ofBijective (galLin τ) hgal'
  let Ψ : A ⊗[𝒪] 𝒪' ≃ₗ[𝒪'] (G → A) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 𝒪' 𝒪' A 𝒪').symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl 𝒪' A) galE) ≪≫ₗ
        (TensorProduct.piScalarRight 𝒪' 𝒪' A G)
  have Ψ_tmul : ∀ (a : A) (b : 𝒪') (g : G),
      Ψ (a ⊗ₜ b) g = algebraMap 𝒪' A (τ g b) * a := by
    intro a b g
    simp only [Ψ, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (galLin τ (1 ⊗ₜ b) g) • a = _
    rw [galLin_tmul, one_mul, Algebra.smul_def]
  have hΦ : ∀ (c : C) (b : 𝒪'),
      Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A) (IsScalarTower.toAlgHom 𝒪 𝒪' A)
        (fun c l => Commute.all _ _) (c ⊗ₜ b) = ι c * algebraMap 𝒪' A b :=
    fun c b => by rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hθlin : ∀ (σ : G) (r : 𝒪) (a : A), θ σ (r • a) = r • θ σ a := by
    intro σ r a
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 𝒪' A,
      hθτ, AlgEquiv.commutes]
  let θl : G → (A →ₗ[𝒪] A) := fun σ =>
    { toFun := θ σ, map_add' := fun x y => map_add (θ σ) x y,
      map_smul' := fun r a => hθlin σ r a }
  have θl_apply : ∀ σ a, θl σ a = θ σ a := fun _ _ => rfl
  have hθmul' : ∀ (σ σ' : G) (a : A), θ (σ * σ') a = θ σ (θ σ' a) := by
    intro σ σ' a; rw [hθmul]; rfl
  have key : ∀ (w : A ⊗[𝒪] 𝒪') (σ g : G),
      Ψ (LinearMap.rTensor 𝒪' (θl σ) w) g = θ σ (Ψ w (σ⁻¹ * g)) := by
    intro w σ g
    induction w using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a b =>
      rw [LinearMap.rTensor_tmul, θl_apply, Ψ_tmul, Ψ_tmul, hθτ,
        ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, hx, map_add, Pi.add_apply, map_add, hy]
  constructor
  · have hzero : ∀ z : C ⊗[𝒪] 𝒪',
        Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A) (IsScalarTower.toAlgHom 𝒪 𝒪' A)
          (fun c l => Commute.all _ _) z = 0 → z = 0 := by
      intro z hz
      let w : A ⊗[𝒪] 𝒪' := LinearMap.rTensor 𝒪' (ι : C →ₐ[𝒪] A).toLinearMap z
      have hfix : ∀ σ : G, LinearMap.rTensor 𝒪' (θl σ) w = w := by
        intro σ
        have hcomp : (θl σ).comp (ι : C →ₐ[𝒪] A).toLinearMap =
            (ι : C →ₐ[𝒪] A).toLinearMap := by
          ext c
          change θ σ (ι c) = ι c
          exact (hιG (ι c)).mpr ⟨c, rfl⟩ σ
        change LinearMap.rTensor 𝒪' (θl σ)
          (LinearMap.rTensor 𝒪' (ι : C →ₐ[𝒪] A).toLinearMap z) = _
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp]
      have hΦΨ : ∀ z : C ⊗[𝒪] 𝒪',
          Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A)
              (IsScalarTower.toAlgHom 𝒪 𝒪' A)
            (fun c l => Commute.all _ _) z =
            Ψ (LinearMap.rTensor 𝒪' (ι : C →ₐ[𝒪] A).toLinearMap z) 1 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul c b =>
          rw [hΦ, LinearMap.rTensor_tmul, Ψ_tmul, map_one, AlgEquiv.one_apply,
            mul_comm]
          rfl
        | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, Pi.add_apply]
      have h1 : Ψ w 1 = 0 := by rw [← hΦΨ z]; exact hz
      have hΨw : Ψ w = 0 := by
        funext g
        rw [Pi.zero_apply, ← hfix g, key, inv_mul_cancel, h1, map_zero]
      have hw : w = 0 := by simpa using hΨw
      have hinjT : Function.Injective
          (LinearMap.rTensor 𝒪' (ι : C →ₐ[𝒪] A).toLinearMap) :=
        Module.Flat.rTensor_preserves_injective_linearMap _ hι
      exact hinjT (by rw [map_zero]; exact hw)
    intro x y hxy
    have hz := hzero (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp hz
  · intro a
    obtain ⟨u, hu⟩ := hgal'.2 (Pi.single (1 : G) (1 : 𝒪'))
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset u
    have hinv : ∀ (y : 𝒪') (ρ : G),
        θ ρ (∑ σ, θ σ (algebraMap 𝒪' A y * a)) =
          ∑ σ, θ σ (algebraMap 𝒪' A y * a) := by
      intro y ρ
      rw [map_sum]
      simp_rw [← hθmul']
      exact Fintype.sum_bijective (ρ * ·) (Group.mulLeft_bijective ρ) _ _
        fun _ => rfl
    have hc : ∀ i : 𝒪' × 𝒪', ∃ c : C,
        ι c = ∑ σ, θ σ (algebraMap 𝒪' A i.2 * a) := fun i => by
      obtain ⟨c, hc⟩ := (hιG _).mp (hinv i.2); exact ⟨c, hc⟩
    choose c hc using hc
    refine ⟨∑ i ∈ S, c i ⊗ₜ i.1, ?_⟩
    rw [map_sum]
    simp_rw [hΦ, hc]
    have hgu : ∀ σ : G, ∑ i ∈ S, i.1 * τ σ i.2 =
        (Pi.single (1 : G) (1 : 𝒪') : G → 𝒪') σ := by
      intro σ
      rw [← hu, hS, map_sum, Finset.sum_apply]
      simp_rw [galLin_tmul]
    calc ∑ i ∈ S, (∑ σ, θ σ (algebraMap 𝒪' A i.2 * a)) * algebraMap 𝒪' A i.1
        = ∑ σ, algebraMap 𝒪' A (∑ i ∈ S, i.1 * τ σ i.2) * θ σ a := by
          simp_rw [hθτ, Finset.sum_mul, map_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ _ =>
            Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul]; ring
      _ = ∑ σ, algebraMap 𝒪' A ((Pi.single (1 : G) (1 : 𝒪') : G → 𝒪') σ) *
            θ σ a := by simp_rw [hgu]
      _ = a := by
          rw [Finset.sum_eq_single (1 : G)]
          · rw [Pi.single_eq_same, map_one, one_mul, hθ1]; rfl
          · intro σ _ hσ; rw [Pi.single_eq_of_ne hσ, map_zero, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
