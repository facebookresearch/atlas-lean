/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions adapted from Fermat's Last Theorem in Lean 4:
Theorems/Thm_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.lean
P2M/Sol/S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff.lean
Commit: 6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0.
No individual author is named for these results in the frozen source files
or project attribution table.
Adapted portions: the exact-source consumer and multiplication-map tensor
identities. The scalar-extension/localization applications and matrix
boundary proofs are new.
-/

module

import MathlibExt.RingTheory.TensorProduct.IntegralCasimir
import MathlibExt.RingTheory.Derivation.Inner
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The importing applications below consume the tensor returned by Casimir.
The explicit matrix tensors later in the file illustrate distinctions; they
do not prescribe which existential witness the public theorem returns.
-/

open scoped TensorProduct

-- Tensor algebra structures use the canonical integer-module instances.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace IntegralCasimirTest

private theorem exact_source
    {R : Type*} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c₀ : R ⊗[ℤ] R)
    (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ =
      c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0) :
    ∃ c : R ⊗[ℤ] R,
      (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
        c * ((1 : R) ⊗ₜ[ℤ] x)) ∧ ψ (LinearMap.mul' ℤ R c) = 1 := by
  exact RingHom.exists_balancedTensor_map_mul_eq_one ℓ ψ hψ hker c₀ hc₀ h₀

private def tensorExtension (S : Type*) [CommRing S] (R : Type*) [Ring R] :
    R ⊗[ℤ] R →ₐ[ℤ] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R) :=
  let i : R →ₐ[ℤ] S ⊗[ℤ] R := Algebra.TensorProduct.includeRight
  let l : S ⊗[ℤ] R →ₐ[S] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R) :=
    Algebra.TensorProduct.includeLeft
  let r : S ⊗[ℤ] R →ₐ[S] (S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R) :=
    Algebra.TensorProduct.includeRight
  Algebra.TensorProduct.lift ((l.restrictScalars ℤ).comp i)
    ((r.restrictScalars ℤ).comp i) fun x y =>
      (Commute.one_right (i x)).tmul (Commute.one_left (i y))

private theorem tensorExtension_tmul
    (S : Type*) [CommRing S] (R : Type*) [Ring R] (x y : R) :
    tensorExtension S R (x ⊗ₜ[ℤ] y) =
      ((1 : S) ⊗ₜ[ℤ] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] y) := by
  simp [tensorExtension]

private theorem tensorExtension_mul
    (S : Type*) [CommRing S] (R : Type*) [Ring R] (c : R ⊗[ℤ] R) :
    LinearMap.mul' S (S ⊗[ℤ] R) (tensorExtension S R c) =
      (1 : S) ⊗ₜ[ℤ] LinearMap.mul' ℤ R c := by
  induction c using TensorProduct.inductionOn with
  | tmul x y => simp [tensorExtension_tmul]
  | add c d hc hd => simp [hc, hd, TensorProduct.tmul_add]

private theorem tensorExtension_balance
    (S : Type*) [CommRing S] (R : Type*) [Ring R]
    (c : R ⊗[ℤ] R)
    (hc : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
      c * ((1 : R) ⊗ₜ[ℤ] x)) :
    ∀ x : S ⊗[ℤ] R, (x ⊗ₜ[S] (1 : S ⊗[ℤ] R)) *
      tensorExtension S R c =
        tensorExtension S R c * ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x) := by
  let : Ring ((S ⊗[ℤ] R) ⊗[S] (S ⊗[ℤ] R)) :=
    Algebra.TensorProduct.instRing
  have hi (x : R) :
      (((1 : S) ⊗ₜ[ℤ] x) ⊗ₜ[S] (1 : S ⊗[ℤ] R)) *
        tensorExtension S R c =
      tensorExtension S R c *
        ((1 : S ⊗[ℤ] R) ⊗ₜ[S] ((1 : S) ⊗ₜ[ℤ] x)) := by
    simpa only [map_mul, tensorExtension_tmul,
      ← Algebra.TensorProduct.one_def] using
      congrArg (tensorExtension S R) (hc x)
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s r =>
    have hsr : s ⊗ₜ[ℤ] r = s • ((1 : S) ⊗ₜ[ℤ] r) :=
      TensorProduct.tmul_eq_smul_one_tmul s r
    rw [hsr, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_mul_assoc, mul_smul_comm, hi]
  | add x y hx hy =>
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add,
      add_mul, mul_add, hx, hy]

private theorem map_balance_of_mul_balance
    (S : Type*) [CommRing S] (B : Type*) [Ring B] [Algebra S B]
    (e : B ⊗[S] B)
    (he : ∀ x : B, (x ⊗ₜ[S] (1 : B)) * e =
      e * ((1 : B) ⊗ₜ[S] x)) (x : B) :
    TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e := by
  have hl : ∀ t : B ⊗[S] B,
      TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id t =
        (x ⊗ₜ[S] (1 : B)) * t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add t u ht hu => simp [ht, hu, mul_add]
  have hr : ∀ t : B ⊗[S] B,
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) t =
        t * ((1 : B) ⊗ₜ[S] x) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add t u ht hu => simp [ht, hu, add_mul]
  rw [hl, hr, he]

private theorem residue_mul_one
    {R : Type*} [Ring R] (ℓ : ℕ) {n : Type} [Fintype n] [DecidableEq n]
    (ψ : R →+* Matrix n n (ZMod ℓ))
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c : R ⊗[ℤ] R) (hc : ψ (LinearMap.mul' ℤ R c) = 1) :
    LinearMap.mul' (ZMod ℓ) (ZMod ℓ ⊗[ℤ] R)
      (tensorExtension (ZMod ℓ) R c) = 1 := by
  rw [tensorExtension_mul]
  let i : R →ₐ[ℤ] ZMod ℓ ⊗[ℤ] R := Algebra.TensorProduct.includeRight
  change i (LinearMap.mul' ℤ R c) = 1
  have hz : ψ (LinearMap.mul' ℤ R c - 1) = 0 := by
    rw [map_sub, hc, map_one, sub_self]
  obtain ⟨y, hy⟩ := (hker _).mp hz
  have hiℓ : i (ℓ : R) = 0 := by
    simp [Algebra.TensorProduct.natCast_def]
  apply sub_eq_zero.mp
  rw [← map_one i, ← map_sub, hy, map_mul, hiℓ, zero_mul]

private theorem inner_from_casimir
    {R : Type*} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c₀ : R ⊗[ℤ] R)
    (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ =
      c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0)
    (M : Type*) [AddCommGroup M] [Module (ZMod ℓ) M]
    (θ : R →+* Module.End (ZMod ℓ) M)
    (ρ : Rᵐᵒᵖ →+* Module.End (ZMod ℓ) M)
    (hθρ : ∀ x y, (θ x).comp (ρ y) = (ρ y).comp (θ x))
    (o : R →+ M)
    (ho : ∀ x y, o (x * y) = θ x (o y) +
      ρ (MulOpposite.op y) (o x)) :
    ∃ ξ : M, ∀ x, o x + θ x ξ - ρ (MulOpposite.op x) ξ = 0 := by
  obtain ⟨c, hc, hμ⟩ :=
    ψ.exists_balancedTensor_map_mul_eq_one ℓ hψ hker c₀ hc₀ h₀
  exact Algebra.exists_inner_of_separabilityElement (ZMod ℓ) R
    (tensorExtension (ZMod ℓ) R c) (residue_mul_one ℓ ψ hker c hμ)
    (map_balance_of_mul_balance _ _ _ (tensorExtension_balance _ _ c hc))
    M θ ρ hθρ o ho

private theorem mu_left (S : Type*) [CommRing S]
    (B : Type*) [Ring B] [Algebra S B] (x : B) (e : B ⊗[S] B) :
    LinearMap.mul' S B ((x ⊗ₜ[S] (1 : B)) * e) =
      x * LinearMap.mul' S B e := by
  induction e using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add e f he hf => simp [mul_add, he, hf]

private theorem mu_right (S : Type*) [CommRing S]
    (B : Type*) [Ring B] [Algebra S B] (x : B) (e : B ⊗[S] B) :
    LinearMap.mul' S B (e * ((1 : B) ⊗ₜ[S] x)) =
      LinearMap.mul' S B e * x := by
  induction e using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add e f he hf => simp [add_mul, he, hf]

private theorem normalize_of_det_unit
    (S : Type*) [CommRing S] (B : Type*) [Ring B] [Algebra S B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S B)
    (e : B ⊗[S] B)
    (he : ∀ x : B, (x ⊗ₜ[S] (1 : B)) * e =
      e * ((1 : B) ⊗ₜ[S] x))
    (hdet : IsUnit (Algebra.leftMulMatrix b (LinearMap.mul' S B e)).det) :
    ∃ u : B, (∀ x : B, x * u = u * x) ∧
      LinearMap.mul' S B e * u = 1 ∧ u * LinearMap.mul' S B e = 1 ∧
      (∀ x : B, (x ⊗ₜ[S] (1 : B)) * ((u ⊗ₜ[S] (1 : B)) * e) =
        ((u ⊗ₜ[S] (1 : B)) * e) * ((1 : B) ⊗ₜ[S] x)) ∧
      LinearMap.mul' S B ((u ⊗ₜ[S] (1 : B)) * e) = 1 := by
  let z := LinearMap.mul' S B e
  have hz (x : B) : x * z = z * x := by
    rw [← mu_left S B, he x, mu_right]
  have hmat : IsUnit (Algebra.leftMulMatrix b z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hlin : IsUnit (LinearMap.mulLeft S z) := by
    have h := hmat.map (LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom
    change IsUnit ((LinearMap.toMatrixAlgEquiv b).symm
      ((LinearMap.toMatrixAlgEquiv b) (LinearMap.mulLeft S z))) at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  obtain ⟨f, hf⟩ := hlin
  let u : B := (↑(f⁻¹) : Module.End S B) 1
  have hzu : z * u = 1 := by
    have hcomp : (f : Module.End S B) * (↑(f⁻¹) : Module.End S B) = 1 :=
      by simp
    have h := congrArg (fun g : Module.End S B => g 1) hcomp
    change (f : Module.End S B) u = 1 at h
    rw [hf] at h
    exact h
  have huz : u * z = 1 := (hz u).trans hzu
  have hu (x : B) : x * u = u * x := by
    calc
      x * u = (u * z) * (x * u) := by rw [huz, one_mul]
      _ = u * ((z * x) * u) := by simp only [mul_assoc]
      _ = u * ((x * z) * u) := by rw [hz x]
      _ = u * x := by rw [mul_assoc x z u, hzu, mul_one]
  refine ⟨u, hu, hzu, huz, ?_, ?_⟩
  · intro x
    have hcomm : Commute (x ⊗ₜ[S] (1 : B)) (u ⊗ₜ[S] (1 : B)) :=
      (show Commute x u from hu x).tmul (Commute.refl 1)
    rw [← mul_assoc, hcomm.eq, mul_assoc, he x, ← mul_assoc]
  · rw [mu_left]
    exact huz

private theorem leftMulMatrix_baseChange
    (S : Type*) [CommRing S] (R : Type*) [Ring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ R) (z : R) :
    Algebra.leftMulMatrix (b.baseChange S) ((1 : S) ⊗ₜ[ℤ] z) =
      (algebraMap ℤ S).mapMatrix (Algebra.leftMulMatrix b z) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Module.Basis.baseChange_repr_tmul]
  simp [Algebra.leftMulMatrix_eq_repr_mul, zsmul_eq_mul]

private theorem determinant_mod_one
    {R : Type*} [Ring R] (ℓ : ℕ)
    {n : Type} [Fintype n] [DecidableEq n]
    (ψ : R →+* Matrix n n (ZMod ℓ))
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ R) (z : R) (hz : ψ z = 1) :
    ((Algebra.leftMulMatrix b z).det : ZMod ℓ) = 1 := by
  have hz0 : ψ (z - 1) = 0 := by rw [map_sub, hz, map_one, sub_self]
  obtain ⟨y, hy⟩ := (hker _).mp hz0
  have hz1 : z = (ℓ : ℤ) • y + 1 := by
    simpa only [zsmul_eq_mul, Int.cast_natCast] using
      (sub_eq_iff_eq_add).mp hy
  have hm : (Int.castRingHom (ZMod ℓ)).mapMatrix
      (Algebra.leftMulMatrix b z) = 1 := by
    ext i j
    change (Algebra.leftMulMatrix b z i j : ZMod ℓ) =
      (1 : Matrix ι ι (ZMod ℓ)) i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hz1, add_mul, one_mul,
      smul_mul_assoc, map_add, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  change (Int.castRingHom (ZMod ℓ)) (Algebra.leftMulMatrix b z).det = 1
  rw [RingHom.map_det, hm, Matrix.det_one]

private theorem localized_normalization
    (S : Type*) [CommRing S] {R : Type*} [Ring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ R)
    (c : R ⊗[ℤ] R)
    [hS : IsLocalization.Away
      (Algebra.leftMulMatrix b (LinearMap.mul' ℤ R c)).det S]
    (hc : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
      c * ((1 : R) ⊗ₜ[ℤ] x)) :
    let e := tensorExtension S R c
    ∃ u : S ⊗[ℤ] R, (∀ x : S ⊗[ℤ] R, x * u = u * x) ∧
      LinearMap.mul' S (S ⊗[ℤ] R) e * u = 1 ∧
      u * LinearMap.mul' S (S ⊗[ℤ] R) e = 1 ∧
      (∀ x : S ⊗[ℤ] R,
        (x ⊗ₜ[S] (1 : S ⊗[ℤ] R)) *
            ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) =
          ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) *
            ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x)) ∧
      LinearMap.mul' S (S ⊗[ℤ] R)
        ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) = 1 := by
  let e := tensorExtension S R c
  have hdet : IsUnit
      (Algebra.leftMulMatrix (b.baseChange S)
        (LinearMap.mul' S (S ⊗[ℤ] R) e)).det := by
    dsimp only [e]
    rw [tensorExtension_mul, leftMulMatrix_baseChange, ← RingHom.map_det]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact normalize_of_det_unit S (S ⊗[ℤ] R) (b.baseChange S) e
    (tensorExtension_balance S R c hc) hdet

private theorem localized_from_casimir
    {R : Type*} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    (c₀ : R ⊗[ℤ] R)
    (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ =
      c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ R) :
    ∃ c : R ⊗[ℤ] R,
      (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
        c * ((1 : R) ⊗ₜ[ℤ] x)) ∧ ψ (LinearMap.mul' ℤ R c) = 1 ∧
      let Δ := (Algebra.leftMulMatrix b (LinearMap.mul' ℤ R c)).det
      let S := Localization.Away Δ
      letI : CommRing S := inferInstance
      let e := tensorExtension S R c
      (Δ : ZMod ℓ) = 1 ∧ ¬ (ℓ : ℤ) ∣ Δ ∧ Δ ≠ 0 ∧
      ∃ u : S ⊗[ℤ] R, (∀ x : S ⊗[ℤ] R, x * u = u * x) ∧
        LinearMap.mul' S (S ⊗[ℤ] R) e * u = 1 ∧
        u * LinearMap.mul' S (S ⊗[ℤ] R) e = 1 ∧
        (∀ x : S ⊗[ℤ] R,
          (x ⊗ₜ[S] (1 : S ⊗[ℤ] R)) *
              ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) =
            ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) *
              ((1 : S ⊗[ℤ] R) ⊗ₜ[S] x)) ∧
        LinearMap.mul' S (S ⊗[ℤ] R)
          ((u ⊗ₜ[S] (1 : S ⊗[ℤ] R)) * e) = 1 := by
  obtain ⟨c, hc, hμ⟩ :=
    ψ.exists_balancedTensor_map_mul_eq_one ℓ hψ hker c₀ hc₀ h₀
  let Δ := (Algebra.leftMulMatrix b (LinearMap.mul' ℤ R c)).det
  let S := Localization.Away Δ
  let : CommRing S := inferInstance
  have hΔ : (Δ : ZMod ℓ) = 1 :=
    determinant_mod_one ℓ ψ hker b _ hμ
  have hnot : ¬ (ℓ : ℤ) ∣ Δ := by
    intro hd
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd Δ ℓ).mpr hd
    rw [hΔ] at hzero
    exact one_ne_zero hzero
  have hnz : Δ ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero _
  let hloc : IsLocalization.Away Δ S :=
    Localization.isLocalization (M := Submonoid.powers Δ)
  refine ⟨c, hc, hμ, hΔ, hnot, hnz, ?_⟩
  exact localized_normalization S b c (hS := by
    convert hloc using 1
    exact Subsingleton.elim _ _) hc

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℤ

private def reduction : M₂ →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (Int.castRingHom (ZMod 2)).mapMatrix

private theorem reduction_surjective : Function.Surjective reduction := by
  intro a
  refine ⟨Matrix.of (fun i j => ((a i j).cast : ℤ)), ?_⟩
  ext i j
  exact ZMod.intCast_zmod_cast (a i j)

private theorem reduction_kernel (x : M₂) :
    reduction x = 0 ↔ ∃ y : M₂, x = (2 : M₂) * y := by
  constructor
  · intro hx
    have hd (i j : Fin 2) : (2 : ℤ) ∣ x i j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      exact congrArg (fun a : Matrix (Fin 2) (Fin 2) (ZMod 2) => a i j) hx
    choose y hy using hd
    refine ⟨Matrix.of y, ?_⟩
    rw [two_mul]
    ext i j
    simpa only [two_mul, Matrix.add_apply, Matrix.of_apply] using hy i j
  · rintro ⟨y, rfl⟩
    rw [two_mul, map_add]
    ext i j
    change reduction y i j + reduction y i j = 0
    rw [← two_mul]
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul]

example : Module.Free ℤ M₂ := inferInstance
example : Module.Finite ℤ M₂ := inferInstance

private def C (m n : Fin 2) : M₂ ⊗[ℤ] M₂ :=
  ∑ i : Fin 2,
    (Matrix.single i m (1 : ℤ)) ⊗ₜ[ℤ] (Matrix.single n i (1 : ℤ))

private theorem C_balance (m n : Fin 2) (x : M₂) :
    (x ⊗ₜ[ℤ] (1 : M₂)) * C m n = C m n * ((1 : M₂) ⊗ₜ[ℤ] x) := by
  have h :
      (LinearMap.mulRight ℤ (C m n)).comp
          ((TensorProduct.mk ℤ M₂ M₂).flip 1) =
        (LinearMap.mulLeft ℤ (C m n)).comp
          (TensorProduct.mk ℤ M₂ M₂ 1) := by
    apply (Matrix.stdBasis ℤ (Fin 2) (Fin 2)).ext
    rintro ⟨i, j⟩
    change ((Matrix.stdBasis ℤ (Fin 2) (Fin 2) (i, j)) ⊗ₜ[ℤ] 1) * C m n =
      C m n * (1 ⊗ₜ[ℤ] (Matrix.stdBasis ℤ (Fin 2) (Fin 2) (i, j)))
    rw [Matrix.stdBasis_eq_single]
    fin_cases i <;> fin_cases j <;> fin_cases m <;> fin_cases n <;>
      simp [C, Fin.sum_univ_two, mul_add, add_mul,
        Matrix.single_mul_single_of_ne]
  exact congrArg (fun f : M₂ →ₗ[ℤ] M₂ ⊗[ℤ] M₂ => f x) h

private theorem C01_coordinate :
    ((Matrix.stdBasis ℤ (Fin 2) (Fin 2)).tensorProduct
      (Matrix.stdBasis ℤ (Fin 2) (Fin 2))).repr (C 0 1)
        ((0, 0), (1, 0)) = 1 := by
  simp [C, Fin.sum_univ_two, ← Matrix.stdBasis_eq_single,
    Module.Basis.tensorProduct_repr_tmul_apply]

private theorem scaled_C01_nonzero : (8 : ℤ) • C 0 1 ≠ 0 := by
  intro h
  have hh := congrArg (fun t : M₂ ⊗[ℤ] M₂ =>
    ((Matrix.stdBasis ℤ (Fin 2) (Fin 2)).tensorProduct
      (Matrix.stdBasis ℤ (Fin 2) (Fin 2))).repr t ((0, 0), (1, 0))) h
  rw [map_smul, Finsupp.smul_apply, C01_coordinate, map_zero,
    Finsupp.zero_apply, smul_eq_mul, mul_one] at hh
  norm_num at hh

private theorem scaled_C01_balance (x : M₂) :
    (x ⊗ₜ[ℤ] (1 : M₂)) * ((8 : ℤ) • C 0 1) =
      ((8 : ℤ) • C 0 1) * ((1 : M₂) ⊗ₜ[ℤ] x) := by
  rw [mul_smul_comm, smul_mul_assoc, C_balance]

private theorem scaled_C01_reduction :
    tensorExtension (ZMod 2) M₂ ((8 : ℤ) • C 0 1) = 0 := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod 2)]
  have height : ((8 : ℤ) : ZMod 2) = 0 := by decide
  rw [height, zero_smul]

private theorem primitive_C01 :
    ¬ (2 : ℤ) ∣ ((Matrix.stdBasis ℤ (Fin 2) (Fin 2)).tensorProduct
      (Matrix.stdBasis ℤ (Fin 2) (Fin 2))).repr (C 0 1)
        ((0, 0), (1, 0)) := by
  rw [C01_coordinate]
  decide

private theorem mu_C01 : LinearMap.mul' ℤ M₂ (C 0 1) = 0 := by
  simp [C, Matrix.single_mul_single_of_ne]

private theorem adjust_C01 :
    ((1 : M₂) ⊗ₜ[ℤ] (Matrix.single 0 1 (1 : ℤ))) * C 0 1 = C 0 0 := by
  simp only [C, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.single_mul_single_same]

private theorem mu_C00 : LinearMap.mul' ℤ M₂ (C 0 0) = 1 := by
  simp only [C, map_sum, LinearMap.mul'_apply,
    Matrix.single_mul_single_same, one_mul, Matrix.sum_single_one]

example : (2 : ZMod 2) = 0 := by decide

private theorem C00_square : C 0 0 * C 0 0 =
    (Matrix.single 0 0 (1 : ℤ)) ⊗ₜ[ℤ] (Matrix.single 0 0 (1 : ℤ)) := by
  simp [C, Fin.sum_univ_two, mul_add, add_mul,
    Matrix.single_mul_single_of_ne]

private theorem C00_not_idempotent : C 0 0 * C 0 0 ≠ C 0 0 := by
  intro h
  rw [C00_square] at h
  have hh := congrArg (fun t : M₂ ⊗[ℤ] M₂ =>
    ((Matrix.stdBasis ℤ (Fin 2) (Fin 2)).tensorProduct
      (Matrix.stdBasis ℤ (Fin 2) (Fin 2))).repr t ((1, 0), (0, 1))) h
  norm_num [C, Fin.sum_univ_two, ← Matrix.stdBasis_eq_single,
    Module.Basis.tensorProduct_repr_tmul_apply] at hh

private theorem three_mu :
    LinearMap.mul' ℤ M₂ ((3 : ℤ) • C 0 0) = (3 : ℤ) • (1 : M₂) := by
  rw [map_smul, mu_C00]

private theorem three_mu_not_one :
    LinearMap.mul' ℤ M₂ ((3 : ℤ) • C 0 0) ≠ 1 := by
  rw [three_mu]
  intro h
  have hh := congrArg (fun a : M₂ => a 0 0) h
  norm_num [Matrix.smul_apply, smul_eq_mul] at hh

private theorem three_mu_reduction :
    reduction (LinearMap.mul' ℤ M₂ ((3 : ℤ) • C 0 0)) = 1 := by
  rw [three_mu, map_zsmul, map_one,
    ← Int.cast_smul_eq_zsmul (ZMod 2)]
  have hthree : ((3 : ℤ) : ZMod 2) = 1 := by decide
  rw [hthree, one_smul]

private theorem three_determinant :
    (Algebra.leftMulMatrix (Matrix.stdBasis ℤ (Fin 2) (Fin 2))
      (LinearMap.mul' ℤ M₂ ((3 : ℤ) • C 0 0))).det = 81 := by
  rw [three_mu, map_zsmul, map_one, Matrix.det_smul]
  norm_num

example : ((81 : ℤ) : ZMod 2) = 1 := by decide

local notation "K₂" => Matrix (Fin 2) (Fin 2) (ZMod 2)

private def leftAction : M₂ →+* Module.End (ZMod 2) K₂ :=
  (Algebra.lmul (ZMod 2) K₂).toRingHom.comp reduction

private def rightAction : M₂ᵐᵒᵖ →+* Module.End (ZMod 2) K₂ :=
  (Algebra.lsmul (ZMod 2) (A := K₂ᵐᵒᵖ) (ZMod 2) K₂).toRingHom.comp
    reduction.op

private theorem leftAction_apply (x : M₂) (m : K₂) :
    leftAction x m = reduction x * m := rfl

private theorem rightAction_apply (y : M₂ᵐᵒᵖ) (m : K₂) :
    rightAction y m = m * reduction y.unop := rfl

private theorem actions_commute (x : M₂) (y : M₂ᵐᵒᵖ) :
    (leftAction x).comp (rightAction y) =
      (rightAction y).comp (leftAction x) := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, leftAction_apply, rightAction_apply]
  exact (mul_assoc (reduction x) m (reduction y.unop)).symm

private def commutator : M₂ →+ K₂ where
  toFun x := reduction x * Matrix.single 0 1 1 -
    Matrix.single 0 1 1 * reduction x
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, add_mul, mul_add]
    abel

private theorem commutator_leibniz (x y : M₂) :
    commutator (x * y) = leftAction x (commutator y) +
      rightAction (MulOpposite.op y) (commutator x) := by
  simp only [leftAction_apply, rightAction_apply, MulOpposite.unop_op]
  change reduction (x * y) * Matrix.single 0 1 1 -
      Matrix.single 0 1 1 * reduction (x * y) =
    reduction x * (reduction y * Matrix.single 0 1 1 -
        Matrix.single 0 1 1 * reduction y) +
      (reduction x * Matrix.single 0 1 1 -
        Matrix.single 0 1 1 * reduction x) * reduction y
  simp only [map_mul, mul_sub, sub_mul, mul_assoc]
  abel

private theorem commutator_nonzero : commutator ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M₂ →+ K₂ => f (Matrix.single 0 0 1) 0 1) h
  change commutator (Matrix.single 0 0 1) 0 1 = 0 at hh
  have hv : commutator (Matrix.single 0 0 1) 0 1 = 1 := by decide
  rw [hv] at hh
  exact one_ne_zero hh

private theorem matrix_inner :
    ∃ ξ : K₂, ∀ x : M₂,
      commutator x + reduction x * ξ - ξ * reduction x = 0 := by
  obtain ⟨ξ, hξ⟩ := inner_from_casimir 2 reduction reduction_surjective
    reduction_kernel ((8 : ℤ) • C 0 1) scaled_C01_balance
    scaled_C01_nonzero K₂ leftAction rightAction actions_commute
    commutator commutator_leibniz
  refine ⟨ξ, fun x => ?_⟩
  simpa only [leftAction_apply, rightAction_apply, MulOpposite.unop_op]
    using hξ x

private theorem three_balance (x : M₂) :
    (x ⊗ₜ[ℤ] (1 : M₂)) * ((3 : ℤ) • C 0 0) =
      ((3 : ℤ) • C 0 0) * ((1 : M₂) ⊗ₜ[ℤ] x) := by
  rw [mul_smul_comm, smul_mul_assoc, C_balance]

example : (Fintype.card (Fin 2) : ZMod 2) = 0 := by decide

example : (Matrix.single 0 0 (1 : ℤ) : M₂) * Matrix.single 0 1 1 ≠
    Matrix.single 0 1 1 * Matrix.single 0 0 1 := by decide

private theorem matrix_localization :
    ∃ c : M₂ ⊗[ℤ] M₂,
      (∀ x : M₂, (x ⊗ₜ[ℤ] (1 : M₂)) * c =
        c * ((1 : M₂) ⊗ₜ[ℤ] x)) ∧
      reduction (LinearMap.mul' ℤ M₂ c) = 1 ∧
      let Δ := (Algebra.leftMulMatrix
        (Matrix.stdBasis ℤ (Fin 2) (Fin 2)) (LinearMap.mul' ℤ M₂ c)).det
      let S := Localization.Away Δ
      letI : CommRing S := inferInstance
      let e := tensorExtension S M₂ c
      (Δ : ZMod 2) = 1 ∧ ¬ (2 : ℤ) ∣ Δ ∧ Δ ≠ 0 ∧
      ∃ u : S ⊗[ℤ] M₂, (∀ x : S ⊗[ℤ] M₂, x * u = u * x) ∧
        LinearMap.mul' S (S ⊗[ℤ] M₂) e * u = 1 ∧
        u * LinearMap.mul' S (S ⊗[ℤ] M₂) e = 1 ∧
        (∀ x : S ⊗[ℤ] M₂,
          (x ⊗ₜ[S] (1 : S ⊗[ℤ] M₂)) *
              ((u ⊗ₜ[S] (1 : S ⊗[ℤ] M₂)) * e) =
            ((u ⊗ₜ[S] (1 : S ⊗[ℤ] M₂)) * e) *
              ((1 : S ⊗[ℤ] M₂) ⊗ₜ[S] x)) ∧
        LinearMap.mul' S (S ⊗[ℤ] M₂)
          ((u ⊗ₜ[S] (1 : S ⊗[ℤ] M₂)) * e) = 1 :=
  localized_from_casimir 2 reduction reduction_surjective reduction_kernel
    ((8 : ℤ) • C 0 1) scaled_C01_balance scaled_C01_nonzero
    (Matrix.stdBasis ℤ (Fin 2) (Fin 2))

private theorem three_nonzero : (3 : ℤ) • C 0 0 ≠ 0 := by
  intro h
  have hh := three_mu_reduction
  rw [h, map_zero, map_zero] at hh
  exact zero_ne_one hh

end IntegralCasimirTest
