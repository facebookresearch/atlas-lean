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
Adapted portions: the statement, balance and centrality lemmas, reduced
basis, sandwich and final adjustment arguments. Common-power normalization
uses the inherited PrimitiveFamily API instead of the source recursion.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Azumaya.Matrix
import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.PrimitiveFamily

/-!
# Integral balanced tensors with identity reduction

A finite free integer algebra with a full matrix special fiber admits a
balanced tensor whose multiplication image reduces to the identity, provided
it has a nonzero balanced tensor. The algebra need not be commutative.

The common-power step uses the inherited integer-family theorem. The matrix
sandwich step uses an opposite tensor only internally; the returned tensor
belongs to the ordinary tensor product. No matrix-size division is used.
-/

open scoped TensorProduct

namespace RingHom

variable {R : Type*} [Ring R]

private theorem balanced_one_tmul_mul {c : R ⊗[ℤ] R}
    (hc : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
      c * ((1 : R) ⊗ₜ[ℤ] x)) (y : R) :
    ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * (((1 : R) ⊗ₜ[ℤ] y) * c) =
      (((1 : R) ⊗ₜ[ℤ] y) * c) * ((1 : R) ⊗ₜ[ℤ] x) := by
  intro x
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, mul_assoc, ← hc x, ← mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem mul_tmul_one_mul (x : R) (c : R ⊗[ℤ] R) :
    LinearMap.mul' ℤ R ((x ⊗ₜ[ℤ] (1 : R)) * c) =
      x * LinearMap.mul' ℤ R c := by
  induction c using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add c d hc hd => simp [mul_add, hc, hd]

private theorem mul_mul_one_tmul (x : R) (c : R ⊗[ℤ] R) :
    LinearMap.mul' ℤ R (c * ((1 : R) ⊗ₜ[ℤ] x)) =
      LinearMap.mul' ℤ R c * x := by
  induction c using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add c d hc hd => simp [add_mul, hc, hd]

private theorem balanced_mul_central {c : R ⊗[ℤ] R}
    (hc : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
      c * ((1 : R) ⊗ₜ[ℤ] x)) (x : R) :
    x * LinearMap.mul' ℤ R c = LinearMap.mul' ℤ R c * x := by
  rw [← mul_tmul_one_mul, hc x, mul_mul_one_tmul]

private theorem exists_primitive_balanced {ι : Type*} [_root_.Finite ι]
    (b : Module.Basis ι ℤ (R ⊗[ℤ] R)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (c₀ : R ⊗[ℤ] R)
    (hc₀ : ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c₀ =
      c₀ * ((1 : R) ⊗ₜ[ℤ] x)) (h₀ : c₀ ≠ 0) :
    ∃ c : R ⊗[ℤ] R,
      (∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c =
        c * ((1 : R) ⊗ₜ[ℤ] x)) ∧ ∃ i, ¬ (ℓ : ℤ) ∣ b.repr c i := by
  classical
  let := Fintype.ofFinite ι
  have hf : (fun i => b.repr c₀ i) ≠ 0 := by
    intro h
    apply h₀
    apply b.ext_elem
    intro i
    simpa using congrFun h i
  obtain ⟨a, f, hf, i, hi⟩ :=
    Int.exists_pow_smul_eq_and_not_dvd _ hf ℓ hℓ.ne_one
  let c : R ⊗[ℤ] R := ∑ j, f j • b j
  have hc : ∀ j, b.repr c j = f j := by
    intro j
    exact congrFun (b.repr_sum_self f) j
  have heq : c₀ = (ℓ : ℤ) ^ a • c := by
    apply b.ext_elem
    intro j
    rw [map_smul, Finsupp.smul_apply, hc, smul_eq_mul]
    simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] using
      congrFun hf j
  have hm : (ℓ : ℤ) ^ a ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hℓ.ne_zero)
  have hinj : Function.Injective (fun t : R ⊗[ℤ] R =>
      (ℓ : ℤ) ^ a • t) := by
    intro t u h
    apply b.ext_elem
    intro j
    have hj := congrArg (fun v => b.repr v j) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hj
    exact mul_left_cancel₀ hm hj
  refine ⟨c, ?_, i, ?_⟩
  · intro x
    apply hinj
    simpa only [heq, mul_smul_comm, smul_mul_assoc] using hc₀ x
  · rwa [hc]

private noncomputable def reducedBasis
    {ℓ : ℕ} [Fact ℓ.Prime] {n : Type} [Fintype n] [DecidableEq n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    {ι : Type*} [_root_.Finite ι] (b : Module.Basis ι ℤ R) :
    Module.Basis ι (ZMod ℓ) (Matrix n n (ZMod ℓ)) := by
  classical
  let := Fintype.ofFinite ι
  refine Module.Basis.mk (v := fun i => ψ (b i)) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    let r : R := ∑ j, ((g j).cast : ℤ) • b j
    have hr : ψ r = 0 := by
      rw [← hg]
      simp only [r, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul (ZMod ℓ), ZMod.intCast_zmod_cast]
    obtain ⟨y, hy⟩ := (hker r).mp hr
    have hcoord : b.repr r i = (ℓ : ℤ) * b.repr y i := by
      rw [hy]
      have heq : (ℓ : R) * y = (ℓ : ℤ) • y := by
        rw [zsmul_eq_mul, Int.cast_natCast]
      rw [heq, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hri : b.repr r i = ((g i).cast : ℤ) := by
      exact congrFun (b.repr_sum_self (fun j => ((g j).cast : ℤ))) i
    rw [hri] at hcoord
    have hz : (((g i).cast : ℤ) : ZMod ℓ) = 0 := by
      rw [hcoord, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul]
    rwa [ZMod.intCast_zmod_cast] at hz
  · intro m _
    obtain ⟨r, rfl⟩ := hψ m
    rw [← b.sum_repr r, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod ℓ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem reducedBasis_apply
    {ℓ : ℕ} [Fact ℓ.Prime] {n : Type} [Fintype n] [DecidableEq n]
    (ψ : R →+* Matrix n n (ZMod ℓ)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : R, ψ x = 0 ↔ ∃ y : R, x = (ℓ : R) * y)
    {ι : Type*} [_root_.Finite ι] (b : Module.Basis ι ℤ R) (i : ι) :
    reducedBasis ψ hψ hker b i = ψ (b i) := by
  classical
  simp only [reducedBasis, Module.Basis.mk_apply]

private theorem exists_nonzero_sandwich
    {K : Type} [Field K] {n : Type} [Fintype n]
    [Nonempty n] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K (Matrix n n K)) (z : ι × ι → K)
    (hz : z ≠ 0) :
    ∃ m : Matrix n n K, ∑ p, z p • (b p.1 * m * b p.2) ≠ 0 := by
  classical
  let bop := b.map (MulOpposite.opLinearEquiv K)
  let bt := b.tensorProduct bop
  let t : Matrix n n K ⊗[K] (Matrix n n K)ᵐᵒᵖ :=
    ∑ p, z p • (b p.1 ⊗ₜ[K] MulOpposite.op (b p.2))
  have hb : ∀ p, bt p = b p.1 ⊗ₜ[K] MulOpposite.op (b p.2) := by
    intro p
    simp only [bt, bop, Module.Basis.tensorProduct_apply',
      Module.Basis.map_apply]
    rfl
  have hs : t = ∑ p, z p • bt p := by simp only [t, hb]
  by_contra h
  have hm : ∀ m : Matrix n n K,
      ∑ p, z p • (b p.1 * m * b p.2) = 0 :=
    fun m => not_not.mp (not_exists.mp h m)
  have he : AlgHom.mulLeftRight K (Matrix n n K) t = 0 := by
    apply LinearMap.ext
    intro m
    simpa only [t, map_sum, map_smul, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.smul_apply, AlgHom.mulLeftRight_apply,
      MulOpposite.unop_op, LinearMap.zero_apply] using hm m
  have ht : t = 0 := (IsAzumaya.matrix K n).bij.1 (by rw [he, map_zero])
  rw [hs] at ht
  have hrepr := bt.repr_sum_self z
  rw [ht, map_zero] at hrepr
  apply hz
  funext p
  exact (congrFun hrepr p).symm

/-- A nonzero balanced integral tensor can be replaced by one whose
multiplication image is the identity in the matrix special fiber.
The source's arbitrary algebra universe and Type0 matrix index are retained;
identity is asserted after `ψ`, not in the integral algebra. -/
public theorem exists_balancedTensor_map_mul_eq_one
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
  classical
  let := Module.Free.ChooseBasisIndex.fintype ℤ R
  let b := Module.Free.chooseBasis ℤ R
  let bt := b.tensorProduct b
  have hb : ∀ p, bt p = b p.1 ⊗ₜ[ℤ] b p.2 :=
    Module.Basis.tensorProduct_apply' b b
  let bm := reducedBasis ψ hψ hker b
  have hbm : ∀ i, bm i = ψ (b i) := reducedBasis_apply ψ hψ hker b
  obtain ⟨c, hc, p₁, hp₁⟩ :=
    exists_primitive_balanced bt ℓ Fact.out c₀ hc₀ h₀
  let z := fun p => bt.repr c p
  have hcz : c = ∑ p, z p • (b p.1 ⊗ₜ[ℤ] b p.2) := by
    conv_lhs => rw [← bt.sum_repr c]
    exact Finset.sum_congr rfl fun p _ => by rw [hb]
  have hsand : ∀ y : R,
      ψ (LinearMap.mul' ℤ R (((1 : R) ⊗ₜ[ℤ] y) * c)) =
        ∑ p, (z p : ZMod ℓ) • (bm p.1 * ψ y * bm p.2) := by
    intro y
    rw [hcz, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_smul_comm, map_zsmul, map_zsmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.mul'_apply,
      map_mul, map_mul, hbm, hbm,
      ← Int.cast_smul_eq_zsmul (ZMod ℓ), mul_assoc]
  let zb := fun p => (z p : ZMod ℓ)
  have hzb : zb ≠ 0 := by
    intro h
    have hi := congrFun h p₁
    simp only [zb, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    exact hp₁ hi
  obtain ⟨m, hm⟩ := exists_nonzero_sandwich bm zb hzb
  have hcentral : ∑ p, zb p • (bm p.1 * m * bm p.2) ∈
      Set.center (Matrix n n (ZMod ℓ)) := by
    obtain ⟨y, rfl⟩ := hψ m
    rw [← hsand]
    apply Semigroup.mem_center_iff.mpr
    intro a
    obtain ⟨x, rfl⟩ := hψ a
    rw [← map_mul, ← map_mul,
      balanced_mul_central (balanced_one_tmul_mul hc y) x]
  rw [Matrix.center_eq_range] at hcentral
  obtain ⟨κ, hκ⟩ := hcentral
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    apply hm
    rw [← hκ]
    simp
  let m₁ := κ⁻¹ • m
  have hm₁ : ∑ p, zb p • (bm p.1 * m₁ * bm p.2) = 1 := by
    have heq : ∑ p, zb p • (bm p.1 * m₁ * bm p.2) =
        κ⁻¹ • ∑ p, zb p • (bm p.1 * m * bm p.2) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [m₁, Matrix.mul_smul, Matrix.smul_mul,
        smul_comm (zb p) κ⁻¹]
    rw [heq, ← hκ, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, inv_mul_cancel₀ hκ0]
  obtain ⟨y, hy⟩ := hψ m₁
  refine ⟨((1 : R) ⊗ₜ[ℤ] y) * c, balanced_one_tmul_mul hc y, ?_⟩
  rw [hsand y, hy]
  exact hm₁

end RingHom
