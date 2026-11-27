/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`Definitions/Def_MvFormalGroup_BasicV2.lean`,
`Definitions/Def_MvFormalGroup_EndRingV2.lean`,
`P2M/Sol/S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`P2M/Sol/S_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric.lean`, and
`P2M/Sol/S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq.lean`
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

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Span

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rescaled logarithms of multivariate formal group laws

For every `a : R`, `MvFormalGroup.rescale` turns a formal group law `F` over `R` into the formal
group law whose coefficients of total degree `n ≥ 1` are those of `F` multiplied by
`a ^ (n - 1)`; when `a` is a unit this is `a⁻¹ F(a X, a Y)`. It is commutative when `F` is.

The main result, `MvFormalGroup.exists_rescaledLog_of_isAdicComplete`, says: if `p` is a
prime that is a non-zero-divisor in a `p`-adically complete ring `𝓞`, then every commutative
`d`-dimensional formal group law `F` over `𝓞` has a rescaling `Fp` (coefficients of total
degree `n` multiplied by `p ^ (n - 1)`) that admits a logarithm `φ` over `𝓞`: `φ` has zero
constant terms, identity linear part, coefficients tending to zero `p`-adically, and turns
`Fp` into the additive formal group law. `MvFormalGroup.exists_log_rescale_of_isAdicComplete`
states the same logarithm for the formal group law `F.rescale p`.

The formal group law API it builds on (`MvFormalGroup`, `MvFormalGroup.IsComm`, base change,
substitution lemmas) is in `MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor`.
-/

noncomputable section

namespace CocycleAux

open MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*}

theorem pderiv_aeval [Fintype σ] {τ : Type*} (w : τ) (φ : σ →
    MvPolynomial τ R) (g : MvPolynomial σ R) :
    pderiv w (aeval φ g) = ∑ u : σ, pderiv w (φ u) * aeval φ (pderiv u g) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X q u₀ h =>
    have hX : ∀ u, aeval φ (pderiv u (q * X u₀)) =
        aeval φ q * (if u = u₀ then 1 else 0) + φ u₀ * aeval φ (pderiv u q) := by
      intro u
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, aeval_X,
          pderiv_X]
      by_cases hu : u = u₀
      · subst hu; simp
      · simp [Ne.symm hu, hu]
    simp_rw [hX, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ,
      ite_true]
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h, Finset.mul_sum,
        mul_comm (aeval φ q)]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring

variable [Fintype σ]

local notation "P1" => MvPolynomial σ R
local notation "P2" => MvPolynomial (σ ⊕ σ) R
local notation "P3" => MvPolynomial (σ ⊕ (σ ⊕ σ)) R

noncomputable def plus (q : MvPolynomial σ R) : MvPolynomial (σ ⊕ σ) R :=
  aeval (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPolynomial (σ ⊕ σ) R)) q

noncomputable def delta (q : MvPolynomial σ R) : MvPolynomial (σ ⊕ σ) R :=
  plus q - rename Sum.inl q - rename Sum.inr q

omit [Fintype σ] in
theorem delta_smul (c : R) (q : MvPolynomial σ R) : delta (c • q) = c • delta q := by
  simp only [delta, plus, map_smul, smul_sub]

omit [Fintype σ] in
theorem delta_sum {ι : Type*} (s : Finset ι) (q : ι → MvPolynomial σ R) :
    delta (∑ i ∈ s, q i) = ∑ i ∈ s, delta (q i) := by
  simp only [delta, plus, map_sum, Finset.sum_sub_distrib]

variable (R σ) in
noncomputable def φYZ : σ ⊕ σ → P3 :=
  Sum.elim (fun s => X (Sum.inr (Sum.inl s))) (fun s => X (Sum.inr (Sum.inr s)))
variable (R σ) in
noncomputable def φXYZ : σ ⊕ σ → P3 :=
  Sum.elim (fun s => X (Sum.inl s) + X (Sum.inr (Sum.inl s))) (fun s => X (Sum.inr (Sum.inr s)))
variable (R σ) in
noncomputable def φXYZ' : σ ⊕ σ → P3 :=
  Sum.elim (fun s => X (Sum.inl s)) (fun s => X (Sum.inr (Sum.inl s)) + X (Sum.inr (Sum.inr s)))
variable (R σ) in
noncomputable def φXY : σ ⊕ σ → P3 :=
  Sum.elim (fun s => X (Sum.inl s)) (fun s => X (Sum.inr (Sum.inl s)))

noncomputable def ev0 : P3 →ₐ[R] P2 :=
  aeval (Sum.elim (fun s => X (Sum.inl s)) (Sum.elim (fun s => X (Sum.inr s)) (fun _ => 0)))

noncomputable def gk (Γ : P2) (k : σ) : P1 := aeval (Sum.elim X (fun _ =>
    (0 : P1))) (pderiv (Sum.inr k) Γ)

omit [Fintype σ] in
open Classical in
theorem pderiv_Z_φ (k : σ) :
    (∀ u, pderiv (Sum.inr (Sum.inr k)) (φYZ R σ u) = if u = Sum.inr k then 1 else 0) ∧
    (∀ u, pderiv (Sum.inr (Sum.inr k)) (φXYZ R σ u) = if u = Sum.inr k then 1 else 0) ∧
    (∀ u, pderiv (Sum.inr (Sum.inr k)) (φXYZ' R σ u) = if u = Sum.inr k then 1 else 0) ∧
    (∀ u, pderiv (Sum.inr (Sum.inr k)) (φXY R σ u) = 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro (s | s) <;>
    simp [φYZ, φXYZ, φXYZ', φXY, pderiv_X, Pi.single_apply, eq_comm]

omit [Fintype σ] in
theorem pderiv_inr_eq [Finite σ] (Γ : P2)
    (hcoc : aeval (φYZ R σ) Γ - aeval (φXYZ R σ) Γ + aeval (φXYZ' R σ) Γ - aeval (φXY R σ) Γ =
        0) (k : σ) :
    pderiv (Sum.inr k) Γ = plus (gk Γ k) - rename Sum.inr (gk Γ k) := by
  cases nonempty_fintype σ
  classical
  obtain ⟨h1, h2, h3, h4⟩ := pderiv_Z_φ (R := R) (σ := σ) k
  have key := congrArg (fun P => ev0 (pderiv (Sum.inr (Sum.inr k)) P)) hcoc
  simp only [map_sub, map_add, map_zero, pderiv_aeval, h1, h2, h3, h4, zero_mul,
      Finset.sum_const_zero,
    ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
  have f1 : (fun u => ev0 (φYZ R σ u)) = fun u => rename Sum.inr (Sum.elim X (fun _ =>
      (0 : P1)) u) := by
    funext u; rcases u with s | s <;> simp [ev0, φYZ]
  have f2 : (fun u => ev0 (φXYZ R σ u)) =
      fun u => aeval (fun s => (X (Sum.inl s) + X (Sum.inr s) : P2)) (Sum.elim X (fun _ =>
          (0 : P1)) u) := by
    funext u; rcases u with s | s <;> simp [ev0, φXYZ]
  have f3 : (fun u => ev0 (φXYZ' R σ u)) = fun u => (X u : P2) := by
    funext u; rcases u with s | s <;> simp [ev0, φXYZ']
  have e1 : ev0 (aeval (φYZ R σ) (pderiv (Sum.inr k) Γ)) = rename Sum.inr (gk Γ k) := by
    rw [comp_aeval_apply, f1, gk]
    exact (comp_aeval_apply _ (rename Sum.inr) _).symm
  have e2 : ev0 (aeval (φXYZ R σ) (pderiv (Sum.inr k) Γ)) = plus (gk Γ k) := by
    rw [comp_aeval_apply, f2, gk, plus]
    exact (comp_aeval_apply _ (aeval _) _).symm
  have e3 : ev0 (aeval (φXYZ' R σ) (pderiv (Sum.inr k) Γ)) = pderiv (Sum.inr k) Γ := by
    rw [comp_aeval_apply, f3, aeval_X_left_apply]
  rw [e1, e2, e3, sub_zero] at key
  linear_combination key

omit [Fintype σ] in
theorem pderiv_inl_eq [Finite σ] (Γ : P2) (hsymm : rename Sum.swap Γ = Γ)
    (hcoc : aeval (φYZ R σ) Γ - aeval (φXYZ R σ) Γ + aeval (φXYZ' R σ) Γ - aeval (φXY R σ) Γ =
        0) (k : σ) :
    pderiv (Sum.inl k) Γ = plus (gk Γ k) - rename Sum.inl (gk Γ k) := by
  have h := pderiv_inr_eq Γ hcoc k
  have hsw : pderiv (Sum.inl k) Γ = rename Sum.swap (pderiv (Sum.inr k) Γ) := by
    conv_lhs => rw [← hsymm]
    exact pderiv_rename Sum.swap_leftInverse.injective (Sum.inr k) Γ
  have e1 : (fun s => rename Sum.swap (X (Sum.inl s) + X (Sum.inr s) : P2)) =
      fun s => (X (Sum.inl s) + X (Sum.inr s) : P2) := by
    funext s; simp [add_comm]
  rw [hsw, h, map_sub, rename_rename, plus, comp_aeval_apply, e1]
  rfl

theorem nsmul_eq_delta (n : ℕ) (Γ : P2) (hhom : Γ.IsHomogeneous n) (hsymm : rename Sum.swap Γ = Γ)
    (hcoc : aeval (φYZ R σ) Γ - aeval (φXYZ R σ) Γ + aeval (φXYZ' R σ) Γ - aeval (φXY R σ) Γ = 0) :
    n • Γ = delta (∑ s, X s * gk Γ s) := by
  have heuler := hhom.sum_X_mul_pderiv
  rw [Fintype.sum_sum_type] at heuler
  simp only [pderiv_inl_eq Γ hsymm hcoc, pderiv_inr_eq Γ hcoc] at heuler
  rw [← heuler, delta_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [delta, plus, map_mul, aeval_X, rename_X]
  ring

theorem isHomogeneous_H (n : ℕ) (hn : n ≠ 0) (Γ : P2) (hhom : Γ.IsHomogeneous n) :
    (∑ s, X s * gk Γ s : P1).IsHomogeneous n := by
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have hg : (gk Γ s).IsHomogeneous (n - 1) := by
    have := (hhom.pderiv (i := Sum.inr s)).aeval (Sum.elim X (fun _ => (0 : P1))) (n := 1)
      (fun u => by
        rcases u with t | t
        · exact isHomogeneous_X R t
        · exact isHomogeneous_zero _ _ _)
    simpa [gk] using this
  have := (isHomogeneous_X R s).mul hg
  rwa [show 1 + (n - 1) = n by omega] at this

omit [Fintype σ] in
theorem main [Finite σ] (n : ℕ) (hn : IsUnit (n : R)) (Γ : P2) (hhom : Γ.IsHomogeneous n)
    (hsymm : rename Sum.swap Γ = Γ)
    (hcoc : aeval (φYZ R σ) Γ - aeval (φXYZ R σ) Γ + aeval (φXYZ' R σ) Γ - aeval (φXY R σ) Γ = 0) :
    ∃ h : P1, h.IsHomogeneous n ∧ Γ = delta h := by
  classical
  cases nonempty_fintype σ
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, isHomogeneous_zero _ _ _, Subsingleton.elim _ _⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 : ¬ IsUnit (0 : R) := not_isUnit_zero
    exact h0 (by simp at hn)
  refine ⟨((hn.unit⁻¹ : Rˣ) : R) • ∑ s, X s * gk Γ s, ?_, ?_⟩
  · exact (homogeneousSubmodule σ R n).smul_mem _ (isHomogeneous_H n hn0 Γ hhom)
  · rw [delta_smul, ← nsmul_eq_delta n Γ hhom hsymm hcoc, ← Nat.cast_smul_eq_nsmul R, smul_smul,
      IsUnit.val_inv_mul, one_smul]

end CocycleAux

universe u v

theorem MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ] (n : ℕ) (hn : IsUnit (n : R))
    (Γ : MvPolynomial (σ ⊕ σ) R) (hhom : Γ.IsHomogeneous n)
    (hsymm : MvPolynomial.rename Sum.swap Γ = Γ)
    (hcoc :
      MvPolynomial.aeval (Sum.elim (fun s =>
          (MvPolynomial.X (Sum.inr (Sum.inl s)) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
          (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) +
            MvPolynomial.X (Sum.inr (Sum.inl s)) :
            MvPolynomial (σ ⊕ (σ ⊕ σ)) R)) (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        + MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕
            (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)) +
                MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕
            (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)))) Γ = 0) :
    ∃ h : MvPolynomial σ R, h.IsHomogeneous n ∧
      Γ = MvPolynomial.aeval (fun s => (MvPolynomial.X (Sum.inl s) +
          MvPolynomial.X (Sum.inr s) : MvPolynomial (σ ⊕ σ) R)) h
        - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h := by
  cases nonempty_fintype σ
  exact CocycleAux.main n hn Γ hhom hsymm hcoc

end


noncomputable section

namespace DualAux

open MvPowerSeries

variable {R : Type*} [CommRing R] {σ : Type*} {τ : Type*} {κ : Type*}

local notation "D" => DualNumber R

noncomputable def iota (a : MvPowerSeries τ R) : MvPowerSeries (τ ⊕ κ) R :=
  subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) a

theorem hasSubst_Xinl : HasSubst (fun t : τ => (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) := by
  classical
  refine ⟨fun t => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d => ?_⟩
  apply Set.Subsingleton.finite
  intro t₁ h₁ t₂ h₂
  simp only [Set.mem_ofPred_eq, coeff_X] at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  · have := e₁.symm.trans e₂
    exact Sum.inl_injective (Finsupp.single_left_injective one_ne_zero this)
  all_goals simp_all

theorem constantCoeff_iota (a : MvPowerSeries τ R) (ha : constantCoeff a = 0) :
    constantCoeff (iota (κ := κ) a) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_Xinl (fun _ => constantCoeff_X _) ha

variable [Fintype σ] [Fintype κ]

noncomputable def Gfam (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    MvPowerSeries (τ ⊕ κ) R :=
  iota (A i) + ∑ k' : κ, X (Sum.inr k') * iota (B i k')

omit [Fintype σ] in
theorem constantCoeff_Gfam (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (i : σ) : constantCoeff (Gfam A B i) = 0 := by
  rw [Gfam, map_add, constantCoeff_iota _ (hA i), map_sum, zero_add]
  exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]

omit [Fintype σ] in
theorem hasSubst_Gfam [Finite σ] (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) : HasSubst (Gfam A B) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_Gfam A hA B)

open Classical in
noncomputable def ak (k : κ) : τ ⊕ κ → MvPowerSeries τ D :=
  Sum.elim (fun t => X t) (fun k' => if k' = k then C DualNumber.eps else 0)

omit [Fintype κ] in
theorem hasSubst_ak [Finite κ] (k : κ) : HasSubst (ak (R := R) (τ := τ) k) := by
  classical
  refine ⟨?_, fun d => ?_⟩
  · rintro (t | k')
    · simp only [ak, Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
    · simp only [ak, Sum.elim_inr]
      split_ifs
      · rw [constantCoeff_C]; exact ⟨2, DualNumber.eps_pow_two⟩
      · rw [map_zero]; exact IsNilpotent.zero
  · apply Set.Finite.subset ((Set.finite_range Sum.inr).union
      (Set.Subsingleton.finite (s := {u : τ ⊕ κ | ∃ t, u = Sum.inl t ∧ d = Finsupp.single t 1}) ?_))
    · rintro (t | k') hu
      · right
        refine ⟨t, rfl, ?_⟩
        simp only [Set.mem_ofPred_eq, ak, Sum.elim_inl, coeff_X] at hu
        by_contra h
        exact hu (ite_eq_right h)
      · left; exact ⟨k', rfl⟩
    · rintro u₁ ⟨t₁, rfl, h₁⟩ u₂ ⟨t₂, rfl, h₂⟩
      rw [h₁] at h₂
      rw [Finsupp.single_left_injective one_ne_zero h₂]

noncomputable def theta (k : κ) : MvPowerSeries (τ ⊕ κ) R →ₐ[R] MvPowerSeries τ D :=
  substAlgHom (hasSubst_ak k)

theorem theta_apply (k : κ) (g : MvPowerSeries (τ ⊕ κ) R) : theta k g = subst (ak k) g := by
  rw [theta, substAlgHom_apply]

open Classical in
theorem theta_X_inr (k k' : κ) :
    theta (R := R) (τ := τ) k (X (Sum.inr k')) = if k' = k then C DualNumber.eps else 0 := by
  classical
  rw [theta, substAlgHom_X]; rfl

theorem theta_iota (k : κ) (a : MvPowerSeries τ R) :
    theta k (iota (κ := κ) a) = map (algebraMap R D) a := by
  rw [theta_apply, iota, subst_comp_subst_apply hasSubst_Xinl (hasSubst_ak k),
      map_algebraMap_eq_subst_X]
  congr 1
  funext t
  rw [subst_X (hasSubst_ak k)]; rfl

omit [Fintype σ] in
theorem theta_Gfam (k : κ) (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    theta k (Gfam A B i) = map (algebraMap R D) (A i) + C DualNumber.eps *
        map (algebraMap R D) (B i k) := by
  classical
  rw [Gfam, map_add, map_sum, theta_iota]
  congr 1
  simp_rw [map_mul, theta_X_inr, theta_iota, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]

theorem C_eps_mul_C_eps : (C DualNumber.eps : MvPowerSeries τ D) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

omit [Fintype κ] in
theorem aeval_dual (k : κ) (A : σ → MvPowerSeries τ R) (B : σ → κ →
    MvPowerSeries τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => map (algebraMap R D) (A i) + C DualNumber.eps *
        map (algebraMap R D) (B i k)) P =
      map (algebraMap R D) (MvPolynomial.aeval A P) +
        C DualNumber.eps * map (algebraMap R D) (∑ i,
            B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i P)) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, mul_zero,
        Finset.sum_const_zero, add_zero]
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, map_C,
        Algebra.algebraMap_self,
      RingHom.id_apply]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X q i₀ h =>
    have hder : ∀ i, MvPolynomial.aeval A (MvPolynomial.pderiv i (q * MvPolynomial.X i₀)) =
        MvPolynomial.aeval A (MvPolynomial.pderiv i q) * A i₀ +
          (if i = i₀ then MvPolynomial.aeval A q else 0) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
          MvPolynomial.aeval_X,
        MvPolynomial.pderiv_X]
      by_cases hi : i = i₀
      · subst hi
        simp only [Pi.single_eq_same, map_one, ite_true]
        ring
      · simp only [Pi.single_eq_of_ne (Ne.symm hi), map_zero, ite_eq_right hi]
        ring
    have hsum : (∑ i, B i k * (MvPolynomial.aeval A (MvPolynomial.pderiv i q) * A i₀ +
        if i = i₀ then MvPolynomial.aeval A q else 0)) =
        (∑ i, B i k *
            MvPolynomial.aeval A (MvPolynomial.pderiv i q)) * A i₀ + B i₀ k *
                MvPolynomial.aeval A q := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true,
        Finset.sum_mul, mul_assoc]
    simp_rw [hder]
    rw [hsum, map_mul, MvPolynomial.aeval_X, h, map_mul, MvPolynomial.aeval_X]
    simp only [map_add, map_mul]
    have hε := C_eps_mul_C_eps (R := R) (τ := τ)
    linear_combination (map (algebraMap R D) (∑ i,
        B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i q)) *
      map (algebraMap R D) (B i₀ k)) * hε

noncomputable def a0 : τ ⊕ κ → MvPowerSeries τ R := Sum.elim (fun t => X t) (fun _ => 0)

omit [Fintype σ] [Fintype κ] in
theorem hasSubst_a0 : HasSubst (a0 (R := R) (τ := τ) (κ := κ)) := by
  classical
  refine ⟨?_, fun d => ?_⟩
  · rintro (t | k')
    · simp only [a0, Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
    · simp only [a0, Sum.elim_inr, map_zero]; exact IsNilpotent.zero
  · apply Set.Subsingleton.finite
    rintro (t₁ | k₁) h₁ (t₂ | k₂) h₂ <;>
      simp only [Set.mem_ofPred_eq, a0, Sum.elim_inl, Sum.elim_inr, coeff_X, map_zero, ne_eq,
        not_true_eq_false] at h₁ h₂
    split_ifs at h₁ h₂ with e₁ e₂
    · rw [e₁] at e₂
      rw [Finsupp.single_left_injective one_ne_zero e₂]
    all_goals simp_all

noncomputable def theta0 : MvPowerSeries (τ ⊕
    κ) R →ₐ[R] MvPowerSeries τ R := substAlgHom hasSubst_a0

omit [Fintype σ] [Fintype κ] in
theorem theta0_apply (g : MvPowerSeries (τ ⊕ κ) R) : theta0 g = subst a0 g := by
  rw [theta0, substAlgHom_apply]

omit [Fintype σ] [Fintype κ] in
theorem theta0_iota (a : MvPowerSeries τ R) : theta0 (iota (κ := κ) a) = a := by
  rw [theta0_apply, iota, subst_comp_subst_apply hasSubst_Xinl hasSubst_a0]
  have : (fun t => subst (a0 (R := R) (κ := κ)) (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) =
      (X : τ → MvPowerSeries τ R) := by
    funext t; rw [subst_X hasSubst_a0]; rfl
  rw [this]
  exact congrFun subst_self a

omit [Fintype σ] in
theorem theta0_Gfam (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    theta0 (Gfam A B i) = A i := by
  rw [Gfam, map_add, map_sum, theta0_iota]
  convert add_zero _
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [map_mul, theta0, substAlgHom_X]
  simp [a0]

omit [Fintype σ] in
theorem prod_X_pow_eq_monomial (n : τ →₀ ℕ) :
    (n.prod fun t e => (X t : MvPowerSeries τ D) ^ e) = monomial n 1 :=
  (MvPowerSeries.monomial_one_eq n).symm

omit [Fintype σ] [Fintype κ] in
theorem prod_X_pow_eq_monomial' (n : τ →₀ ℕ) :
    (n.prod fun t e => (X t : MvPowerSeries τ R) ^ e) = monomial n 1 :=
  (MvPowerSeries.monomial_one_eq n).symm

omit [Fintype σ] in
open Classical in
omit [Fintype κ] in
theorem coeff_prod_ak (k : κ) (m : τ →₀ ℕ) (n : τ ⊕ κ →₀ ℕ) :
    coeff m (n.prod fun u e => ak (R := R) k u ^ e) =
      if n = m.sumElim 0 then 1 else if n =
          m.sumElim (Finsupp.single k 1) then DualNumber.eps else 0 := by
  set nτ : τ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
  set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
  have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
  have hsplit : ∀ (c : κ →₀ ℕ), (nτ.sumElim nκ = m.sumElim c ↔ m = nτ ∧ nκ = c) := by
    intro c
    constructor
    · intro h
      exact ⟨Eq.symm (by simpa using congrArg (fun c =>
          Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
        by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  rw [hn, Finsupp.prod_sumElim]
  simp only [Function.comp_def, ak, Sum.elim_inl, Sum.elim_inr, prod_X_pow_eq_monomial]
  have hY : (nκ.prod fun k' e => ((if k' =
      k then C DualNumber.eps else 0 : MvPowerSeries τ D)) ^ e) =
      if nκ = 0 then 1 else if nκ = Finsupp.single k 1 then C DualNumber.eps else 0 := by
    by_cases h0 : nκ = 0
    · rw [h0, ite_eq_left rfl, Finsupp.prod_zero_index]
    rw [ite_eq_right h0]
    by_cases hsupp : nκ.support ⊆ {k}
    · have hj : nκ = Finsupp.single k (nκ k) := by
        ext k'
        by_cases hk' : k' = k
        · subst hk'; rw [Finsupp.single_eq_same]
        · rw [Finsupp.single_eq_of_ne hk']
          by_contra hne
          exact hk' (Finset.mem_singleton.1 (hsupp (Finsupp.mem_support_iff.2 hne)))
      have hk0 : nκ k ≠ 0 := fun h => h0 (by rw [hj, h, Finsupp.single_zero])
      rw [hj, Finsupp.prod_single_index (by simp), ite_eq_left rfl]
      obtain ⟨j, hjj⟩ : ∃ j, nκ k = j + 1 := ⟨nκ k - 1, by omega⟩
      rw [hjj]
      rcases j with _ | j
      · simp
      · rw [ite_eq_right, pow_succ, pow_succ, mul_assoc, C_eps_mul_C_eps, mul_zero]
        intro h
        have := congrArg (fun c => c k) h
        simp at this
    · obtain ⟨k', hk'mem, hk'⟩ : ∃ k' ∈ nκ.support, k' ≠ k := by
        by_contra h
        apply hsupp
        intro k' hk'
        by_contra hkk
        exact h ⟨k', hk', fun e => hkk (Finset.mem_singleton.2 e)⟩
      rw [Finsupp.prod, Finset.prod_eq_zero hk'mem (by rw [ite_eq_right hk',
          zero_pow (Finsupp.mem_support_iff.1 hk'mem)]),
        ite_eq_right]
      intro h
      rw [h, Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hk'] at hk'mem
      exact hk'mem rfl
  rw [hY]
  simp only [hsplit]
  have hk1 : (Finsupp.single k 1 : κ →₀ ℕ) ≠ 0 := by simp
  clear_value nτ nκ
  clear hY hn hnτ hnκ hsplit
  split_ifs <;> simp_all [coeff_monomial, coeff_mul_C, eq_comm (a := (0 : κ →₀ ℕ))]

omit [Fintype σ] in
theorem coeff_theta (k : κ) (g : MvPowerSeries (τ ⊕ κ) R) (m : τ →₀ ℕ) :
    coeff m (theta k g) = TrivSqZeroExt.inl (coeff (m.sumElim 0) g) +
      (coeff (m.sumElim (Finsupp.single k 1)) g) • DualNumber.eps := by
  classical
  have hne : m.sumElim (0 : κ →₀ ℕ) ≠ m.sumElim (Finsupp.single k 1) := by
    intro h
    have := congrArg (fun c => c (Sum.inr k)) h
    simp at this
  rw [theta_apply, coeff_subst (hasSubst_ak k),
    finsum_eq_sum_of_support_subset (s := {m.sumElim 0, m.sumElim (Finsupp.single k 1)})]
  · rw [Finset.sum_pair hne, coeff_prod_ak, coeff_prod_ak, ite_eq_left rfl, ite_eq_right hne.symm,
        ite_eq_left rfl]
    rw [Algebra.smul_def, mul_one, TrivSqZeroExt.algebraMap_eq_inl]
  · intro n hn
    rw [Function.mem_support, coeff_prod_ak] at hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    rw [not_or] at h
    rw [ite_eq_right h.1, ite_eq_right h.2, smul_zero] at hn
    exact hn rfl

omit [Fintype σ] [Fintype κ] in
theorem coeff_pderiv (Q : MvPolynomial σ R) (i : σ) (n : σ →₀ ℕ) :
    (MvPolynomial.pderiv i Q).coeff n = ((n i + 1 : ℕ) : R) * Q.coeff (n + Finsupp.single i 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = n + Finsupp.single i 1
    · subst hs
      rw [ite_eq_left (add_tsub_cancel_right _ _), ite_eq_left rfl, Finsupp.add_apply,
          Finsupp.single_eq_same, mul_comm]
    · rw [ite_eq_right hs, mul_zero]
      split_ifs with h
      · have hsi : s i = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2
              hne))).symm
        rw [hsi, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]

open Classical in
noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f =>
      Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

omit [Fintype κ] in
theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

noncomputable def truncTot (N : ℕ) (f : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ n ∈ lowDeg σ N, MvPolynomial.monomial n (coeff n f)

omit [Fintype κ] in
theorem coeff_truncTot (N : ℕ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    (truncTot N f).coeff n = if n.degree ≤ N then coeff n f else 0 := by
  classical
  rw [truncTot, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [mem_lowDeg]

omit [Fintype κ] in
theorem le_order_sub_truncTot (N : ℕ) (f : MvPowerSeries σ R) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (f - (truncTot N f : MvPowerSeries σ R)).order :=
  nat_le_order fun n hn => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTot, ite_eq_left (by omega), sub_self]

omit [Fintype κ] in
theorem le_order_Df_sub (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
        coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (N : ℕ) (i : σ) :
    (N : ℕ∞) ≤ (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order :=
  nat_le_order fun n hn => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_pderiv, coeff_truncTot, hDf,
      ite_eq_left (by rw [map_add, Finsupp.degree_single]; omega), sub_self]

omit [Fintype σ] in
theorem one_le_iInf_order (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) : (1 : ℕ∞) ≤ ⨅ i, (Gfam A B i).order := by
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, constantCoeff_Gfam A hA B]

omit [Fintype σ] [Fintype κ] in
theorem one_le_iInf_order' (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) :
    (1 : ℕ∞) ≤ ⨅ i, (A i).order := by
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, hA]

omit [Fintype σ] [Fintype κ] in
theorem degree_sumElim (m : τ →₀ ℕ) (c : κ →₀ ℕ) : (m.sumElim c).degree = m.degree + c.degree := by
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

theorem coeff_subst_eq_coeff_aeval (f : MvPowerSeries σ R) (A : σ → MvPowerSeries τ R)
    (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R) (N : ℕ) (e : τ ⊕ κ →₀ ℕ)
    (he : e.degree ≤ N) :
    coeff e (subst (Gfam A B) f) = coeff e (MvPolynomial.aeval (Gfam A B) (truncTot N f)) := by
  have hG := hasSubst_Gfam A hA B
  have hdec : subst (Gfam A B) f = subst (Gfam A B) (truncTot N f : MvPowerSeries σ R) +
      subst (Gfam A B) (f - (truncTot N f : MvPowerSeries σ R)) := by
    rw [← subst_add hG]; congr 1; ring
  rw [hdec, subst_coe, map_add]
  convert add_zero _
  apply coeff_of_lt_order
  calc ((e.degree : ℕ) : ℕ∞) < (N + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le he
    _ ≤ (f - (truncTot N f : MvPowerSeries σ R)).order := le_order_sub_truncTot N f
    _ ≤ (⨅ i, (Gfam A B i).order) * (f - (truncTot N f : MvPowerSeries σ R)).order :=
        le_mul_of_one_le_left (by simp) (one_le_iInf_order A hA B)
    _ ≤ _ := le_order_subst hG _

theorem coeff_theta_subst (k : κ) (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
        coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) (c : κ →₀ ℕ) (hc : c.degree ≤ 1) :
    coeff (m.sumElim c) (subst (Gfam A B) f) =
      coeff (m.sumElim c) (MvPolynomial.aeval (Gfam A B) (truncTot (m.degree + 1) f)) ∧
    coeff m (subst A f) = coeff m (MvPolynomial.aeval A (truncTot (m.degree + 1) f)) ∧
    coeff m (∑ i, B i k * subst A (Df i)) =
      coeff m (∑ i,
          B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i (truncTot (m.degree + 1) f))) := by
  set N := m.degree + 1 with hN
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  refine ⟨coeff_subst_eq_coeff_aeval f A hA B N _ (by rw [degree_sumElim]; omega), ?_, ?_⟩
  · have hdec : subst A f = subst A (truncTot N f : MvPowerSeries σ R) +
        subst A (f - (truncTot N f : MvPowerSeries σ R)) := by
      rw [← subst_add hAs]; congr 1; ring
    rw [hdec, subst_coe, map_add]
    convert add_zero _
    apply coeff_of_lt_order
    calc ((m.degree : ℕ) : ℕ∞) < (N + 1 : ℕ) := by exact_mod_cast (by omega : m.degree < N + 1)
      _ ≤ (f - (truncTot N f : MvPowerSeries σ R)).order := le_order_sub_truncTot N f
      _ ≤ (⨅ i, (A i).order) * (f - (truncTot N f : MvPowerSeries σ R)).order :=
          le_mul_of_one_le_left (by simp) (one_le_iInf_order' A hA)
      _ ≤ _ := le_order_subst hAs _
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdec : subst A (Df i) =
        subst A (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R) +
        subst A (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)) := by
      rw [← subst_add hAs]; congr 1; ring
    rw [hdec, subst_coe, mul_add, map_add]
    convert add_zero _
    apply coeff_of_lt_order
    calc ((m.degree : ℕ) : ℕ∞) < N := by exact_mod_cast (by omega : m.degree < N)
      _ ≤ (Df i -
          (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order :=
              le_order_Df_sub f Df hDf N i
      _ ≤ (⨅ i,
          (A i).order) * (Df i -
              (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order :=
          le_mul_of_one_le_left (by simp) (one_le_iInf_order' A hA)
      _ ≤ (subst A (Df i -
          (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R))).order := le_order_subst hAs _
      _ ≤ (B i k).order + (subst A (Df i -
          (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R))).order :=
          le_add_self
      _ ≤ _ := le_order_mul

theorem main1 (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
        coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) (k : κ) :
    coeff (m.sumElim (Finsupp.single k 1)) (subst (Gfam A B) f) = coeff m (∑ i,
        B i k * subst A (Df i)) := by
  classical
  obtain ⟨h1, -,
      h3⟩ := coeff_theta_subst k f Df hDf A hA B m (Finsupp.single k 1) (by rw
          [Finsupp.degree_single])
  rw [h1, h3]
  set P := truncTot (m.degree + 1) f
  set W := ∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i P) with hW
  have key := coeff_theta k (MvPolynomial.aeval (Gfam A B) P : MvPowerSeries (τ ⊕ κ) R) m
  rw [MvPolynomial.comp_aeval_apply, show (fun i => theta k (Gfam A B i)) =
      fun i => map (algebraMap R D) (A i) + C DualNumber.eps * map (algebraMap R D) (B i k) from
        funext fun i => theta_Gfam k A B i, aeval_dual, ← hW, map_add, coeff_map, coeff_C_mul,
            coeff_map] at key
  have := congrArg TrivSqZeroExt.snd key
  simp [TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_eps, DualNumber.fst_eps] at this
  exact this.symm

omit [Fintype σ] [Fintype κ] in
open Classical in
theorem coeff_prod_a0 (m : τ →₀ ℕ) (n : τ ⊕ κ →₀ ℕ) :
    coeff m (n.prod fun u e => a0 (R := R) (κ := κ) u ^ e) = if n = m.sumElim 0 then 1 else 0 := by
  classical
  set nτ : τ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
  set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
  have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
  have hsplit : (nτ.sumElim nκ = m.sumElim 0 ↔ m = nτ ∧ nκ = 0) := by
    constructor
    · intro h
      exact ⟨Eq.symm (by simpa using congrArg (fun c =>
          Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
        by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  rw [hn, Finsupp.prod_sumElim]
  simp only [Function.comp_def, a0, Sum.elim_inl, Sum.elim_inr, prod_X_pow_eq_monomial']
  have hY : (nκ.prod fun _ e => ((0 : MvPowerSeries τ R)) ^ e) = if nκ = 0 then 1 else 0 := by
    by_cases h0 : nκ = 0
    · rw [h0, ite_eq_left rfl, Finsupp.prod_zero_index]
    · rw [ite_eq_right h0]
      obtain ⟨k', hk'⟩ := Finsupp.support_nonempty_iff.2 h0
      rw [Finsupp.prod, Finset.prod_eq_zero hk' (by rw [zero_pow (Finsupp.mem_support_iff.1 hk')])]
  rw [hY]
  simp only [hsplit]
  clear_value nτ nκ
  clear hY hn hnτ hnκ hsplit
  split_ifs <;> simp_all [coeff_monomial]

omit [Fintype σ] in
omit [Fintype κ] in
theorem coeff_theta0 (g : MvPowerSeries (τ ⊕ κ) R) (m : τ →₀ ℕ) :
    coeff m (theta0 g) = coeff (m.sumElim 0) g := by
  classical
  rw [theta0_apply, coeff_subst hasSubst_a0, finsum_eq_single _ (m.sumElim 0)]
  · rw [coeff_prod_a0, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro n hn
    rw [coeff_prod_a0, ite_eq_right hn, smul_zero]

omit [Fintype σ] in
theorem main0 [Finite σ] (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) :
    coeff (m.sumElim 0) (subst (Gfam A B) f) = coeff m (subst A f) := by
  rw [← coeff_theta0, theta0_apply, subst_comp_subst_apply (hasSubst_Gfam A hA B) hasSubst_a0]
  congr 2
  funext i
  rw [← theta0_apply, theta0_Gfam]

end DualAux

universe u v w x

theorem MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (Df i) = ((m i + 1 : ℕ) : R) * MvPowerSeries.coeff (m +
          Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) (k : κ) :
    MvPowerSeries.coeff (m.sumElim (Finsupp.single k 1))
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕
              κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕
                  κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (∑ i : σ, B i k * MvPowerSeries.subst A (Df i)) :=
  DualAux.main1 f Df hDf A hA B m k

end


noncomputable section

namespace RescaledLogAux

open MvPowerSeries

section Cong

variable {S : Type*} [CommRing S] {σ : Type*}

def Cong (n : ℕ) (f g : MvPowerSeries σ S) : Prop := ∀ m : σ →₀ ℕ,
    m.degree ≤ n → coeff m f = coeff m g

namespace Cong

variable {n : ℕ} {f g h : MvPowerSeries σ S}

theorem refl (f : MvPowerSeries σ S) : Cong n f f := fun _ _ => rfl
theorem symm (hfg : Cong n f g) : Cong n g f := fun m hm => (hfg m hm).symm
theorem trans (hfg : Cong n f g) (hgh : Cong n g h) : Cong n f h := fun m hm =>
    (hfg m hm).trans (hgh m hm)
theorem of_eq (e : f = g) : Cong n f g := fun _ _ => by rw [e]
theorem mono {n' : ℕ} (h' : n' ≤
    n) (hfg : Cong n f g) : Cong n' f g := fun m hm => hfg m (hm.trans h')

theorem add {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f +
    f') (g + g') :=
  fun m hm => by rw [map_add, map_add, h₁ m hm, h₂ m hm]
theorem neg (h₁ : Cong n f g) : Cong n (-f) (-g) := fun m hm => by rw [map_neg, map_neg, h₁ m hm]
theorem sub {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f -
    f') (g - g') :=
  fun m hm => by rw [map_sub, map_sub, h₁ m hm, h₂ m hm]
theorem smul (c : S) (h₁ : Cong n f g) : Cong n (c • f) (c • g) :=
  fun m hm => by rw [map_smul, map_smul, h₁ m hm]

theorem sum {ι : Type*} (s : Finset ι) {F G : ι → MvPowerSeries σ S} (h : ∀ i ∈ s,
    Cong n (F i) (G i)) :
    Cong n (∑ i ∈ s, F i) (∑ i ∈ s, G i) := fun m hm => by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi m hm

theorem mul {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f *
    f') (g * g') := by
  classical
  intro m hm
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h1 : x.1.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  have h2 : x.2.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  rw [h₁ _ h1, h₂ _ h2]

theorem prod {ι : Type*} (s : Finset ι) {F G : ι → MvPowerSeries σ S} (h : ∀ i ∈ s,
    Cong n (F i) (G i)) :
    Cong n (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pow (h₁ : Cong n f g) (k : ℕ) : Cong n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero]; exact refl _
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h₁

theorem finsuppProd {ι : Type*} (d : ι →₀ ℕ) {F G : ι → MvPowerSeries σ S} (h : ∀ i,
    Cong n (F i) (G i)) :
    Cong n (d.prod fun i e => F i ^ e) (d.prod fun i e => G i ^ e) :=
  prod _ fun i _ => (h i).pow _

theorem iff_le_order : Cong n f g ↔ ((n + 1 : ℕ) : ℕ∞) ≤ (f - g).order := by
  constructor
  · intro h
    exact nat_le_order fun m hm => by rw [map_sub, h m (by omega), sub_self]
  · intro h m hm
    have := coeff_of_lt_order (d := m) (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) h)
    rwa [map_sub, sub_eq_zero] at this

theorem zero_iff_le_order : Cong n f 0 ↔ ((n + 1 : ℕ) : ℕ∞) ≤ f.order := by
  rw [iff_le_order, sub_zero]

theorem substLeft {τ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (ha0 : ∀ i,
    constantCoeff (a i) = 0)
    (hfg : Cong n f g) : Cong n (subst a f) (subst a g) := by
  rw [iff_le_order] at hfg ⊢
  rw [← subst_sub ha]
  refine hfg.trans ((le_mul_of_one_le_left (by simp) ?_).trans (le_order_subst ha _))
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, ha0]

theorem substRight {τ : Type*} {a b : τ → MvPowerSeries σ S} (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, Cong n (a i) (b i)) (F : MvPowerSeries τ S) : Cong n (subst a F) (subst b F) := by
  intro m hm
  rw [coeff_subst ha, coeff_subst hb]
  exact finsum_congr fun d => by rw [(finsuppProd d hab) m hm]

end Cong

theorem card_le_order_prod {ι : Type*} (s : Finset ι) (u : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) : (s.card : ℕ∞) ≤ (∏ i ∈ s, u i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one,
        add_comm]
    refine le_trans (add_le_add ?_ (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))) le_order_mul
    refine nat_le_order fun d hd => ?_
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hu a (Finset.mem_insert_self a s)]

theorem Cong.prod_of_cong_one {ι : Type*} (s : Finset ι) (u v : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) (hv : ∀ i ∈ s, constantCoeff (v i) = 0)
    (h : ∀ i ∈ s, Cong 1 (u i) (v i)) : Cong s.card (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Cong.refl _
  | insert a s ha ih =>
    have hu' := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hv' := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have ih' := ih hu' hv' fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Cong.iff_le_order,
      show u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        (u a - v a) * ∏ i ∈ s, u i + v a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) by ring]
    refine le_trans ?_ min_order_le_add
    refine le_min ?_ ?_
    · have h1 : ((2 : ℕ) : ℕ∞) ≤ (u a - v a).order := by
        have := (Cong.iff_le_order).1 (h a (Finset.mem_insert_self a s)); exact_mod_cast this
      have h2 := card_le_order_prod s u hu'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (2 : ℕ) + (s.card : ℕ∞) := by push_cast; ring
        _ ≤ (u a - v a).order + (∏ i ∈ s, u i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul
    · have h1 : ((1 : ℕ) : ℕ∞) ≤ (v a).order := nat_le_order fun d hd => by
        have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
        rw [this, coeff_zero_eq_constantCoeff_apply, hv a (Finset.mem_insert_self a s)]
      have h2 : ((s.card + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ s, u i - ∏ i ∈ s,
          v i).order := (Cong.iff_le_order).1 ih'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (1 : ℕ) + ((s.card + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (v a).order + (∏ i ∈ s, u i - ∏ i ∈ s, v i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul

theorem finsuppProd_eq_prod_sigma {ι : Type*} (d : ι →₀ ℕ) (F : ι → MvPowerSeries σ S) :
    (d.prod fun i e => F i ^ e) = ∏ x ∈ d.support.sigma (fun i => Finset.range (d i)), F x.1 := by
  rw [Finsupp.prod, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finset.prod_const, Finset.card_range]

theorem card_sigma_range {ι : Type*} (d : ι →₀ ℕ) : (d.support.sigma fun i =>
    Finset.range (d i)).card = d.degree := by
  rw [Finset.card_sigma, Finsupp.degree_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.card_range _

theorem Cong.aeval_of_isHomogeneous {τ : Type*} {N : ℕ} (P : MvPolynomial τ S) (hP :
    P.IsHomogeneous N)
    (a b : τ → MvPowerSeries σ S) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i,
        constantCoeff (b i) = 0)
    (hab : ∀ i, Cong 1 (a i) (b i)) :
    Cong N (MvPolynomial.aeval a P : MvPowerSeries σ S) (MvPolynomial.aeval b P) := by
  classical
  have key : ∀ d ∈ P.support, Cong N (d.prod fun i e => a i ^ e) (d.prod fun i e => b i ^ e) := by
    intro d hd
    have hdeg : d.degree = N := by
      have := hP (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.degree_eq_weight_one]
      simpa [Pi.one_def] using this
    rw [finsuppProd_eq_prod_sigma, finsuppProd_eq_prod_sigma, ← hdeg, ← card_sigma_range d]
    exact Cong.prod_of_cong_one _ _ _ (fun x _ => ha x.1) (fun x _ => hb x.1) (fun x _ => hab x.1)
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  refine Cong.sum _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  exact (Cong.refl _).mul (key d hd)

end Cong

section Pieces

variable {S : Type*} [CommRing S] {σ : Type*}

section Fin
variable [Fintype σ]

open Classical in
noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f =>
      Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

noncomputable def homogPart (N : ℕ) (g : MvPowerSeries σ S) : MvPolynomial σ S :=
  ∑ m ∈ (lowDeg σ N).filter (fun m => m.degree = N), MvPolynomial.monomial m (coeff m g)

theorem coeff_homogPart (N : ℕ) (g : MvPowerSeries σ S) (m : σ →₀ ℕ) :
    (homogPart N g).coeff m = if m.degree = N then coeff m g else 0 := by
  classical
  rw [homogPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_lowDeg]
  by_cases h : m.degree = N
  · rw [ite_eq_left ⟨h.le, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]

theorem isHomogeneous_homogPart (N : ℕ) (g : MvPowerSeries σ S) : (homogPart N
    g).IsHomogeneous N := by
  classical
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  exact MvPolynomial.isHomogeneous_monomial _ (Finset.mem_filter.1 hm).2

theorem Cong.homogPart {N : ℕ} {g : MvPowerSeries σ S} (hg : Cong N g 0) :
    Cong (N + 1) g (homogPart (N + 1) g : MvPolynomial σ S) := by
  intro m hm
  rw [MvPolynomial.coeff_coe, coeff_homogPart]
  split_ifs with h
  · rfl
  · rw [hg m (by omega), map_zero]

omit [Fintype σ] in
theorem eq_of_cong_of_isHomogeneous {N : ℕ} {P Q : MvPolynomial σ S} (hP : P.IsHomogeneous N) (hQ :
    Q.IsHomogeneous N)
    (h : Cong N (P : MvPowerSeries σ S) Q) : P = Q := by
  ext m
  by_cases hm : m.degree ≤ N
  · have := h m hm
    rwa [MvPolynomial.coeff_coe, MvPolynomial.coeff_coe] at this
  · rw [hP.coeff_eq_zero (by omega), hQ.coeff_eq_zero (by omega)]

end Fin

theorem exists_eq_single_of_degree_eq_one {m : σ →₀ ℕ} (hm : m.degree = 1) : ∃ u,
    m = Finsupp.single u 1 := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.2 hm0
  have hu1 : m u = 1 := by
    have h1 := Finsupp.le_degree u m
    have h2 := Finsupp.mem_support_iff.1 hu
    omega
  refine ⟨u, ?_⟩
  have hle : Finsupp.single u 1 ≤ m := Finsupp.single_le_iff.2 hu1.ge
  have hrest : m - Finsupp.single u 1 = 0 := by
    apply (Finsupp.degree_eq_zero_iff _).1
    have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single, hm] at this
    omega
  have := tsub_add_cancel_of_le hle
  rw [hrest, zero_add] at this
  exact this.symm

theorem Cong.one_iff {f g : MvPowerSeries σ S} :
    Cong 1 f g ↔ constantCoeff f = constantCoeff g ∧ ∀ u,
        coeff (Finsupp.single u 1) f = coeff (Finsupp.single u 1) g := by
  constructor
  · intro h
    exact ⟨by rw [← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply]; exact h 0 (by simp),
      fun u => h _ (by rw [Finsupp.degree_single])⟩
  · rintro ⟨h0, h1⟩ m hm
    rcases Nat.lt_or_ge m.degree 1 with hlt | hge
    · have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    · obtain ⟨u, rfl⟩ := exists_eq_single_of_degree_eq_one (m := m) (by omega)
      exact h1 u

theorem coeff_mapDomain_subst_X_comp {τ : Type*} {e : σ →
    τ} (he : Function.Injective e) (g : MvPowerSeries σ S)
    (d : σ →₀ ℕ) : coeff (d.mapDomain e) (subst (fun s =>
        (X (e s) : MvPowerSeries τ S)) g) = coeff d g := by
  classical
  have ha : HasSubst (fun s => (X (e s) : MvPowerSeries τ S)) := by
    refine ⟨fun s => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d' => ?_⟩
    apply Set.Subsingleton.finite
    intro s₁ h₁ s₂ h₂
    simp only [Set.mem_ofPred_eq, coeff_X] at h₁ h₂
    split_ifs at h₁ h₂ with e₁ e₂
    · rw [e₁] at e₂; exact he (Finsupp.single_left_injective one_ne_zero e₂)
    all_goals simp_all
  have hmono : ∀ d' : σ →₀ ℕ,
      (d'.prod fun s k => (X (e s) : MvPowerSeries τ S) ^ k) = monomial (d'.mapDomain e) 1 := by
    intro d'
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_mapDomain_index_inj he]
  rw [coeff_subst ha, finsum_eq_single _ d]
  · rw [hmono, coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro d' hd'
    rw [hmono, coeff_monomial, ite_eq_right (fun h => hd' (Finsupp.mapDomain_injective he h).symm),
        smul_zero]

end Pieces

section Lazard

variable {K : Type*} [CommRing K] {d : ℕ} (F : MvFormalGroup d K)

noncomputable def inlX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j => X (Sum.inl j)
noncomputable def inrX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j => X (Sum.inr j)

omit F in
theorem constantCoeff_inlX (j : Fin d) : constantCoeff (inlX (K := K) j) = 0 := constantCoeff_X _
omit F in
theorem constantCoeff_inrX (j : Fin d) : constantCoeff (inrX (K := K) j) = 0 := constantCoeff_X _

noncomputable def Edef (φ : Fin d → MvPowerSeries (Fin d) K) (i : Fin d) : MvPowerSeries (Fin d ⊕
    Fin d) K :=
  subst F.toPowerSeries (φ i) - subst inlX (φ i) - subst inrX (φ i)

theorem cong_one_law (i : Fin d) : Cong 1 (F.toPowerSeries i) (inlX i + inrX i) := by
  classical
  rw [Cong.one_iff]
  refine ⟨by rw [F.constantCoeff_eq_zero, map_add, constantCoeff_inlX, constantCoeff_inrX,
      add_zero], ?_⟩
  rintro (j | j)
  · rw [F.coeff_single_inl, map_add, inlX, inrX, coeff_X, coeff_X]
    by_cases h : i = j
    · subst h; simp [Finsupp.single_eq_single_iff]
    · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]
  · rw [F.coeff_single_inr, map_add, inlX, inrX, coeff_X, coeff_X]
    by_cases h : i = j
    · subst h; simp [Finsupp.single_eq_single_iff]
    · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]

theorem subst_Edef {τ : Type*} (φ : Fin d → MvPowerSeries (Fin d) K) (_hφ : ∀ i,
    constantCoeff (φ i) = 0)
    {a b : Fin d → MvPowerSeries τ K} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j,
        constantCoeff (b j) = 0)
    (i : Fin d) :
    subst (Sum.elim a b) (Edef F φ i) =
      subst (fun j =>
          subst (Sum.elim a b) (F.toPowerSeries j)) (φ i) - subst a (φ i) - subst b (φ i) := by
  have hab := MvFormalGroup.hasSubst_elim ha hb
  rw [Edef, subst_sub hab, subst_sub hab, subst_comp_subst_apply F.hasSubst_toPowerSeries hab,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero constantCoeff_inlX) hab,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero constantCoeff_inrX) hab]
  congr 2
  · congr 1; funext j; rw [inlX, subst_X hab]; rfl
  · funext j; rw [inrX, subst_X hab]; rfl

structure Stage (n : ℕ) where
  φ : Fin d → MvPowerSeries (Fin d) K
  const : ∀ i, constantCoeff (φ i) = 0
  lin : ∀ i, Cong 1 (φ i) (X i)
  addit : ∀ i, Cong n (Edef F φ i) 0

noncomputable def stageOne : Stage F 1 where
  φ := fun i => X i
  const := fun i => constantCoeff_X i
  lin := fun _ => Cong.refl _
  addit := fun i => by
    have h : Edef F (fun i => X i) i = F.toPowerSeries i - (inlX i + inrX i) := by
      rw [Edef, subst_X F.hasSubst_toPowerSeries,
          subst_X (hasSubst_of_constantCoeff_zero constantCoeff_inlX),
        subst_X (hasSubst_of_constantCoeff_zero constantCoeff_inrX)]
      ring
    rw [h]
    have := (cong_one_law F i).sub (Cong.refl (inlX i + inrX i))
    rwa [sub_self] at this

variable [F.IsComm]

section Step

variable {F} {n : ℕ} (s : Stage F (n + 1))

noncomputable def Γ (i : Fin d) : MvPolynomial (Fin d ⊕ Fin d) K := homogPart (n + 2) (Edef F s.φ i)

omit [F.IsComm] in
theorem cong_E_Γ (i : Fin d) : Cong (n + 2) (Edef F s.φ i) (Γ s i : MvPolynomial (Fin d ⊕
    Fin d) K) :=
  (s.addit i).homogPart

omit [F.IsComm] in
theorem isHomogeneous_Γ (i : Fin d) : (Γ s i).IsHomogeneous (n + 2) := isHomogeneous_homogPart _ _

theorem subst_swap_E (i : Fin d) :
    subst (fun u => (X (Sum.swap u) : MvPowerSeries (Fin d ⊕
        Fin d) K)) (Edef F s.φ i) = Edef F s.φ i := by
  have hsw : (fun u => (X (Sum.swap u) : MvPowerSeries (Fin d ⊕
      Fin d) K)) = Sum.elim inrX inlX := by
    funext u; rcases u with j | j <;> rfl
  rw [hsw, subst_Edef F s.φ s.const constantCoeff_inrX constantCoeff_inlX, Edef]
  have hcomm : (fun j => subst (Sum.elim inrX inlX) (F.toPowerSeries j)) = F.toPowerSeries := by
    funext j; exact MvFormalGroup.IsComm.comm (F := F) j
  rw [hcomm]
  ring

theorem rename_swap_Γ (i : Fin d) : MvPolynomial.rename Sum.swap (Γ s i) = Γ s i := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain Sum.swap (Finsupp.mapDomain Sum.swap m) := by
    rw [← Finsupp.mapDomain_comp]; simp
  conv_lhs => rw [hm, MvPolynomial.coeff_rename_mapDomain _ Sum.swap_leftInverse.injective]
  rw [Γ, coeff_homogPart, coeff_homogPart, Finsupp.degree_mapDomain]
  split_ifs with h
  · conv_lhs => rw [← subst_swap_E s i]
    rw [coeff_mapDomain_subst_X_comp Sum.swap_leftInverse.injective]
  · rfl

local notation "T3" => MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) K

noncomputable def bX : Fin d → T3 := fun j => X (Sum.inl j)
noncomputable def bY : Fin d → T3 := fun j => X (Sum.inr (Sum.inl j))
noncomputable def bZ : Fin d → T3 := fun j => X (Sum.inr (Sum.inr j))

noncomputable def FF (a b : Fin d →
    T3) : Fin d → T3 := fun j => subst (Sum.elim a b) (F.toPowerSeries j)

omit [F.IsComm] in
theorem FF_def (a b : Fin d → T3) : FF (F :=
    F) a b = fun j => subst (Sum.elim a b) (F.toPowerSeries j) := rfl

omit [F.IsComm] in
theorem constantCoeff_FF {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j,
    constantCoeff (b j) = 0)
    (j : Fin d) : constantCoeff (FF (F := F) a b j) = 0 :=
  constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim ha hb)
    (by rintro (l | l); exacts [ha l, hb l])
    (F.constantCoeff_eq_zero j)

theorem cbX (j : Fin d) : constantCoeff (bX (K := K) (d := d) j) = 0 := constantCoeff_X _
theorem cbY (j : Fin d) : constantCoeff (bY (K := K) (d := d) j) = 0 := constantCoeff_X _
theorem cbZ (j : Fin d) : constantCoeff (bZ (K := K) (d := d) j) = 0 := constantCoeff_X _

omit [F.IsComm] in
theorem cong_one_FF {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j,
    constantCoeff (b j) = 0)
    (j : Fin d) : Cong 1 (FF (F := F) a b j) (a j + b j) := by
  have hab := MvFormalGroup.hasSubst_elim ha hb
  have := (cong_one_law F j).substLeft hab (by rintro (l | l); exacts [ha l, hb l])
  simp only [subst_add hab, inlX, inrX, subst_X hab, Sum.elim_inl, Sum.elim_inr] at this
  exact this

omit [F.IsComm] in
theorem cocycle_E (i : Fin d) :
    subst (Sum.elim bX bY) (Edef F s.φ i) + subst (Sum.elim (FF (F := F) bX bY) bZ) (Edef F s.φ i) =
      subst (Sum.elim bY bZ) (Edef F s.φ i) + subst (Sum.elim bX (FF (F :=
          F) bY bZ)) (Edef F s.φ i) := by
  have hFXY := constantCoeff_FF (F := F) cbX cbY
  have hFYZ := constantCoeff_FF (F := F) cbY cbZ
  rw [subst_Edef F s.φ s.const cbX cbY, subst_Edef F s.φ s.const hFXY cbZ,
      subst_Edef F s.φ s.const cbY cbZ,
    subst_Edef F s.φ s.const cbX hFYZ]
  have hassoc : (fun j => subst (Sum.elim (FF (F := F) bX bY) bZ) (F.toPowerSeries j)) =
      fun j => subst (Sum.elim bX (FF (F := F) bY bZ)) (F.toPowerSeries j) := by
    funext j
    exact MvFormalGroup.subst_elim_assoc (F := F) cbX cbY cbZ j
  rw [hassoc]
  simp only [FF_def]
  ring

omit [F.IsComm] in
theorem coe_aeval {υ τ : Type*} (q : υ → MvPolynomial τ K) (P : MvPolynomial υ K) :
    ((MvPolynomial.aeval q P : MvPolynomial τ K) : MvPowerSeries τ K) =
      MvPolynomial.aeval (fun u => (q u : MvPowerSeries τ K)) P := by
  have h := MvPolynomial.comp_aeval_apply (f := q) (MvPolynomial.coeToMvPowerSeries.algHom K) P
  simpa only [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id,
    RingHom.id_apply] using h

omit [F.IsComm] in
theorem cocycle_Γ (i : Fin d) :
    MvPolynomial.aeval (Sum.elim (fun j =>
        (MvPolynomial.X (Sum.inr (Sum.inl j)) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
        (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      - MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) +
          MvPolynomial.X (Sum.inr (Sum.inl j)) :
          MvPolynomial (Fin d ⊕ (Fin d ⊕
              Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      + MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕
          (Fin d ⊕ Fin d)) K))
          (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)) +
              MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      - MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕
          (Fin d ⊕ Fin d)) K))
          (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)))) (Γ s i) = 0 := by
  set pYZ := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inr (Sum.inl j)) :
      MvPolynomial (Fin d ⊕ (Fin d ⊕
          Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpYZ
  set pXYZ := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) +
      MvPolynomial.X (Sum.inr (Sum.inl j)) :
      MvPolynomial (Fin d ⊕ (Fin d ⊕
          Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpXYZ
  set pXYZ' := MvPolynomial.aeval (Sum.elim (fun j =>
      (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)) +
          MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpXYZ'
  set pXY := MvPolynomial.aeval (Sum.elim (fun j =>
      (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)))) (Γ s i) with hpXY
  have hlin : ∀ (q : Fin d ⊕ Fin d → MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K), (∀ u,
      (q u).IsHomogeneous 1) →
      (MvPolynomial.aeval q (Γ s i)).IsHomogeneous (n + 2) := fun q hq => by
    simpa using (isHomogeneous_Γ s i).aeval q hq
  have hX1 : ∀ u : Fin d ⊕ (Fin d ⊕ Fin d),
      (MvPolynomial.X u : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K).IsHomogeneous 1 :=
    fun u => MvPolynomial.isHomogeneous_X K u
  have h1 : (pYZ + pXYZ').IsHomogeneous (n + 2) :=
    (hlin _ (by rintro (j | j); exacts [hX1 _, hX1 _])).add
      (hlin _ (by rintro (j | j); exacts [hX1 _, (hX1 _).add (hX1 _)]))
  have h2 : (pXY + pXYZ).IsHomogeneous (n + 2) :=
    (hlin _ (by rintro (j | j); exacts [hX1 _, hX1 _])).add
      (hlin _ (by rintro (j | j); exacts [(hX1 _).add (hX1 _), hX1 _]))
  suffices hc : Cong (n + 2) ((pXY + pXYZ : MvPolynomial _ K) : T3) ((pYZ +
      pXYZ' : MvPolynomial _ K) : T3) by
    have := eq_of_cong_of_isHomogeneous h2 h1 hc
    linear_combination -this
  have hΓsub : ∀ {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j,
      constantCoeff (b j) = 0),
      Cong (n +
          2) (subst (Sum.elim a b) (Edef F s.φ i)) (MvPolynomial.aeval (Sum.elim a b) (Γ s i)) := by
    intro a b ha hb
    have hab := MvFormalGroup.hasSubst_elim ha hb
    have := (cong_E_Γ s i).substLeft hab (by rintro (l | l); exacts [ha l, hb l])
    rwa [subst_coe] at this
  have hFXY := constantCoeff_FF (F := F) cbX cbY
  have hFYZ := constantCoeff_FF (F := F) cbY cbZ
  have e1 : Cong (n + 2) (subst (Sum.elim bX bY) (Edef F s.φ i)) (pXY : T3) := by
    refine (hΓsub cbX cbY).trans (Cong.of_eq ?_)
    rw [hpXY, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY])
  have e2 : Cong (n + 2) (subst (Sum.elim (FF (F := F) bX bY) bZ) (Edef F s.φ i)) (pXYZ : T3) := by
    refine (hΓsub hFXY cbZ).trans ?_
    refine (Cong.aeval_of_isHomogeneous (Γ s i) (isHomogeneous_Γ s i) _ (Sum.elim (fun j => bX j +
        bY j) bZ)
      (by rintro (l | l); exacts [hFXY l, cbZ l]) (by rintro (l | l) <;> simp [bX, bY, bZ])
      (by rintro (l | l); exacts [cong_one_FF cbX cbY l, Cong.refl _])).trans (Cong.of_eq ?_)
    rw [hpXYZ, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have e3 : Cong (n + 2) (subst (Sum.elim bY bZ) (Edef F s.φ i)) (pYZ : T3) := by
    refine (hΓsub cbY cbZ).trans (Cong.of_eq ?_)
    rw [hpYZ, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bY, bZ])
  have e4 : Cong (n + 2) (subst (Sum.elim bX (FF (F := F) bY bZ)) (Edef F s.φ i)) (pXYZ' : T3) := by
    refine (hΓsub cbX hFYZ).trans ?_
    refine (Cong.aeval_of_isHomogeneous (Γ s i) (isHomogeneous_Γ s i) _ (Sum.elim bX (fun j =>
        bY j + bZ j))
      (by rintro (l | l); exacts [cbX l, hFYZ l]) (by rintro (l | l) <;> simp [bX, bY, bZ])
      (by rintro (l | l); exacts [Cong.refl _, cong_one_FF cbY cbZ l])).trans (Cong.of_eq ?_)
    rw [hpXYZ', coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have := (e1.add e2).symm.trans ((Cong.of_eq (cocycle_E s i)).trans (e3.add e4))
  simpa only [MvPolynomial.coe_add] using this

end Step

end Lazard

section Construct

variable {K : Type*} [CommRing K] {d : ℕ} {F : MvFormalGroup d K} [F.IsComm]
  (hK : ∀ n : ℕ, IsUnit ((n + 1 : ℕ) : K))

section
variable {n : ℕ} (s : Stage F (n + 1))

include hK in
theorem exists_corr (i : Fin d) : ∃ h : MvPolynomial (Fin d) K, h.IsHomogeneous (n + 2) ∧
    Γ s i = MvPolynomial.aeval (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Fin d ⊕
          Fin d) K)) h - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h :=
  MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric (n + 2) (hK (n + 1))
    (Γ s i) (isHomogeneous_Γ s i) (rename_swap_Γ s i) (cocycle_Γ s i)

noncomputable def corr (i : Fin d) : MvPolynomial (Fin d) K := Classical.choose (exists_corr hK s i)

theorem isHomogeneous_corr (i : Fin d) : (corr hK s i).IsHomogeneous (n +
    2) := (Classical.choose_spec (exists_corr hK s i)).1

theorem Γ_eq_delta_corr (i : Fin d) : Γ s i = MvPolynomial.aeval (fun j =>
    (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Fin d ⊕ Fin d) K)) (corr hK s i) - MvPolynomial.rename Sum.inl (corr hK s i)
      - MvPolynomial.rename Sum.inr (corr hK s i) := (Classical.choose_spec (exists_corr hK s i)).2

theorem cong_corr_zero (i : Fin d) : Cong (n +
    1) (corr hK s i : MvPowerSeries (Fin d) K) 0 := fun m hm => by
  rw [MvPolynomial.coeff_coe, map_zero, (isHomogeneous_corr hK s i).coeff_eq_zero (by omega)]

theorem cong_E_corr (i : Fin d) :
    Cong (n + 2) (Edef F (fun i =>
        (corr hK s i : MvPowerSeries (Fin d) K)) i) (Γ s i : MvPolynomial (Fin d ⊕ Fin d) K) := by
  have hplus : subst F.toPowerSeries (corr hK s i : MvPowerSeries (Fin d) K) =
      MvPolynomial.aeval F.toPowerSeries (corr hK s i) := subst_coe _
  have h1 : Cong (n + 2) (subst F.toPowerSeries (corr hK s i : MvPowerSeries (Fin d) K))
      ((MvPolynomial.aeval (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
        MvPolynomial (Fin d ⊕
            Fin d) K)) (corr hK s i) : MvPolynomial (Fin d ⊕ Fin d) K) : MvPowerSeries (Fin d ⊕
                Fin d) K) := by
    rw [hplus, coe_aeval]
    refine (Cong.aeval_of_isHomogeneous _ (isHomogeneous_corr hK s i) _ _ F.constantCoeff_eq_zero
      (fun j => by simp) (fun j => ?_))
    have := cong_one_law F j
    simpa [inlX, inrX] using this
  have h2 : subst inlX (corr hK s i : MvPowerSeries (Fin d) K) =
      ((MvPolynomial.rename (Sum.inl : Fin d → Fin d ⊕ Fin d) (corr hK s i) : MvPolynomial (Fin d ⊕
          Fin d) K) :
        MvPowerSeries (Fin d ⊕ Fin d) K) := by
    rw [subst_coe, show MvPolynomial.rename (Sum.inl : Fin d → Fin d ⊕ Fin d) (corr hK s i) =
      MvPolynomial.aeval (fun j => MvPolynomial.X (Sum.inl j)) (corr hK s i) from by
        rw [MvPolynomial.rename_eq_aeval]; rfl, coe_aeval]
    exact congrArg (fun q : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K =>
        MvPolynomial.aeval q (corr hK s i))
      (funext fun u => by simp [inlX])
  have h3 : subst inrX (corr hK s i : MvPowerSeries (Fin d) K) =
      ((MvPolynomial.rename (Sum.inr : Fin d → Fin d ⊕ Fin d) (corr hK s i) : MvPolynomial (Fin d ⊕
          Fin d) K) :
        MvPowerSeries (Fin d ⊕ Fin d) K) := by
    rw [subst_coe, show MvPolynomial.rename (Sum.inr : Fin d → Fin d ⊕ Fin d) (corr hK s i) =
      MvPolynomial.aeval (fun j => MvPolynomial.X (Sum.inr j)) (corr hK s i) from by
        rw [MvPolynomial.rename_eq_aeval]; rfl, coe_aeval]
    exact congrArg (fun q : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K =>
        MvPolynomial.aeval q (corr hK s i))
      (funext fun u => by simp [inrX])
  have coe_sub' : ∀ P Q : MvPolynomial (Fin d ⊕ Fin d) K,
      ((P - Q : MvPolynomial (Fin d ⊕ Fin d) K) : MvPowerSeries (Fin d ⊕
          Fin d) K) = (P : MvPowerSeries (Fin d ⊕ Fin d) K) - Q :=
    fun P Q => by simpa using map_sub (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin d ⊕
        Fin d) (R := K)) P Q
  rw [Edef, h2, h3, Γ_eq_delta_corr hK s i, coe_sub', coe_sub']
  exact (h1.sub (Cong.refl _)).sub (Cong.refl _)

omit [F.IsComm] in
theorem Edef_sub (φ ψ : Fin d → MvPowerSeries (Fin d) K) (i : Fin d) :
    Edef F (fun i => φ i - ψ i) i = Edef F φ i - Edef F ψ i := by
  simp only [Edef, subst_sub F.hasSubst_toPowerSeries,
      subst_sub (hasSubst_of_constantCoeff_zero constantCoeff_inlX),
    subst_sub (hasSubst_of_constantCoeff_zero constantCoeff_inrX)]
  ring

noncomputable def step : Stage F (n + 2) where
  φ := fun i => s.φ i - (corr hK s i : MvPowerSeries (Fin d) K)
  const := fun i => by
    rw [map_sub, s.const, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      (isHomogeneous_corr hK s i).coeff_eq_zero (by simp), sub_zero]
  lin := fun i => by
    have := (s.lin i).sub (cong_corr_zero hK s i |>.mono (by omega))
    rwa [sub_zero] at this
  addit := fun i => by
    rw [Edef_sub]
    have := (cong_E_Γ s i).sub (cong_E_corr hK s i)
    rwa [sub_self] at this

theorem step_cong (i : Fin d) : Cong (n + 1) ((step hK s).φ i) (s.φ i) := by
  have := (Cong.refl (s.φ i)).sub (cong_corr_zero hK s i)
  rwa [sub_zero] at this

end

variable (F) in
noncomputable def stages : (k : ℕ) → Stage F (k + 1)
  | 0 => stageOne F
  | k + 1 => step hK (stages k)

theorem stages_cong {k l : ℕ} (hkl : k ≤ l) (i : Fin d) : Cong (k +
    1) ((stages F hK l).φ i) ((stages F hK k).φ i) := by
  induction l with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact Cong.refl _
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with hlt | hge
    · exact ((step_cong hK (stages F hK l) i).mono (by omega)).trans (ih (by omega))
    · obtain rfl : k = l + 1 := by omega
      exact Cong.refl _

variable (F) in
noncomputable def logK (i : Fin d) : MvPowerSeries (Fin d) K := fun m =>
    coeff m ((stages F hK m.degree).φ i)

theorem coeff_logK (i : Fin d) (m : Fin d →₀ ℕ) : coeff m (logK F hK i) =
    coeff m ((stages F hK m.degree).φ i) := rfl

theorem cong_logK (N : ℕ) (i : Fin d) : Cong (N + 1) (logK F hK i) ((stages F hK N).φ i) := by
  intro m hm
  rw [coeff_logK]
  rcases Nat.lt_or_ge m.degree (N + 1) with hlt | hge
  · exact ((stages_cong hK (show m.degree ≤ N by omega) i) m (Nat.le_succ _)).symm
  · have hdeg : m.degree = N + 1 := by omega
    rw [hdeg]
    exact (stages_cong hK (Nat.le_succ N) i) m (by omega)

theorem constantCoeff_logK (i : Fin d) : constantCoeff (logK F hK i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logK, coeff_zero_eq_constantCoeff_apply]
  exact (stages F hK _).const i

theorem cong_one_logK (i : Fin d) : Cong 1 (logK F hK i) (X i) :=
  (cong_logK hK 0 i).trans ((stages F hK 0).lin i)

omit [F.IsComm] in
theorem Edef_cong {N : ℕ} {φ ψ : Fin d → MvPowerSeries (Fin d) K} (h : ∀ i,
    Cong N (φ i) (ψ i)) (i : Fin d) :
    Cong N (Edef F φ i) (Edef F ψ i) :=
  (((h i).substLeft F.hasSubst_toPowerSeries F.constantCoeff_eq_zero).sub
    ((h i).substLeft (hasSubst_of_constantCoeff_zero constantCoeff_inlX) constantCoeff_inlX)).sub
    ((h i).substLeft (hasSubst_of_constantCoeff_zero constantCoeff_inrX) constantCoeff_inrX)

theorem Edef_logK (i : Fin d) : Edef F (logK F hK) i = 0 := by
  ext m
  rw [map_zero]
  have h1 := Edef_cong (F := F) (cong_logK (F := F) hK m.degree) i
  have h2 := (stages F hK m.degree).addit i
  rw [h1 m (by omega), h2 m (by omega), map_zero]

end Construct

section Weighted

variable {S : Type*} [CommRing S] {σ : Type*}

def CongW (w : σ → ℕ) (n : ℕ) (f g : MvPowerSeries σ S) : Prop :=
  ∀ m : σ →₀ ℕ, Finsupp.weight w m ≤ n → coeff m f = coeff m g

namespace CongW
variable {w : σ → ℕ} {n : ℕ} {f g : MvPowerSeries σ S}

theorem refl (f : MvPowerSeries σ S) : CongW w n f f := fun _ _ => rfl

theorem mul {f' g' : MvPowerSeries σ S} (h₁ : CongW w n f g) (h₂ : CongW w n f' g') : CongW w n (f
    * f') (g * g') := by
  classical
  intro m hm
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h1 : Finsupp.weight w x.1 ≤ n := by
    have := congrArg (Finsupp.weight w) hx'; rw [map_add] at this; omega
  have h2 : Finsupp.weight w x.2 ≤ n := by
    have := congrArg (Finsupp.weight w) hx'; rw [map_add] at this; omega
  rw [h₁ _ h1, h₂ _ h2]

theorem pow (h₁ : CongW w n f g) (k : ℕ) : CongW w n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero]; exact refl _
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h₁

theorem finsuppProd {ι : Type*} (d : ι →₀ ℕ) {F G : ι → MvPowerSeries σ S} (h : ∀ i,
    CongW w n (F i) (G i)) :
    CongW w n (d.prod fun i e => F i ^ e) (d.prod fun i e => G i ^ e) := by
  classical
  rw [Finsupp.prod, Finsupp.prod]
  induction d.support using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | insert a s ha ih => rw [Finset.prod_insert ha,
                            Finset.prod_insert ha]; exact ((h a).pow _).mul ih

theorem substRight {τ : Type*} {a b : τ → MvPowerSeries σ S} (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i,
        CongW w n (a i) (b i)) (F : MvPowerSeries τ S) : CongW w n (subst a F) (subst b F) := by
  intro m hm
  rw [coeff_subst ha, coeff_subst hb]
  exact finsum_congr fun d => by rw [(finsuppProd d hab) m hm]

end CongW

variable {κ : Type*}

def wY : σ ⊕ κ → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem weight_wY_sumElim (m : σ →₀ ℕ) (c : κ →₀ ℕ) : Finsupp.weight (wY (σ := σ) (κ :=
    κ)) (m.sumElim c) = c.degree := by
  classical
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.weight_apply, Finsupp.weight_apply,
      Finsupp.sum_mapDomain_index_inj
    Sum.inl_injective, Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
  simp [wY, Finsupp.degree_apply, Finsupp.sum]

noncomputable def emb (a : MvPowerSeries σ S) : MvPowerSeries (σ ⊕ κ) S :=
  subst (fun t => (X (Sum.inl t) : MvPowerSeries (σ ⊕ κ) S)) a

theorem hasSubst_X_comp {τ : Type*} {e : σ → τ} (he : Function.Injective e) :
    HasSubst (fun s => (X (e s) : MvPowerSeries τ S)) := by
  classical
  refine ⟨fun s => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d' => ?_⟩
  apply Set.Subsingleton.finite
  intro s₁ h₁ s₂ h₂
  simp only [Set.mem_ofPred_eq, coeff_X] at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  · rw [e₁] at e₂; exact he (Finsupp.single_left_injective one_ne_zero e₂)
  all_goals simp_all

theorem coeff_subst_X_comp_eq_zero {τ : Type*} {e : σ →
    τ} (he : Function.Injective e) (g : MvPowerSeries σ S)
    (n : τ →₀ ℕ) (hn : ∀ d : σ →₀ ℕ, n ≠ Finsupp.mapDomain e d) :
    coeff n (subst (fun s => (X (e s) : MvPowerSeries τ S)) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_X_comp he), finsum_eq_zero_of_forall_eq_zero]
  intro d
  rw [show (d.prod fun s k => (X (e s) : MvPowerSeries τ S) ^ k) = monomial (d.mapDomain e) 1 by
    rw [MvPowerSeries.monomial_one_eq,
        Finsupp.prod_mapDomain_index_inj he], coeff_monomial, ite_eq_right (hn d), smul_zero]

theorem mapDomain_inl_eq_sumElim (m : σ →₀ ℕ) : m.mapDomain Sum.inl = m.sumElim (0 : κ →₀ ℕ) := by
  rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_zero, add_zero]

theorem mapDomain_inr_eq_sumElim (c : κ →₀ ℕ) : c.mapDomain Sum.inr = (0 : σ →₀ ℕ).sumElim c := by
  rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_zero, zero_add]

theorem coeff_sumElim_zero_emb (a : MvPowerSeries σ S) (m : σ →₀ ℕ) : coeff (m.sumElim (0 : κ →₀
    ℕ)) (emb a) = coeff m a := by
  rw [emb, ← mapDomain_inl_eq_sumElim, coeff_mapDomain_subst_X_comp Sum.inl_injective]

theorem coeff_sumElim_emb_eq_zero (a : MvPowerSeries σ S) (m : σ →₀ ℕ) {c : κ →₀ ℕ} (hc : c ≠ 0) :
    coeff (m.sumElim c) (emb a) = 0 := by
  apply coeff_subst_X_comp_eq_zero Sum.inl_injective
  intro d' h
  apply hc
  have := congrArg (fun n => Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn) h
  simpa [mapDomain_inl_eq_sumElim] using this

variable [Fintype κ]

noncomputable def linY (g : MvPowerSeries (σ ⊕ κ) S) : MvPowerSeries (σ ⊕ κ) S :=
  emb (fun m => coeff (m.sumElim 0) g) + ∑ k,
      X (Sum.inr k) * emb (fun m => coeff (m.sumElim (Finsupp.single k 1)) g)

omit [Fintype κ] in
theorem coeff_X_inr_mul (k : κ) (g : MvPowerSeries (σ ⊕ κ) S) (m : σ →₀ ℕ) (c : κ →₀ ℕ) :
    coeff (m.sumElim c) (X (Sum.inr k) * g) = if Finsupp.single k 1 ≤ c then coeff (m.sumElim (c -
        Finsupp.single k 1)) g else 0 := by
  classical
  rw [X_def, ← Finsupp.sumElim_zero_single, coeff_monomial_mul]
  have hiff : (0 : σ →₀ ℕ).sumElim (Finsupp.single k 1) ≤ m.sumElim c ↔ Finsupp.single k 1 ≤ c := by
    simp only [Finsupp.le_def]
    constructor
    · intro h k'; simpa [Finsupp.single_apply] using h (Sum.inr k')
    · rintro h (t | k')
      · simp
      · simpa [Finsupp.single_apply] using h k'
  by_cases h : Finsupp.single k 1 ≤ c
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, one_mul]
    congr 2
    ext u; rcases u with t | k' <;> simp [Finsupp.single_apply]
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]

theorem congW_linY (g : MvPowerSeries (σ ⊕ κ) S) : CongW wY 1 g (linY g) := by
  classical
  intro n hn
  obtain ⟨m, c, rfl⟩ : ∃ (m : σ →₀ ℕ) (c : κ →₀ ℕ), n = m.sumElim c :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain n).symm⟩
  rw [weight_wY_sumElim] at hn
  rw [linY, map_add, map_sum]
  rcases Nat.lt_or_ge c.degree 1 with h0 | h1
  · have hc : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    subst hc
    erw [coeff_sumElim_zero_emb, Finset.sum_eq_zero fun k _ => ?_, add_zero]
    · rfl
    · rw [coeff_X_inr_mul, ite_eq_right]; intro h; have := h k; simp at this
  · obtain ⟨k, rfl⟩ := exists_eq_single_of_degree_eq_one (m := c) (by omega)
    erw [coeff_sumElim_emb_eq_zero _ _ (by simp), zero_add, Finset.sum_eq_single k]
    · erw [coeff_X_inr_mul, ite_eq_left le_rfl, tsub_self, coeff_sumElim_zero_emb]; rfl
    · intro k' _ hk'
      rw [coeff_X_inr_mul, ite_eq_right]
      intro h; have := h k'; simp [hk'] at this
    · intro hk; exact absurd (Finset.mem_univ k) hk

omit [Fintype κ] in
theorem constantCoeff_emb (a : MvPowerSeries σ S) (ha : constantCoeff a =
    0) : constantCoeff (emb (κ := κ) a) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_X_comp Sum.inl_injective) (fun _ => constantCoeff_X _) ha

end Weighted

section Honda

variable {𝓞 : Type*} [CommRing 𝓞] {K : Type*} [CommRing K] (φ : 𝓞 →+*
    K) {d : ℕ} (F𝓞 : MvFormalGroup d 𝓞)

theorem coeff_subst_elim_X_zero {S : Type*} [CommRing S] {σ κ : Type*} (g : MvPowerSeries (σ ⊕
    κ) S) (m : σ →₀ ℕ) :
    coeff m (subst (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ =>
        0)) g) = coeff (m.sumElim 0) g := by
  classical
  have ha : HasSubst (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ : κ => 0)) := by
    refine ⟨?_, fun d => ?_⟩
    · rintro (t | k')
      · simp only [Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
      · simp only [Sum.elim_inr, map_zero]; exact IsNilpotent.zero
    · apply Set.Subsingleton.finite
      rintro (t₁ | k₁) h₁ (t₂ | k₂) h₂ <;>
        simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, coeff_X, map_zero, ne_eq,
            not_true_eq_false] at h₁ h₂
      split_ifs at h₁ h₂ with e₁ e₂
      · rw [e₁] at e₂; rw [Finsupp.single_left_injective one_ne_zero e₂]
      all_goals simp_all
  have key : ∀ n : σ ⊕ κ →₀ ℕ,
      coeff m (n.prod fun u e => (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ =>
          0) u) ^ e) =
      if n = m.sumElim 0 then 1 else 0 := by
    intro n
    set nτ : σ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
    set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
    have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
    have hsplit : (nτ.sumElim nκ = m.sumElim 0 ↔ m = nτ ∧ nκ = 0) := by
      constructor
      · intro h
        exact ⟨Eq.symm (by simpa using congrArg (fun c =>
            Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
          by simpa using congrArg (fun c =>
              Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
    rw [hn, Finsupp.prod_sumElim]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← MvPowerSeries.monomial_one_eq]
    have hY : (nκ.prod fun _ e => ((0 : MvPowerSeries σ S)) ^ e) = if nκ = 0 then 1 else 0 := by
      by_cases h0 : nκ = 0
      · rw [h0, ite_eq_left rfl, Finsupp.prod_zero_index]
      · rw [ite_eq_right h0]
        obtain ⟨k', hk'⟩ := Finsupp.support_nonempty_iff.2 h0
        rw [Finsupp.prod,
            Finset.prod_eq_zero hk' (by rw [zero_pow (Finsupp.mem_support_iff.1 hk')])]
    rw [hY]
    simp only [hsplit]
    clear_value nτ nκ
    clear hY hn hnτ hnκ hsplit
    split_ifs <;> simp_all [coeff_monomial]
  rw [coeff_subst ha, finsum_eq_single _ (m.sumElim 0)]
  · rw [key, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro n hn
    rw [key, ite_eq_right hn, smul_zero]

theorem coeff_sumElim_zero_law {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j : Fin d) (m :
    Fin d →₀ ℕ) :
    coeff (m.sumElim 0) (G.toPowerSeries j) = coeff m (X j : MvPowerSeries (Fin d) S) := by
  rw [← coeff_subst_elim_X_zero, MvFormalGroup.subst_elim_X_zero]

noncomputable def Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin
    d) : MvPowerSeries (Fin d) S :=
  fun m => coeff (m.sumElim (Finsupp.single k 1)) (G.toPowerSeries j)

theorem coeff_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin d) (m : Fin d →₀ ℕ) :
    coeff m (Psi G j k) = coeff (m.sumElim (Finsupp.single k 1)) (G.toPowerSeries j) := rfl

theorem constantCoeff_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin d) :
    constantCoeff (Psi G j k) = if j = k then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Psi, Finsupp.sumElim_zero_single,
      G.coeff_single_inr]

theorem Psi_map (j k : Fin d) : Psi (F𝓞.map φ) j k = MvPowerSeries.map φ (Psi F𝓞 j k) := by
  ext m
  rw [coeff_Psi, coeff_map, coeff_Psi]
  change coeff _ (MvPowerSeries.map φ (F𝓞.toPowerSeries j)) = _
  rw [coeff_map]

theorem isUnit_det_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) :
    IsUnit (Matrix.det (Matrix.of fun j k => Psi G j k)) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (RingHom.mapMatrix (constantCoeff : MvPowerSeries (Fin d) S →+* S)) (Matrix.of fun j k =>
      Psi G j k) = 1 := by
    ext j k
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_Psi, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

variable (f : Fin d → MvPowerSeries (Fin d) K) (hf0 : ∀ i, constantCoeff (f i) = 0) (hf1 : ∀ i,
    Cong 1 (f i) (X i))
  (hfadd : ∀ i, subst (F𝓞.map φ).toPowerSeries (f i) = subst inlX (f i) + subst inrX (f i))

noncomputable def Dlog (i j : Fin d) : MvPowerSeries (Fin d) K :=
  fun m => ((m j + 1 : ℕ) : K) * coeff (m + Finsupp.single j 1) (f i)

include hf1 hfadd in
theorem sum_Dlog_mul_Psi (i k : Fin d) : ∑ j,
    Psi (F𝓞.map φ) j k * Dlog f i j = if i = k then 1 else 0 := by
  classical
  set F := F𝓞.map φ with hF
  set A : Fin d → MvPowerSeries (Fin d) K := fun j m =>
      coeff (m.sumElim (0 : Fin d →₀ ℕ)) (F.toPowerSeries j) with hA
  have hAX : A = fun j => X j := by funext j; ext m; exact coeff_sumElim_zero_law F j m
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by rw [hAX]; exact constantCoeff_X j
  set G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j =>
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) (A j) +
      ∑ k', X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕
          Fin d) K)) (Psi F j k') with hG
  have hGlin : ∀ j, G j = linY (F.toPowerSeries j) := fun j => rfl
  have hG0 : ∀ j, constantCoeff (G j) = 0 := fun j => by
    rw [hG]; dsimp only
    rw [map_add, map_sum]
    rw [show subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) (A j) =
        emb (A j) from rfl,
      constantCoeff_emb _ (hA0 j), zero_add]
    exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]
  have hGs : HasSubst G := hasSubst_of_constantCoeff_zero hG0
  have taylor := fun m => MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (f i) (Dlog f i)
    (fun j m => rfl) A hA0 (fun j k' => Psi F j k') m k
  have hFG : ∀ m : Fin d →₀ ℕ,
      coeff (m.sumElim (Finsupp.single k 1)) (subst F.toPowerSeries (f i)) =
      coeff (m.sumElim (Finsupp.single k 1)) (subst G (f i)) := fun m =>
    (CongW.substRight F.hasSubst_toPowerSeries hGs (fun j =>
        by rw [hGlin]; exact congW_linY _) (f i)) _
      (by rw [weight_wY_sumElim, Finsupp.degree_single])
  have hLHS : ∀ m : Fin d →₀ ℕ,
      coeff (m.sumElim (Finsupp.single k 1)) (subst F.toPowerSeries (f i)) =
      if m = 0 then (if i = k then 1 else 0) else 0 := by
    intro m
    rw [hfadd, map_add, show subst inlX (f i) = emb (f i) from rfl,
        coeff_sumElim_emb_eq_zero _ _ (by simp), zero_add]
    unfold inrX
    by_cases hm : m = 0
    · subst hm
      rw [ite_eq_left rfl, ← mapDomain_inr_eq_sumElim,
          coeff_mapDomain_subst_X_comp Sum.inr_injective, (hf1 i) _
        (by rw [Finsupp.degree_single]), coeff_X]
      by_cases hik : i = k
      · subst hik; simp
      · rw [ite_eq_right hik,
            ite_eq_right (fun h => hik (Finsupp.single_left_injective one_ne_zero h).symm)]
    · rw [ite_eq_right hm]
      apply coeff_subst_X_comp_eq_zero Sum.inr_injective
      intro d' h
      apply hm
      have := congrArg (fun n => Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn) h
      simpa [mapDomain_inr_eq_sumElim] using this
  ext m
  have := (hLHS m).symm.trans ((hFG m).trans (taylor m))
  rw [hAX] at this
  simp only [show (fun j => (X j : MvPowerSeries (Fin d) K)) = X from rfl,
    show ∀ g : MvPowerSeries (Fin d) K, subst (X : Fin d → MvPowerSeries (Fin d) K) g = g from
      fun g => congrFun subst_self g] at this
  rw [← this]
  split_ifs <;> simp [coeff_one, *]

include hf1 hfadd in
theorem exists_coeff_Dlog (i j : Fin d) (m : Fin d →₀ ℕ) : ∃ c : 𝓞, φ c = coeff m (Dlog f i j) := by
  classical
  set ΨO : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) 𝓞) := Matrix.of fun j k =>
      Psi F𝓞 j k with hΨO
  set ΨK : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) K) := Matrix.of fun j k =>
      Psi (F𝓞.map φ) j k with hΨK
  set D : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) K) := Matrix.of fun i j =>
      Dlog f i j with hD
  have hmap : ΨK = (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO := by
    ext j k; simp [hΨK, hΨO, RingHom.mapMatrix_apply, Matrix.map_apply, Psi_map]
  have hDΨ : D * ΨK = 1 := by
    refine Matrix.ext fun i k => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hD, hΨK, Matrix.of_apply]
    rw [← sum_Dlog_mul_Psi φ F𝓞 f hf1 hfadd i k]
    exact Finset.sum_congr rfl fun j _ => mul_comm (Dlog f i j) (Psi (F𝓞.map φ) j k)
  have hunit := isUnit_det_Psi F𝓞
  have hD' : D = (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO⁻¹ := by
    calc D = D * (RingHom.mapMatrix (MvPowerSeries.map φ)) (ΨO * ΨO⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hunit, map_one, mul_one]
      _ = D * ΨK * (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO⁻¹ := by rw [map_mul, ← hmap,
          mul_assoc]
      _ = _ := by rw [hDΨ, one_mul]
  refine ⟨coeff m ((ΨO⁻¹) i j), ?_⟩
  have := congrFun (congrFun hD' i) j
  simp only [hD, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at this
  rw [this, coeff_map]

end Honda

section UnitsSec

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

theorem isUnit_natCast_of_not_dvd [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : 𝓞)) := by
  have hcop : IsCoprime (n : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : 𝓞) * n + (b : 𝓞) * p = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hab
    simpa using this
  have hjac : (b : 𝓞) * p ∈ Ring.jacobson 𝓞 :=
    IsAdicComplete.le_jacobson (Ideal.span {(p : 𝓞)}) (Ideal.mul_mem_left _ _
        (Ideal.mem_span_singleton_self _))
  have hu : IsUnit ((a : 𝓞) * n) := by
    rw [Ring.mem_jacobson_iff] at hjac
    have := hjac (-1)
    rwa [show (b : 𝓞) * p * (-1) + 1 = (a : 𝓞) * n by linear_combination (-1 : 𝓞) * h1] at this
  exact isUnit_of_mul_isUnit_right hu

theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega

theorem two_mul_le_of_pow_mul {k u n : ℕ} (hu : u ≠ 0) (h : n = p ^ k * u) : 2 * k ≤ n := by
  have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
  have h2 : p ^ k ≤ n := by rw [h]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu)
  have := two_mul_le_two_pow k
  omega

end UnitsSec

section Rescale

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*}

noncomputable def rho (p : ℕ) : MvPowerSeries σ 𝓞 →+* MvPowerSeries σ 𝓞 := rescale (fun _ =>
    (p : 𝓞))

theorem coeff_rho (p : ℕ) (f : MvPowerSeries σ 𝓞) (m : σ →₀ ℕ) :
    coeff m (rho p f) = (p : 𝓞) ^ m.degree * coeff m f := by
  rw [rho, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

theorem rho_eq_subst (p : ℕ) (f : MvPowerSeries σ 𝓞) :
    rho p f = subst ((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) f :=
  rescale_eq_subst _ f

theorem rho_X (p : ℕ) (s : σ) : rho (𝓞 := 𝓞) p (X s) = (p : 𝓞) • X s := by
  rw [rho_eq_subst, subst_X (HasSubst.smul_X _)]
  rfl

theorem rho_subst (p : ℕ) {τ : Type*} {a : τ →
    MvPowerSeries σ 𝓞} (ha : HasSubst a) (f : MvPowerSeries τ 𝓞) :
    rho p (subst a f) = subst (fun t => rho p (a t)) f := by
  rw [rho_eq_subst, subst_comp_subst_apply ha (HasSubst.smul_X _)]
  congr 1
  funext t
  rw [rho_eq_subst]

theorem subst_smul_family (p : ℕ) {τ : Type*} {a : σ →
    MvPowerSeries τ 𝓞} (ha : HasSubst a) (f : MvPowerSeries σ 𝓞) :
    subst (fun s => (p : 𝓞) • a s) f = subst a (rho p f) := by
  rw [rho_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext s
  change (p : 𝓞) • a s = subst a (((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) s)
  rw [Pi.smul_apply', subst_smul ha, subst_X ha]

end Rescale

section Descent

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

local notation "K" => Localization.Away (p : 𝓞)
local notation "φ" => algebraMap 𝓞 (Localization.Away (p : 𝓞))

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
include hpR in
theorem φ_injective : Function.Injective φ :=
  IsLocalization.injective (M :=
      Submonoid.powers (p : 𝓞)) (Localization.Away (p : 𝓞)) (Submonoid.powers_le.2 hpR)

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
theorem isUnit_φp : IsUnit (φ (p : 𝓞)) := IsLocalization.Away.algebraMap_isUnit (p : 𝓞)

theorem isUnit_succ (n : ℕ) : IsUnit ((n + 1 : ℕ) : K) := by
  obtain ⟨k, u, hu,
      hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n + 1 ≠ 0 by omega) p hp.out.ne_one
  rw [hk, Nat.cast_mul, Nat.cast_pow]
  refine IsUnit.mul (IsUnit.pow _ ?_) ?_
  · have := isUnit_φp (𝓞 := 𝓞) p; rwa [map_natCast] at this
  · have := (isUnit_natCast_of_not_dvd (𝓞 := 𝓞) p hu).map φ; rwa [map_natCast] at this

scoped instance isComm_map {S : Type*} [CommRing S] (g : 𝓞 →+* S) : (F.map g).IsComm where
  comm := fun i => by
    have h := congrArg (MvPowerSeries.map g) (MvFormalGroup.IsComm.comm (F := F) i)
    rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;>
        simp [constantCoeff_X]))] at h
    have hfam : (fun s => MvPowerSeries.map g (Sum.elim (fun j =>
        (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        (fun j => X (Sum.inl j)) s)) = Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕
            Fin d) S)) (fun j => X (Sum.inl j)) := by
      funext s; rcases s with j | j <;> simp
    rw [hfam] at h
    exact h

noncomputable def fK : Fin d → MvPowerSeries (Fin d) K := logK (F.map φ) (isUnit_succ p)

theorem fK_const (i : Fin d) : constantCoeff (fK p F i) = 0 := constantCoeff_logK _ i
theorem fK_lin (i : Fin d) : Cong 1 (fK p F i) (X i) := cong_one_logK _ i
theorem fK_add (i : Fin d) : subst (F.map φ).toPowerSeries (fK p F i) = subst inlX (fK p F i) +
    subst inrX (fK p F i) := by
  have := Edef_logK (F := F.map φ) (isUnit_succ p) i
  rw [Edef] at this
  unfold fK
  linear_combination this

theorem exists_pre (i : Fin d) (m : Fin d →₀ ℕ) (hm : m ≠ 0) :
    ∃ c : 𝓞, φ c = φ (p : 𝓞) ^ (m.degree - 1) * coeff m (fK p F i) ∧
      ∃ k : ℕ, 2 * k ≤ m.degree ∧ c ∈ Ideal.span {(p : 𝓞) ^ (m.degree - 1 - k)} := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    exact hm (Finsupp.ext fun j => not_not.1 (not_exists.1 h j))
  obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj p hp.out.ne_one
  have hu0 : u ≠ 0 := fun h => hj (by rw [hk, h, mul_zero])
  set m' := m - Finsupp.single j 1 with hm'
  have hmm' : m' + Finsupp.single j 1 = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hj))
  have hmj : m' j + 1 = m j := by
    have := congrArg (fun n => n j) hmm'; simpa using this
  obtain ⟨c₀, hc₀⟩ := exists_coeff_Dlog φ F (fK p F) (fK_lin p F) (fK_add p F) i j m'
  rw [show coeff m' (Dlog (fK p F) i j) = ((m' j + 1 : ℕ) : K) * coeff (m' +
      Finsupp.single j 1) (fK p F i) from rfl,
    hmj, hmm', hk, Nat.cast_mul, Nat.cast_pow] at hc₀
  obtain ⟨uu, huu⟩ := isUnit_natCast_of_not_dvd (𝓞 := 𝓞) p hu
  have hkdeg : k ≤ m.degree - 1 := by
    have h2 := two_mul_le_of_pow_mul p hu0 hk
    have h3 : m j ≤ m.degree := Finsupp.le_degree j m
    have : 0 < m j := Nat.pos_of_ne_zero hj
    omega
  refine ⟨(p : 𝓞) ^ (m.degree - 1 - k) * c₀ * ↑uu⁻¹, ?_, k, ?_, ?_⟩
  · rw [map_mul, map_mul, map_pow, hc₀, map_natCast]
    have huK : (u : K) * φ (↑uu⁻¹ : 𝓞) = 1 := by rw [← map_natCast φ u, ← map_mul, ← huu,
        Units.mul_inv, map_one]
    have hpk : (p : K) ^ (m.degree - 1) = (p : K) ^ (m.degree - 1 - k) * (p : K) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkdeg]
    rw [hpk]
    linear_combination ((p : K) ^ (m.degree - 1 - k) * (p : K) ^ k * coeff m (fK p F i)) * huK
  · have h2 := two_mul_le_of_pow_mul p hu0 hk
    exact h2.trans (Finsupp.le_degree j m)
  · rw [mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

noncomputable def bcoef (i : Fin d) (m : Fin d →₀ ℕ) : 𝓞 :=
  if hm : m = 0 then 0 else Classical.choose (exists_pre p F i m hm)

theorem φ_bcoef (i : Fin d) (m : Fin d →₀ ℕ) :
    φ (bcoef p F i m) = φ (p : 𝓞) ^ (m.degree - 1) * coeff m (fK p F i) := by
  rw [bcoef]
  split_ifs with hm
  · rw [hm, map_zero, coeff_zero_eq_constantCoeff_apply, fK_const, mul_zero]
  · exact (Classical.choose_spec (exists_pre p F i m hm)).1

include hpR in
theorem bcoef_mem (i : Fin d) (m : Fin d →₀ ℕ) (N : ℕ) (hN : 2 * N + 2 ≤ m.degree) :
    bcoef p F i m ∈ Ideal.span {(p : 𝓞) ^ N} := by
  have hm : m ≠ 0 := by rintro rfl; simp at hN
  obtain ⟨c, hc, k, hk, hmem⟩ := exists_pre p F i m hm
  have hcb : c = bcoef p F i m := φ_injective p hpR (by rw [hc, φ_bcoef])
  rw [← hcb]
  refine Ideal.span_singleton_le_span_singleton.2 ?_ hmem
  exact pow_dvd_pow _ (by omega)

noncomputable def phiSer (i : Fin d) : MvPowerSeries (Fin d) 𝓞 := fun m => bcoef p F i m

open Classical in
noncomputable def FpSer (i : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
  fun m => if m = 0 then 0 else (p : 𝓞) ^ (m.degree - 1) * coeff m (F.toPowerSeries i)

theorem coeff_phiSer (i : Fin d) (m : Fin d →₀ ℕ) : coeff m (phiSer p F i) =
    bcoef p F i m := rfl

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [F.IsComm] in
open Classical in
theorem coeff_FpSer (i : Fin d) (m : Fin d ⊕ Fin d →₀ ℕ) :
    coeff m (FpSer p F i) = if m = 0 then 0 else (p : 𝓞) ^ (m.degree -
        1) * coeff m (F.toPowerSeries i) := rfl

noncomputable def π : Kˣ := (isUnit_φp (𝓞 := 𝓞) p).unit

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
theorem π_val : ((π p : Kˣ) : K) = (p : K) := by rw [π, IsUnit.unit_spec, map_natCast]

theorem map_phiSer (i : Fin d) : MvPowerSeries.map φ (phiSer p F i) = ((π p)⁻¹ : Kˣ).val •
    rho p (fK p F i) := by
  ext m
  rw [coeff_map, coeff_phiSer, φ_bcoef, map_smul, coeff_rho, smul_eq_mul, map_natCast, ← π_val]
  by_cases hm : m = 0
  · rw [hm, coeff_zero_eq_constantCoeff_apply, fK_const, mul_zero, mul_zero, mul_zero]
  · have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h =>
        hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ,
      show (((π p)⁻¹ : Kˣ) : K) * ((((π p) : Kˣ) : K) ^ t * (((π p) : Kˣ) : K) *
          coeff m (fK p F i)) =
        (((π p) : Kˣ) : K) ^ t * coeff m (fK p F i) * ((((π p)⁻¹ : Kˣ) : K) *
            (((π p) : Kˣ) : K)) by ring,
      Units.inv_mul, mul_one]

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [F.IsComm] in
theorem map_FpSer (i : Fin d) :
    MvPowerSeries.map φ (FpSer p F i) = ((π p)⁻¹ : Kˣ).val • rho p ((F.map φ).toPowerSeries i) := by
  classical
  ext m
  rw [coeff_map, coeff_FpSer, map_smul, coeff_rho, smul_eq_mul, ← π_val]
  change _ = _ * (_ * coeff m (MvPowerSeries.map φ (F.toPowerSeries i)))
  rw [coeff_map]
  by_cases hm : m = 0
  · rw [ite_eq_left hm, map_zero, hm, coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero,
        map_zero]
    simp
  · rw [ite_eq_right hm, map_mul, map_pow, map_natCast, ← π_val]
    have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h =>
        hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ,
      show (((π p)⁻¹ : Kˣ) : K) * ((((π p) : Kˣ) : K) ^ t * (((π p) : Kˣ) : K) *
          φ (coeff m (F.toPowerSeries i))) =
        (((π p) : Kˣ) : K) ^ t * φ (coeff m (F.toPowerSeries i)) * ((((π p)⁻¹ : Kˣ) : K) *
            (((π p) : Kˣ) : K)) by ring,
      Units.inv_mul, mul_one]

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
include hpR in
theorem map_injective : Function.Injective (MvPowerSeries.map (σ := Fin d ⊕ Fin d) φ) := by
  intro f g h
  ext m
  apply φ_injective p hpR
  rw [← coeff_map, ← coeff_map, h]

omit hp [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] [F.IsComm] in
theorem hasSubst_FpK : HasSubst fun j => ((π p)⁻¹ : Kˣ).val • rho p ((F.map φ).toPowerSeries j) :=
  hasSubst_of_constantCoeff_zero fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, map_smul, coeff_rho, coeff_zero_eq_constantCoeff_apply,
      (F.map φ).constantCoeff_eq_zero, mul_zero, smul_zero]

include hpR in
theorem phiSer_add (i : Fin d) :
    subst (FpSer p F) (phiSer p F i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (phiSer p F i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (phiSer p F i) := by
  classical
  apply map_injective p hpR
  have hFp0 : ∀ j, constantCoeff (FpSer p F j) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_FpSer, ite_eq_left rfl]
  have hFpS := hasSubst_of_constantCoeff_zero hFp0
  have hinl : HasSubst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have hinr : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have hinlK : HasSubst (inlX : Fin d → MvPowerSeries (Fin d ⊕
      Fin d) K) := hasSubst_of_constantCoeff_zero constantCoeff_inlX
  have hinrK : HasSubst (inrX : Fin d → MvPowerSeries (Fin d ⊕
      Fin d) K) := hasSubst_of_constantCoeff_zero constantCoeff_inrX
  rw [map_add, MvPowerSeries.map_subst hFpS, MvPowerSeries.map_subst hinl,
      MvPowerSeries.map_subst hinr, map_phiSer]
  simp only [map_FpSer, MvPowerSeries.map_X]
  set u : K := ((π p)⁻¹ : Kˣ).val with hu
  set FK := F.map φ with hFK
  have hpu : (p : K) * u = 1 := by rw [hu, ← π_val, Units.mul_inv]
  have hL : subst (fun j => u • rho p (FK.toPowerSeries j)) (u •
      rho p (fK p F i)) = u • rho p (subst FK.toPowerSeries (fK p F i)) := by
    rw [subst_smul (hasSubst_FpK p F), ← subst_smul_family p (hasSubst_FpK p F)]
    have hfam : (fun s => (p : K) • (u •
        rho p (FK.toPowerSeries s))) = fun s => rho p (FK.toPowerSeries s) := by
      funext s; rw [smul_smul, hpu, one_smul]
    rw [hfam, rho_subst p FK.hasSubst_toPowerSeries]
  have hinlK' : HasSubst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) :=
    hasSubst_of_constantCoeff_zero (fun t => constantCoeff_X _)
  have hinrK' : HasSubst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin d ⊕ Fin d) K)) :=
    hasSubst_of_constantCoeff_zero (fun t => constantCoeff_X _)
  rw [hL, fK_add, map_add, rho_subst p hinlK, rho_subst p hinrK, smul_add]
  simp only [inlX, inrX, rho_X]
  rw [subst_smul_family p hinlK', subst_smul_family p hinrK', subst_smul hinlK', subst_smul hinrK']

end Descent

section MainSec

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

include hpR in
theorem main :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) := by
  classical
  refine ⟨FpSer p F, phiSer p F, ?_, ?_, ?_, ?_, ?_, fun i => phiSer_add p hpR F i⟩
  · intro i m hm
    show coeff m (FpSer p F i) * _ = _ * coeff m (F.toPowerSeries i)
    rw [coeff_FpSer, ite_eq_right hm]
    have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h =>
        hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ]
    ring
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_FpSer, ite_eq_left rfl]
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_phiSer, bcoef, dite_eq_left rfl]
  · ext i j
    rw [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.one_apply]
    show coeff (Finsupp.single j 1) (phiSer p F i) = _
    rw [coeff_phiSer]
    apply φ_injective p hpR
    rw [φ_bcoef, Finsupp.degree_single, Nat.sub_self, pow_zero, one_mul,
      (fK_lin p F i) _ (by rw [Finsupp.degree_single]), coeff_X]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right (fun h => hij (Finsupp.single_left_injective one_ne_zero h).symm),
          ite_eq_right hij, map_zero]
  · intro N i
    refine Filter.eventually_cofinite.2 ((lowDeg (Fin d) (2 * N +
        1)).finite_toSet.subset fun m hm => ?_)
    rw [Finset.mem_coe, mem_lowDeg]
    by_contra h
    exact hm (bcoef_mem p hpR F i m N (by omega))

end MainSec

end RescaledLogAux

end

@[expose] public section

open MvPowerSeries

universe u

namespace MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

/-- Power series that agree after multiplication by a non-zero-divisor are equal. -/
private theorem eq_of_smul_eq_smul {σ : Type*} {a : R} (ha : a ∈ nonZeroDivisors R)
    {f f' : MvPowerSeries σ R} (h : a • f = a • f') : f = f' := by
  ext m
  have hm := congrArg (coeff m) h
  rw [coeff_smul, coeff_smul] at hm
  exact (mul_cancel_left_mem_nonZeroDivisors ha).mp hm

/-- A family with the coefficients of the rescaling satisfies `a • G = F(a X, a Y)`. -/
private theorem smul_eq_rescale_of_coeff (F : MvFormalGroup g R) {a : R}
    {G : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R}
    (hG : ∀ i m, coeff m (G i) =
      if m = 0 then 0 else a ^ (m.degree - 1) * coeff m (F.toPowerSeries i))
    (i : Fin g) : a • G i = MvPowerSeries.rescale (fun _ => a) (F.toPowerSeries i) := by
  ext m
  rw [coeff_smul, hG, MvPowerSeries.coeff_rescale]
  have hprod : (m.prod fun _ k => a ^ k) = a ^ m.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
    rfl
  split_ifs with hm
  · rw [hm, coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero, mul_zero, mul_zero]
  · obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 :=
      ⟨m.degree - 1, by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega⟩
    rw [hprod, ht, Nat.add_sub_cancel, pow_succ]
    ring

/-- If `a • G = F(a X, a Y)`, then `a • G(b) = F(a • b)`. -/
private theorem smul_subst_of_smul_eq (F : MvFormalGroup g R) {a : R}
    {G : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R}
    (hG : ∀ i, a • G i = MvPowerSeries.rescale (fun _ => a) (F.toPowerSeries i))
    {τ : Type*} {b : Fin g ⊕ Fin g → MvPowerSeries τ R} (hb : HasSubst b) (i : Fin g) :
    a • subst b (G i) = subst (fun s => a • b s) (F.toPowerSeries i) := by
  rw [← subst_smul hb a (G i), hG, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X _) hb]
  congr 1
  funext s
  change subst b (a • (X s : MvPowerSeries (Fin g ⊕ Fin g) R)) = a • b s
  rw [subst_smul hb a, subst_X hb]

/-- Associativity of `F` transfers to a family `G` with `a • G = F(a X, a Y)`. -/
private theorem subst_elim_assoc_of_smul_eq (F : MvFormalGroup g R) {a : R}
    (ha : a ∈ nonZeroDivisors R) {G : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R}
    (hG0 : ∀ i, (G i).constantCoeff = 0)
    (hG : ∀ i, a • G i = MvPowerSeries.rescale (fun _ => a) (F.toPowerSeries i))
    {τ : Type*} {u v w : Fin g → MvPowerSeries τ R}
    (hu : ∀ i, (u i).constantCoeff = 0) (hv : ∀ i, (v i).constantCoeff = 0)
    (hw : ∀ i, (w i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun j => subst (Sum.elim u v) (G j)) w) (G i)
      = subst (Sum.elim u fun j => subst (Sum.elim v w) (G j)) (G i) := by
  have hsm : ∀ {x : Fin g → MvPowerSeries τ R}, (∀ i, (x i).constantCoeff = 0) →
      ∀ i, (a • x i).constantCoeff = 0 := fun hx i => by rw [constantCoeff_smul, hx i, smul_zero]
  have huv := hasSubst_elim hu hv
  have hvw := hasSubst_elim hv hw
  have hL : HasSubst (Sum.elim (fun j => subst (Sum.elim u v) (G j)) w) :=
    hasSubst_elim (fun j => constantCoeff_subst_eq_zero huv
      (by rintro (l | l); exacts [hu l, hv l]) (hG0 j)) hw
  have hR : HasSubst (Sum.elim u fun j => subst (Sum.elim v w) (G j)) :=
    hasSubst_elim hu (fun j => constantCoeff_subst_eq_zero hvw
      (by rintro (l | l); exacts [hv l, hw l]) (hG0 j))
  apply eq_of_smul_eq_smul ha
  rw [smul_subst_of_smul_eq F hG hL, smul_subst_of_smul_eq F hG hR]
  have e1 : (fun s => a • (Sum.elim (fun j => subst (Sum.elim u v) (G j)) w) s) =
      Sum.elim (fun j => subst (Sum.elim (fun l => a • u l) fun l => a • v l)
        (F.toPowerSeries j)) fun l => a • w l := by
    funext s
    rcases s with j | j
    · change a • subst (Sum.elim u v) (G j) = _
      rw [smul_subst_of_smul_eq F hG huv]
      congr 1
      funext t
      rcases t with l | l <;> rfl
    · rfl
  have e2 : (fun s => a • (Sum.elim u fun j => subst (Sum.elim v w) (G j)) s) =
      Sum.elim (fun l => a • u l) fun j => subst (Sum.elim (fun l => a • v l) fun l => a • w l)
        (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · rfl
    · change a • subst (Sum.elim v w) (G j) = _
      rw [smul_subst_of_smul_eq F hG hvw]
      congr 1
      funext t
      rcases t with l | l <;> rfl
  rw [e1, e2]
  exact subst_elim_assoc F (hsm hu) (hsm hv) (hsm hw) i

/-- Commutativity of `F` transfers to a family `G` with `a • G = F(a X, a Y)`. -/
private theorem subst_swap_of_smul_eq (F : MvFormalGroup g R) [F.IsComm] {a : R}
    (ha : a ∈ nonZeroDivisors R) {G : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R}
    (hG : ∀ i, a • G i = MvPowerSeries.rescale (fun _ => a) (F.toPowerSeries i)) (i : Fin g) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) (G i) = G i := by
  have hswap : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have hsX : ∀ s : Fin g ⊕ Fin g,
      (a • (X s : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 := fun s => by
    rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  apply eq_of_smul_eq_smul ha
  rw [smul_subst_of_smul_eq F hG hswap, hG, rescale_eq_subst]
  have e1 : (fun s => a • (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s) =
      Sum.elim (fun j => a • (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => a • X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> rfl
  have e2 : ((fun _ : Fin g ⊕ Fin g => a) •
      (X : Fin g ⊕ Fin g → MvPowerSeries (Fin g ⊕ Fin g) R)) =
      Sum.elim (fun j => a • (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => a • X (Sum.inr j) := by
    funext s
    rcases s with j | j <;> rfl
  rw [e1, e2]
  exact subst_elim_comm F (fun j => hsX _) (fun j => hsX _) i

/-- The coefficients of the rescaling of `F` by `a`. -/
private def rescaleSeries (F : MvFormalGroup g R) (a : R) (i : Fin g) :
    MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun m => if m = 0 then 0 else a ^ (m.degree - 1) * coeff m (F.toPowerSeries i)

private theorem coeff_rescaleSeries (F : MvFormalGroup g R) (a : R) (i : Fin g)
    (m : Fin g ⊕ Fin g →₀ ℕ) :
    coeff m (rescaleSeries F a i) =
      if m = 0 then 0 else a ^ (m.degree - 1) * coeff m (F.toPowerSeries i) :=
  rfl

private theorem constantCoeff_rescaleSeries (F : MvFormalGroup g R) (a : R) (i : Fin g) :
    (rescaleSeries F a i).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescaleSeries, ite_eq_left rfl]

private theorem coeff_single_inl_rescaleSeries (F : MvFormalGroup g R) (a : R) (i j : Fin g) :
    coeff (Finsupp.single (Sum.inl j) 1) (rescaleSeries F a i) = if i = j then 1 else 0 := by
  rw [coeff_rescaleSeries, ite_eq_right (Finsupp.single_ne_zero.mpr one_ne_zero),
    Finsupp.degree_single, Nat.sub_self, pow_zero, one_mul, F.coeff_single_inl]

private theorem coeff_single_inr_rescaleSeries (F : MvFormalGroup g R) (a : R) (i j : Fin g) :
    coeff (Finsupp.single (Sum.inr j) 1) (rescaleSeries F a i) = if i = j then 1 else 0 := by
  rw [coeff_rescaleSeries, ite_eq_right (Finsupp.single_ne_zero.mpr one_ne_zero),
    Finsupp.degree_single, Nat.sub_self, pow_zero, one_mul, F.coeff_single_inr]

/-- The rescaling by a non-zero-divisor `a`, whose laws follow by cancelling `a`. -/
private def rescaleOfMem (F : MvFormalGroup g R) {a : R} (ha : a ∈ nonZeroDivisors R) :
    MvFormalGroup g R where
  toPowerSeries := rescaleSeries F a
  constantCoeff_eq_zero := constantCoeff_rescaleSeries F a
  coeff_single_inl := coeff_single_inl_rescaleSeries F a
  coeff_single_inr := coeff_single_inr_rescaleSeries F a
  assoc := subst_elim_assoc_of_smul_eq F ha (constantCoeff_rescaleSeries F a)
    (smul_eq_rescale_of_coeff F (coeff_rescaleSeries F a))
    (u := fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
    (v := fun l => X (Sum.inr (Sum.inl l))) (w := fun l => X (Sum.inr (Sum.inr l)))
    (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)

private theorem isComm_rescaleOfMem (F : MvFormalGroup g R) [F.IsComm] {a : R}
    (ha : a ∈ nonZeroDivisors R) : (rescaleOfMem F ha).IsComm :=
  ⟨subst_swap_of_smul_eq F ha (smul_eq_rescale_of_coeff F (coeff_rescaleSeries F a))⟩

/-- The rescaling of `F` by `a` is the image under evaluation at `a` of the rescaling of `F` by
the non-zero-divisor `X` of `R[X]`. -/
private theorem rescaleSeries_eq_map (F : MvFormalGroup g R) (a : R) :
    rescaleSeries F a = ((rescaleOfMem (F.map Polynomial.C) Polynomial.X_mem_nonZeroDivisors).map
      (Polynomial.evalRingHom a)).toPowerSeries := by
  funext i
  ext m
  change coeff m (rescaleSeries F a i) =
    coeff m (MvPowerSeries.map (Polynomial.evalRingHom a)
      (rescaleSeries (F.map Polynomial.C) Polynomial.X i))
  rw [coeff_map, coeff_rescaleSeries, coeff_rescaleSeries]
  split_ifs
  · rw [map_zero]
  · change _ = Polynomial.evalRingHom a (Polynomial.X ^ (m.degree - 1) *
      coeff m (MvPowerSeries.map Polynomial.C (F.toPowerSeries i)))
    rw [coeff_map, map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_X,
      Polynomial.eval_C]

/-- **Rescaled formal group law.** For `a : R`, the formal group law whose constant terms are
zero and whose coefficient at a multi-index `m ≠ 0` of total degree `|m|` is `a ^ (|m| - 1)`
times that of `F`. When `a` is a unit it is `a⁻¹ F(a X, a Y)`; in general `a` need not be a unit
or a non-zero-divisor (rescaling by `0` gives the additive formal group law). -/
@[no_expose]
def rescale (F : MvFormalGroup g R) (a : R) : MvFormalGroup g R where
  toPowerSeries := rescaleSeries F a
  constantCoeff_eq_zero := constantCoeff_rescaleSeries F a
  coeff_single_inl := coeff_single_inl_rescaleSeries F a
  coeff_single_inr := coeff_single_inr_rescaleSeries F a
  assoc := by
    rw [rescaleSeries_eq_map]
    exact MvFormalGroup.assoc _

@[simp]
theorem coeff_rescale (F : MvFormalGroup g R) (a : R) (i : Fin g) (m : Fin g ⊕ Fin g →₀ ℕ) :
    coeff m ((F.rescale a).toPowerSeries i) =
      if m = 0 then 0 else a ^ (m.degree - 1) * coeff m (F.toPowerSeries i) :=
  coeff_rescaleSeries F a i m

instance (F : MvFormalGroup g R) [F.IsComm] (a : R) : (F.rescale a).IsComm where
  comm := by
    have := RescaledLogAux.isComm_map F (Polynomial.C : R →+* Polynomial R)
    have := isComm_rescaleOfMem (F.map Polynomial.C) Polynomial.X_mem_nonZeroDivisors
    change ∀ i, subst _ (rescaleSeries F a i) = rescaleSeries F a i
    rw [rescaleSeries_eq_map]
    exact (RescaledLogAux.isComm_map _ (Polynomial.evalRingHom a)).comm

end MvFormalGroup

/-- **Integral logarithm of a rescaled formal group law.** Let `p` be a prime whose image in `𝓞`
is a non-zero-divisor, with `𝓞` complete for the `(p)`-adic topology, and let `F` be a
commutative `d`-dimensional formal group law over `𝓞`. Then there are power series `Fp` and `φ`
over `𝓞` such that:

- for every multi-index `m ≠ 0` of total degree `|m|`,
  `p · coeff m (Fp i) = p ^ |m| · coeff m (F i)`, so `Fp` is `F` with its coefficients of total
  degree `n` multiplied by `p ^ (n - 1)`;
- every `Fp i` and every `φ i` has zero constant term;
- the linear part of `φ` is the identity matrix;
- for every `N`, all but finitely many coefficients of each `φ i` lie in the ideal `(p ^ N)`;
- `φ (Fp (X, Y)) = φ (X) + φ (Y)`, so `φ` is a logarithm of `Fp`. -/
public theorem MvFormalGroup.exists_rescaledLog_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :=
  RescaledLogAux.main p hp F

/-- **Integral logarithm of the rescaled law `F.rescale p`.** Let `p` be a prime whose image in
`𝓞` is a non-zero-divisor, with `𝓞` complete for the `(p)`-adic topology, and let `F` be a
commutative `d`-dimensional formal group law over `𝓞`. Then there are power series `φ` over `𝓞`
such that:

- every `φ i` has zero constant term, and the linear part of `φ` is the identity matrix;
- for every `N`, all but finitely many coefficients of each `φ i` lie in the ideal `(p ^ N)`;
- `φ (G (X, Y)) = φ (X) + φ (Y)` for the formal group law `G = F.rescale p`, whose coefficients
  of total degree `n ≥ 1` are those of `F` multiplied by `p ^ (n - 1)`; so `φ` is a logarithm
  of `G`. -/
public theorem MvFormalGroup.exists_log_rescale_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst (F.rescale (p : 𝓞)).toPowerSeries (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) := by
  obtain ⟨Fp, φ, hcoeff, hFp0, hφ0, hlin, hdec, hlog⟩ :=
    MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F
  have hFp : Fp = (F.rescale (p : 𝓞)).toPowerSeries := by
    funext i
    ext m
    rw [MvFormalGroup.coeff_rescale]
    split_ifs with hm
    · rw [hm, coeff_zero_eq_constantCoeff_apply, hFp0]
    · refine (mul_cancel_right_mem_nonZeroDivisors hp).mp ?_
      rw [hcoeff i m hm]
      obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 :=
        ⟨m.degree - 1, by have := (Finsupp.degree_eq_zero_iff m).not.mpr hm; omega⟩
      rw [ht, Nat.add_sub_cancel, pow_succ]
      ring
  subst hFp
  exact ⟨φ, hφ0, hlin, hdec, hlog⟩
