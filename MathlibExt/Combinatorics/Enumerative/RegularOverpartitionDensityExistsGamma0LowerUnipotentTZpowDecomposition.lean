/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.Enumerative.Partition.FiniteEulerProductCongruence
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Double coset representatives for `Γ₀(N)`

This module proves `exists_gamma0_lowerUnipotent_T_zpow_decomposition`: when `N` is squarefree,
or even with `N / 2` squarefree, then for every `γ` in `SL(2, ℤ)` there is exactly one divisor
`δ` of `N` for which `γ` factors as an element of `Γ₀(N)` times the lower unipotent matrix of
`δ` times an integer power of `T`.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 3 (`integers-2025-A3-lem-3`), quoting Wang, Lemma 4.3.
-/

namespace MetaMathlibExt

open Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The lower unipotent matrix with `δ` below the diagonal. -/
private def lowerUnipotent (δ : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩

private theorem mul_val_10 (A B : SL(2, ℤ)) :
    (A * B).1 1 0 = A.1 1 0 * B.1 0 0 + A.1 1 1 * B.1 1 0 :=
  (Matrix.two_mul_expl A.1 B.1).2.2.1

private theorem mul_val_11 (A B : SL(2, ℤ)) :
    (A * B).1 1 1 = A.1 1 0 * B.1 0 1 + A.1 1 1 * B.1 1 1 :=
  (Matrix.two_mul_expl A.1 B.1).2.2.2

private theorem inv_val_00 (A : SL(2, ℤ)) : (A⁻¹).1 0 0 = A.1 1 1 := by
  rw [SL2_inv_expl A]
  rfl

private theorem inv_val_10 (A : SL(2, ℤ)) : (A⁻¹).1 1 0 = -A.1 1 0 := by
  rw [SL2_inv_expl A]
  rfl

private theorem L_val_10 (δ : ℕ) : (lowerUnipotent δ).1 1 0 = (δ : ℤ) := rfl

private theorem L_val_11 (δ : ℕ) : (lowerUnipotent δ).1 1 1 = 1 := rfl

private theorem Tpow_val_00 (h : ℤ) : ((ModularGroup.T ^ h : SL(2, ℤ)).1) 0 0 = 1 := by
  simp [ModularGroup.coe_T_zpow]

private theorem Tpow_val_10 (h : ℤ) : ((ModularGroup.T ^ h : SL(2, ℤ)).1) 1 0 = 0 := by
  simp [ModularGroup.coe_T_zpow]

private theorem Tpow_val_01 (h : ℤ) : ((ModularGroup.T ^ h : SL(2, ℤ)).1) 0 1 = h := by
  simp [ModularGroup.coe_T_zpow]

private theorem Tpow_val_11 (h : ℤ) : ((ModularGroup.T ^ h : SL(2, ℤ)).1) 1 1 = 1 := by
  simp [ModularGroup.coe_T_zpow]

private theorem B_val_10 (δ : ℕ) (h : ℤ) :
    ((lowerUnipotent δ * ModularGroup.T ^ h : SL(2, ℤ)).1) 1 0 = (δ : ℤ) := by
  rw [mul_val_10, L_val_10, L_val_11, Tpow_val_00, Tpow_val_10]
  ring

private theorem B_val_11 (δ : ℕ) (h : ℤ) :
    ((lowerUnipotent δ * ModularGroup.T ^ h : SL(2, ℤ)).1) 1 1
      = (δ : ℤ) * h + 1 := by
  rw [mul_val_11, L_val_10, L_val_11, Tpow_val_01, Tpow_val_11]
  ring

private theorem A_val_10 (γ : SL(2, ℤ)) (δ : ℕ) (h : ℤ) :
    ((γ * (lowerUnipotent δ * ModularGroup.T ^ h)⁻¹ : SL(2, ℤ)).1) 1 0
      = γ.1 1 0 * ((δ : ℤ) * h + 1) + γ.1 1 1 * (-(δ : ℤ)) := by
  rw [mul_val_10, inv_val_00, inv_val_10, B_val_11, B_val_10]

private theorem gamma_mem_iff (N : ℕ) (γ : SL(2, ℤ)) (δ : ℕ) (h : ℤ) :
    γ * (lowerUnipotent δ * ModularGroup.T ^ h)⁻¹ ∈ CongruenceSubgroup.Gamma0 N
      ↔ (N : ℤ) ∣ γ.1 1 0 * ((δ : ℤ) * h + 1) + γ.1 1 1 * (-(δ : ℤ)) := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, A_val_10]

private theorem bottom_row_coprime (γ : SL(2, ℤ)) :
    IsCoprime (γ.1 1 0) (γ.1 1 1) := by
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  exact ⟨-γ.1 0 1, γ.1 0 0, by linear_combination hdet⟩

private theorem gamma_factor (γ : SL(2, ℤ)) (δ : ℕ) (h : ℤ) :
    γ = γ * (lowerUnipotent δ * ModularGroup.T ^ h)⁻¹
      * (lowerUnipotent δ * ModularGroup.T ^ h) := by
  group

private theorem nat_ne_zero_of_squarefree (N : ℕ) (h : Squarefree N) : N ≠ 0 := by
  rintro rfl
  have h2 := h 2 (dvd_zero _)
  rw [Nat.isUnit_iff] at h2
  omega

private theorem N_ne_zero (N : ℕ)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2))) : N ≠ 0 := by
  rcases hsq with h | ⟨-, h⟩
  · exact nat_ne_zero_of_squarefree N h
  · have h2 := nat_ne_zero_of_squarefree (N / 2) h
    omega

private theorem pos_of_dvd_ne_zero (a b : ℕ) (h : a ∣ b) (hb : b ≠ 0) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · exact absurd (zero_dvd_iff.mp h) hb
  · exact hpos

private theorem nat_dvd_natAbs_of_int_dvd (a : ℕ) (c : ℤ) (h : (a : ℤ) ∣ c) :
    a ∣ c.natAbs := by
  have h' := Int.natAbs_dvd_natAbs.mpr h
  rwa [Int.natAbs_natCast] at h'

private theorem int_dvd_of_nat_dvd_natAbs (a : ℕ) (c : ℤ) (h : a ∣ c.natAbs) :
    (a : ℤ) ∣ c := by
  have h' : ((a : ℤ)).natAbs ∣ c.natAbs := by rwa [Int.natAbs_natCast]
  exact Int.natAbs_dvd_natAbs.mp h'

private theorem odd_of_coprime_left_even (c d : ℤ) (hcop : IsCoprime c d)
    (hc : Even c) : Odd d := by
  by_contra hd
  rw [Int.not_odd_iff_even] at hd
  obtain ⟨u, v, huv⟩ := hcop
  rw [even_iff_two_dvd] at hc hd
  have h2 : (2 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right hc u) (dvd_mul_of_dvd_right hd v)
  omega

private theorem nat_odd_of_coprime_right_even (C' N' : ℕ)
    (hcop : Nat.Coprime C' N') (heven : Even N') : Odd C' := by
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  rw [even_iff_two_dvd] at hcon heven
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hcon heven hcop

private theorem exists_int_sol (A B M g' A₁ B₁ M₁ : ℤ)
    (hA : A = g' * A₁) (hB : B = g' * B₁) (hM : M = g' * M₁)
    (hcop : IsCoprime A₁ M₁) : ∃ h : ℤ, M ∣ A * h + B := by
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨-B₁ * u, B₁ * v, by rw [hA, hB, hM]; linear_combination -(g' * B₁) * huv⟩

private theorem gcd_mul_self_dvd (a b N : ℕ) (hN : a * b = N) :
    Nat.gcd a b * Nat.gcd a b ∣ N := by
  rw [← hN]
  exact Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

private theorem gcd_eq_one_of_squarefree_mul (a b N : ℕ) (hN : a * b = N)
    (hsq : Squarefree N) : Nat.gcd a b = 1 := by
  have h := gcd_mul_self_dvd a b N hN
  have hu := hsq _ h
  rwa [Nat.isUnit_iff] at hu

private theorem odd_prime_not_dvd_gcd (a b N : ℕ) (hN : a * b = N) (h2N : 2 ∣ N)
    (hsq2 : Squarefree (N / 2)) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpg : p ∣ Nat.gcd a b) : False := by
  have hpa : p ∣ a := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ b := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  have hpp : p * p ∣ N := by
    rw [← hN]
    exact Nat.mul_dvd_mul hpa hpb
  have hN2 : N = 2 * (N / 2) := by
    have h := Nat.div_mul_cancel h2N
    omega
  rw [hN2] at hpp
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : Nat.Coprime (p * p) 2 :=
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).mul_left
      ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hpp2 := hcop.dvd_of_dvd_mul_left hpp
  have hu := hsq2 p hpp2
  rw [Nat.isUnit_iff] at hu
  exact hp.ne_one hu

private theorem gcd_eq_one_or_two (a b N : ℕ) (hN : a * b = N) (h2N : 2 ∣ N)
    (hsq2 : Squarefree (N / 2)) : Nat.gcd a b = 1 ∨ Nat.gcd a b = 2 := by
  by_cases h1 : Nat.gcd a b = 1
  · exact Or.inl h1
  · obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h1
    have hp2 : p = 2 := by
      by_contra hne
      exact odd_prime_not_dvd_gcd a b N hN h2N hsq2 p hp
        (hp.odd_of_ne_two hne) hpg
    have h2g : 2 ∣ Nat.gcd a b := by
      rw [← hp2]
      exact hpg
    by_cases h2 : Nat.gcd a b = 2
    · exact Or.inr h2
    · exfalso
      have hdmc := Nat.div_mul_cancel h2g
      have hne1 : Nat.gcd a b / 2 ≠ 1 := by
        intro hc
        exact h2 (by omega)
      obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd hne1
      have hqg' : q ∣ Nat.gcd a b := by
        have hqdvd : q ∣ Nat.gcd a b / 2 * 2 := dvd_mul_of_dvd_left hqg 2
        rwa [hdmc] at hqdvd
      have hq2 : q = 2 := by
        by_contra hne
        exact odd_prime_not_dvd_gcd a b N hN h2N hsq2 q hq
          (hq.odd_of_ne_two hne) hqg'
      have h4g : 4 ∣ Nat.gcd a b := by
        rw [hq2] at hqg
        obtain ⟨k, hk⟩ := hqg
        exact ⟨k, by omega⟩
      have h4a : 4 ∣ a := dvd_trans h4g (Nat.gcd_dvd_left _ _)
      have h4b : 4 ∣ b := dvd_trans h4g (Nat.gcd_dvd_right _ _)
      have h16 : 16 ∣ N := by
        have h := Nat.mul_dvd_mul h4a h4b
        rw [hN] at h
        norm_num at h
        exact h
      have hN2 := Nat.div_mul_cancel h2N
      obtain ⟨t, ht⟩ := h16
      have h8 : 8 ∣ N / 2 := ⟨t, by omega⟩
      have h4 : 4 ∣ N / 2 := dvd_trans (by norm_num) h8
      have h22 : 2 * 2 ∣ N / 2 := by
        obtain ⟨k, hk⟩ := h4
        exact ⟨k, by omega⟩
      have hu := hsq2 2 h22
      rw [Nat.isUnit_iff] at hu
      omega

private theorem gcd_eq_one_or_two_of_hsq (a b N : ℕ) (hN : a * b = N)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2))) :
    Nat.gcd a b = 1 ∨ Nat.gcd a b = 2 := by
  rcases hsq with h | ⟨h2N, hsq2⟩
  · exact Or.inl (gcd_eq_one_of_squarefree_mul a b N hN h)
  · exact gcd_eq_one_or_two a b N hN h2N hsq2

private theorem exists_linear_sol (c' d : ℤ) (δ₀ N' C' : ℕ)
    (hcopCN : Nat.Coprime C' N')
    (hc'nat : c'.natAbs = C')
    (hcop : IsCoprime ((δ₀ : ℤ) * c') d)
    (hsq : Squarefree (δ₀ * N') ∨ (2 ∣ δ₀ * N' ∧ Squarefree (δ₀ * N' / 2))) :
    ∃ h : ℤ, (N' : ℤ) ∣ (c' * δ₀) * h + (c' - d) := by
  have hN'ne : N' ≠ 0 := by
    intro hz
    subst hz
    rw [mul_zero] at hsq
    have h0 : ¬ Squarefree (0 : ℕ) := fun h => nat_ne_zero_of_squarefree 0 h rfl
    rcases hsq with h | ⟨-, h⟩
    · exact h0 h
    · rw [show (0 : ℕ) / 2 = 0 by omega] at h
      exact h0 h
  have hg'pos : 0 < Nat.gcd δ₀ N' :=
    pos_of_dvd_ne_zero _ _ (Nat.gcd_dvd_right _ _) hN'ne
  have hg12 := gcd_eq_one_or_two_of_hsq δ₀ N' (δ₀ * N') rfl hsq
  have hcopδN' : Nat.Coprime (δ₀ / Nat.gcd δ₀ N') (N' / Nat.gcd δ₀ N') :=
    Nat.coprime_div_gcd_div_gcd hg'pos
  have hNdvd : N' / Nat.gcd δ₀ N' ∣ N' :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have hcopCN' : Nat.Coprime C' (N' / Nat.gcd δ₀ N') :=
    Nat.Coprime.coprime_dvd_right hNdvd hcopCN
  have hcopA : Nat.Coprime (C' * (δ₀ / Nat.gcd δ₀ N')) (N' / Nat.gcd δ₀ N') :=
    Nat.Coprime.mul_left hcopCN' hcopδN'
  have hδ₀eq : δ₀ = (δ₀ / Nat.gcd δ₀ N') * Nat.gcd δ₀ N' :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_left δ₀ N')).symm
  have hN'eq : N' = (N' / Nat.gcd δ₀ N') * Nat.gcd δ₀ N' :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right δ₀ N')).symm
  have hδ₀c : (δ₀ : ℤ) = ((δ₀ / Nat.gcd δ₀ N' : ℕ) : ℤ) * (Nat.gcd δ₀ N' : ℤ) := by
    exact_mod_cast hδ₀eq
  have hN'c : (N' : ℤ) = ((N' / Nat.gcd δ₀ N' : ℕ) : ℤ) * (Nat.gcd δ₀ N' : ℤ) := by
    exact_mod_cast hN'eq
  have hA : c' * (δ₀ : ℤ) = (Nat.gcd δ₀ N' : ℤ)
      * (c' * ((δ₀ / Nat.gcd δ₀ N' : ℕ) : ℤ)) := by
    rw [hδ₀c]
    ring
  have hM : (N' : ℤ) = (Nat.gcd δ₀ N' : ℤ) * (((N' / Nat.gcd δ₀ N' : ℕ)) : ℤ) := by
    rw [hN'c]
    ring
  have hcopAB : IsCoprime (c' * ((δ₀ / Nat.gcd δ₀ N' : ℕ) : ℤ))
      (((N' / Nat.gcd δ₀ N' : ℕ)) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    have e1 : (c' * ((δ₀ / Nat.gcd δ₀ N' : ℕ) : ℤ)).natAbs
        = C' * (δ₀ / Nat.gcd δ₀ N') := by
      rw [Int.natAbs_mul, hc'nat, Int.natAbs_natCast]
    have e2 : ((((N' / Nat.gcd δ₀ N' : ℕ))) : ℤ).natAbs = N' / Nat.gcd δ₀ N' :=
      Int.natAbs_natCast _
    rw [e1, e2]
    exact hcopA
  rcases hg12 with hg1 | hg1
  · exact exists_int_sol _ _ _ _ _ (c' - d) _ hA
      (by rw [hg1, Nat.cast_one, one_mul]) hM hcopAB
  · have h2δ : 2 ∣ δ₀ := by
      rw [← hg1]
      exact Nat.gcd_dvd_left _ _
    have h2N' : 2 ∣ N' := by
      rw [← hg1]
      exact Nat.gcd_dvd_right _ _
    have hC'odd : Odd C' := nat_odd_of_coprime_right_even C' N' hcopCN
      (even_iff_two_dvd.mpr h2N')
    have hc'odd : Odd c' := by
      rw [← Int.natAbs_odd, hc'nat]
      exact hC'odd
    have h2δℤ : (2 : ℤ) ∣ (δ₀ : ℤ) := by exact_mod_cast h2δ
    have hceven : Even ((δ₀ : ℤ) * c') :=
      even_iff_two_dvd.mpr (dvd_mul_of_dvd_left h2δℤ c')
    have hdodd : Odd d := odd_of_coprime_left_even _ _ hcop hceven
    have hBeven : Even (c' - d) := hc'odd.sub_odd hdodd
    obtain ⟨r, hr⟩ := hBeven
    have h2cast : ((2 : ℕ) : ℤ) = 2 := by norm_num
    exact exists_int_sol _ _ _ _ _ r _ hA (by rw [hg1, hr, h2cast]; ring) hM hcopAB

private theorem exists_delta_h (c d : ℤ) (N : ℕ) (hcop : IsCoprime c d)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2))) :
    ∃ δ₀ : ℕ, δ₀ ∣ N ∧ ∃ h : ℤ,
      (N : ℤ) ∣ c * ((δ₀ : ℤ) * h + 1) + d * (-(δ₀ : ℤ)) := by
  have hN0 : N ≠ 0 := N_ne_zero N hsq
  set δ₀ := Nat.gcd c.natAbs N
  have hδ₀N : δ₀ ∣ N := Nat.gcd_dvd_right _ _
  have hδ₀C : δ₀ ∣ c.natAbs := Nat.gcd_dvd_left _ _
  have hδ₀pos : 0 < δ₀ := pos_of_dvd_ne_zero δ₀ N hδ₀N hN0
  obtain ⟨c', hc'⟩ := int_dvd_of_nat_dvd_natAbs δ₀ c hδ₀C
  have hNeq : δ₀ * (N / δ₀) = N := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hδ₀N
  have hcopCN : Nat.Coprime (c.natAbs / δ₀) (N / δ₀) :=
    Nat.coprime_div_gcd_div_gcd hδ₀pos
  have hc'nat : c'.natAbs = c.natAbs / δ₀ := by
    have hC : c.natAbs = δ₀ * c'.natAbs := by
      rw [hc', Int.natAbs_mul, Int.natAbs_natCast]
    rw [hC, Nat.mul_div_cancel_left _ hδ₀pos]
  have hcop' : IsCoprime ((δ₀ : ℤ) * c') d := by
    rw [← hc']
    exact hcop
  have hsq' : Squarefree (δ₀ * (N / δ₀)) ∨
      (2 ∣ δ₀ * (N / δ₀) ∧ Squarefree (δ₀ * (N / δ₀) / 2)) := by
    rwa [hNeq]
  obtain ⟨h, hsol⟩ := exists_linear_sol c' d δ₀ (N / δ₀) (c.natAbs / δ₀)
    hcopCN hc'nat hcop' hsq'
  refine ⟨δ₀, hδ₀N, h, ?_⟩
  have hNc : (N : ℤ) = (δ₀ : ℤ) * ((N / δ₀ : ℕ) : ℤ) := by
    exact_mod_cast hNeq.symm
  rw [hNc, hc']
  have hsol' := mul_dvd_mul_left ((δ₀ : ℤ)) hsol
  obtain ⟨k, hk⟩ := hsol'
  exact ⟨k, by linear_combination hk⟩

private theorem eq_gcd_of_valid (c d : ℤ) (N : ℕ) (hcop : IsCoprime c d)
    (δ : ℕ) (hδN : δ ∣ N) (h : ℤ)
    (hdiv : (N : ℤ) ∣ c * ((δ : ℤ) * h + 1) + d * (-(δ : ℤ))) :
    δ = Nat.gcd c.natAbs N := by
  have hdiv' : (N : ℤ) ∣ c + (δ : ℤ) * (c * h - d) := by
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by linear_combination hk⟩
  have hδc : (δ : ℤ) ∣ c := by
    have h1 : (δ : ℤ) ∣ (N : ℤ) := by exact_mod_cast hδN
    have h2 := dvd_trans h1 hdiv'
    have h3 : (δ : ℤ) ∣ (δ : ℤ) * (c * h - d) := dvd_mul_right _ _
    have h4 := dvd_sub h2 h3
    obtain ⟨k, hk⟩ := h4
    exact ⟨k, by linear_combination hk⟩
  have hδC : δ ∣ c.natAbs := nat_dvd_natAbs_of_int_dvd δ c hδc
  have hδδ₀ : δ ∣ Nat.gcd c.natAbs N := Nat.dvd_gcd hδC hδN
  have hδ₀C : Nat.gcd c.natAbs N ∣ c.natAbs := Nat.gcd_dvd_left _ _
  have hδ₀N : Nat.gcd c.natAbs N ∣ N := Nat.gcd_dvd_right _ _
  have hδ₀c : ((Nat.gcd c.natAbs N : ℕ) : ℤ) ∣ c :=
    int_dvd_of_nat_dvd_natAbs _ _ hδ₀C
  have hδ₀e : ((Nat.gcd c.natAbs N : ℕ) : ℤ) ∣ (δ : ℤ) * (c * h - d) := by
    have h1 : ((Nat.gcd c.natAbs N : ℕ) : ℤ) ∣ (N : ℤ) := by exact_mod_cast hδ₀N
    have h2 := dvd_trans h1 hdiv'
    have h4 := dvd_sub h2 hδ₀c
    obtain ⟨k, hk⟩ := h4
    exact ⟨k, by linear_combination hk⟩
  have hcopδE : Nat.Coprime (Nat.gcd c.natAbs N) (c * h - d).natAbs := by
    by_contra hnc
    rw [Nat.coprime_iff_gcd_eq_one] at hnc
    have hne1 : Nat.gcd (Nat.gcd c.natAbs N) (c * h - d).natAbs ≠ 1 := hnc
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne1
    have hpδ : p ∣ Nat.gcd c.natAbs N :=
      dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpE : p ∣ (c * h - d).natAbs :=
      dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hpc : (p : ℤ) ∣ c :=
      int_dvd_of_nat_dvd_natAbs p c (dvd_trans hpδ hδ₀C)
    have hpe : (p : ℤ) ∣ c * h - d :=
      int_dvd_of_nat_dvd_natAbs p _ hpE
    have hpd : (p : ℤ) ∣ d := by
      have hch : (p : ℤ) ∣ c * h := dvd_mul_of_dvd_left hpc h
      have hsub := dvd_sub hch hpe
      obtain ⟨k, hk⟩ := hsub
      exact ⟨k, by linear_combination hk⟩
    have hcopCD := Int.isCoprime_iff_nat_coprime.mp hcop
    have hpC : p ∣ c.natAbs := dvd_trans hpδ hδ₀C
    have hpD : p ∣ d.natAbs := nat_dvd_natAbs_of_int_dvd p d hpd
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpC hpD hcopCD
  have hδ₀δe : Nat.gcd c.natAbs N ∣ δ * (c * h - d).natAbs := by
    have h := nat_dvd_natAbs_of_int_dvd (Nat.gcd c.natAbs N)
      ((δ : ℤ) * (c * h - d)) hδ₀e
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at h
  have hδ₀δ : Nat.gcd c.natAbs N ∣ δ :=
    Nat.Coprime.dvd_of_dvd_mul_right hcopδE hδ₀δe
  exact Nat.dvd_antisymm hδδ₀ hδ₀δ

/-- **Double coset representatives for $\Gamma_0(N)$.** Let $N$ be a natural number such that
either $N$ is squarefree, or $N$ is even and $N/2$ is squarefree. Write $\Gamma_0(N)$ for the
group of matrices in $\mathrm{SL}_2(\mathbb{Z})$ whose lower left entry is divisible by $N$, and
$T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. Then for every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$ there is exactly one natural number $\delta$ dividing $N$
for which there exist $A \in \Gamma_0(N)$ and an integer $h$ with
$$\gamma = A \begin{pmatrix} 1 & 0 \\ \delta & 1 \end{pmatrix} T^h.$$

Equivalently, the matrices $\begin{pmatrix} 1 & 0 \\ \delta & 1 \end{pmatrix}$ with
$\delta \mid N$ form a complete set of representatives, without repetition, of the double cosets
$\Gamma_0(N) \backslash \mathrm{SL}_2(\mathbb{Z}) / \Gamma_\infty$, where $\Gamma_\infty$ is
generated by $T$; adding $-I$ to $\Gamma_\infty$ changes nothing, as $-I \in \Gamma_0(N)$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 3 (`integers-2025-A3-lem-3`), quoting Wang, Lemma 4.3.
"`N / 2` is squarefree" is read with `2 ∣ N`. -/
public theorem exists_gamma0_lowerUnipotent_T_zpow_decomposition (N : ℕ)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃! δ : ℕ, δ ∣ N ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 N, ∃ h : ℤ,
      γ = A * ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩ * ModularGroup.T ^ h := by
  have hcopγ := bottom_row_coprime γ
  obtain ⟨δ₀, hδ₀N, h, hdiv⟩ := exists_delta_h _ _ _ hcopγ hsq
  have hδ₀eq : δ₀ = Nat.gcd (γ.1 1 0).natAbs N :=
    eq_gcd_of_valid _ _ _ hcopγ δ₀ hδ₀N h hdiv
  refine ⟨δ₀, ⟨hδ₀N, γ * (lowerUnipotent δ₀ * ModularGroup.T ^ h)⁻¹,
    (gamma_mem_iff N γ δ₀ h).mpr hdiv, h, ?_⟩, ?_⟩
  · have hγ := gamma_factor γ δ₀ h
    rw [← mul_assoc] at hγ
    exact hγ
  · intro δ hδ
    obtain ⟨hδN, A, hA, h', hγ'⟩ := hδ
    have hγB : γ = A * (lowerUnipotent δ * ModularGroup.T ^ h') := by
      rw [← mul_assoc]
      exact hγ'
    have hAeq : A = γ * (lowerUnipotent δ * ModularGroup.T ^ h')⁻¹ := by
      rw [hγB]
      group
    have hAmem : γ * (lowerUnipotent δ * ModularGroup.T ^ h')⁻¹
        ∈ CongruenceSubgroup.Gamma0 N := by
      rw [← hAeq]
      exact hA
    have hdiv' := (gamma_mem_iff N γ δ h').mp hAmem
    have hδeq := eq_gcd_of_valid _ _ _ hcopγ δ hδN h' hdiv'
    exact hδeq.trans hδ₀eq.symm

end MetaMathlibExt
