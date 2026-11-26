/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem.lean`
and
`P2M/Sol/S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem.lean`
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

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

open Polynomial

private theorem prod_sub_prod_mem_pow {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (I : Ideal R) (P L : ι → R)
    (hL : ∀ i ∈ s, L i ∈ I) (hPL : ∀ i ∈ s, P i - L i ∈ I ^ 2) :
    (∏ i ∈ s, P i) - (∏ i ∈ s, L i) ∈ I ^ (s.card + 1) ∧
      (∏ i ∈ s, L i) ∈ I ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
      (fun i hi => hPL i (Finset.mem_insert_of_mem hi))
    have hLa : L a ∈ I := hL a (Finset.mem_insert_self a s)
    have hPLa : P a - L a ∈ I ^ 2 := hPL a (Finset.mem_insert_self a s)
    have hPa : P a ∈ I := by
      have h := I.add_mem (Ideal.pow_le_self two_ne_zero hPLa) hLa
      simpa using h
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Finset.card_insert_of_notMem ha]
    refine ⟨?_, ?_⟩
    · have hsplit : P a * ∏ i ∈ s, P i - L a * ∏ i ∈ s, L i =
          P a * (∏ i ∈ s, P i - ∏ i ∈ s, L i) + (P a - L a) * ∏ i ∈ s, L i := by
        ring
      rw [hsplit]
      refine Ideal.add_mem _ ?_ ?_
      · have h := Ideal.mul_mem_mul hPa ih1
        rwa [← pow_succ'] at h
      · have h := Ideal.mul_mem_mul hPLa ih2
        rwa [← pow_add, show 2 + s.card = s.card + 1 + 1 by omega] at h
    · have h := Ideal.mul_mem_mul hLa ih2
      rwa [← pow_succ'] at h

private theorem prod_X_add_C_mul (q : ℕ) [Fact q.Prime] [NeZero q] :
    ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X)) =
      X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  set p : Polynomial (Polynomial (ZMod q)) :=
    X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X with hp
  have hdeg1 : (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hmonic : p.Monic := by
    apply (monic_X_pow q).sub_of_left
    calc degree (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X) ≤ 1 := by
            exact (degree_le_natDegree).trans (by exact_mod_cast hdeg1)
      _ < degree ((X : Polynomial (Polynomial (ZMod q))) ^ q) := by
            rw [degree_X_pow]; exact_mod_cast hq1
  have hnat : p.natDegree = q := by
    rw [hp, natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
    exact lt_of_le_of_lt hdeg1 hq1
  have hroot : ∀ c : ZMod q, p.IsRoot (C c * X) := by
    intro c
    have hc : c ^ q = c := by
      have h := FiniteField.pow_card (K := ZMod q) c
      rwa [ZMod.card] at h
    simp only [hp, IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C, mul_pow,
      ← C_pow, hc]
    rw [sub_eq_zero, mul_comm (X ^ (q - 1)) (C c * X), mul_assoc,
      mul_pow_sub_one hq0]
  have hinj : Function.Injective (fun c : ZMod q => C c * (X : Polynomial (ZMod q))) := by
    intro c d h
    have := congrArg (fun f : Polynomial (ZMod q) => f.coeff 1) h
    simpa using this
  set m : Multiset (Polynomial (ZMod q)) :=
    (Finset.univ : Finset (ZMod q)).val.map (fun c => C c * X) with hm
  have hm_nodup : m.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
  have hm_le : m ≤ p.roots := by
    rw [Multiset.le_iff_subset hm_nodup]
    intro a ha
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hmonic.ne_zero).mpr (hroot c)
  have hcard : m.card = q := by simp [hm, ZMod.card]
  have hroots : p.roots = m :=
    (Multiset.eq_of_le_of_card_le hm_le
      (by rw [hcard]; exact (card_roots' p).trans hnat.le)).symm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    (by rw [hroots, hcard, hnat])
  rw [hroots, hm, Multiset.map_map] at hprod
  calc ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X))
      = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C (-c) * X)) :=
          Finset.prod_congr rfl (fun c _ => by simp)
    _ = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C c * X)) :=
          Fintype.prod_equiv (Equiv.neg (ZMod q)) _ _ (fun c => rfl)
    _ = (Multiset.map ((fun a => X - C a) ∘ fun c => C c * X)
          (Finset.univ : Finset (ZMod q)).val).prod := by
          rw [Finset.prod_eq_multiset_prod]; rfl
    _ = p := hprod

private theorem prod_add_mul_eq (q : ℕ) [Fact q.Prime] [NeZero q] {B : Type*} [CommRing B]
    (ψ : ZMod q →+* B) (a b : B) :
    ∏ c : ZMod q, (a + ψ c * b) = a ^ q - b ^ (q - 1) * a := by
  have h := congrArg (eval₂RingHom (eval₂RingHom ψ b) a) (prod_X_add_C_mul q)
  simp only [map_prod, map_add, map_sub, map_mul, map_pow] at h
  simpa [Polynomial.coe_eval₂RingHom, eval₂_X, eval₂_C] using h

private noncomputable def drinP (q : ℕ) [NeZero q] : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 * ∏ c : ZMod q,
    (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0) -
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1)

private theorem drinP_isHomogeneous (q : ℕ) [Fact q.Prime] [NeZero q] :
    (drinP q).IsHomogeneous (q + 1) := by
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  have hlin : ∀ c : ZMod q,
      (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := by
    intro c
    refine hX1.add ?_
    have := (MvPolynomial.isHomogeneous_C (Fin 2) (((c.val : ℕ) : ℤ))).mul hX0
    rwa [zero_add] at this
  have hprod : (∏ c : ZMod q, (MvPolynomial.X 1 +
      MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) ℤ)).IsHomogeneous q := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (ZMod q)) _
      (fun _ => 1) (fun c _ => hlin c)
    rwa [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at this
  unfold drinP
  refine MvPolynomial.IsHomogeneous.sub ?_ (MvPolynomial.IsHomogeneous.sub ?_ ?_)
  · have := hX0.mul hprod; rwa [add_comm] at this
  · have := hX0.mul (hX1.pow q); rwa [one_mul, add_comm] at this
  · have := (hX0.pow q).mul hX1; rwa [one_mul] at this

private theorem map_drinP_eq_zero (q : ℕ) [Fact q.Prime] [NeZero q] :
    MvPolynomial.map (Int.castRingHom (ZMod q)) (drinP q) = 0 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have key := prod_add_mul_eq q (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)))
    (MvPolynomial.X 1) (MvPolynomial.X 0)
  unfold drinP
  simp only [map_sub, map_mul, map_prod, map_add, map_pow, MvPolynomial.map_X,
    MvPolynomial.map_C, map_natCast]
  have hC : ∀ c : ZMod q, ((c.val : ℕ) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c
    rw [← map_natCast (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q))),
      ZMod.natCast_zmod_val]
  have hC2 : ∀ c : ZMod q,
      (MvPolynomial.C ((c.val : ℕ) : ZMod q) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c; rw [ZMod.natCast_zmod_val]; rfl
  simp only [hC, hC2]
  rw [key, ← pow_sub_one_mul hq0 (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod q))]
  ring

private theorem dvd_coeff_drinP (q : ℕ) [Fact q.Prime] [NeZero q] (m : Fin 2 →₀ ℕ) :
    (q : ℤ) ∣ (drinP q).coeff m := by
  have h := congrArg (fun p : MvPolynomial (Fin 2) (ZMod q) => p.coeff m)
    (map_drinP_eq_zero q)
  rw [MvPolynomial.coeff_map] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by simpa using h)

/-- For a prime `q` whose cast lies in an ideal `𝔪`, elements `x₀, x₁ ∈ 𝔪`,
and approximations `P c` to `x₁ + ((c.val : ℕ) : R) * x₀` modulo `𝔪 ^ 2`,
where `c.val` is the canonical natural representative of `c : ZMod q`, the
product of the approximations, multiplied by `x₀`, agrees with
`x₀ * x₁ ^ q - x₀ ^ q * x₁` modulo `𝔪 ^ (q + 2)`. -/
public theorem Ideal.mul_prod_sub_mem_pow_of_sub_mem_sq_of_natCast_mem
    (q : ℕ) [Fact q.Prime] {R : Type*} [CommRing R] (𝔪 : Ideal R)
    (hq : ((q : ℕ) : R) ∈ 𝔪) (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R)
    (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨h1, -⟩ := prod_sub_prod_mem_pow (Finset.univ : Finset (ZMod q)) 𝔪 P
    (fun c => x₁ + ((c.val : ℕ) : R) * x₀)
    (fun c _ => 𝔪.add_mem hx₁ (𝔪.mul_mem_left _ hx₀)) (fun c _ => hP c)
  rw [Finset.card_univ, ZMod.card] at h1
  have h3 : x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) -
      (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
    have heval : MvPolynomial.eval₂Hom (Int.castRingHom R) (![x₀, x₁] : Fin 2 → R)
        (drinP q) =
        x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) -
          (x₀ * x₁ ^ q - x₀ ^ q * x₁) := by
      unfold drinP
      simp only [map_sub, map_mul, map_prod, map_add, map_pow,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, map_natCast,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← heval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨k, hk⟩ := dvd_coeff_drinP q m
    have hdeg : m 0 + m 1 = q + 1 := by
      have hw := drinP_isHomogeneous q (MvPolynomial.mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hw
    rw [hk, map_mul, map_natCast, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hmon : x₀ ^ m 0 * x₁ ^ m 1 ∈ 𝔪 ^ (q + 1) := by
      rw [← hdeg, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx₀ _) (Ideal.pow_mem_pow hx₁ _)
    have hmem : ((q : ℕ) : R) * (Int.castRingHom R k) * (x₀ ^ m 0 * x₁ ^ m 1) ∈
        𝔪 ^ (q + 2) := by
      rw [pow_succ']; exact Ideal.mul_mem_mul (𝔪.mul_mem_right _ hq) hmon
    simpa [mul_assoc] using hmem
  have hsplit : x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) =
      x₀ * ((∏ c : ZMod q, P c) -
        ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀)) +
        (x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) -
          (x₀ * x₁ ^ q - x₀ ^ q * x₁)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ h3
  have h := Ideal.mul_mem_mul hx₀ h1
  rwa [← pow_succ', show q + 1 + 1 = q + 2 by ring] at h
