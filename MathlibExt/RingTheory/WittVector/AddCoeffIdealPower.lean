/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow.lean`
and
`P2M/Sol/S_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow.lean`
and the supporting
`Theorems/Thm_WittVector_isWeightedHomogeneous_wittStructureInt.lean`
and
`P2M/Sol/S_WittVector_isWeightedHomogeneous_wittStructureInt.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.RingTheory.WittVector.Basic

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

namespace WittVector

private theorem isWeightedHomogeneous_sub {σ M R : Type*} [CommRing R]
    [AddCommMonoid M] {w : σ → M} {φ ψ : MvPolynomial σ R} {m : M}
    (hφ : MvPolynomial.IsWeightedHomogeneous w φ m)
    (hψ : MvPolynomial.IsWeightedHomogeneous w ψ m) :
    MvPolynomial.IsWeightedHomogeneous w (φ - ψ) m := by
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at hφ hψ ⊢
  exact Submodule.sub_mem _ hφ hψ

private theorem isWeightedHomogeneous_bind₁ {σ τ R : Type*} [CommRing R]
    (w : τ → ℕ) (f : σ → MvPolynomial τ R) (m : ℕ)
    (hf : ∀ b, MvPolynomial.IsWeightedHomogeneous w (f b) m)
    (Φ : MvPolynomial σ R) (k : ℕ) (hΦ : Φ.IsHomogeneous k) :
    MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.bind₁ f Φ) (k * m) := by
  classical
  rw [Φ.as_sum, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [MvPolynomial.bind₁_monomial]
  have hk : ∑ i ∈ d.support, d i = k := by
    have h := hΦ (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    simpa using h
  have h := (MvPolynomial.IsWeightedHomogeneous.prod d.support
    (fun i => f i ^ d i) (fun i => d i • m)
    fun i _ => (hf i).pow (d i)).C_mul (Φ.coeff d)
  rw [← Finset.sum_smul, hk, smul_eq_mul] at h
  exact h

private theorem isWeightedHomogeneous_rename_wittPolynomial (p : ℕ) [Fact p.Prime]
    {idx R : Type*} [CommRing R] (b : idx) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2)
      (MvPolynomial.rename (fun i => (b, i)) (wittPolynomial p R n)) (p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
  rw [map_mul, MvPolynomial.rename_C, map_pow (MvPolynomial.rename (fun i => (b, i))),
    MvPolynomial.rename_X]
  have h := ((MvPolynomial.isWeightedHomogeneous_X R
    (fun bi : idx × ℕ => p ^ bi.2) (b, i)).pow (p ^ (n - i))).C_mul ((p : R) ^ i)
  rw [smul_eq_mul, ← pow_add,
    Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))] at h
  exact h

private theorem isWeightedHomogeneous_wittStructureRat (p : ℕ) [Fact p.Prime]
    {idx : Type*} (Φ : MvPolynomial idx ℚ) (k : ℕ) (hΦ : Φ.IsHomogeneous k) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2)
      (wittStructureRat p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [wittStructureRat_rec]
    refine (isWeightedHomogeneous_sub ?_ ?_).C_mul _
    · exact isWeightedHomogeneous_bind₁ _ _ (p ^ n)
        (fun b => isWeightedHomogeneous_rename_wittPolynomial (R := ℚ) p b n) Φ k hΦ
    · refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h := ((ih i hi').pow (p ^ (n - i))).C_mul ((p : ℚ) ^ i)
      rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le] at h
      exact h

private theorem isWeightedHomogeneous_wittStructureInt (p : ℕ) [Fact p.Prime]
    {idx : Type*} (Φ : MvPolynomial idx ℤ) (k : ℕ) (hΦ : Φ.IsHomogeneous k) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2)
      (wittStructureInt p Φ n) (k * p ^ n) := by
  intro d hd
  have hΦ' : (MvPolynomial.map (Int.castRingHom ℚ) Φ).IsHomogeneous k := hΦ.map _
  have h := isWeightedHomogeneous_wittStructureRat p _ k hΦ' n
  rw [← map_wittStructureInt] at h
  refine h ?_
  rw [MvPolynomial.coeff_map]
  intro h0
  simp only [eq_intCast, Int.cast_eq_zero] at h0
  exact hd h0

private theorem sub_one_mul_geom_add_one (p e : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ k ∈ Finset.range e, p ^ k) + 1 = p ^ e := by
  induction e with
  | zero => simp
  | succ e IH =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, IH, pow_succ]
    have h : (p - 1) * p ^ e + p ^ e = p ^ e * p := by
      rw [mul_comm, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    omega

private theorem padicValNat_factorial_prime_pow (p : ℕ) [hp : Fact p.Prime] (e : ℕ) :
    padicValNat p (p ^ e).factorial = ∑ k ∈ Finset.range e, p ^ k := by
  induction e with
  | zero => simp [Nat.padicValNat_def]
  | succ e IH =>
    rw [Nat.padicValNat_def] at IH ⊢
    rw [pow_succ, mul_comm, multiplicity_factorial_mul, IH, Finset.sum_range_succ]

private theorem sub_one_mul_padicValNat_factorial_prime_pow (p : ℕ) [hp : Fact p.Prime]
    (e : ℕ) : (p - 1) * padicValNat p (p ^ e).factorial + 1 = p ^ e := by
  rw [padicValNat_factorial_prime_pow, sub_one_mul_geom_add_one p e hp.out.one_lt.le]

private theorem padicValNat_le_of_dvd (p : ℕ) [hp : Fact p.Prime] {a b : ℕ} (hb : b ≠ 0)
    (h : a ∣ b) : padicValNat p a ≤ padicValNat p b := by
  simp only [Nat.padicValNat_def]
  exact (multiplicity_dvd_iff_le hb).mp ((pow_multiplicity_dvd p a).trans h)

private theorem sum_mul_sub_one_le (p : ℕ) [hp : Fact p.Prime] {ι : Type*}
    (s : Finset ι) (a e : ι → ℕ) :
    ∑ t ∈ s, a t * (p ^ e t - 1) ≤
      (p - 1) * padicValNat p (∑ t ∈ s, a t * p ^ e t).factorial := by
  classical
  have hdvd : (∏ x ∈ s.sigma fun t => Finset.range (a t), (p ^ e x.1).factorial) ∣
      (∑ x ∈ s.sigma fun t => Finset.range (a t), p ^ e x.1).factorial :=
    Nat.prod_factorial_dvd_factorial_sum _ _
  have hsum : (∑ x ∈ s.sigma fun t => Finset.range (a t), p ^ e x.1) =
      ∑ t ∈ s, a t * p ^ e t := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hprod : (∏ x ∈ s.sigma fun t => Finset.range (a t), (p ^ e x.1).factorial) =
      ∏ t ∈ s, ((p ^ e t).factorial) ^ a t := by
    rw [Finset.prod_sigma]
    refine Finset.prod_congr rfl fun t _ => ?_
    dsimp only
    rw [Finset.prod_const, Finset.card_range]
  rw [hsum, hprod] at hdvd
  have hle := padicValNat_le_of_dvd p (Nat.factorial_ne_zero _) hdvd
  have hval : padicValNat p (∏ t ∈ s, ((p ^ e t).factorial) ^ a t) =
      ∑ t ∈ s, a t * padicValNat p (p ^ e t).factorial := by
    simp only [Nat.padicValNat_def]
    rw [← Nat.factorization_def _ hp.out, Nat.factorization_prod fun t _ =>
      pow_ne_zero _ (Nat.factorial_ne_zero _)]
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_def _ hp.out]
  rw [hval] at hle
  calc ∑ t ∈ s, a t * (p ^ e t - 1)
      = ∑ t ∈ s, a t * ((p - 1) * padicValNat p (p ^ e t).factorial) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have h := sub_one_mul_padicValNat_factorial_prime_pow p (e t)
        congr 1; omega
    _ = (p - 1) * ∑ t ∈ s, a t * padicValNat p (p ^ e t).factorial := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ ≤ (p - 1) * padicValNat p (∑ t ∈ s, a t * p ^ e t).factorial :=
        Nat.mul_le_mul_left _ hle

private theorem sub_one_mul_padicValNat_factorial_add_le (p : ℕ) [hp : Fact p.Prime]
    {M n : ℕ} (hM : M < p ^ n) :
    (p - 1) * (padicValNat p M.factorial + n) + 1 ≤ p ^ n := by
  have hdvd : p ^ n * M.factorial ∣ (p ^ n).factorial := by
    have h1 : M.factorial ∣ (p ^ n - 1).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have h2 : p ^ n * (p ^ n - 1).factorial = (p ^ n).factorial :=
      Nat.mul_factorial_pred (pow_pos hp.out.pos n).ne'
    rw [← h2]
    exact Nat.mul_dvd_mul_left _ h1
  have hle := padicValNat_le_of_dvd p (Nat.factorial_ne_zero _) hdvd
  rw [Nat.padicValNat_def,
    Nat.multiplicity_mul (pow_ne_zero _ hp.out.ne_zero) (Nat.factorial_ne_zero _),
    Nat.multiplicity_prime_pow, ← Nat.padicValNat_def] at hle
  have hmono : (p - 1) * (padicValNat p M.factorial + n) ≤
      (p - 1) * padicValNat p (p ^ n).factorial :=
    Nat.mul_le_mul_left _ (by omega)
  have h := sub_one_mul_padicValNat_factorial_prime_pow p n
  omega

private theorem carry_ineq (p : ℕ) [hp : Fact p.Prime] {ι : Type*} (s : Finset ι)
    (a e : ι → ℕ) (n W : ℕ) (hW : 1 ≤ W) (h : ∑ t ∈ s, a t * p ^ e t + W = p ^ n) :
    (p - 1) * n + 1 ≤ ∑ t ∈ s, a t + W := by
  have h1 := sum_mul_sub_one_le p s a e
  have h2 := sub_one_mul_padicValNat_factorial_add_le p
    (M := ∑ t ∈ s, a t * p ^ e t) (n := n) (by omega)
  have h3 : ∑ t ∈ s, a t * (p ^ e t - 1) + ∑ t ∈ s, a t = ∑ t ∈ s, a t * p ^ e t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have ht : 1 ≤ p ^ e t := Nat.one_le_pow _ _ hp.out.pos
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ ht)]
  have h4 : (p - 1) * (padicValNat p (∑ t ∈ s, a t * p ^ e t).factorial + n) =
      (p - 1) * padicValNat p (∑ t ∈ s, a t * p ^ e t).factorial + (p - 1) * n := by
    ring
  omega

private theorem prod_mem_pow_sum {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*}
    (s : Finset ι) (f : ι → R) (e : ι → ℕ) (h : ∀ t ∈ s, f t ∈ I ^ e t) :
    ∏ t ∈ s, f t ∈ I ^ ∑ t ∈ s, e t := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod h

/-- The `n`-th coefficient of a sum of Witt vectors differs from the `n`-th
coefficient of the first summand by an element of a high power of `I`, when
every coefficient of the first summand lies in `I` and the `i`-th coefficient
of the second summand lies in `I ^ (p ^ i + c)`. -/
theorem add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
    (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] (I : Ideal R) (c : ℕ)
    (x y : WittVector p R) (hx : ∀ i : ℕ, x.coeff i ∈ I)
    (hy : ∀ i : ℕ, y.coeff i ∈ I ^ (p ^ i + c)) (n : ℕ) :
    (x + y).coeff n - x.coeff n ∈ I ^ ((p - 1) * n + 1 + c) := by
  classical
  set S := WittVector.wittAdd p n with hS
  have hhom : MvPolynomial.IsWeightedHomogeneous
      (fun bi : Fin 2 × ℕ => p ^ bi.2) S (1 * p ^ n) :=
    isWeightedHomogeneous_wittStructureInt p (MvPolynomial.X 0 + MvPolynomial.X 1) 1
      ((MvPolynomial.isHomogeneous_X ℤ 0).add (MvPolynomial.isHomogeneous_X ℤ 1)) n
  have key : ∀ z : WittVector p R, (x + z).coeff n =
      ∑ d ∈ S.support, (algebraMap ℤ R) (S.coeff d) *
        ∏ bi ∈ d.support, Function.uncurry ![x.coeff, z.coeff] bi ^ d bi := by
    intro z
    rw [WittVector.add_coeff, WittVector.peval, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_eq]
  have hx0 : x.coeff n = (x + 0).coeff n := by rw [add_zero]
  rw [hx0, key y, key 0, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← mul_sub]
  refine Ideal.mul_mem_left _ _ ?_
  set A := d.support.filter fun bi : Fin 2 × ℕ => bi.1 = 0 with hA
  set B := d.support.filter fun bi : Fin 2 × ℕ => ¬ bi.1 = 0 with hB
  have hval0 : ∀ (z : WittVector p R), ∀ bi ∈ A,
      Function.uncurry ![x.coeff, z.coeff] bi = x.coeff bi.2 := by
    intro z bi hbi
    rw [hA, Finset.mem_filter] at hbi
    obtain ⟨b, i⟩ := bi
    simp only at hbi
    rw [hbi.2]
    rfl
  have hval1 : ∀ (z : WittVector p R), ∀ bi ∈ B,
      Function.uncurry ![x.coeff, z.coeff] bi = z.coeff bi.2 := by
    intro z bi hbi
    rw [hB, Finset.mem_filter] at hbi
    obtain ⟨b, i⟩ := bi
    simp only at hbi
    have hb : b = 1 := by
      fin_cases b
      · exact absurd rfl hbi.2
      · rfl
    subst hb
    rfl
  have hsplit : ∀ z : WittVector p R,
      ∏ bi ∈ d.support, Function.uncurry ![x.coeff, z.coeff] bi ^ d bi =
        (∏ bi ∈ A, x.coeff bi.2 ^ d bi) * ∏ bi ∈ B, z.coeff bi.2 ^ d bi := by
    intro z
    rw [← Finset.prod_filter_mul_prod_filter_not d.support
      (fun bi : Fin 2 × ℕ => bi.1 = 0)]
    congr 1
    · exact Finset.prod_congr rfl fun bi hbi => by rw [hval0 z bi hbi]
    · exact Finset.prod_congr rfl fun bi hbi => by rw [hval1 z bi hbi]
  rw [hsplit y, hsplit 0, ← mul_sub]
  by_cases hBe : B = ∅
  · rw [hBe, Finset.prod_empty, Finset.prod_empty, sub_self, mul_zero]
    exact Ideal.zero_mem _
  obtain ⟨bi₀, hbi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
  have hd0 : ∀ bi ∈ B, d bi ≠ 0 := fun bi hbi => by
    rw [hB, Finset.mem_filter] at hbi
    exact Finsupp.mem_support_iff.mp hbi.1
  have hzero : ∏ bi ∈ B, (0 : WittVector p R).coeff bi.2 ^ d bi = 0 :=
    Finset.prod_eq_zero hbi₀ (by rw [WittVector.zero_coeff, zero_pow (hd0 bi₀ hbi₀)])
  rw [hzero, sub_zero]
  have hmemA : ∏ bi ∈ A, x.coeff bi.2 ^ d bi ∈ I ^ ∑ bi ∈ A, d bi :=
    prod_mem_pow_sum I A _ _ fun bi _ => Ideal.pow_mem_pow (hx _) _
  have hmemB : ∏ bi ∈ B, y.coeff bi.2 ^ d bi ∈
      I ^ ∑ bi ∈ B, d bi * (p ^ bi.2 + c) :=
    prod_mem_pow_sum I B _ _ fun bi _ => by
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (hy _) _
  have hmem : (∏ bi ∈ A, x.coeff bi.2 ^ d bi) * ∏ bi ∈ B, y.coeff bi.2 ^ d bi ∈
      I ^ (∑ bi ∈ A, d bi + ∑ bi ∈ B, d bi * (p ^ bi.2 + c)) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hmemA hmemB
  refine Ideal.pow_le_pow_right ?_ hmem
  have hw : ∑ bi ∈ A, d bi * p ^ bi.2 + ∑ bi ∈ B, d bi * p ^ bi.2 = p ^ n := by
    have h := hhom (MvPolynomial.mem_support_iff.mp hd)
    rw [one_mul, Finsupp.weight_apply, Finsupp.sum] at h
    rw [← h, ← Finset.sum_filter_add_sum_filter_not d.support
      (fun bi : Fin 2 × ℕ => bi.1 = 0)]
    simp only [smul_eq_mul, hA, hB]
  have hW : 1 ≤ ∑ bi ∈ B, d bi * p ^ bi.2 := by
    have ht : 1 ≤ d bi₀ * p ^ bi₀.2 :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (hd0 bi₀ hbi₀) (pow_ne_zero _ hp.out.ne_zero))
    exact ht.trans (Finset.single_le_sum (f := fun bi => d bi * p ^ bi.2)
      (fun _ _ => Nat.zero_le _) hbi₀)
  have hcarry := carry_ineq p A (fun bi => d bi) (fun bi => bi.2) n _ hW hw
  have hBsum : ∑ bi ∈ B, d bi * p ^ bi.2 + c ≤
      ∑ bi ∈ B, d bi * (p ^ bi.2 + c) := by
    have hc : c ≤ ∑ bi ∈ B, d bi * c := by
      have ht : c ≤ d bi₀ * c :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hd0 bi₀ hbi₀))
      exact ht.trans (Finset.single_le_sum (f := fun bi => d bi * c)
        (fun _ _ => Nat.zero_le _) hbi₀)
    rw [show (∑ bi ∈ B, d bi * (p ^ bi.2 + c)) =
        ∑ bi ∈ B, d bi * p ^ bi.2 + ∑ bi ∈ B, d bi * c by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    omega
  omega

end WittVector
