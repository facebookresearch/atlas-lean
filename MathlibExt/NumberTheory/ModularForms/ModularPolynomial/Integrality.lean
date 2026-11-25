/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean`,
`P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean`,
`Theorems/Thm_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean`,
and
`P2M/Sol/S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean`
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

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.PhiGen
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Polynomial

namespace ModularCurve

namespace PhiGen

section JqIntegrality

private theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

private theorem intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by
  intro m
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  by_cases hneg : (m - -(n : ℤ)) < 0
  · exact ⟨0, by rw [ofPowerSeries_coeff_of_neg _ hneg, Int.cast_zero]⟩
  · refine ⟨(PowerSeries.coeff (m - -(n : ℤ)).toNat (jNum ^ n) : ℤ), ?_⟩
    have hcast : (m - -(n : ℤ)) = (((m - -(n : ℤ)).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (not_lt.mp hneg)).symm
    rw [hcast, HahnSeries.ofPowerSeries_apply_coeff]
    change PowerSeries.coeff _ (jNumQ ^ n) = _
    rw [jNumQ, ← map_pow, PowerSeries.coeff_map]
    rfl

private theorem intCoeffs_jq : IntCoeffs jq := by
  have h := intCoeffs_jq_pow 1
  rwa [pow_one] at h

end JqIntegrality

section IntegralCoeffs

variable {K : Type*} [Field K]

private def CoeffsIntegral (f : LaurentSeries K) : Prop :=
  ∀ m : ℤ, f.coeff m ∈ integralClosure ℤ K

private theorem coeffsIntegral_zero : CoeffsIntegral (0 : LaurentSeries K) := fun _ =>
  Subalgebra.zero_mem _

private theorem coeffsIntegral_one : CoeffsIntegral (1 : LaurentSeries K) := by
  intro m
  rw [HahnSeries.coeff_one]
  split
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

private theorem CoeffsIntegral.neg {f : LaurentSeries K} (hf : CoeffsIntegral f) :
    CoeffsIntegral (-f) := by
  intro m
  rw [HahnSeries.coeff_neg]
  exact Subalgebra.neg_mem _ (hf m)

private theorem CoeffsIntegral.mul {f g : LaurentSeries K} (hf : CoeffsIntegral f)
    (hg : CoeffsIntegral g) : CoeffsIntegral (f * g) := by
  intro m
  rw [HahnSeries.coeff_mul]
  exact Subalgebra.sum_mem _ fun ij _ => Subalgebra.mul_mem _ (hf ij.1) (hg ij.2)

private theorem CoeffsIntegral.qExpand {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (N : ℕ) [NeZero N] : CoeffsIntegral (ModularCurve.qExpand K N f) := by
  intro m
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    exact hf c
  · rw [qExpand_coeff_of_not_dvd N f hdvd]
    exact Subalgebra.zero_mem _

private theorem CoeffsIntegral.qTwist {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (u : Kˣ) (hu : ∀ m : ℤ, ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K) :
    CoeffsIntegral (ModularCurve.qTwist u f) := by
  intro m
  rw [qTwist_coeff]
  exact Subalgebra.mul_mem _ (hu m) (hf m)

private theorem intCast_mem_integralClosure (z : ℤ) : (z : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X - Polynomial.C z, Polynomial.monic_X_sub_C z, ?_⟩
  simp

private theorem val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : (u : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
  have hval : (u : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  simp [hval]

private theorem zpow_val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) (m : ℤ) : ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K := by
  have hrw : u ^ m = u ^ (m % (n : ℤ)).toNat := by
    have h1 : u ^ m = u ^ (m % (n : ℤ)) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv m (n : ℤ)]
      rw [zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, mul_one]
    rw [h1, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hn))]
  rw [hrw, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (val_mem_integralClosure_of_pow_eq_one hn hu) _

private theorem coeffsIntegral_coeff_X_sub_C {a : LaurentSeries K}
    (ha : CoeffsIntegral a) (k : ℕ) :
    CoeffsIntegral ((Polynomial.X - Polynomial.C a).coeff k) := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact CoeffsIntegral.neg ha
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      ite_eq_right (one_ne_zero), sub_zero]
    exact coeffsIntegral_one
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    exact coeffsIntegral_zero

private theorem coeffsIntegral_coeff_mul {p q : Polynomial (LaurentSeries K)}
    (hp : ∀ k, CoeffsIntegral (p.coeff k)) (hq : ∀ k, CoeffsIntegral (q.coeff k))
    (k : ℕ) : CoeffsIntegral ((p * q).coeff k) := by
  rw [Polynomial.coeff_mul]
  intro a
  rw [HahnSeries.coeff_sum]
  exact Subalgebra.sum_mem _ fun ij _ => CoeffsIntegral.mul (hp ij.1) (hq ij.2) a

private theorem coeffsIntegral_coeff_prod {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial (LaurentSeries K))
    (hp : ∀ i ∈ s, ∀ k, CoeffsIntegral ((p i).coeff k)) :
    ∀ k, CoeffsIntegral ((∏ i ∈ s, p i).coeff k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using coeffsIntegral_one
    · rw [Polynomial.coeff_one, ite_eq_right (by omega)]
      exact coeffsIntegral_zero
  | cons a s _ha ih =>
    intro k
    rw [Finset.prod_cons]
    exact coeffsIntegral_coeff_mul (hp a (Finset.mem_cons_self a s))
      (ih fun i hi k => hp i (Finset.mem_cons_of_mem hi) k) k

end IntegralCoeffs

section ConjIntegral

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem coeffsIntegral_jqK : CoeffsIntegral (coeffEmb K jq) := by
  intro m
  obtain ⟨z, hz⟩ := intCoeffs_jq m
  rw [coeffEmb_coeff, hz, map_intCast]
  exact intCast_mem_integralClosure z

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem coeffsIntegral_conj (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    CoeffsIntegral (conj ℓ ζ i) := by
  induction i using Fin.cases with
  | zero =>
    rw [conj_zero]
    exact CoeffsIntegral.qExpand coeffsIntegral_jqK (ℓ * ℓ)
  | succ b =>
    rw [conj_succ]
    refine CoeffsIntegral.qTwist coeffsIntegral_jqK _ fun m => ?_
    refine zpow_val_mem_integralClosure_of_pow_eq_one hℓ.out.ne_zero ?_ m
    rw [← pow_mul, mul_comm (b : ℕ) ℓ, pow_mul, hζ1, one_pow]

variable {ℓ ζ}

private theorem coeffsIntegral_phiProd_coeff (hζ1 : ζ ^ ℓ = 1) (k : ℕ) :
    CoeffsIntegral ((phiProd ℓ (conj ℓ ζ)).coeff k) := by
  rw [phiProd]
  exact coeffsIntegral_coeff_prod Finset.univ _
    (fun i _ k => coeffsIntegral_coeff_X_sub_C (coeffsIntegral_conj ℓ ζ hζ1 i) k) k

end ConjIntegral

section IntegralityDescent

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem exists_intCast_eq_of_mem {q : ℚ}
    (h : algebraMap ℚ K q ∈ integralClosure ℤ K) : ∃ z : ℤ, q = (z : ℚ) := by
  rw [mem_integralClosure_iff] at h
  obtain ⟨P, hPmonic, hPeval⟩ := h
  have hcomp : algebraMap ℤ K = (algebraMap ℚ K).comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  rw [hcomp, ← Polynomial.hom_eval₂] at hPeval
  have h0 : Polynomial.eval₂ (Int.castRingHom ℚ) q P = 0 :=
    FaithfulSMul.algebraMap_injective ℚ K (by rw [hPeval, map_zero])
  have hint : IsIntegral ℤ q :=
    ⟨P, hPmonic, by
      rwa [show algebraMap ℤ ℚ = Int.castRingHom ℚ from Subsingleton.elim _ _]⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by rw [← hz]; simp⟩

variable {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}

theorem PhiGenDescends.intCoeffs (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) :
    IntCoeffs (c k) := by
  intro m
  have h1 : algebraMap ℚ K ((c k).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
    rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]
  have h2 := coeffsIntegral_phiProd_coeff hζ1 k ((ℓ : ℤ) * m)
  rw [← h1] at h2
  exact exists_intCast_eq_of_mem h2

end IntegralityDescent

end PhiGen

end ModularCurve

end

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

namespace TPoleOrderLE

private theorem mono {K : Type*} [Field K] {f : LaurentSeries K} {m n : ℕ}
    (hf : TPoleOrderLE f m) (hmn : m ≤ n) : TPoleOrderLE f n :=
  fun k hk => hf k (by omega)

end TPoleOrderLE
@[scoped simp]
private theorem tPoleOrderLE_zero {K : Type*} [Field K] (n : ℕ) :
    TPoleOrderLE (0 : LaurentSeries K) n :=
  fun _ _ => rfl

private theorem tPoleOrderLE_one {K : Type*} [Field K] : TPoleOrderLE (1 : LaurentSeries K) 0 := by
  intro m hm
  rw [HahnSeries.coeff_one, ite_eq_right (by omega)]

namespace TPoleOrderLE
private theorem neg {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) : TPoleOrderLE (-f) n := by
  intro m hm
  rw [HahnSeries.coeff_neg, hf m hm, neg_zero]

end TPoleOrderLE
private theorem TPoleOrderLE.add {K : Type*} [Field K] {f g : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (hg : TPoleOrderLE g n) : TPoleOrderLE (f + g) n := by
  intro m hm
  rw [HahnSeries.coeff_add, hf m hm, hg m hm, add_zero]

namespace TPoleOrderLE

private theorem mul {K : Type*} [Field K] {f g : LaurentSeries K} {m n : ℕ}
    (hf : TPoleOrderLE f m) (hg : TPoleOrderLE g n) : TPoleOrderLE (f * g) (m + n) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < -(m : ℤ)
  · rw [hf ij.1 hi, zero_mul]
  · refine mul_eq_zero_of_right _ (hg ij.2 ?_)
    push_cast at hk
    omega

end TPoleOrderLE
namespace TPoleOrderLE

private theorem qTwist {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (u : Kˣ) : TPoleOrderLE (ModularCurve.qTwist u f) n := by
  intro m hm
  rw [qTwist_coeff, hf m hm, mul_zero]

end TPoleOrderLE
namespace TPoleOrderLE

private theorem qExpand {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : TPoleOrderLE f n) (N : ℕ) [NeZero N] :
    TPoleOrderLE (ModularCurve.qExpand K N f) (N * n) := by
  intro m hm
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine hf c ?_
    have hN : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    push_cast at hm
    nlinarith
  · exact qExpand_coeff_of_not_dvd N f hdvd

end TPoleOrderLE

private theorem tPoleOrderLE_of_jSimplePole {K : Type*} [Field K] (J : LaurentSeries K)
    (hJ : JSimplePole J) : TPoleOrderLE J 1 := by
  intro m hm
  exact hJ m (by push_cast at hm; omega)

private def conjPoleBound (ℓ : ℕ) : Fin (ℓ + 1) → ℕ :=
  fun i => if i = 0 then ℓ * ℓ else 1

@[scoped simp]
private theorem conjPoleBound_zero (ℓ : ℕ) : conjPoleBound ℓ 0 = ℓ * ℓ := ite_eq_left rfl

@[scoped simp]
private theorem conjPoleBound_succ (ℓ : ℕ) (b : Fin ℓ) : conjPoleBound ℓ b.succ = 1 :=
  ite_eq_right (Fin.succ_ne_zero b)

private theorem sum_conjPoleBound (ℓ : ℕ) :
    ∑ i : Fin (ℓ + 1), conjPoleBound ℓ i = ℓ * ℓ + ℓ := by
  rw [Fin.sum_univ_succ, conjPoleBound_zero]
  congr 1
  simp only [conjPoleBound_succ]
  simp

private theorem tPoleOrderLE_conj_zero {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) (hJ : JSimplePole J) :
    TPoleOrderLE (conj 0) (ℓ * ℓ) := by
  rw [hconj0]
  have h := (tPoleOrderLE_of_jSimplePole J hJ).qExpand (ℓ * ℓ)
  simpa using h

private theorem tPoleOrderLE_conj_succ {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (b : Fin ℓ) : TPoleOrderLE (conj b.succ) 1 := by
  rw [hconjS b]
  exact (tPoleOrderLE_of_jSimplePole J hJ).qTwist _

private theorem tPoleOrderLE_conj {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (i : Fin (ℓ + 1)) :
    TPoleOrderLE (conj i) (conjPoleBound ℓ i) := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
  · rw [conjPoleBound_zero]
    exact tPoleOrderLE_conj_zero hconj0 hJ
  · rw [conjPoleBound_succ]
    exact tPoleOrderLE_conj_succ hconjS hJ b

private theorem tPoleOrderLE_coeff_X_sub_C {K : Type*} [Field K] {a : LaurentSeries K} {n : ℕ}
    (ha : TPoleOrderLE a n) (k : ℕ) :
    TPoleOrderLE ((Polynomial.X - Polynomial.C a).coeff k) n := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact ha.neg
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      ite_eq_right (one_ne_zero), sub_zero]
    exact tPoleOrderLE_one.mono (Nat.zero_le _)
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    exact tPoleOrderLE_zero _

private theorem tPoleOrderLE_coeff_mul {K : Type*} [Field K] {p q : Polynomial (LaurentSeries K)}
    {m n : ℕ} (hp : ∀ k, TPoleOrderLE (p.coeff k) m) (hq : ∀ k, TPoleOrderLE (q.coeff k) n)
    (k : ℕ) : TPoleOrderLE ((p * q).coeff k) (m + n) := by
  rw [Polynomial.coeff_mul]
  intro a ha
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun ij _ => (hp ij.1).mul (hq ij.2) a ha

private theorem tPoleOrderLE_coeff_prod {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial (LaurentSeries K)) (n : ι → ℕ)
    (hp : ∀ i ∈ s, ∀ k, TPoleOrderLE ((p i).coeff k) (n i)) :
    ∀ k, TPoleOrderLE ((∏ i ∈ s, p i).coeff k) (∑ i ∈ s, n i) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simp only [Finset.prod_empty, Finset.sum_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using tPoleOrderLE_one
    · rw [Polynomial.coeff_one, ite_eq_right (by omega)]
      exact tPoleOrderLE_zero 0
  | cons a s ha ih =>
    intro k
    rw [Finset.prod_cons, Finset.sum_cons]
    exact tPoleOrderLE_coeff_mul (hp a (Finset.mem_cons_self a s))
      (ih fun i hi k => hp i (Finset.mem_cons_of_mem hi) k) k

private theorem phiProd_def {K : Type*} [Field K] (ℓ : ℕ)
    (conj : Fin (ℓ + 1) → LaurentSeries K) :
    phiProd ℓ conj = ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i)) := rfl

private theorem tPoleOrderLE_phiProd_coeff {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (J : LaurentSeries K) (conj : Fin (ℓ + 1) → LaurentSeries K)
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (k : ℕ) :
    TPoleOrderLE ((phiProd ℓ conj).coeff k) (ℓ * ℓ + ℓ) := by
  rw [phiProd_def, ← sum_conjPoleBound ℓ]
  exact tPoleOrderLE_coeff_prod Finset.univ _ (conjPoleBound ℓ)
    (fun i _ k => tPoleOrderLE_coeff_X_sub_C (tPoleOrderLE_conj hconj0 hconjS hJ i) k) k

namespace IntCoeffs
private theorem sub {f g : LaurentSeries ℚ} (hf : IntCoeffs f)
    (hg : IntCoeffs g) : IntCoeffs (f - g) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  obtain ⟨b, hb⟩ := hg m
  exact ⟨a - b, by rw [HahnSeries.coeff_sub, ha, hb]; push_cast; ring⟩

end IntCoeffs

private theorem intCoeffs_algebraMap_int_mul_jq_pow (z : ℤ) (n : ℕ) :
    IntCoeffs (algebraMap ℚ (LaurentSeries ℚ) ((z : ℚ)) * jq ^ n) := by
  intro m
  obtain ⟨a, ha⟩ := intCoeffs_jq_pow n m
  refine ⟨z * a, ?_⟩
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, ha]
  push_cast
  ring

private theorem coeff_aeval_jq_neg (P : Polynomial ℚ) {m : ℕ} (hm : P.natDegree ≤ m) :
    (Polynomial.aeval jq P).coeff (-(m : ℤ)) = P.coeff m := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single m]
  · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
      mul_one]
  · intro i hi hin
    have hilt : i < m :=
      lt_of_le_of_ne (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hm) hin
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro hm'
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simp only [Finset.mem_range, not_lt] at hm'; omega),
      zero_mul]

theorem aeval_jq_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree = d →
      IntCoeffs (Polynomial.aeval jq P) → ∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ) by
    exact H P.natDegree P rfl hP k
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hd hP k
  obtain ⟨zd, hzd⟩ := hP (-(d : ℤ))
  have hlead : P.coeff d = (zd : ℚ) := by
    rw [← coeff_aeval_jq_neg P hd.le, hzd]
  rcases lt_trichotomy k d with hk | rfl | hk
  · set Q : Polynomial ℚ := P - Polynomial.C (P.coeff d) * Polynomial.X ^ d with hQ
    have hQcoeff : Q.coeff k = P.coeff k := by
      rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (by omega), mul_zero, sub_zero]
    have hQdeg : Q.natDegree < d := by
      rcases eq_or_ne Q 0 with hQ0 | hQ0
      · rw [hQ0, Polynomial.natDegree_zero]; omega
      refine lt_of_le_of_ne ?_ ?_
      · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hd]
        exact max_le le_rfl (Polynomial.natDegree_C_mul_X_pow_le _ _)
      · intro hcon
        apply hQ0
        rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, hcon, hQ,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl,
          mul_one, sub_self]
    have hQint : IntCoeffs (Polynomial.aeval jq Q) := by
      rw [hQ, map_sub, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hlead]
      exact hP.sub (intCoeffs_algebraMap_int_mul_jq_pow zd d)
    obtain ⟨z, hz⟩ := ih Q.natDegree hQdeg Q rfl hQint k
    exact ⟨z, by rw [← hQcoeff, hz]⟩
  · exact ⟨zd, hlead⟩
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]⟩

end PhiGen
end ModularCurve

end
