/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_top.lean`,
`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean`,
`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE.lean`,
`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean`,
`Theorems/Thm_ModularCurve_PhiGen_evalAtJ_injective.lean`,
`P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean`,
`Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`,
`P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean`,
`Theorems/Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean`,
and
`P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.PhiGen
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.Integrality
import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.CosetProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

private theorem coeffEmb_qExpand_injective {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] :
    Function.Injective (fun f : LaurentSeries ℚ => coeffEmb K (qExpand ℚ ℓ f)) :=
  (coeffEmb_injective K).comp (qExpand_injective (R := ℚ) ℓ)

theorem PhiGenDescends.c_top {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) : c (ℓ + 1) = 1 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff (ℓ + 1) = 1 := by
    have h := (phiProd_monic ℓ (conj ℓ ζ)).coeff_natDegree
    rwa [phiProd_natDegree ℓ (conj ℓ ζ)] at h
  simp only [← hc (ℓ + 1), h1, map_one]

theorem PhiGenDescends.c_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) {k : ℕ} (hk : ℓ + 1 < k) : c k = 0 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [phiProd_natDegree]; exact hk)
  simp only [← hc k, h1, map_zero]

theorem PhiGenDescends.poleOrderLE {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : PoleOrderLE (c k) (ℓ + 1) := by
  intro m hm
  refine (algebraMap ℚ K).injective ?_
  have h := poleOrderLE_phiProd_conj_coeff ℓ ζ k ((ℓ : ℤ) * m) (by
    have hℓ2 : (2 : ℤ) ≤ ℓ := by exact_mod_cast hℓ.out.two_le
    push_cast at hm ⊢
    nlinarith)
  rw [hc k, coeffEmb_coeff, qExpand_coeff_mul] at h
  rw [h, map_zero]

theorem PhiGenDescends.sum_mul_jqN_pow_eq_zero {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) :
    ∑ k ∈ Finset.range (ℓ + 2), c k * (jqN ℓ) ^ k = 0 := by
  set F : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ ℓ) with hF
  have hFapp : ∀ f : LaurentSeries ℚ, F f = coeffEmb K (qExpand ℚ ℓ f) := fun f => rfl
  have hFinj : Function.Injective F := coeffEmb_qExpand_injective
  have hconj0 : conj ℓ ζ (0 : Fin (ℓ + 1)) = F (jqN ℓ) := by
    change conj ℓ ζ 0 = coeffMap (algebraMap ℚ K) (qExpand ℚ ℓ (jqN ℓ))
    rw [conj_zero, jqN, qExpand_qExpand, coeffMap_qExpand]
    rfl
  have hterm : ∀ k ∈ Finset.range (ℓ + 2),
      F (c k * (jqN ℓ) ^ k)
        = (phiProd ℓ (conj ℓ ζ)).coeff k * (conj ℓ ζ 0) ^ k := by
    intro k _
    rw [map_mul, map_pow, ← hconj0, hFapp, hc k]
  refine hFinj ?_
  rw [map_zero, map_sum, Finset.sum_congr rfl hterm]
  rw [← Polynomial.eval_eq_sum_range' (n := ℓ + 2) (by rw [phiProd_natDegree]; omega)]
  exact phiProd_eval_conj ℓ _ 0

theorem evalAtJ_eq_aeval_map (Q : Polynomial ℤ) :
    evalAtJ Q = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ)) := by
  have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
      = algebraMap ℤ (LaurentSeries ℚ) := Subsingleton.elim _ _
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  rfl

theorem evalAtJ_injective : Function.Injective evalAtJ := by
  intro P Q hPQ
  refine Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective ?_
  rw [evalAtJ_eq_aeval_map, evalAtJ_eq_aeval_map] at hPQ
  have h0 : Polynomial.aeval jq
      (P.map (Int.castRingHom ℚ) - Q.map (Int.castRingHom ℚ)) = 0 := by
    rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp (aeval_jq_eq_zero h0)

end PhiGen
end ModularCurve

end

noncomputable section

open PowerSeries HahnSeries Polynomial

namespace ModularCurve

namespace PhiGen

section PermLemma

variable {K : Type*} [Field K] {ℓ : ℕ} {conj : Fin (ℓ + 1) → LaurentSeries K}

private theorem map_phiProd_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) :
    (phiProd ℓ conj).map F = phiProd ℓ conj := by
  rw [phiProd, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, h0]
  congr 1
  calc ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (conj b.succ)))
      = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj (e b).succ)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [hS b]
    _ = ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ)) :=
        e.prod_comp fun b => Polynomial.X - Polynomial.C (conj b.succ)

private theorem map_phiProd_coeff_of_perm (F : LaurentSeries K →+* LaurentSeries K)
    (e : Fin ℓ ≃ Fin ℓ) (h0 : F (conj 0) = conj 0)
    (hS : ∀ b : Fin ℓ, F (conj b.succ) = conj (e b).succ) (k : ℕ) :
    F ((phiProd ℓ conj).coeff k) = (phiProd ℓ conj).coeff k := by
  conv_rhs => rw [← map_phiProd_of_perm F e h0 hS]
  rw [Polynomial.coeff_map]

end PermLemma

section TwistRoot

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem zeta_pow_mod (hζ : IsPrimitiveRoot (ζ : K) ℓ) (n : ℕ) :
    ζ ^ (n % ℓ) = ζ ^ n :=
  (pow_eq_pow_mod n (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_eq_one).symm

end TwistRoot

section TwistConj

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
  {conj : Fin (ℓ + 1) → LaurentSeries K} {ζ : Kˣ} {J : LaurentSeries K}

private theorem qTwist_conj_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) : qTwist ζ (conj 0) = conj 0 := by
  rw [hconj0, qTwist_qExpand]
  congr 1
  rw [zpow_natCast, pow_mul, (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_eq_one, one_pow,
    qTwist_one_apply]

private theorem qTwist_conj_succ (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (b : Fin ℓ) :
    qTwist ζ (conj b.succ) = conj ((Equiv.addRight (1 : Fin ℓ)) b).succ := by
  rw [hconjS b, hconjS ((Equiv.addRight (1 : Fin ℓ)) b), qTwist_qTwist]
  congr 1
  simp only [Equiv.coe_addRight]
  have h1 : ((1 : Fin ℓ) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hℓ.out.one_lt
  rw [Fin.val_add, h1, zeta_pow_mod hζ ((b : ℕ) + 1), pow_succ, mul_comm ζ (ζ ^ (b : ℕ))]

private theorem qTwist_phiProd_coeff (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (k : ℕ) :
    qTwist ζ ((phiProd ℓ conj).coeff k) = (phiProd ℓ conj).coeff k :=
  map_phiProd_coeff_of_perm (qTwist ζ) (Equiv.addRight (1 : Fin ℓ))
    (qTwist_conj_zero hζ hconj0) (qTwist_conj_succ hζ hconjS) k

end TwistConj

section SupportCollapse

variable {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}

private theorem coeff_eq_zero_of_qTwist_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) :
    f.coeff m = 0 := by
  have h := congrArg (fun g => HahnSeries.coeff g m) hf
  simp only [qTwist_coeff] at h
  by_contra hc
  apply hm
  rw [← hζ.zpow_eq_one_iff_dvd]
  have hunit : ((ζ ^ m : Kˣ) : K) = (ζ : K) ^ m := Units.val_zpow_eq_zpow_val ζ m
  have hzero : (((ζ ^ m : Kˣ) : K) - 1) * f.coeff m = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp hzero with h1 | h1
  · rw [hunit] at h1
    linear_combination h1
  · exact absurd h1 hc

end SupportCollapse

section Contract

variable {K : Type*} [Field K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

private def qContract (f : LaurentSeries K) : LaurentSeries K where
  coeff m := f.coeff ((ℓ : ℤ) * m)
  isPWO_support' := by
    have hsub : (Function.support fun m : ℤ => f.coeff ((ℓ : ℤ) * m)) ⊆
        (fun k : ℤ => k / (ℓ : ℤ)) '' f.support := by
      intro m hm
      refine ⟨(ℓ : ℤ) * m, hm, ?_⟩
      exact Int.mul_ediv_cancel_left m (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
    exact (f.isPWO_support'.image_of_monotone fun a b hab =>
      Int.ediv_le_ediv (Int.natCast_pos.mpr hℓ.out.pos) hab).mono hsub

@[scoped simp]
private theorem qContract_coeff (f : LaurentSeries K) (m : ℤ) :
    (qContract ℓ f).coeff m = f.coeff ((ℓ : ℤ) * m) := rfl

variable {ℓ}

private theorem qExpand_qContract {f : LaurentSeries K}
    (hf : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → f.coeff m = 0) :
    qExpand K ℓ (qContract ℓ f) = f := by
  ext k
  by_cases hk : (ℓ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qContract_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hk, hf k hk]

private theorem mem_range_qExpand_of_qTwist_eq {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {f : LaurentSeries K} (hf : qTwist ζ f = f) : f ∈ Set.range (qExpand K ℓ) :=
  ⟨qContract ℓ f, qExpand_qContract fun _ hm => coeff_eq_zero_of_qTwist_eq hζ hf hm⟩

end Contract

section RangeDescent

variable {K : Type*} [Field K]

private theorem phiProd_coeff_mem_range_qExpand (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    (J : LaurentSeries K) (conj : Fin (ℓ + 1) → LaurentSeries K)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (k : ℕ) :
    (phiProd ℓ conj).coeff k ∈ Set.range (qExpand K ℓ) :=
  mem_range_qExpand_of_qTwist_eq hζ (qTwist_phiProd_coeff hζ hconj0 hconjS k)

end RangeDescent

section GaloisMap

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_qTwist (σ : R →+* S) (u : Rˣ) (v : Sˣ) (huv : (v : S) = σ (u : R))
    (f : LaurentSeries R) : coeffMap σ (qTwist u f) = qTwist v (coeffMap σ f) := by
  have hmap : Units.map (σ : R →* S) u = v :=
    Units.ext (by rw [Units.coe_map, huv]; rfl)
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← hmap, ← map_zpow, Units.coe_map]
  rfl

end GaloisMap

section GaloisCoeff

variable {K : Type*} [Field K]

private theorem coeffMap_phiProd_coeff (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    (J : LaurentSeries K) (conj : Fin (ℓ + 1) → LaurentSeries K) (σ : K →+* K)
    (hσJ : coeffMap σ J = J) (e : Fin ℓ ≃ Fin ℓ)
    (hσζ : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ))
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J) (k : ℕ) :
    coeffMap σ ((phiProd ℓ conj).coeff k) = (phiProd ℓ conj).coeff k := by
  refine map_phiProd_coeff_of_perm (coeffMap σ) e ?_ ?_ k
  · rw [hconj0, coeffMap_qExpand, hσJ]
  · intro b
    rw [hconjS b, hconjS (e b),
      coeffMap_qTwist σ (ζ ^ (b : ℕ)) (ζ ^ ((e b : Fin ℓ) : ℕ))
        (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hσζ b]),
      hσJ]

end GaloisCoeff

section FixedField

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_of_forall_coeffMap_eq
    (hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c)
    {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) :
    f ∈ Set.range (coeffEmb K) := by
  have hcoeff : ∀ m : ℤ, ∃ r : ℚ, algebraMap ℚ K r = f.coeff m := fun m =>
    hfix (f.coeff m) fun σ => by
      have hcongr := congrArg (fun g => HahnSeries.coeff g m) (hf σ)
      simpa using hcongr
  choose r hr using hcoeff
  refine ⟨⟨r, ?_⟩, ?_⟩
  · refine f.isPWO_support'.mono fun m hm => ?_
    simp only [Function.mem_support] at hm ⊢
    intro h
    exact hm (FaithfulSMul.algebraMap_injective ℚ K (by rw [hr m, h, map_zero]))
  · ext m
    exact hr m

end FixedField

section GaloisPerm

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}

private theorem exists_galoisPerm (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) :
    ∃ e : Fin ℓ ≃ Fin ℓ,
      ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by
  have hσζ : (σ (ζ : K)) ^ ℓ = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  set e₀ : Fin ℓ → Fin ℓ := fun b => ⟨(a * (b : ℕ)) % ℓ, Nat.mod_lt _ hℓ.out.pos⟩
  have hkey : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e₀ b : Fin ℓ) : ℕ) := by
    intro b
    change σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((a * (b : ℕ)) % ℓ)
    rw [map_pow, ← ha, ← pow_mul]
    exact pow_eq_pow_mod _ hζ.pow_eq_one
  have hinj : Function.Injective e₀ := by
    intro b b' hbb'
    have h1 : σ ((ζ : K) ^ (b : ℕ)) = σ ((ζ : K) ^ ((b' : Fin ℓ) : ℕ)) := by
      rw [hkey b, hkey b', hbb']
    exact Fin.ext (hζ.pow_inj b.isLt b'.isLt (σ.injective h1))
  exact ⟨Equiv.ofBijective e₀ (Finite.injective_iff_bijective.mp hinj), hkey⟩

end GaloisPerm

section Descent

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem mem_range_coeffEmb_qExpand_of_mem_inter {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ))
    (h2 : f ∈ Set.range (coeffEmb K)) :
    ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by
  obtain ⟨h, hh⟩ := h2
  have hsupp : ∀ m : ℤ, ¬ (ℓ : ℤ) ∣ m → h.coeff m = 0 := by
    intro m hm
    obtain ⟨g, hg⟩ := h1
    refine FaithfulSMul.algebraMap_injective ℚ K ?_
    rw [map_zero, ← coeffEmb_coeff, hh, ← hg, qExpand_coeff_of_not_dvd ℓ g hm]
  refine ⟨qContract ℓ h, ?_⟩
  rw [qExpand_qContract hsupp]
  exact hh.symm

theorem exists_phiGenDescends (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
    [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by
  have hmem : ∀ k : ℕ, ∃ g : LaurentSeries ℚ,
      (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by
    intro k
    refine mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
    · exact phiProd_coeff_mem_range_qExpand ℓ ζ (coeffEmb K jq) (conj ℓ ζ)
        hζ (conj_zero ℓ ζ) (conj_succ ℓ ζ) k
    · refine mem_range_coeffEmb_of_forall_coeffMap_eq
        (fun x hx => (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx) ?_
      intro σ
      obtain ⟨e, he⟩ := exists_galoisPerm hζ (σ : K →+* K)
      exact coeffMap_phiProd_coeff ℓ ζ (coeffEmb K jq) (conj ℓ ζ) (σ : K →+* K)
        (coeffMap_coeffEmb σ jq) e he (conj_zero ℓ ζ) (conj_succ ℓ ζ) k
  choose c hc using hmem
  exact ⟨c, hc⟩

end Descent

end PhiGen

end ModularCurve

end

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

private theorem natDegree_le_of_poleOrderLE_aeval (P : Polynomial ℚ) {n : ℕ}
    (hn : PoleOrderLE (Polynomial.aeval jq P) n) : P.natDegree ≤ n := by
  by_contra h
  push Not at h
  have hP : P ≠ 0 := by
    rintro rfl
    simp at h
  have h0 := hn (-(P.natDegree : ℤ)) (by omega)
  rw [coeff_aeval_jq_neg P le_rfl] at h0
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) h0

private theorem exists_aeval_jq_eq_of_mem_adjoin {f : LaurentSeries ℚ}
    (hf : f ∈ Algebra.adjoin ℚ {jq}) {n : ℕ} (hn : PoleOrderLE f n) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ f = Polynomial.aeval jq P := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hf
  obtain ⟨P, rfl⟩ := hf
  exact ⟨P, natDegree_le_of_poleOrderLE_aeval P hn, rfl⟩

section Exits

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

namespace PhiGenDescends

private theorem exists_intPoly (hc : PhiGenDescends ℓ ζ c)
    (hint : ∀ k, IntCoeffs (c k)) (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) (k : ℕ) :
    ∃ Q : Polynomial ℤ, Q.natDegree ≤ ℓ + 1 ∧ evalAtJ Q = c k := by
  obtain ⟨P, hPdeg, hP⟩ := exists_aeval_jq_eq_of_mem_adjoin (hmem k) (hc.poleOrderLE k)
  have hPint : ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ) :=
    aeval_jq_intCoeffs_descent P (by rw [← hP]; exact hint k)
  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨z, hz⟩ := hPint n
    exact ⟨z, by rw [eq_intCast]; exact hz.symm⟩
  obtain ⟨Q, hQ⟩ := hlift
  have hQmap : Q.map (Int.castRingHom ℚ) = P := hQ
  refine ⟨Q, ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ)
      Int.cast_injective Q, hQmap]
    exact hPdeg
  · rw [evalAtJ_eq_aeval_map, hQmap, hP]

end PhiGenDescends
end Exits

section StrongExistence

private theorem coeff_sum_C_mul_X_pow (Q : ℕ → Polynomial ℤ) (n m : ℕ) (hm : m < n) :
    (∑ k ∈ Finset.range n, Polynomial.C (Q k) * Polynomial.X ^ k).coeff m = Q m := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hk), mul_zero]
  · intro hm'
    exact absurd (Finset.mem_range.mpr hm) hm'

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

theorem exists_modularPolynomialData_coeff_eq (hc : PhiGenDescends ℓ ζ c)
    (hint : ∀ k, IntCoeffs (c k)) (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) :
    ∃ data : ModularPolynomialData ℓ, ∀ k, evalAtJ (data.Φ.coeff k) = c k := by
  choose Q hQdeg hQeval using hc.exists_intPoly hint hmem
  have hQtop : Q (ℓ + 1) = 1 := by
    refine evalAtJ_injective ?_
    rw [hQeval (ℓ + 1), hc.c_top, map_one]
  set Φ : Polynomial (Polynomial ℤ) :=
    ∑ k ∈ Finset.range (ℓ + 2), Polynomial.C (Q k) * Polynomial.X ^ k with hΦ
  have hΦtop : Φ.coeff (ℓ + 1) = 1 := by
    rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) (ℓ + 1) (by omega), hQtop]
  have hΦdeg_le : Φ.natDegree ≤ ℓ + 1 := by
    rw [hΦ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hΦdeg : Φ.natDegree = ℓ + 1 :=
    le_antisymm hΦdeg_le
      (Polynomial.le_natDegree_of_ne_zero (by rw [hΦtop]; exact one_ne_zero))
  have hΦcoeff : ∀ k, evalAtJ (Φ.coeff k) = c k := by
    intro k
    by_cases hk : k < ℓ + 2
    · rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) k hk, hQeval k]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Φ.natDegree < k), map_zero,
        hc.c_eq_zero (by omega : ℓ + 1 < k)]
  refine ⟨⟨Φ, ?_, ?_, ?_⟩, hΦcoeff⟩
  · change Φ.coeff Φ.natDegree = 1
    rw [hΦdeg]
    exact hΦtop
  · rw [hΦdeg, ArithmeticFunction.dedekindPsi_prime hℓ.out]
  · rw [Polynomial.eval₂_eq_sum_range' evalAtJ (n := ℓ + 2) (by rw [hΦdeg]; omega) (jqN ℓ)]
    have hterm : ∀ k ∈ Finset.range (ℓ + 2),
        evalAtJ (Φ.coeff k) * (jqN ℓ) ^ k = c k * (jqN ℓ) ^ k := by
      intro k _
      rw [hΦcoeff k]
    rw [Finset.sum_congr rfl hterm]
    exact hc.sum_mul_jqN_pow_eq_zero

end StrongExistence

end PhiGen
end ModularCurve

end
