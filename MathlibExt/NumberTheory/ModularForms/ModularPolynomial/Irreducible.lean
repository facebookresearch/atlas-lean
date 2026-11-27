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

`Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean`,
`Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_splits.lean`,
`Theorems/Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean`,
and
`P2M/Sol/S_ModularCurve_PhiGen_phiIrreducible_of_splits.lean`
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
import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.CosetProduct
import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.Descends
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace ModularCurve

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

section JqNLead

variable (N : ℕ) [NeZero N]

private theorem coeff_jqN_self : (jqN N).coeff (-(N : ℤ)) = 1 := by
  have h : (-(N : ℤ)) = (N : ℤ) * (-1) := by ring
  rw [jqN, h, qExpand_coeff_mul, coeff_jq_neg_one]

private theorem coeff_jqN_of_lt {m : ℤ} (hm : m < -(N : ℤ)) : (jqN N).coeff m = 0 := by
  rw [jqN]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine coeff_jq_of_lt ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    nlinarith
  · exact qExpand_coeff_of_not_dvd N jq hdvd

end JqNLead

theorem evalAtJGen_injective : Function.Injective evalAtJGen := by
  intro a b hab
  apply PhiGen.evalAtJ_injective
  rw [← algebraMap_comp_evalAtJGen]
  simp only [RingHom.comp_apply, hab]

namespace PhiGen

section Distinctness

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem conj_zero_coeff_neg_one :
    (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) = 0 := by
  rw [conj_zero]
  refine qExpand_coeff_of_not_dvd _ _ ?_
  intro h
  have h1 : ((ℓ * ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp h
  have h2 : (ℓ * ℓ : ℕ) ∣ 1 := by exact_mod_cast h1
  have h3 : ℓ * ℓ = 1 := Nat.dvd_one.mp h2
  have h4 : 2 ≤ ℓ := hℓ.out.two_le
  nlinarith

private theorem conj_succ_coeff_neg_one (b : Fin ℓ) :
    (conj ℓ ζ b.succ).coeff (-1 : ℤ) = (((ζ ^ (b : ℕ))⁻¹ : Kˣ) : K) := by
  rw [conj_succ, qTwist_coeff, coeff_coeffEmb_jq_neg_one, mul_one, zpow_neg_one]

private theorem conj_injective (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Function.Injective (conj ℓ ζ (K := K)) := by
  have hne : ∀ b : Fin ℓ, (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) ≠
      (conj ℓ ζ b.succ).coeff (-1 : ℤ) := by
    intro b
    rw [conj_zero_coeff_neg_one, conj_succ_coeff_neg_one]
    exact fun h => Units.ne_zero _ h.symm
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ b => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij) (hne b)
  | succ b =>
    induction j using Fin.cases with
    | zero => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij.symm) (hne b)
    | succ b' =>
      have hcoeff := congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij
      simp only [conj_succ_coeff_neg_one] at hcoeff
      have hu : (ζ ^ (b : ℕ))⁻¹ = (ζ ^ (b' : ℕ))⁻¹ := Units.ext hcoeff
      have hpow : (ζ : K) ^ (b : ℕ) = (ζ : K) ^ (b' : ℕ) := by
        have hv := congrArg Units.val (inv_injective hu)
        push_cast at hv
        exact hv
      exact congrArg Fin.succ (Fin.ext (hζ.pow_inj b.isLt b'.isLt hpow))

end Distinctness

section ScalarEmbedding

variable (K : Type*) [Field K] [Algebra ℚ K]

private def ratC : ℚ →+* LaurentSeries K := (HahnSeries.C).comp (algebraMap ℚ K)

private theorem ratC_apply (c : ℚ) : ratC K c = HahnSeries.single 0 (algebraMap ℚ K c) :=
  rfl

private theorem coeff_ratC_of_ne (c : ℚ) {k : ℤ} (hk : k ≠ 0) : (ratC K c).coeff k = 0 := by
  rw [ratC_apply]
  exact HahnSeries.coeff_single_of_ne hk

private theorem coeffMap_jq : coeffMap (algebraMap ℚ K) jq = (coeffEmb K jq) := by
  ext k
  rfl

end ScalarEmbedding

section PoleOrder

private theorem coeff_aeval_jq_of_lt (P : Polynomial ℚ) {m : ℤ}
    (hm : m < -(P.natDegree : ℤ)) : (Polynomial.aeval jq P).coeff m = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_of_lt,
    mul_zero]
  have : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  omega

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] {P : Polynomial ℚ}

private theorem ne_zero_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) : P ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  have h1 := coeff_jqN_self ℓ
  rw [← h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

private theorem natDegree_eq_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) :
    P.natDegree = ℓ := by
  have hP0 : P ≠ 0 := ne_zero_of_aeval_jq_eq_jqN ℓ h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (Polynomial.aeval jq P).coeff (-(ℓ : ℤ)) = 0 :=
      coeff_aeval_jq_of_lt P (by omega)
    rw [h, coeff_jqN_self] at h1
    exact one_ne_zero h1
  · have h1 := coeff_aeval_jq_neg P le_rfl
    rw [h, coeff_jqN_of_lt ℓ (by omega)] at h1
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp h1.symm)

private theorem monic_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) : P.Monic := by
  have hd := natDegree_eq_of_aeval_jq_eq_jqN ℓ h
  have h1 := coeff_aeval_jq_neg P le_rfl
  rw [h, hd, coeff_jqN_self] at h1
  change P.coeff P.natDegree = 1
  rw [hd]
  exact h1.symm

end PoleOrder

section Transfer

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

omit [Algebra ℚ K] hℓ in
private theorem zeta_pow_zpow_eq_one (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) :
    (ζ ^ b) ^ ((ℓ : ℕ) : ℤ) = (1 : Kˣ) := by
  rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_eq_one,
    one_pow]

variable {P : Polynomial ℚ}

private theorem eval₂_ratC_jqK_of_aeval_jq_eq (h : Polynomial.aeval jq P = jqN ℓ) :
    P.eval₂ (ratC K) (coeffEmb K jq) = qExpand K ℓ (coeffEmb K jq) := by
  have h2 := congrArg (coeffMap (algebraMap ℚ K)) h
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, jqN, coeffMap_qExpand, coeffMap_jq,
    Subsingleton.elim ((coeffMap (algebraMap ℚ K)).comp (algebraMap ℚ (LaurentSeries ℚ)))
      (ratC K)] at h2
  exact h2

private theorem eval₂_ratC_conj_succ_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) (b : Fin ℓ) :
    P.eval₂ (ratC K) (conj ℓ ζ b.succ) = qExpand K ℓ (coeffEmb K jq) := by
  have h2 := congrArg (qTwist (ζ ^ (b : ℕ))) (eval₂_ratC_jqK_of_aeval_jq_eq ℓ h)
  rw [Polynomial.hom_eval₂,
    Subsingleton.elim ((qTwist (ζ ^ (b : ℕ))).comp (ratC K)) (ratC K),
    qTwist_qExpand, zeta_pow_zpow_eq_one ℓ ζ hζ, qTwist_one_apply, ← conj_succ] at h2
  exact h2

end Transfer

section Vieta

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
variable {P : Polynomial ℚ}

private theorem sum_conj_succ_eq_ratC_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) :
    ∑ b : Fin ℓ, conj ℓ ζ b.succ = ratC K (-(P.coeff (ℓ - 1))) := by
  have hPdeg : P.natDegree = ℓ := natDegree_eq_of_aeval_jq_eq_jqN ℓ h
  have hPmonic : P.Monic := monic_of_aeval_jq_eq_jqN ℓ h
  set A : Polynomial (LaurentSeries K) := P.map (ratC K) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj ℓ ζ b.succ)) with hB
  have hAmonic : A.Monic := hPmonic.map _
  have hAdeg : A.natDegree = ℓ := by rw [hA, hPmonic.natDegree_map, hPdeg]
  have hBmonic : B.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = ℓ := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hinj : Function.Injective (fun b : Fin ℓ => conj ℓ ζ b.succ) := fun b b' hbb' =>
    Fin.succ_injective ℓ (conj_injective ℓ ζ hζ hbb')
  have key : A - B = Polynomial.C (qExpand K ℓ (coeffEmb K jq)) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun b => ?_) ?_
    · have hAev : A.eval (conj ℓ ζ b.succ) = qExpand K ℓ (coeffEmb K jq) := by
        rw [hA, Polynomial.eval_map]
        exact eval₂_ratC_conj_succ_of_aeval_jq_eq ℓ ζ hζ h b
      have hBev : B.eval (conj ℓ ζ b.succ) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hℓ.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]
        exact hℓ.out.pos
      · refine lt_of_lt_of_eq
          (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt_left
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero,
                Polynomial.degree_eq_natDegree hBmonic.ne_zero, hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])
  have hcoeff := congrArg (fun p : Polynomial (LaurentSeries K) => p.coeff (ℓ - 1)) key
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C,
    ite_eq_right (by omega : ¬(ℓ - 1 = 0))] at hcoeff
  have hBcoeff : B.coeff (ℓ - 1) = -∑ b : Fin ℓ, conj ℓ ζ b.succ := by
    have hv := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin ℓ))
      (fun b => conj ℓ ζ b.succ) (by simp [hℓ.out.pos])
    simpa using hv
  have hAcoeff : A.coeff (ℓ - 1) = ratC K (P.coeff (ℓ - 1)) := Polynomial.coeff_map _ _
  rw [hAcoeff, hBcoeff, sub_neg_eq_add, add_comm] at hcoeff
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left hcoeff

end Vieta

section Refutation

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem coeff_sum_conj_succ_self (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (∑ b : Fin ℓ, conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) =
      (ℓ : K) * algebraMap ℚ K (jq.coeff ((ℓ : ℕ) : ℤ)) := by
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ b : Fin ℓ, (conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) =
      algebraMap ℚ K (jq.coeff ((ℓ : ℕ) : ℤ)) := by
    intro b
    rw [conj_succ, qTwist_coeff, zeta_pow_zpow_eq_one ℓ ζ hζ, Units.val_one, one_mul,
      coeffEmb_coeff]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem coeff_sum_conj_succ_ne_zero
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (∑ b : Fin ℓ, conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) ≠ 0 := by
  rw [coeff_sum_conj_succ_self ℓ ζ hζ]
  refine mul_ne_zero ?_ ?_
  · rw [show ((ℓ : ℕ) : K) = algebraMap ℚ K ((ℓ : ℕ) : ℚ) from (map_natCast _ _).symm]
    intro hc
    exact (Nat.cast_ne_zero (R := ℚ)).mpr hℓ.out.ne_zero
      ((algebraMap ℚ K).injective (by rw [hc, map_zero]))
  · intro hc
    have h0 : jq.coeff ((ℓ : ℕ) : ℤ) = 0 :=
      (algebraMap ℚ K).injective (by rw [hc, map_zero])
    have h1 := hpos ℓ
    rw [h0] at h1
    norm_num at h1

private theorem aeval_jq_ne_jqN_of_isPrimitiveRoot
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (P : Polynomial ℚ) : Polynomial.aeval jq P ≠ jqN ℓ := by
  intro h
  have h1 := sum_conj_succ_eq_ratC_of_aeval_jq_eq ℓ ζ hζ h
  have h2 := coeff_sum_conj_succ_ne_zero ℓ ζ hpos hζ
  rw [h1] at h2
  exact h2 (coeff_ratC_of_ne K _ (by exact_mod_cast hℓ.out.ne_zero))

end Refutation

section Headline

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

private theorem aeval_jq_ne_jqN (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (P : Polynomial ℚ) :
    Polynomial.aeval jq P ≠ jqN ℓ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  refine aeval_jq_ne_jqN_of_isPrimitiveRoot ℓ hzu.unit hpos ?_ P
  rw [hzu.unit_spec]
  exact hz

private theorem jqN_not_mem_adjoin_jq (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) :
    jqN ℓ ∉ Algebra.adjoin ℚ {jq} := by
  intro hmem
  obtain ⟨P, hP⟩ := Algebra.adjoin_mem_exists_aeval _ _ hmem
  exact aeval_jq_ne_jqN ℓ hpos P hP

end Headline

end PhiGen

section FractionField

private scoped instance instUFMAdjoinJq : UniqueFactorizationMonoid adjoinJq :=
  transcendental_jq.uniqueFactorizationMonoid_adjoin

private theorem algebraMap_comp_evalAtJAdj :
    (algebraMap adjoinJq ℚ⟮jq⟯).comp evalAtJAdj = evalAtJGen := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  change algebraMap adjoinJq ℚ⟮jq⟯ (evalAtJAdj Polynomial.X) = evalAtJGen Polynomial.X
  rw [show evalAtJAdj Polynomial.X = jAdj from Polynomial.eval₂_X _ _,
    show evalAtJGen Polynomial.X = jGen from Polynomial.eval₂_X _ _]
  exact Subtype.ext rfl

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem _root_.ModularCurve.ModularPolynomialData.aeval_jqN_toAdjoin :
    Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
  rw [Polynomial.aeval_def, toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

private theorem _root_.ModularCurve.ModularPolynomialData.minpoly_jqN_eq
    (hirr : PhiIrreducible data) :
    minpoly ℚ⟮jq⟯ (jqN N) = data.toAdjoin :=
  (minpoly.eq_of_irreducible_of_monic hirr data.aeval_jqN_toAdjoin data.toAdjoin_monic).symm

end ModularPolynomialData

end FractionField

namespace PhiGen

section Embed

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ]

private def qEmbedT : LaurentSeries ℚ →+* LaurentSeries K :=
  (qExpand K ℓ).comp (coeffMap (algebraMap ℚ K))

private theorem qEmbedT_apply (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = qExpand K ℓ (coeffMap (algebraMap ℚ K) x) := rfl

private theorem qEmbedT_injective : Function.Injective (qEmbedT K ℓ) :=
  (qEmbedT K ℓ).injective

private theorem qEmbedT_jq : qEmbedT K ℓ jq = qExpand K ℓ (coeffEmb K jq) := by
  rw [qEmbedT_apply, coeffMap_jq]

private theorem qEmbedT_eq_coeffEmb_qExpand (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = coeffEmb K (qExpand ℚ ℓ x) := by
  rw [coeffEmb_qExpand]
  rfl

private theorem coeffEmb_comp_qExpand_comp_evalAtJ :
    ((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ = (qEmbedT K ℓ).comp evalAtJ := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply]
  rw [qEmbedT_eq_coeffEmb_qExpand]

end Embed

section EmbedPrime

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem qEmbedT_jqN : qEmbedT K ℓ (jqN ℓ) = conj ℓ ζ (0 : Fin (ℓ + 1)) := by
  rw [conj_zero, qEmbedT_apply, jqN, coeffMap_qExpand, coeffMap_jq, qExpand_qExpand]

private theorem qTwist_comp_qEmbedT (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) :
    (qTwist (ζ ^ b)).comp (qEmbedT K ℓ) = qEmbedT K ℓ := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, qEmbedT_apply, qTwist_qExpand, zeta_pow_zpow_eq_one ℓ ζ hζ b,
    qTwist_one_apply]

private theorem conj_succ_zero : conj ℓ ζ (0 : Fin ℓ).succ = (coeffEmb K jq) := by
  rw [conj_succ, Fin.val_zero, pow_zero, qTwist_one_apply]

end EmbedPrime

section FactorAnalysis

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private def adjoinEmbedT : adjoinJq →+* LaurentSeries K :=
  (qEmbedT K ℓ).comp (algebraMap adjoinJq (LaurentSeries ℚ))

private theorem adjoinEmbedT_apply (x : adjoinJq) :
    adjoinEmbedT K ℓ x = qEmbedT K ℓ (x : LaurentSeries ℚ) := rfl

private theorem adjoinEmbedT_injective : Function.Injective (adjoinEmbedT K ℓ) :=
  fun _ _ h => Subtype.ext (qEmbedT_injective K ℓ h)

private theorem adjoinEmbedT_comp_evalAtJAdj :
    (adjoinEmbedT K ℓ).comp evalAtJAdj = (qEmbedT K ℓ).comp evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  change adjoinEmbedT K ℓ (evalAtJAdj Polynomial.X) = qEmbedT K ℓ (evalAtJ Polynomial.X)
  rw [show evalAtJAdj Polynomial.X = jAdj from Polynomial.eval₂_X _ _, evalAtJ_X]
  rfl

variable {K ℓ ζ}

private theorem eval_map_conj_succ_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0)
    (b : Fin ℓ) : (D.map (adjoinEmbedT K ℓ)).eval (conj ℓ ζ b.succ) = 0 := by
  have hcomp : (qTwist (ζ ^ (b : ℕ))).comp (adjoinEmbedT K ℓ) = adjoinEmbedT K ℓ := by
    rw [adjoinEmbedT, ← RingHom.comp_assoc, qTwist_comp_qEmbedT K ℓ ζ hζ]
  have key : qTwist (ζ ^ (b : ℕ)) ((D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
      = (D.map (adjoinEmbedT K ℓ)).eval (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
    rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]
  rw [conj_succ, ← key, h, map_zero]

private theorem le_natDegree_of_eval_map_jqK_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (hD : D ≠ 0)
    (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0) : ℓ ≤ D.natDegree := by
  have hmap : ℓ ≤ (D.map (adjoinEmbedT K ℓ)).natDegree := by
    by_contra hlt
    rw [not_le] at hlt
    have hzero : D.map (adjoinEmbedT K ℓ) = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
        (f := fun b : Fin ℓ => conj ℓ ζ b.succ)
        (fun b b' hbb' => Fin.succ_injective ℓ (conj_injective ℓ ζ hζ hbb'))
        (fun b => eval_map_conj_succ_eq_zero hζ h b)
        (by rwa [Fintype.card_fin])
    exact hD (Polynomial.map_injective _ (adjoinEmbedT_injective K ℓ)
      (by rw [hzero, Polynomial.map_zero]))
  exact le_trans hmap Polynomial.natDegree_map_le

private theorem eval_map_evalAtJAdj_ne_zero
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ))
    (β : adjoinJq) : (data.Φ.map evalAtJAdj).eval β ≠ 0 := by
  intro heval
  have hmap : (phiProd ℓ (conj ℓ ζ)).eval (adjoinEmbedT K ℓ β) = 0 := by
    rw [← hsplit, Polynomial.eval_map, Polynomial.eval₂_at_apply, heval, map_zero]
  rw [phiProd, Polynomial.eval_prod] at hmap
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hmap
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
  · rw [adjoinEmbedT_apply, ← qEmbedT_jqN K ℓ ζ] at hi
    have hβ : (β : LaurentSeries ℚ) = jqN ℓ := qEmbedT_injective K ℓ hi
    exact jqN_not_mem_adjoin_jq ℓ hpos (hβ ▸ β.2)
  · have h0 : (adjoinEmbedT K ℓ β).coeff (-1 : ℤ) = 0 := by
      rw [adjoinEmbedT_apply, qEmbedT_apply]
      refine qExpand_coeff_of_not_dvd _ _ ?_
      intro hdvd
      have h1 : ((ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp hdvd
      have h2 : ℓ ∣ 1 := by exact_mod_cast h1
      exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp h2)
    rw [hi, conj_succ_coeff_neg_one] at h0
    exact Units.ne_zero _ h0

private theorem isUnit_of_dvd_of_natDegree_le_one
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ))
    {B : Polynomial adjoinJq} (hdvd : B ∣ data.Φ.map evalAtJAdj)
    (hlc : IsUnit B.leadingCoeff) (hdeg : B.natDegree ≤ 1) : IsUnit B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    refine Polynomial.isUnit_C.mpr ?_
    have hc : B.coeff 0 = B.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
    rw [hc]
    exact hlc
  · exfalso
    obtain ⟨u, hu⟩ := hlc
    obtain ⟨D, hD⟩ := hdvd
    have hu1 : (u : adjoinJq) = B.coeff 1 := by rw [hu, Polynomial.leadingCoeff, h1]
    have hBev : ∀ x : adjoinJq, B.eval x = B.coeff 1 * x + B.coeff 0 := fun x => by
      conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
    have hroot : B.eval ((↑u⁻¹ : adjoinJq) * -B.coeff 0) = 0 := by
      rw [hBev, ← hu1]
      linear_combination (-B.coeff 0) * u.mul_inv
    refine eval_map_evalAtJAdj_ne_zero hpos data hsplit ((↑u⁻¹ : adjoinJq) * -B.coeff 0) ?_
    rw [hD, Polynomial.eval_mul, hroot, zero_mul]

end FactorAnalysis

section Irreducibility

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem irreducible_map_evalAtJAdj_of_splits
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    Irreducible (data.Φ.map evalAtJAdj) := by
  have hmonic : (data.Φ.map evalAtJAdj).Monic := data.monic.map _
  have hdeg : (data.Φ.map evalAtJAdj).natDegree = ℓ + 1 := by
    rw [data.monic.natDegree_map, data.natDegree_eq, ArithmeticFunction.dedekindPsi_prime hℓ.out]
  constructor
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by omega)
  · intro A B hAB
    have hA0 : A ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, mul_zero])
    have hlcmul : A.leadingCoeff * B.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hAB]
      exact hmonic.leadingCoeff
    have hlcA : IsUnit A.leadingCoeff := IsUnit.of_mul_eq_one _ hlcmul
    have hlcB : IsUnit B.leadingCoeff := IsUnit.of_mul_eq_one_right _ hlcmul
    have hAdvd : A ∣ data.Φ.map evalAtJAdj := ⟨B, hAB⟩
    have hBdvd : B ∣ data.Φ.map evalAtJAdj := ⟨A, hAB.trans (mul_comm A B)⟩
    have hsum : A.natDegree + B.natDegree = ℓ + 1 := by
      rw [← Polynomial.natDegree_mul hA0 hB0, ← hAB, hdeg]
    have hzero : ((A.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
        * ((B.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq)) = 0 := by
      rw [← Polynomial.eval_mul, ← Polynomial.map_mul, ← hAB, hsplit,
        ← conj_succ_zero K ℓ ζ]
      exact phiProd_eval_conj ℓ _ _
    rcases mul_eq_zero.mp hzero with hAz | hBz
    · right
      have hAdeg : ℓ ≤ A.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hA0 hAz
      exact isUnit_of_dvd_of_natDegree_le_one hpos data hsplit hBdvd hlcB (by omega)
    · left
      have hBdeg : ℓ ≤ B.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hB0 hBz
      exact isUnit_of_dvd_of_natDegree_le_one hpos data hsplit hAdvd hlcA (by omega)

private theorem toAdjoin_eq_map_evalAtJAdj {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    data.toAdjoin = (data.Φ.map evalAtJAdj).map (algebraMap adjoinJq ℚ⟮jq⟯) := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.map_map, algebraMap_comp_evalAtJAdj]

theorem phiIrreducible_of_splits (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data := by
  rw [coeffEmb_comp_qExpand_comp_evalAtJ K ℓ] at hsplit
  have hsplit' : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ)
      = phiProd ℓ (conj ℓ ζ) := by
    rw [Polynomial.map_map, adjoinEmbedT_comp_evalAtJAdj]
    exact hsplit
  change Irreducible data.toAdjoin
  rw [toAdjoin_eq_map_evalAtJAdj]
  exact ((data.monic.map evalAtJAdj).irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_map_evalAtJAdj_of_splits ℓ ζ one_le_coeff_jq hζ data hsplit')

end Irreducibility

end PhiGen

section SwapEval

private theorem eval₂_aeval_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries ℚ) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = Polynomial.aevalAeval x y Φ := by
  have h : Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) x).toRingHom y =
      (Polynomial.aevalAeval x y : Polynomial (Polynomial ℤ) →ₐ[ℤ] LaurentSeries ℚ).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact DFunLike.congr_fun h Φ

private theorem swap_eval₂ (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries ℚ) :
    (Polynomial.Bivariate.swap Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  rw [eval₂_aeval_eq_aevalAeval, eval₂_aeval_eq_aevalAeval, Polynomial.Bivariate.aevalAeval_swap]

private theorem evalSymm_of_swap_eq {Φ : Polynomial (Polynomial ℤ)}
    (h : Polynomial.Bivariate.swap Φ = Φ) : EvalSymm Φ := fun x y => by
  conv_lhs => rw [← h]
  exact swap_eval₂ Φ x y

end SwapEval

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

private theorem _root_.ModularCurve.ModularPolynomialData.aeval_jqN_transposeToAdjoin
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) :
    Polynomial.aeval (jqN N) ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen,
    evalAtJ_def, swap_eval₂, ← evalAtJqN_def]
  exact hswap

private theorem _root_.ModularCurve.ModularPolynomialData.swap_eq_of_irreducible
    (hirr : PhiIrreducible data)
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0)
    (hTmonic : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).natDegree ≤
      ArithmeticFunction.dedekindPsi N) :
    Polynomial.Bivariate.swap data.Φ = data.Φ := by
  apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
  change (Polynomial.Bivariate.swap data.Φ).map evalAtJGen = data.toAdjoin
  have hdvd : data.toAdjoin ∣ (Polynomial.Bivariate.swap data.Φ).map evalAtJGen := by
    rw [← data.minpoly_jqN_eq hirr]
    exact minpoly.dvd _ _ (data.aeval_jqN_transposeToAdjoin hswap)
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le data.toAdjoin_monic hTmonic hdvd ?_
  rw [toAdjoin, data.monic.natDegree_map, data.natDegree_eq]
  exact hTdeg

private theorem _root_.ModularCurve.ModularPolynomialData.evalSymm_of_irreducible
    (hirr : PhiIrreducible data)
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0)
    (hTmonic : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).natDegree ≤
      ArithmeticFunction.dedekindPsi N) :
    EvalSymm data.Φ :=
  evalSymm_of_swap_eq (data.swap_eq_of_irreducible hirr hswap hTmonic hTdeg)

end ModularPolynomialData

section Engine

private theorem degree_swap_lt {Ψ : Polynomial (Polynomial ℤ)} {D : ℕ}
    (h : ∀ k, (Ψ.coeff k).degree < (D : WithBot ℕ)) :
    (Polynomial.Bivariate.swap Ψ).degree < (D : WithBot ℕ) := by
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow Ψ, map_sum]
  refine (Polynomial.degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe D)).2 fun k _ => ?_)
  rw [map_mul, map_pow, Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y, ← map_pow]
  refine lt_of_le_of_lt (le_trans (Polynomial.degree_mul_le _ _) ?_) (h k)
  calc ((Ψ.coeff k).map Polynomial.C).degree + (Polynomial.C (Polynomial.X ^ k)).degree
      ≤ (Ψ.coeff k).degree + 0 := by
        gcongr
        · exact le_of_eq (Polynomial.degree_map_eq_of_injective Polynomial.C_injective _)
        · exact Polynomial.degree_C_le
    _ = (Ψ.coeff k).degree := add_zero _

private theorem swap_monic_of_coeff_bounds {Φ : Polynomial (Polynomial ℤ)} {d : ℕ}
    (h0 : (Φ.coeff 0).Monic) (h0deg : (Φ.coeff 0).natDegree = d)
    (hk : ∀ k, k ≠ 0 → (Φ.coeff k).degree < (d : WithBot ℕ)) :
    (Polynomial.Bivariate.swap Φ).Monic ∧ (Polynomial.Bivariate.swap Φ).natDegree = d := by
  have hsplit : Polynomial.Bivariate.swap Φ =
      Polynomial.C Polynomial.X * Polynomial.Bivariate.swap Φ.divX
        + (Φ.coeff 0).map Polynomial.C := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Φ]
    rw [map_add, map_mul, Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C]
  have hmap : ((Φ.coeff 0).map Polynomial.C).Monic := h0.map _
  have hmapdeg : ((Φ.coeff 0).map Polynomial.C).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmap.ne_zero, h0.natDegree_map, h0deg]
  have hsmall : (Polynomial.C Polynomial.X * Polynomial.Bivariate.swap Φ.divX).degree
      < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hX : (Polynomial.C (Polynomial.X : Polynomial ℤ)).degree = 0 :=
      Polynomial.degree_C Polynomial.X_ne_zero
    rw [hX, zero_add]
    exact degree_swap_lt fun k => by
      rw [Polynomial.coeff_divX]; exact hk (k + 1) (Nat.succ_ne_zero k)
  have hlt : (Polynomial.C Polynomial.X * Polynomial.Bivariate.swap Φ.divX).degree
      < ((Φ.coeff 0).map Polynomial.C).degree := by rw [hmapdeg]; exact hsmall
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact hmap.add_of_right hlt
  · rw [hsplit, Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_right_of_degree_lt hlt), h0.natDegree_map, h0deg]

end Engine

section Dictionary

private theorem degree_lt_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D ≤ m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.degree < (D : WithBot ℕ) := by
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe D
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0]
  by_contra hle
  rw [not_lt] at hle
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := P.natDegree) hQdeg.le
  rw [← PhiGen.evalAtJ_eq_aeval_map, h P.natDegree hle, Polynomial.coeff_map,
    eq_intCast] at hcoeff
  have hlead : P.coeff P.natDegree = 0 := by exact_mod_cast hcoeff.symm
  exact hP0 (Polynomial.leadingCoeff_eq_zero.mp hlead)

private theorem monic_of_evalAtJ_coeff_eq_one {P : Polynomial ℤ} {D : ℕ}
    (hle : P.natDegree ≤ D) (h1 : (evalAtJ P).coeff (-(D : ℤ)) = 1) :
    P.Monic ∧ P.natDegree = D := by
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := D) (hQdeg.le.trans hle)
  rw [← PhiGen.evalAtJ_eq_aeval_map, h1, Polynomial.coeff_map, eq_intCast] at hcoeff
  have hPD : P.coeff D = 1 := by exact_mod_cast hcoeff.symm
  have hge : D ≤ P.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hPD]; exact one_ne_zero)
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one D hle hPD, le_antisymm hle hge⟩

private theorem natDegree_le_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D < m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.natDegree ≤ D := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  by_contra hlt
  rw [not_le] at hlt
  have hdeg := degree_lt_of_evalAtJ_coeff_eq_zero (P := P) (D := D + 1)
    (fun m hm => h m (by omega))
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0] at hdeg
  omega

end Dictionary

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

private theorem _root_.ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_coeff_bounds
    (h0 : (data.Φ.coeff 0).Monic)
    (h0deg : (data.Φ.coeff 0).natDegree = ArithmeticFunction.dedekindPsi N)
    (hk : ∀ k, k ≠ 0 → (data.Φ.coeff k).degree < (ArithmeticFunction.dedekindPsi N : WithBot ℕ)) :
    ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).Monic ∧
      ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).natDegree =
        ArithmeticFunction.dedekindPsi N := by
  obtain ⟨hmonic, hdeg⟩ := swap_monic_of_coeff_bounds h0 h0deg hk
  exact ⟨hmonic.map _, by rw [hmonic.natDegree_map, hdeg]⟩

theorem transposeToAdjoin_monic_of_qExpansion
    (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(ArithmeticFunction.dedekindPsi N : ℤ)) = 1)
    (h0le : ∀ m : ℕ, ArithmeticFunction.dedekindPsi N < m →
      (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0)
    (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, ArithmeticFunction.dedekindPsi N ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) :
    ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).Monic ∧
      ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).natDegree =
        ArithmeticFunction.dedekindPsi N := by
  obtain ⟨h0monic, h0deg⟩ := monic_of_evalAtJ_coeff_eq_one
    (natDegree_le_of_evalAtJ_coeff_eq_zero h0le) h0top
  exact data.transposeToAdjoin_monic_of_coeff_bounds h0monic h0deg
    fun k hk0 => degree_lt_of_evalAtJ_coeff_eq_zero (hk k hk0)

end ModularPolynomialData

namespace PhiGen

section Swap

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem eval_swap_eq_zero_of_splits (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) :
    data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 := by
  rw [coeffEmb_comp_qExpand_comp_evalAtJ K ℓ] at hsplit
  have h1 : data.Φ.eval₂ ((qEmbedT K ℓ).comp evalAtJ) (coeffEmb K jq) = 0 := by
    rw [← Polynomial.eval_map, hsplit, ← conj_succ_zero K ℓ ζ, phiProd,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin ℓ).succ)) (by simp)
  have h2 : data.Φ.eval₂ ((qExpand K ℓ).comp ((qEmbedT K ℓ).comp evalAtJ))
      (qExpand K ℓ (coeffEmb K jq)) = 0 := by
    have h := congrArg (qExpand K ℓ) h1
    rwa [Polynomial.hom_eval₂, map_zero] at h
  apply qEmbedT_injective K ℓ
  rw [map_zero, Polynomial.hom_eval₂, qEmbedT_jq]
  have hhom : (qEmbedT K ℓ).comp (evalAtJqN ℓ)
      = (qExpand K ℓ).comp ((qEmbedT K ℓ).comp evalAtJ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    change qEmbedT K ℓ (evalAtJqN ℓ Polynomial.X)
      = qExpand K ℓ (qEmbedT K ℓ (evalAtJ Polynomial.X))
    rw [evalAtJqN_X, evalAtJ_X, qEmbedT_jq, qEmbedT_jqN K ℓ ζ, conj_zero, qExpand_qExpand]
  rw [hhom]
  exact h2

theorem evalSymm_of_splits (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ))
    (hTmonic : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((Polynomial.Bivariate.swap data.Φ).map evalAtJGen).natDegree ≤
      ArithmeticFunction.dedekindPsi ℓ) :
    EvalSymm data.Φ :=
  data.evalSymm_of_irreducible (phiIrreducible_of_splits ℓ ζ hζ data hsplit)
    (eval_swap_eq_zero_of_splits ℓ ζ data hsplit) hTmonic hTdeg

end Swap

end PhiGen

end ModularCurve

end
