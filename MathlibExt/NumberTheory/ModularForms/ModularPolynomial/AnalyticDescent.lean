/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`,
`P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`,
`Theorems/Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean`,
and
`P2M/Sol/S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean`
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

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.HeckeCosets
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.SlashInvariant
import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

private def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

private lemma add (hA : RealL h A F) (hB : RealL h B G) : RealL h (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

private lemma neg (hA : RealL h A F) : RealL h (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

private lemma sub (hA : RealL h A F) (hB : RealL h B G) : RealL h (A - B) (F - G) := fun τ => by
  simpa [sub_mul] using (hA τ).sub (hB τ)

private lemma mul (hh : 0 < h) (hA : RealL h A F) (hB : RealL h B G) : RealL h (A * B) (F * G) :=
    fun τ =>
  hasSum_qParam_mul_laurent h hh A B F G hA hB τ

private lemma single (h : ℝ) (a : ℂ) (n : ℤ) :
    RealL h (HahnSeries.single n a) (fun τ => a * 𝕢 h (τ : ℂ) ^ n) := fun τ => by
  refine (hasSum_ite_eq n (a * 𝕢 h (τ : ℂ) ^ n)).congr_fun fun m => ?_
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, hm]

private lemma C (h : ℝ) (a : ℂ) : RealL h (HahnSeries.C a) (fun _ => a) := by
  simpa using single h a 0

private lemma one (h : ℝ) : RealL h 1 1 := by
  have h__af := C h 1
  simp at h__af
  exact h__af

private lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

private lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A') (h2 : ∀ τ,
    F τ = F' τ) :
    RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

private lemma prod (hh : 0 < h) {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => (have h__af := one h; simp at h__af ⊢; exact h__af)
  | insert a s ha ih =>
    have h1 := (hAF a (Finset.mem_insert_self a s)).mul hh (ih fun i hi =>
        hAF i (Finset.mem_insert_of_mem hi))
    refine h1.congr (Finset.prod_insert ha).symm fun τ => ?_
    simp [Finset.prod_insert ha]

private lemma coeff_prod_X_sub_C (hh : 0 < h) {ι : Type} (s : Finset ι) {a : ι → LaurentSeries ℂ}
    {α : ι → ℍ → ℂ} (haα : ∀ i ∈ s, RealL h (a i) (α i)) (k : ℕ) :
    RealL h ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (fun τ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    by_cases hk : k = 0
    · subst hk; (have h__af := one h; simp at h__af ⊢; exact h__af)
    · have h__af := zero h
      simp [hk] at h__af ⊢
      exact h__af
  | insert b s hb ih =>
    have ih' := fun k => ih (fun i hi => haα i (Finset.mem_insert_of_mem hi)) k
    have hb' := haα b (Finset.mem_insert_self b s)
    have hA : (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (a i))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) * (Polynomial.X - Polynomial.C (a b)) :=
      (Finset.prod_insert hb).trans (mul_comm (G := Polynomial (LaurentSeries ℂ)) _ _)
    have hfun : ∀ τ : ℍ, (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (α i τ))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))) * (Polynomial.X - Polynomial.C (α b τ)) :=
      fun τ => (Finset.prod_insert hb).trans (mul_comm (G := Polynomial ℂ) _ _)
    cases k with
    | zero =>
      refine ((ih' 0).mul hh hb').neg.congr ?_ fun τ => ?_
      · rw [hA, Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub]
        exact (mul_neg (α := LaurentSeries ℂ) _ _).symm
      · simp only [hfun τ, Polynomial.mul_coeff_zero, Pi.neg_apply, Pi.mul_apply,
          Polynomial.coeff_sub,
          Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    | succ k =>
      refine ((ih' k).sub ((ih' (k + 1)).mul hh hb')).congr ?_ fun τ => ?_
      · rw [hA, Polynomial.coeff_mul_X_sub_C]
      · simp only [hfun τ, Polynomial.coeff_mul_X_sub_C, Pi.sub_apply, Pi.mul_apply]

end RealL

section Sigma

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

private def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

private lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

private def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  let : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

variable (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

private lemma sigma_zeta : sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  let : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ := ⟨expRoot ℓ,
      (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit hℓ in
private lemma sigma_ratCast' (σ : CyclotomicField ℓ ℚ →+* ℂ) (q : ℚ) :
    σ (q : CyclotomicField ℓ ℚ) = (q : ℂ) :=
  map_ratCast σ q

end Sigma

section JT

private def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

private def jqC : LaurentSeries ℂ := coeffMap castC jq

private lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

private lemma realL_jqC : RealL 1 jqC jt := fun τ => ModularCurve.hasSum_jq_qParam τ

end JT

section Translates

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
  (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

private def conjC (i : Fin (ℓ + 1)) : LaurentSeries ℂ := coeffMap (sigma ℓ ζ hζ) (PhiGen.conj ℓ ζ i)

private def rep (i : Fin (ℓ + 1)) : GL (Fin 2) ℝ :=
  Fin.cases (ModularForm.heckeDiagMatrix ℓ) (fun b : Fin ℓ =>
      ModularForm.heckeUpperMatrix ℓ (b : ℕ)) i

omit hℓ in
@[scoped simp] private lemma rep_zero : rep ℓ 0 = ModularForm.heckeDiagMatrix ℓ := by simp [rep]
omit hℓ in
@[scoped simp] private lemma rep_succ (b : Fin ℓ) :
    rep ℓ b.succ = ModularForm.heckeUpperMatrix ℓ (b : ℕ) := by simp [rep]

private lemma realL_conjC_zero : RealL ℓ (conjC ℓ ζ hζ 0) (fun τ =>
    jt (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  intro τ
  have h := ModularCurve.hasSum_qParam_heckeDiagMatrix_smul ℓ jqC jt realL_jqC τ
  have hconj : conjC ℓ ζ hζ 0 = qExpand ℂ (ℓ * ℓ) jqC := by
    rw [conjC, PhiGen.conj_zero, coeffMap_qExpand]
    congr 1
    ext m
    simp [jqC_coeff, map_ratCast]
  rw [hconj]
  exact h

omit hℓ in
private lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

private lemma realL_conjC_succ (b : Fin ℓ) :
    RealL ℓ (conjC ℓ ζ hζ b.succ) (fun τ => jt (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ)) := by
  intro τ
  have h := ModularCurve.hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) jqC jt realL_jqC τ
  refine h.congr_fun fun m => ?_
  congr 1
  rw [conjC, PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, Units.val_pow_eq_pow_val, map_pow, sigma_zeta, expRoot_pow_zpow]
  congr 1
  simp [jqC_coeff, map_ratCast]

private lemma realL_conjC (i : Fin (ℓ + 1)) : RealL ℓ (conjC ℓ ζ hζ i) (fun τ =>
    jt (rep ℓ i • τ)) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · simpa only [rep_zero] using realL_conjC_zero ℓ ζ hζ
  · simpa only [rep_succ] using realL_conjC_succ ℓ ζ hζ b

private lemma map_phiProd : (PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ)) =
    ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjC ℓ ζ hζ i)) := by
  rw [PhiGen.phiProd, ← Polynomial.coe_mapRingHom, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conjC]

private lemma realL_phiProd_coeff (k : ℕ) :
    RealL ℓ (((PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ))).coeff k)
      (fun τ => (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))).coeff k) := by
  rw [map_phiProd]
  exact RealL.coeff_prod_X_sub_C (by exact_mod_cast hℓ.out.pos) Finset.univ
    (fun i _ => realL_conjC ℓ ζ hζ i) k

private lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hx : RealL ℓ (qExpand ℂ ℓ x) F) :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

private lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap (sigma ℓ ζ hζ) (coeffEmb (CyclotomicField ℓ ℚ) x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

include hζ in
private theorem hasSum_coeff_of_phiGenDescends (c : ℕ → LaurentSeries ℚ)
    (hc : PhiGen.PhiGenDescends ℓ ζ c)
    (k : ℕ) (τ : ℍ) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C
          (ModularForm.E₄ (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ) ^ 3 /
            ModularForm.discriminant (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ)))).coeff k) := by
  have h1 := realL_phiProd_coeff ℓ ζ hζ k
  rw [Polynomial.coeff_map, hc k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1 τ
  have hprod : (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))) =
      (Polynomial.X - Polynomial.C (jt (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ,
            (Polynomial.X - Polynomial.C (jt (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ))) := by
    rw [Fin.prod_univ_succ]; simp only [rep_zero, rep_succ]
  rw [hprod] at h2
  exact h2

end Translates

end ModularCurve

theorem ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ)
    (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C
          (ModularForm.E₄ (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ) ^ 3 /
            ModularForm.discriminant (ModularForm.heckeUpperMatrix ℓ (b : ℕ) • τ)))).coeff k) :=
  ModularCurve.hasSum_coeff_of_phiGenDescends ℓ ζ hζ c hc k τ

end

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

section JT

private lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

end JT

end ModularCurve

open ModularCurve ModularCurve.PhiGen in
theorem ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)
    (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq} := by
  refine ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant (c k) _
    (ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff ℓ ζ hζ c hc k) fun γ τ => ?_
  exact congrArg (fun p : Polynomial ℂ => p.coeff k)
    (ModularCurve.cosetPoly_smul ℓ hℓ.out ModularCurve.jt ModularCurve.jt_smul γ τ)

end
