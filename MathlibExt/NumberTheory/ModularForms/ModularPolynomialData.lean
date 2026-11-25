/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_X0.lean`
and
`Definitions/Def_ModularCurve_PhiGen.lean`
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

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.LaurentSeries
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi
public import MathlibExt.NumberTheory.ModularForms.JCoefficientBound

@[expose] public section

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section QExpand

variable {R : Type*} [CommRing R]

variable (R) in
def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ} (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

@[simp]
theorem qExpand_C (r : R) : qExpand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C

theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective

theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]

theorem qExpand_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) (f : LaurentSeries R) :
    qExpand R M f = qExpand R K f := by
  subst h; rfl

theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM

end QExpand

section RatAlgebra

variable (N : ℕ) [NeZero N]

theorem algebraMap_apply_eq_single (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c := by
  have h1 : algebraMap ℚ (PowerSeries ℚ) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

def qExpandₐ : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ where
  __ := qExpand ℚ N
  commutes' r := by
    show qExpand ℚ N (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r
    rw [algebraMap_apply_eq_single, qExpand_single, mul_zero]

@[simp]
theorem qExpandₐ_apply (f : LaurentSeries ℚ) : qExpandₐ N f = qExpand ℚ N f := rfl

end RatAlgebra

def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq

@[simp]
theorem jqN_one : jqN 1 = jq := qExpand_one_apply jq

section NamedInputs

def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp]
theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]

structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where

  Φ : Polynomial (Polynomial ℤ)

  monic : Φ.Monic

  natDegree_eq : Φ.natDegree = ArithmeticFunction.dedekindPsi N

  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0

def modularPolynomialDataOne : ModularPolynomialData 1 where
  Φ := Polynomial.X - Polynomial.C Polynomial.X
  monic := Polynomial.monic_X_sub_C _
  natDegree_eq := by simp
  eval_eq_zero := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, jqN_one,
      evalAtJ_X, sub_self]

def FunctionFieldGeneration (M : ℕ) [NeZero M] : Prop :=
  ∀ d : ℕ, d ∣ M → ∀ (_ : NeZero d), qExpand ℚ d jq ∈
    IntermediateField.adjoin ℚ {jq, qExpand ℚ M jq}

theorem functionFieldGeneration_one : FunctionFieldGeneration 1 := by
  intro d hd hne
  haveI := hne
  rw [Nat.dvd_one] at hd
  subst hd
  exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end NamedInputs

section FunctionField

variable (N : ℕ) [NeZero N]

def modularFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq}

theorem jq_mem : jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

theorem jqN_mem : qExpand ℚ N jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

theorem modularFunctionField_one : modularFunctionField 1 = ℚ⟮jq⟯ := by
  rw [modularFunctionField, qExpand_one_apply, Set.pair_eq_singleton]

theorem adjoin_jq_le : ℚ⟮jq⟯ ≤ modularFunctionField N := by
  rw [IntermediateField.adjoin_le_iff]
  exact Set.singleton_subset_iff.mpr (jq_mem N)

end FunctionField

def jGen : ℚ⟮jq⟯ := ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩

def evalAtJGen : Polynomial ℤ →+* ℚ⟮jq⟯ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℚ⟮jq⟯) jGen

theorem algebraMap_comp_evalAtJGen :
    (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)).comp evalAtJGen = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) (evalAtJGen Polynomial.X) = evalAtJ Polynomial.X
  rw [evalAtJ_X]
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)
    (Polynomial.eval₂ (Int.castRingHom ℚ⟮jq⟯) jGen Polynomial.X) = jq
  rw [Polynomial.eval₂_X]
  rfl

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

def toAdjoin : Polynomial ℚ⟮jq⟯ := data.Φ.map evalAtJGen

theorem toAdjoin_monic : data.toAdjoin.Monic := data.monic.map _

end ModularPolynomialData

section AllDivisors

variable (N : ℕ) [NeZero N]

def divisorExpansions : Set (LaurentSeries ℚ) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand ℚ d jq}

omit [NeZero N] in
theorem mem_divisorExpansions {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ divisorExpansions N :=
  ⟨d, ‹_›, hd, rfl⟩

def modularFunctionFieldFull : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions N)

omit [NeZero N] in
theorem jqd_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ modularFunctionFieldFull N :=
  subset_adjoin ℚ _ (mem_divisorExpansions N hd)

theorem modularFunctionField_le_full :
    modularFunctionField N ≤ modularFunctionFieldFull N := by
  rw [modularFunctionField, adjoin_le_iff]
  rintro x (rfl | rfl)
  · have h := jqd_mem_full N (one_dvd N)
    rwa [qExpand_one_apply] at h
  · exact jqd_mem_full N dvd_rfl

theorem full_degeneracy_le {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) :
    modularFunctionFieldFull N ≤ modularFunctionFieldFull M := by
  rw [modularFunctionFieldFull, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  exact jqd_mem_full M (hdvd.trans h)

omit [NeZero N] in

theorem full_degeneracy_map_le (ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFull N).map (qExpandₐ ℓ) ≤ modularFunctionFieldFull (N * ℓ) := by
  rw [modularFunctionFieldFull, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  haveI := hne
  haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  show qExpandₐ ℓ (qExpand ℚ d jq) ∈ _
  rw [qExpandₐ_apply, qExpand_qExpand]
  exact jqd_mem_full (N * ℓ) ((mul_dvd_mul_left ℓ hdvd).trans (dvd_of_eq (mul_comm ℓ N)))

theorem qExpandₐ_comp (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] :
    (qExpandₐ ℓ).comp (qExpandₐ ℓ') = qExpandₐ (ℓ * ℓ') := by
  refine AlgHom.ext fun f => ?_
  simp only [AlgHom.comp_apply, qExpandₐ_apply]
  exact qExpand_qExpand ℓ' ℓ f

end AllDivisors

/-- Symmetry of a bivariate integral polynomial under exchanging the two
variables, evaluated on Laurent series. -/
def EvalSymm (Φ : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ x y : LaurentSeries ℚ,
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x

/-- The level-one modular polynomial data, given by `X - Y`, is an exemplar
of the carrier. -/
theorem nonempty_modularPolynomialData_one :
    Nonempty (ModularPolynomialData 1) :=
  ⟨modularPolynomialDataOne⟩

end ModularCurve
