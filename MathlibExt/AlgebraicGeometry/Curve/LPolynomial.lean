/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_exists_LPolynomial_of_finite.lean`,
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`,
`Definitions/Def_AlgebraicCurve_IsCurveOver.lean`,
`Definitions/Def_AlgebraicCurve_AdelicIndex.lean`
and
`P2M/Sol/S_AlgebraicCurve_exists_LPolynomial_of_finite.lean`
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

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Bezout
public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.AlgebraicGeometry.Curve.Place

import Mathlib.LinearAlgebra.Projectivization.Cardinality

@[expose] public section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

/-- The degree of a place: the dimension of its residue field over the base. -/
noncomputable def deg (v : Place K F) : ℕ :=
  Module.finrank K (IsLocalRing.ResidueField v.toValuationSubring)

variable (v : Place K F)

theorem adicValuation_le_one_of_mem {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_algebraMap_le_one (a : K) :
    v.adicValuation (algebraMap K F a) ≤ 1 :=
  v.adicValuation_le_one_of_mem (v.algebraMap_mem' a)

theorem adicValuation_eq_exp_neg_ord {f : F} (hf : f ≠ 0) :
    v.adicValuation f = exp (-v.ord f) := by
  unfold ord
  rw [neg_neg, exp_log (v.adicValuation_ne_zero hf)]

theorem adicValuation_le_exp_iff {f : F} {n : ℤ} :
    v.adicValuation f ≤ exp n ↔ f = 0 ∨ -n ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [v.adicValuation_eq_exp_neg_ord hf, exp_le_exp, neg_le, or_iff_right hf]

end Place

/-- A divisor on a curve: a finitely supported integer combination of places. -/
abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor

variable {K F}

/-- The degree of a divisor, weighted by the degrees of its places. -/
noncomputable def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

/-- The subgroup of degree-zero divisors. -/
noncomputable def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero ↔ degree D = 0 := Iff.rfl

/-- A divisor is principal when it is the divisor of a nonzero function. -/
def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

/-- The subgroup of principal divisors. -/
noncomputable def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} : D ∈ principal ↔ IsPrincipal D := Iff.rfl

theorem degree_nonneg_of_nonneg {E : Divisor K F}
    (hE : ∀ w, 0 ≤ E w) : 0 ≤ degree E := by
  have hsum : degree E = ∑ v ∈ E.support, E v * (v.deg : ℤ) := by
    simp [degree, Finsupp.sum]
  rw [hsum]
  refine Finset.sum_nonneg fun v _ => ?_
  exact mul_nonneg (hE v) (by exact_mod_cast Nat.zero_le _)

end Divisor

/-- The degree-zero Picard group of a curve. -/
abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0

variable {K F}

/-- The class of a degree-zero divisor in the Picard group. -/
noncomputable def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E := rfl

end Pic0

variable {K F}

/-- The Riemann-Roch space of a divisor: functions whose poles are bounded by
the divisor at every place. -/
def LSpace (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ v : Place K F, v.adicValuation f ≤ exp (D v)}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro f g hf hg v
    exact (Valuation.map_add _ _ _).trans (max_le (hf v) (hg v))
  smul_mem' := by
    intro c f hf v
    change v.adicValuation (c • f) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    calc v.adicValuation (algebraMap K F c) * v.adicValuation f
        ≤ 1 * v.adicValuation f := by
          gcongr
          exact v.adicValuation_algebraMap_le_one c
      _ = v.adicValuation f := one_mul _
      _ ≤ exp (D v) := hf v

/-- The dimension of the Riemann-Roch space of a divisor. -/
noncomputable def ell (D : Divisor K F) : ℕ := Module.finrank K (LSpace D)

theorem mem_lSpace_iff {D : Divisor K F} {f : F} :
    f ∈ LSpace D ↔ ∀ v : Place K F, v.adicValuation f ≤ exp (D v) := Iff.rfl

theorem mem_lSpace_iff_ord {D : Divisor K F} {f : F} :
    f ∈ LSpace D ↔ f = 0 ∨ ∀ v : Place K F, -D v ≤ v.ord f := by
  rw [mem_lSpace_iff]
  constructor
  · intro h
    by_cases hf : f = 0
    · exact Or.inl hf
    · refine Or.inr fun v => ?_
      rcases (v.adicValuation_le_exp_iff).mp (h v) with h0 | h0
      · exact absurd h0 hf
      · exact h0
  · intro h v
    rcases h with rfl | h
    · simp
    · exact (v.adicValuation_le_exp_iff).mpr (Or.inr (h v))

theorem mul_mem_lSpace_add {A B : Divisor K F} {f g : F}
    (hf : f ∈ LSpace A) (hg : g ∈ LSpace B) : f * g ∈ LSpace (A + B) := by
  intro v
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  rw [map_mul, show (A + B) v = A v + B v from Finsupp.add_apply A B v, WithZero.exp_add]
  exact mul_le_mul (hf v) (hg v) (zero_le') (zero_le')

/-- The constants of the function field are exactly the base field. -/
def ConstantsAreBase (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F)

theorem ell_zero_eq_one_of_constantsAreBase (h : ConstantsAreBase K F) :
    ell (0 : Divisor K F) = 1 := by
  rw [ell, h, LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
    (algebraMap K F).injective, Module.finrank_self]

/-- The adele space of a curve, used to define its genus. -/
def repartitions (K F : Type*) [Field K] [Field F] [Algebra K F] :
    Subalgebra F (Place K F → F) :=
  Algebra.adjoin F
    {α : Place K F → F | {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite}

/-- Bounded repartitions for a divisor. -/
def repartitionsOf (K F : Type*) [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) : Submodule K ↥(repartitions K F) where
  carrier :=
    {α | ∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ exp (D v)}
  zero_mem' := by
    intro v
    change v.adicValuation (0 : F) ≤ exp (D v)
    simp
  add_mem' := by
    intro α β hα hβ v
    exact (Valuation.map_add _ _ _).trans (max_le (hα v) (hβ v))
  smul_mem' := by
    intro c α hα v
    change v.adicValuation (c • (α : Place K F → F) v) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    calc v.adicValuation (algebraMap K F c) *
          v.adicValuation ((α : Place K F → F) v)
        ≤ 1 * v.adicValuation ((α : Place K F → F) v) := by
          gcongr
          exact v.adicValuation_algebraMap_le_one c
      _ = v.adicValuation ((α : Place K F → F) v) := one_mul _
      _ ≤ exp (D v) := hα v

/-- Principal repartitions: the diagonally embedded function field. -/
def principalRepartitions (K F : Type*) [Field K] [Field F] [Algebra K F] :
    Submodule K ↥(repartitions K F) :=
  (LinearMap.range (Algebra.linearMap F ↥(repartitions K F))).restrictScalars K

/-- The first cohomology of the structure sheaf twisted by a divisor, as a
quotient of the repartitions. -/
abbrev H1 (K F : Type*) [Field K] [Field F] [Algebra K F] (D : Divisor K F) : Type _ :=
  ↥(repartitions K F) ⧸ (repartitionsOf K F D ⊔ principalRepartitions K F)

/-- The genus of a curve: the dimension of `H1` of the structure sheaf. -/
noncomputable def genusFF (K F : Type*) [Field K] [Field F] [Algebra K F] : ℕ :=
  Module.finrank K (H1 K F (0 : Divisor K F))

/-- A curve over `K` with function field `F`, as in the cited source: every
residue field is finite over the base, every nonzero function has a principal
divisor of degree zero, and the Kähler differentials of `F` over `K` form a
free `F`-module of rank one. -/
class IsCurveOver (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop where
  /-- Every residue field is finite over the base. -/
  finiteResidue : ∀ v : Place K F,
    Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring)
  /-- Every nonzero function has a principal divisor of degree zero. -/
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0
  /-- The Kähler differentials of `F` over `K` are free of rank one. -/
  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

namespace IsCurveOver

theorem finiteResidueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring) :=
  IsCurveOver.finiteResidue v

theorem one_le_deg [IsCurveOver K F] (v : Place K F) : 1 ≤ v.deg := by
  haveI := IsCurveOver.finiteResidue v
  rw [Place.deg]
  exact Module.finrank_pos

end IsCurveOver

section Counts

open Polynomial
open scoped LinearAlgebra.Projectivization

private def geom (r : ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => r ^ n

private theorem one_sub_mul_geom (r : ℤ) :
    (1 - PowerSeries.C r * PowerSeries.X) * geom r = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [geom, pow_succ, mul_comm]

private theorem reflect_comp_eq (q : ℤ) (g' : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ 2 * g')
    (H3 : ∀ n, n ≤ 2 * g' → q ^ g' * P.coeff n = q ^ n * P.coeff (2 * g' - n)) :
    (reflect (2 * g') P).comp (C q * X) = C (q ^ g') * P := by
  ext n
  rw [comp_C_mul_X_coeff, coeff_reflect, coeff_C_mul]
  by_cases hn : n ≤ 2 * g'
  · rw [revAt_le hn, mul_comm, ← H3 n hn]
  · push Not at hn
    have h1 : (revAt (2 * g')) n = n := by
      have hfun : revAtFun (2 * g') n = n := if_neg (not_le.mpr hn)
      rwa [revAtFun_eq] at hfun
    rw [h1, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hn), zero_mul, mul_zero]

private theorem lpoly_of_counts (q h : ℤ) (hq1 : q - 1 ≠ 0) (g : ℕ) (A T : ℕ → ℤ)
    (H1 : ∀ n, (q - 1) * A n + h = T n)
    (H2 : ∀ n, 2 * g ≤ n + 1 → T n = h * q ^ (n + 1 - g))
    (H3 : ∀ n, n + 2 ≤ 2 * g → q ^ (g - 1) * T n = q ^ n * T (2 * g - 2 - n))
    (H4 : A 0 = 1) :
    ∃ L : Polynomial ℤ, L.natDegree ≤ 2 * g ∧ L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * g, L.coeff (2 * g - i) * q ^ i = q ^ g * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk A =
        (L : PowerSeries ℤ) := by
  set W : PowerSeries ℤ :=
    (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk A with hW
  have hZ : PowerSeries.C (q - 1) * PowerSeries.mk A =
      PowerSeries.mk T - PowerSeries.C h * geom 1 := by
    ext n
    rw [PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_C_mul]
    simp [geom, ← H1 n]
  have hg1 : (1 - PowerSeries.X) * geom 1 = 1 := by simpa using one_sub_mul_geom 1
  have hgq := one_sub_mul_geom q
  have hW0 : PowerSeries.coeff 0 W = 1 := by
    simp [hW, PowerSeries.coeff_zero_eq_constantCoeff_apply, H4]
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · subst hg0
    have hT : PowerSeries.mk T = PowerSeries.C h * PowerSeries.C q * geom q := by
      ext n
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
      simp [geom, H2 n (by omega), pow_succ, mul_comm, mul_left_comm]
    have hW1 : PowerSeries.C (q - 1) * W = PowerSeries.C (q - 1) * PowerSeries.C h := by
      rw [hW]
      linear_combination (norm := skip)
        ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) * hZ +
        ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) * hT +
        (PowerSeries.C h * PowerSeries.C q * (1 - PowerSeries.X)) * hgq -
        (PowerSeries.C h * (1 - PowerSeries.C q * PowerSeries.X)) * hg1
      simp only [map_sub, map_one]
      ring
    have hW2 : W = PowerSeries.C h := by
      ext n
      have h1 := congrArg (PowerSeries.coeff n) hW1
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at h1
      exact mul_left_cancel₀ hq1 h1
    have hh : h = 1 := by
      have hcc := hW0
      rwa [hW2, PowerSeries.coeff_zero_C] at hcc
    refine ⟨1, by simp, by simp, fun i hi => ?_, ?_⟩
    · obtain rfl : i = 0 := by omega
      simp
    · rw [hW2, hh]; simp
  · obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    set P : ℤ[X] := PowerSeries.trunc (2 * g' + 1) (PowerSeries.mk T) with hPdef
    have hPcoeff : ∀ n, P.coeff n = if n < 2 * g' + 1 then T n else 0 := fun n => by
      rw [hPdef, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]
    have hPdeg : P.natDegree ≤ 2 * g' :=
      Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ _)
    set a : ℤ := h * q ^ (g' + 1) with ha
    have hT : PowerSeries.mk T =
        (P : PowerSeries ℤ) + PowerSeries.X ^ (2 * g' + 1) * (PowerSeries.C a * geom q) := by
      ext n
      rw [map_add, Polynomial.coeff_coe, hPcoeff, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      by_cases hn : n < 2 * g' + 1
      · rw [if_pos hn, if_neg (by omega), add_zero]
      · rw [if_neg hn, if_pos (by omega), zero_add, H2 n (by omega), ha, geom,
          PowerSeries.coeff_mk, mul_assoc, ← pow_add]
        congr 2
        omega
    set Up : ℤ[X] := C 1 * X ^ 0 + C (-(q + 1)) * X ^ 1 + C q * X ^ 2 with hUp
    set R : ℤ[X] := C a * X ^ (2 * g' + 1) + C (-a) * X ^ (2 * g' + 2) + C (-h) * X ^ 0 +
      C (h * q) * X ^ 1 with hR
    set M : ℤ[X] := Up * P + R with hM
    have hUpc :
        (Up : PowerSeries ℤ) = (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) := by
      simp only [hUp, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X]
      simp only [map_neg, map_add, map_one]
      ring
    have hRc : (R : PowerSeries ℤ) = PowerSeries.C a * PowerSeries.X ^ (2 * g' + 1) -
        PowerSeries.C a * PowerSeries.X ^ (2 * g' + 2) - PowerSeries.C h +
        PowerSeries.C h * PowerSeries.C q * PowerSeries.X := by
      simp only [hR, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X]
      simp only [map_neg, map_mul]
      ring
    have hMW : (M : PowerSeries ℤ) = PowerSeries.C (q - 1) * W := by
      rw [hM, Polynomial.coe_add, Polynomial.coe_mul, hUpc, hRc, hW]
      linear_combination (norm := skip)
        (-((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) * hZ +
        (-((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) * hT +
        (-(PowerSeries.C a * (1 - PowerSeries.X) * PowerSeries.X ^ (2 * g' + 1))) * hgq +
        (PowerSeries.C h * (1 - PowerSeries.C q * PowerSeries.X)) * hg1
      simp only [map_sub, map_one]
      ring
    have hUpdeg : Up.natDegree ≤ 2 := by
      rw [hUp]
      refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact natDegree_C_mul_X_pow_le _ _
    have hRdeg : R.natDegree ≤ 2 * g' + 2 := by
      rw [hR]
      refine natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact natDegree_C_mul_X_pow_le _ _
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hMdeg : M.natDegree ≤ 2 * g' + 2 := by
      rw [hM]
      refine natDegree_add_le_of_degree_le (natDegree_mul_le.trans ?_) hRdeg
      omega
    have hWcoeff : ∀ n, 2 * g' + 2 < n → PowerSeries.coeff n W = 0 := by
      intro n hn
      have h1 : PowerSeries.coeff n (M : PowerSeries ℤ) = 0 := by
        rw [Polynomial.coeff_coe]
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hMdeg hn)
      rw [hMW, PowerSeries.coeff_C_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hq1
    set L : ℤ[X] := PowerSeries.trunc (2 * g' + 2 + 1) W with hL
    have hLW : (L : PowerSeries ℤ) = W := by
      ext n
      rw [Polynomial.coeff_coe, hL, PowerSeries.coeff_trunc]
      split_ifs with hn
      · rfl
      · exact (hWcoeff n (by omega)).symm
    have hML : M = C (q - 1) * L := by
      rw [← Polynomial.coe_inj, hMW, Polynomial.coe_mul, Polynomial.coe_C, hLW]
    have hMLc : ∀ n, M.coeff n = (q - 1) * L.coeff n := fun n => by
      rw [hML, coeff_C_mul]
    have hP3 : (reflect (2 * g') P).comp (C q * X) = C (q ^ g') * P := by
      refine reflect_comp_eq q g' P hPdeg fun n hn => ?_
      rw [hPcoeff, hPcoeff, if_pos (by omega), if_pos (by omega)]
      have h3 := H3 n (by omega)
      rwa [show g' + 1 - 1 = g' by omega, show 2 * (g' + 1) - 2 - n = 2 * g' - n by omega]
        at h3
    have hρ : (reflect (2 * g' + 2) M).comp (C q * X) = C (q ^ (g' + 1)) * M := by
      have hrefl : reflect (2 * g' + 2) M =
          reflect 2 Up * reflect (2 * g') P + reflect (2 * g' + 2) R := by
        rw [hM, reflect_add, show 2 * g' + 2 = 2 + 2 * g' by ring, reflect_mul Up P hUpdeg hPdeg]
      have hUr : reflect 2 Up = C 1 * X ^ 2 + C (-(q + 1)) * X ^ 1 + C q * X ^ 0 := by
        rw [hUp, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
          reflect_C_mul_X_pow, revAt_le (by omega), revAt_le (by omega), revAt_le (by omega)]
      have hRr : reflect (2 * g' + 2) R = C a * X ^ 1 + C (-a) * X ^ 0 +
          C (-h) * X ^ (2 * g' + 2) + C (h * q) * X ^ (2 * g' + 1) := by
        rw [hR, reflect_add, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
          reflect_C_mul_X_pow, reflect_C_mul_X_pow, revAt_le (by omega), revAt_le (by omega),
          revAt_le (by omega), revAt_le (by omega)]
        congr 3 <;> [congr 2; skip] <;> [omega; congr 2] ; omega
      rw [hrefl, add_comp, mul_comp, hP3, hUr, hRr]
      simp only [add_comp, mul_comp, C_comp, pow_comp, X_comp]
      rw [hM, hUp, hR, ha]
      simp only [map_neg, map_add, map_one, map_mul, map_pow]
      ring
    have hFEM : ∀ i ≤ 2 * g' + 2,
        M.coeff (2 * g' + 2 - i) * q ^ i = q ^ (g' + 1) * M.coeff i := by
      intro i hi
      have hci := congrArg (fun f : ℤ[X] => f.coeff i) hρ
      simp only [comp_C_mul_X_coeff, coeff_reflect, coeff_C_mul, revAt_le hi] at hci
      exact hci
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (g' + 1) = 2 * g' + 2 by ring]
      exact Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ _)
    · rw [hL, PowerSeries.coeff_trunc, if_pos (by omega), hW0]
    · intro i hi
      have h1 := hFEM i (by omega)
      rw [hMLc, hMLc, show 2 * g' + 2 - i = 2 * (g' + 1) - i by omega] at h1
      refine mul_left_cancel₀ hq1 ?_
      linear_combination h1
    · exact hLW.symm

/-- A constant has order zero at every place. -/
private theorem ord_algebraMap (c : K) (v : Place K F) :
    v.ord (algebraMap K F c) = 0 := by
  have h1 := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

/-- A nonzero element of the maximal ideal of a place has positive order. -/
private theorem one_le_ord_of_mem_maximalIdeal (v : Place K F) {x : v.toValuationSubring}
    (hx : x ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (hx0 : x ≠ 0) :
    1 ≤ v.ord (x : F) := by
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hne : v.ord (x : F) ≠ 0 := fun h => (IsLocalRing.mem_maximalIdeal x).mp hx
    ((v.adicValuation_coe_eq_one_iff x).mp (by
      rw [v.adicValuation_eq_exp_neg_ord hxF, h, neg_zero, exp_zero]))
  have := v.ord_nonneg_of_mem x.2
  omega

private theorem lSpace_mono {D E : Divisor K F} (h : D ≤ E) : LSpace D ≤ LSpace E :=
  fun _ hf v => (hf v).trans (exp_le_exp.mpr (Finsupp.le_def.mp h v))

variable [IsCurveOver K F]

private theorem self_mem_lSpace_neg {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z ∈ LSpace (-P) := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [hP v]

private theorem inv_mem_lSpace {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z⁻¹ ∈ LSpace P := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [Place.ord_inv, hP v]

private theorem ell_add_eq_of_ord_eq {z : F} (hz : z ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord z) (A : Divisor K F) : ell (A + P) = ell A := by
  have h1 : ∀ f : F, f ∈ LSpace (A + P) → f * z ∈ LSpace A := fun f hf => by
    have hmul := mul_mem_lSpace_add hf (self_mem_lSpace_neg hP)
    rwa [add_neg_cancel_right] at hmul
  have h2 : ∀ g : F, g ∈ LSpace A → g * z⁻¹ ∈ LSpace (A + P) := fun g hg =>
    mul_mem_lSpace_add hg (inv_mem_lSpace hP)
  let e : LSpace (A + P) ≃ₗ[K] LSpace A :=
    { toFun := fun f => ⟨f.1 * z, h1 f.1 f.2⟩
      map_add' := fun f g => by
        ext
        simp [add_mul]
      map_smul' := fun c f => by
        ext
        simp
      invFun := fun g => ⟨g.1 * z⁻¹, h2 g.1 g.2⟩
      left_inv := fun f => by
        ext
        simp [mul_inv_cancel_right₀ hz]
      right_inv := fun g => by
        ext
        simp [inv_mul_cancel_right₀ hz] }
  exact e.finrank_eq

private theorem ell_eq_of_isPrincipal_sub {D E : Divisor K F}
    (h : Divisor.IsPrincipal (D - E)) : ell D = ell E := by
  obtain ⟨z, hz, hP⟩ := h
  have hEq := ell_add_eq_of_ord_eq hz hP E
  rwa [add_sub_cancel] at hEq

private theorem degree_eq_zero_of_isPrincipal {P : Divisor K F}
    (h : Divisor.IsPrincipal P) : Divisor.degree P = 0 := by
  obtain ⟨z, hz, hP⟩ := h
  obtain ⟨D, hD, hdeg⟩ := IsCurveOver.exists_divisor (K := K) (F := F) z hz
  have hDP : D = P := Finsupp.ext fun v => by rw [hD v, hP v]
  rwa [hDP] at hdeg

private theorem ell_eq_zero_of_degree_neg {D : Divisor K F}
    (hD : Divisor.degree D < 0) : ell D = 0 := by
  have hbot : LSpace D = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_cases hf0 : f = 0
    · exact hf0
    · exfalso
      rw [mem_lSpace_iff_ord] at hf
      obtain hf' : ∀ v : Place K F, -D v ≤ v.ord f := by
        rcases hf with h0 | h0
        · exact absurd h0 hf0
        · exact h0
      obtain ⟨P, hP, hdeg⟩ := IsCurveOver.exists_divisor (K := K) (F := F) f hf0
      have hnonneg : 0 ≤ Divisor.degree (D + P) :=
        Divisor.degree_nonneg_of_nonneg (fun v => by
          rw [Finsupp.add_apply, hP v]
          linarith [hf' v])
      rw [map_add, hdeg, add_zero] at hnonneg
      omega
  rw [ell, hbot]
  simp

private theorem degree_pos_of_nonneg_of_ne_zero {E : Divisor K F} (hE : 0 ≤ E)
    (hE0 : E ≠ 0) : 0 < Divisor.degree E := by
  classical
  have hEnn : ∀ w, 0 ≤ E w := fun w => by simpa using (Finsupp.le_def.mp hE) w
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hE0 (Finsupp.ext hcon)
  have hEv : 1 ≤ E v := by
    have hnn := hEnn v
    omega
  have hsplit : E = Finsupp.single v (E v) + Finsupp.erase v E :=
    (Finsupp.single_add_erase v E).symm
  have herase : ∀ w, 0 ≤ Finsupp.erase v E w := fun w => by
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hEnn w
  have h1 : 0 ≤ Divisor.degree (Finsupp.erase v E) :=
    Divisor.degree_nonneg_of_nonneg herase
  have h2 : (1 : ℤ) ≤ v.deg := by exact_mod_cast IsCurveOver.one_le_deg v
  rw [hsplit, map_add, Divisor.degree_single]
  nlinarith

/-- Raising a divisor `A` by one at a place `P` keeps its Riemann-Roch space
finite-dimensional: `L(P + A) / L(A)` embeds in the residue field at `P`
through `f ↦ π ^ n * f` for a uniformizer `π` and `n = A P + 1`. -/
private theorem finite_lSpace_single_add (P : Place K F) {A : Divisor K F}
    [Module.Finite K (LSpace A)] : Module.Finite K (LSpace (Finsupp.single P 1 + A)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hB : (Finsupp.single P 1 + A : Divisor K F) P = A P + 1 := by simp [add_comm]
  have hmem : ∀ f : LSpace (Finsupp.single P 1 + A),
      (π : F) ^ (A P + 1) * (f : F) ∈ P.toValuationSubring := by
    intro f
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · rw [h0, mul_zero]
      exact zero_mem _
    · have hfP := (mem_lSpace_iff_ord.mp f.2).resolve_left h0 P
      rw [hB] at hfP
      refine P.mem_of_ord_nonneg (mul_ne_zero (zpow_ne_zero _ hπ0) h0) ?_
      rw [P.ord_mul (zpow_ne_zero _ hπ0) h0, P.ord_zpow, P.ord_coe_irreducible hπ, mul_one]
      linarith
  let φ : LSpace (Finsupp.single P 1 + A) →ₗ[K] P.toValuationSubring :=
    { toFun := fun f => ⟨(π : F) ^ (A P + 1) * (f : F), hmem f⟩
      map_add' := fun f g => Subtype.ext (by simp [mul_add])
      map_smul' := fun c f => Subtype.ext (by simp [Algebra.smul_def, mul_left_comm]) }
  let ψ := (IsScalarTower.toAlgHom K P.toValuationSubring
    (IsLocalRing.ResidueField P.toValuationSubring)).toLinearMap ∘ₗ φ
  have hker : ∀ f, ψ f = 0 → (f : F) ∈ LSpace A := by
    intro f hf
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr fun v => ?_
    have hfv := (mem_lSpace_iff_ord.mp f.2).resolve_left h0 v
    by_cases hv : v = P
    · subst hv
      have hres : IsLocalRing.residue _ (φ f) = 0 := by
        simpa [ψ, IsLocalRing.ResidueField.algebraMap_eq] using hf
      have hne : φ f ≠ 0 := fun h =>
        mul_ne_zero (zpow_ne_zero _ hπ0) h0 (congrArg Subtype.val h)
      have h1 := one_le_ord_of_mem_maximalIdeal v ((IsLocalRing.residue_eq_zero_iff _).mp hres) hne
      change 1 ≤ v.ord ((π : F) ^ (A v + 1) * (f : F)) at h1
      rw [v.ord_mul (zpow_ne_zero _ hπ0) h0, v.ord_zpow, v.ord_coe_irreducible hπ,
        mul_one] at h1
      linarith
    · have hAv : (Finsupp.single P 1 + A : Divisor K F) v = A v := by
        simp [Ne.symm hv]
      rwa [hAv] at hfv
  have : Module.Finite K (IsLocalRing.ResidueField P.toValuationSubring) :=
    IsCurveOver.finiteResidue P
  have hkerFin : Module.Finite K (LinearMap.ker ψ) := by
    let ι : LinearMap.ker ψ →ₗ[K] LSpace A :=
      { toFun := fun f => ⟨((f : LSpace (Finsupp.single P 1 + A)) : F), hker f f.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective ι fun f g h => ?_
    have h' : ((f : LSpace (Finsupp.single P 1 + A)) : F) =
        ((g : LSpace (Finsupp.single P 1 + A)) : F) :=
      congrArg (fun x : LSpace A => (x : F)) h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker ψ (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq]
  exact Module.Finite.iff_fg.mp hkerFin

private theorem finite_lSpace_single_natCast_add (P : Place K F) (m : ℕ) {A : Divisor K F}
    [Module.Finite K (LSpace A)] :
    Module.Finite K (LSpace (Finsupp.single P (m : ℤ) + A)) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, Finsupp.single_zero, zero_add]
    infer_instance
  | succ m ih =>
    rw [Nat.cast_succ, Finsupp.single_add, add_comm (Finsupp.single P (m : ℤ)), add_assoc]
    exact finite_lSpace_single_add P

/-- Riemann-Roch spaces are finite-dimensional when the constants are the base
field: `L(0)` is the base field, raising a divisor at one place keeps its
Riemann-Roch space finite-dimensional, and lowering it shrinks the space. -/
private theorem finite_lSpace (hC : ConstantsAreBase K F) (D : Divisor K F) :
    Module.Finite K (LSpace D) := by
  induction D using Finsupp.induction with
  | zero =>
    refine Module.finite_of_finrank_pos ?_
    change 0 < ell (0 : Divisor K F)
    rw [ell_zero_eq_one_of_constantsAreBase hC]
    exact Nat.one_pos
  | single_add P b A _ _ ih =>
    rcases le_or_gt 0 b with hb | hb
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      exact finite_lSpace_single_natCast_add P m
    · have hle : Finsupp.single P b + A ≤ A := Finsupp.le_def.mpr fun v => by
        rw [Finsupp.add_apply]
        by_cases hv : P = v
        · subst hv
          rw [Finsupp.single_eq_same]
          omega
        · simp [hv]
      exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hle))
        (Submodule.inclusion_injective _)

/-- Effective divisors of a given degree. -/
private abbrev Eff (n : ℕ) : Type _ :=
  {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)}

/-- Effective divisors whose difference from `C` is principal. -/
private abbrev LinSys (C : Divisor K F) : Type _ :=
  {D : Divisor K F // 0 ≤ D ∧ Divisor.IsPrincipal (D - C)}

private theorem card_eff_zero : Nat.card (Eff (K := K) (F := F) 0) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun D E => Subtype.ext ?_⟩, ⟨⟨0, le_rfl, by simp⟩⟩⟩
  have hD : (D : Divisor K F) = 0 := by
    by_contra hne
    have hpos := degree_pos_of_nonneg_of_ne_zero D.2.1 hne
    rw [D.2.2] at hpos
    simp at hpos
  have hE : (E : Divisor K F) = 0 := by
    by_contra hne
    have hpos := degree_pos_of_nonneg_of_ne_zero E.2.1 hne
    rw [E.2.2] at hpos
    simp at hpos
  rw [hD, hE]

/-- The divisor of a nonzero function. -/
private noncomputable def divOf {f : F} (hf : f ≠ 0) : Divisor K F :=
  (IsCurveOver.exists_divisor (K := K) f hf).choose

private theorem divOf_apply {f : F} (hf : f ≠ 0) (v : Place K F) :
    divOf (K := K) hf v = v.ord f :=
  (IsCurveOver.exists_divisor (K := K) f hf).choose_spec.1 v

/-- The effective divisor `div f + C` of a nonzero `f ∈ L(C)`. -/
private noncomputable def toLinSys (C : Divisor K F) (f : {f : LSpace C // f ≠ 0}) :
    LinSys (K := K) (F := F) C :=
  have hf : ((f : LSpace C) : F) ≠ 0 := fun h => f.2 (Subtype.ext h)
  ⟨divOf (K := K) hf + C, Finsupp.le_def.mpr fun v => by
      have hv := (mem_lSpace_iff_ord.mp (f : LSpace C).2).resolve_left hf v
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divOf_apply]
      linarith,
    ⟨_, hf, fun v => by rw [add_sub_cancel_right, divOf_apply]⟩⟩

private theorem toLinSys_smul (C : Divisor K F) (a b : {f : LSpace C // f ≠ 0}) (t : K)
    (h : (a : LSpace C) = t • (b : LSpace C)) : toLinSys C a = toLinSys C b := by
  have ht : t ≠ 0 := by
    rintro rfl
    exact a.2 (by rw [h, zero_smul])
  have hb : ((b : LSpace C) : F) ≠ 0 := fun h0 => b.2 (Subtype.ext h0)
  have hab : ((a : LSpace C) : F) = algebraMap K F t * ((b : LSpace C) : F) := by
    rw [h, Submodule.coe_smul, Algebra.smul_def]
  refine Subtype.ext (congrArg (· + C) (Finsupp.ext fun v => ?_))
  rw [divOf_apply, divOf_apply, hab, v.ord_mul ((_root_.map_ne_zero _).mpr ht) hb,
    ord_algebraMap t, zero_add]

private theorem toLinSys_injective (hC : ConstantsAreBase K F) (C : Divisor K F) :
    Function.Injective (Projectivization.lift (toLinSys C) (toLinSys_smul C)) := by
  intro x y hxy
  induction x using Projectivization.ind with | h f hf => ?_
  induction y using Projectivization.ind with | h g hg => ?_
  rw [Projectivization.lift_mk, Projectivization.lift_mk] at hxy
  have hf' : (f : F) ≠ 0 := fun h => hf (Subtype.ext h)
  have hg' : (g : F) ≠ 0 := fun h => hg (Subtype.ext h)
  have hdiv : ∀ v : Place K F, v.ord (f : F) = v.ord (g : F) := fun v => by
    have h1 := DFunLike.congr_fun (add_right_cancel (congrArg Subtype.val hxy)) v
    rwa [divOf_apply, divOf_apply] at h1
  have hmem : (f : F) / g ∈ LSpace (0 : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [div_eq_mul_inv, v.ord_mul hf' (inv_ne_zero hg'), v.ord_inv, hdiv v]
    simp
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  rw [Algebra.linearMap_apply] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact div_ne_zero hf' hg' hc.symm
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc0, Subtype.ext ?_⟩
  rw [Units.smul_def, Units.val_mk0, Submodule.coe_smul, Algebra.smul_def, hc,
    div_mul_cancel₀ _ hg']

private theorem toLinSys_surjective (C : Divisor K F) :
    Function.Surjective (Projectivization.lift (toLinSys C) (toLinSys_smul C)) := by
  rintro ⟨D, hD0, g, hg, hgD⟩
  have hgC : g ∈ LSpace C := by
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    have h1 := (Finsupp.le_def.mp hD0) v
    have h2 := hgD v
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2
    linarith
  refine ⟨Projectivization.mk K (⟨g, hgC⟩ : LSpace C) fun h => hg (congrArg Subtype.val h), ?_⟩
  rw [Projectivization.lift_mk]
  refine Subtype.ext (Finsupp.ext fun v => ?_)
  have h2 := hgD v
  simp only [Finsupp.coe_sub, Pi.sub_apply] at h2
  change divOf (K := K) _ v + C v = D v
  rw [divOf_apply]
  linarith

/-- The effective divisors linearly equivalent to `C` correspond to the points
of the projective space of `L(C)`. -/
private noncomputable def linSysEquiv (hC : ConstantsAreBase K F) (C : Divisor K F) :
    ℙ K (LSpace C) ≃ LinSys (K := K) (F := F) C :=
  Equiv.ofBijective _ ⟨toLinSys_injective hC C, toLinSys_surjective C⟩

/-- Counting the effective divisors in a complete linear system over a finite
base: they correspond to the nonzero vectors of `L(C)` up to scaling. -/
private theorem card_linSys [Finite K] (hC : ConstantsAreBase K F) (C : Divisor K F) :
    (Nat.card K - 1) * Nat.card (LinSys (K := K) (F := F) C) + 1 = Nat.card K ^ ell C := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hP := Projectivization.card K (LSpace C)
  rw [← Nat.card_congr (linSysEquiv hC C)]
  by_cases hfin : Module.Finite K (LSpace C)
  · have hV : Nat.card (LSpace C) = Nat.card K ^ ell C := Module.natCard_eq_pow_finrank
    have hpos : 0 < Nat.card K ^ ell C := pow_pos (by omega) _
    rw [hV] at hP
    rw [mul_comm, ← hP]
    omega
  · have hinf : Infinite (LSpace C) := by
      rw [← not_finite_iff_infinite, ← Module.finite_iff_finite (R := K)]
      exact hfin
    rw [Nat.card_eq_zero_of_infinite, zero_tsub] at hP
    have h0 : Nat.card (ℙ K (LSpace C)) = 0 := by
      rcases Nat.mul_eq_zero.mp hP.symm with h | h
      · exact h
      · omega
    rw [h0, ell, Module.finrank_of_not_finite hfin]
    simp

private theorem finite_linSys [Finite K] (hC : ConstantsAreBase K F) (C : Divisor K F) :
    Finite (LinSys (K := K) (F := F) C) := by
  have : Module.Finite K (LSpace C) := finite_lSpace hC C
  have : Finite (LSpace C) := Module.finite_of_finite K
  exact Finite.of_equiv _ (linSysEquiv hC C)

omit [IsCurveOver K F] in
private theorem exists_W (hC : ConstantsAreBase K F)
    (hRR : ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ)) :
    ∃ W : Divisor K F, Divisor.degree W = 2 * (genusFF K F : ℤ) - 2 ∧
      ∀ D : Divisor K F, (ell D : ℤ) - (ell (W - D) : ℤ) =
        Divisor.degree D + 1 - (genusFF K F : ℤ) := by
  obtain ⟨W, hW⟩ := hRR
  refine ⟨W, ?_, hW⟩
  have h0 := hW 0
  have hW' := hW W
  rw [sub_zero, map_zero, ell_zero_eq_one_of_constantsAreBase hC] at h0
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at hW'
  push_cast at h0 hW'
  linarith

variable (D₁ : {D : Divisor K F // Divisor.degree D = 1})

private noncomputable def toDegZero (D : Divisor K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨D - Divisor.degree D • (D₁ : Divisor K F), by
    rw [Divisor.mem_degZero, map_sub, map_zsmul, D₁.2, smul_eq_mul, mul_one, sub_self]⟩

private theorem coe_toDegZero (D : Divisor K F) :
    (toDegZero D₁ D : Divisor K F) = D - Divisor.degree D • (D₁ : Divisor K F) := rfl

private noncomputable def cls (D : Divisor K F) : Pic0 K F := Pic0.mk (toDegZero D₁ D)

private noncomputable def rep (c : Pic0 K F) (n : ℤ) : Divisor K F :=
  ((Pic0.mk_surjective c).choose : Divisor K F) + n • (D₁ : Divisor K F)

private theorem degree_rep (c : Pic0 K F) (n : ℤ) :
    Divisor.degree (rep D₁ c n) = n := by
  have hdeg : Divisor.degree ((Pic0.mk_surjective c).choose : Divisor K F) = 0 :=
    (Pic0.mk_surjective c).choose.2
  rw [rep, map_add, map_zsmul, D₁.2, hdeg, smul_eq_mul, mul_one, zero_add]

private theorem mk_eq_mk_iff (x y : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk x = Pic0.mk y ↔ Divisor.IsPrincipal ((x : Divisor K F) - (y : Divisor K F)) := by
  show (QuotientAddGroup.mk x : Pic0 K F) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  show -(x : Divisor K F) + y ∈ Divisor.principal ↔ _
  rw [neg_add_eq_sub, ← neg_sub, neg_mem_iff]
  rfl

private theorem cls_eq_iff {D : Divisor K F} {n : ℤ} (hD : Divisor.degree D = n)
    (c : Pic0 K F) :
    cls D₁ D = c ↔ Divisor.IsPrincipal (D - rep D₁ c n) := by
  conv_lhs => rw [← (Pic0.mk_surjective c).choose_spec]
  rw [cls, mk_eq_mk_iff, coe_toDegZero, hD, rep]
  congr! 1
  abel

private noncomputable def effEquiv (n : ℕ) :
    Eff (K := K) (F := F) n ≃ Σ c : Pic0 K F, LinSys (K := K) (F := F) (rep D₁ c n) :=
  (Equiv.sigmaFiberEquiv fun D : Eff (K := K) (F := F) n => cls D₁ (D : Divisor K F)).symm.trans
    (Equiv.sigmaCongrRight fun c =>
      { toFun := fun D => ⟨(D.1 : Divisor K F), D.1.2.1, (cls_eq_iff D₁ D.1.2.2 c).mp D.2⟩
        invFun := fun D =>
          have hdeg : Divisor.degree (D.1 : Divisor K F) = n := by
            have hzero := degree_eq_zero_of_isPrincipal D.2.2
            rw [map_sub, degree_rep] at hzero
            linarith
          ⟨⟨D.1, D.2.1, hdeg⟩, (cls_eq_iff D₁ hdeg c).mpr D.2.2⟩
        left_inv := fun D => Subtype.ext (Subtype.ext rfl)
        right_inv := fun D => Subtype.ext rfl })

private theorem card_eff_eq_sum [Finite K] [Fintype (Pic0 K F)]
    (hC : ConstantsAreBase K F) (n : ℕ) :
    Nat.card (Eff (K := K) (F := F) n) =
      ∑ c : Pic0 K F, Nat.card (LinSys (K := K) (F := F) (rep D₁ c n)) := by
  haveI : ∀ c : Pic0 K F, Finite (LinSys (K := K) (F := F) (rep D₁ c (n : ℤ))) :=
    fun c => finite_linSys hC _
  rw [Nat.card_congr (effEquiv D₁ n), Nat.card_sigma]

private theorem count_H1 [Finite K] [Fintype (Pic0 K F)] (hC : ConstantsAreBase K F)
    (n : ℕ) :
    ((Nat.card K : ℤ) - 1) * Nat.card (Eff (K := K) (F := F) n) + Nat.card (Pic0 K F) =
      ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hc : ∀ c : Pic0 K F,
      ((Nat.card K : ℤ) - 1) *
          Nat.card (LinSys (K := K) (F := F) (rep D₁ c (n : ℤ))) + 1 =
        (Nat.card K : ℤ) ^ ell (rep D₁ c n) := fun c => by
    have hcard := card_linSys hC (rep D₁ c n)
    have h2 : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := by
      push_cast [hq]
      ring
    rw [← h2]
    exact_mod_cast hcard
  rw [card_eff_eq_sum D₁ hC n, Nat.cast_sum, Finset.mul_sum,
    Nat.card_eq_fintype_card (α := Pic0 K F), ← Finset.sum_congr rfl fun c _ => hc c,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

private theorem count_H2 [Finite K] [Fintype (Pic0 K F)] (hC : ConstantsAreBase K F)
    (hRR : ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ))
    (n : ℕ) (hn : 2 * genusFF K F ≤ n + 1) :
    ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) =
      Nat.card (Pic0 K F) * (Nat.card K : ℤ) ^ (n + 1 - genusFF K F) := by
  obtain ⟨W, hdegW, hRR⟩ := exists_W hC hRR
  have hc : ∀ c : Pic0 K F, ell (rep D₁ c n) = n + 1 - genusFF K F := fun c => by
    have h1 := hRR (rep D₁ c n)
    have h2 : ell (W - rep D₁ c n) = 0 := by
      apply ell_eq_zero_of_degree_neg
      rw [map_sub, hdegW, degree_rep]
      omega
    rw [h2, degree_rep] at h1
    push_cast at h1
    omega
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card (α := Pic0 K F)]

private theorem count_H3 [Finite K] [Fintype (Pic0 K F)] (hC : ConstantsAreBase K F)
    (hRR : ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ))
    (n : ℕ) (hn : n + 2 ≤ 2 * genusFF K F) :
    (Nat.card K : ℤ) ^ (genusFF K F - 1) *
        ∑ c : Pic0 K F, (Nat.card K : ℤ) ^ ell (rep D₁ c n) =
      (Nat.card K : ℤ) ^ n *
        ∑ c : Pic0 K F,
          (Nat.card K : ℤ) ^ ell (rep D₁ c ((2 * genusFF K F - 2 - n : ℕ) : ℤ)) := by
  obtain ⟨W, hdegW, hRR⟩ := exists_W hC hRR
  set g := genusFF K F with hg
  set m : ℕ := 2 * g - 2 - n with hm
  have hmn : (m : ℤ) + n = 2 * (g : ℤ) - 2 := by rw [hm]; omega
  set w₀ : Pic0 K F := cls D₁ W with hw₀
  have hkey : ∀ c : Pic0 K F, ell (rep D₁ (w₀ - c) m) = ell (W - rep D₁ c n) := by
    intro c
    apply ell_eq_of_isPrincipal_sub
    have h1 : cls D₁ (rep D₁ (w₀ - c) (m : ℤ) + rep D₁ c n) = w₀ := by
      have e1 := (cls_eq_iff D₁ (degree_rep D₁ (w₀ - c) (m : ℤ)) (w₀ - c)).mpr
        (by rw [sub_self]; exact ⟨1, one_ne_zero, fun v => by simp⟩)
      have e2 := (cls_eq_iff D₁ (degree_rep D₁ c (n : ℤ)) c).mpr
        (by rw [sub_self]; exact ⟨1, one_ne_zero, fun v => by simp⟩)
      have hadd : cls D₁ (rep D₁ (w₀ - c) (m : ℤ) + rep D₁ c n) =
          cls D₁ (rep D₁ (w₀ - c) (m : ℤ)) + cls D₁ (rep D₁ c n) := by
        rw [cls, cls, cls, ← Pic0.mk_add]
        congr 1
        apply Subtype.ext
        simp only [coe_toDegZero, AddSubgroup.coe_add, map_add, degree_rep]
        rw [add_smul]
        abel
      rw [hadd, e1, e2, sub_add_cancel]
    have h2 := (cls_eq_iff D₁ (n := 2 * (g : ℤ) - 2) (by
      rw [map_add, degree_rep, degree_rep, hmn]) w₀).mp h1
    have h3 : Divisor.IsPrincipal (W - rep D₁ w₀ (2 * (g : ℤ) - 2)) :=
      (cls_eq_iff D₁ hdegW w₀).mp rfl
    obtain ⟨f₂, hf₂, hP₂⟩ := h2
    obtain ⟨f₃, hf₃, hP₃⟩ := h3
    refine ⟨f₂ * f₃⁻¹, mul_ne_zero hf₂ (inv_ne_zero hf₃), fun v => ?_⟩
    rw [v.ord_mul hf₂ (inv_ne_zero hf₃), Place.ord_inv, ← hP₂ v, ← hP₃ v]
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply]
    ring
  have hexp : ∀ c : Pic0 K F, (g - 1) + ell (rep D₁ c n) =
      n + ell (rep D₁ (w₀ - c) m) := by
    intro c
    have h1 := hRR (rep D₁ c n)
    rw [degree_rep, ← hkey c] at h1
    omega
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft w₀) _ _ fun c => ?_
  rw [← pow_add, ← pow_add, hexp c, Equiv.subLeft_apply]

end Counts

/-- Existence of the `L`-polynomial of a curve over a finite field, conditional
on three standard inputs that are hypotheses here, not results proved in this
file: the Riemann-Roch formula for some divisor `W` with the genus
`genusFF k F` (`hRR`), finiteness of the degree-zero Picard group (`hPic`), and
the existence of a divisor of degree one (`hD₁`). Under these hypotheses the
divisor-counting zeta series of the function field is, up to the two standard
denominator factors, a polynomial of degree at most twice the genus, with
constant coefficient `1` and the functional-equation symmetry of its
coefficients. -/
public theorem exists_LPolynomial_of_finite_of_riemannRoch
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : ConstantsAreBase k F)
    (hRR : ∃ W : Divisor k F, ∀ D : Divisor k F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF k F : ℤ))
    (hPic : Finite (Pic0 k F)) (hD₁ : ∃ D : Divisor k F, Divisor.degree D = 1) :
    ∃ L : Polynomial ℤ,
      L.natDegree ≤ 2 * genusFF k F ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * genusFF k F,
        L.coeff (2 * genusFF k F - i) * (Nat.card k : ℤ) ^ i =
          (Nat.card k : ℤ) ^ genusFF k F * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n : ℕ =>
            (Nat.card {D : Divisor k F //
                0 ≤ D ∧ Divisor.degree D = (n : ℤ)} : ℤ)) =
        (L : PowerSeries ℤ) := by
  let : Fintype (Pic0 k F) := @Fintype.ofFinite _ hPic
  obtain ⟨D₁, hD₁⟩ := hD₁
  have hq1 : (Nat.card k : ℤ) - 1 ≠ 0 := by
    have hcard : 1 < Nat.card k := Finite.one_lt_card
    omega
  exact lpoly_of_counts (Nat.card k : ℤ) (Nat.card (Pic0 k F)) hq1 (genusFF k F)
    (fun n => (Nat.card (Eff (K := k) (F := F) n) : ℤ))
    (fun n => ∑ c : Pic0 k F, (Nat.card k : ℤ) ^ ell (rep ⟨D₁, hD₁⟩ c n))
    (fun n => count_H1 ⟨D₁, hD₁⟩ hC n) (fun n hn => count_H2 ⟨D₁, hD₁⟩ hC hRR n hn)
    (fun n hn => count_H3 ⟨D₁, hD₁⟩ hC hRR n hn)
    (show (Nat.card (Eff (K := k) (F := F) 0) : ℤ) = 1 by exact_mod_cast card_eff_zero)

end AlgebraicCurve
