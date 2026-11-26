/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_
isAttached_both_ends.lean`,
`P2M/Sol/S_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_
isAttached_both_ends.lean`,
`Theorems/Thm_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends.lean`
and
`P2M/Sol/S_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends.lean`
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

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup
public import MathlibExt.AlgebraicGeometry.Curve.SemistableCharts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationOrd
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute values of functions on an annulus attached at both ends

Let `A` be the valuation subring of an absolute value `μ` on `L`, and let `F / L` be a function
field with principal divisors. Suppose two annuli `An`, `An'` have the same places and modulus
`π ≠ 0`, with coordinates multiplying to `π`, and that `An` is attached to a component chart `C`
at a node `x` while `An'` is attached to a chart `C'` at a node `x'`. If the coordinate of `An`
takes at least two distinct absolute values on the annulus, then:

* `AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends`: for a
  function `h` with no poles on the annulus, a unit reduction on `C`, and a unit reduction on
  `C'` after dividing by an integral constant `c'`, the orders at the two nodes have nonnegative
  sum, `|h| ≤ 1` on the annulus (strictly when `|c'| < 1` or the sum is positive), and in the
  balanced case `h` is a unit of absolute value `1` on the annulus.
* `AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends`: a nonzero function `g`
  without poles on the annulus, integral on `C`, and integral on `C'` after dividing by a nonzero
  constant `b`, satisfies `|g| ≤ max 1 |b|` on the annulus, strictly when `|b| ≠ 1`.

This is the maximum principle on a semistable annulus: the absolute value of a regular function
is controlled by its reductions at the two ends.
-/

@[expose] public section

open IsLocalRing

namespace AlgebraicCurve

private theorem abv_sub_le_max {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (a b : L) :
    μ (a - b) ≤ max (μ a) (μ b) := by
  rcases le_total (μ b) (μ a) with hab | hab
  · rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero] at hab
      have hb : b = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg b))
      simp [hb]
    have hq : b * a⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos ha0)).2 (by simpa using hab))
    have h1 : 1 - b * a⁻¹ ∈ A := sub_mem (one_mem _) hq
    have h2 : μ (1 - b * a⁻¹) ≤ 1 := (hμA _).1 h1
    have : a - b = a * (1 - b * a⁻¹) := by field_simp
    rw [this, map_mul]
    calc μ a * μ (1 - b * a⁻¹) ≤ μ a * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg a)
      _ = μ a := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_left _ _
  · rcases eq_or_ne b 0 with rfl | hb0
    · rw [map_zero] at hab
      have ha : a = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg a))
      simp [ha]
    have hq : a * b⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos hb0)).2 (by simpa using hab))
    have h1 : a * b⁻¹ - 1 ∈ A := sub_mem hq (one_mem _)
    have h2 : μ (a * b⁻¹ - 1) ≤ 1 := (hμA _).1 h1
    have : a - b = b * (a * b⁻¹ - 1) := by field_simp
    rw [this, map_mul]
    calc μ b * μ (a * b⁻¹ - 1) ≤ μ b * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg b)
      _ = μ b := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_right _ _

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

private theorem abv_lt_one_of_mem_maximalIdeal_vs {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem residue_eq_zero_of_mem_maximalIdeal' {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L} (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.residue A ⟨a, ha⟩ = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2 hm

private theorem abv_evalAt_eq_zpow_of_isAttached
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar)
    (hatt : An.IsAttached C x) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q (hQ : Q ∈ An.dom), 0 < μ (Q.evalAt (An.isRational Q hQ) An.param) ∧
      μ (Q.evalAt (An.isRational Q hQ) An.param) < 1 ∧
      μ (Q.evalAt (An.isRational Q hQ) f) =
        μ (Q.evalAt (An.isRational Q hQ) An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  have hμz1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
  have hμz0 := μ.pos hz0
  have hunit1 := abv_eq_one_of_isUnit_vs μ hμA hw hunit
  rw [map_mul, map_zpow₀, zpow_neg] at hunit1
  exact ⟨hμz0, hμz1, (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1⟩

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord
  rw [Valuation.map_neg]

private theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

private theorem ord_prod' {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]


end Place

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2


private theorem ComponentChart.isUnit_of_residue_ne_zero'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this


private theorem ComponentChart.residue_inv'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1


private theorem two_end_profile_bound {ι : Type*} (Z : Finset ι) (m : ι → ℕ) (γ : ι → ℝ)
    (p u C H : ℝ) (a a' : ℤ)
    (hp0 : 0 < p) (hpu : p < u) (hu1 : u < 1) (hγ : ∀ Q ∈ Z, p < γ Q ∧ γ Q < 1)
    (hm : ∀ Q ∈ Z, 0 < m Q) (hC0 : 0 < C) (hC1 : C ≤ 1)
    (hn : ((∑ Q ∈ Z, m Q : ℕ) : ℤ) = a + a')
    (h1 : H ≤ u ^ (a - ((∑ Q ∈ Z, m Q : ℕ) : ℤ)) * ∏ Q ∈ Z, (max (γ Q) u) ^ m Q)
    (h2 : H ≤ C * (p / u) ^ a' * ∏ Q ∈ Z, (max 1 (u / γ Q)) ^ m Q) :
    H ≤ 1 ∧ ((C < 1 ∨ 0 < a + a') → H < 1) := by
  classical
  have hu0 : 0 < u := hp0.trans hpu
  have hpu1 : p / u < 1 := (div_lt_one hu0).2 hpu
  have hpu0 : 0 < p / u := div_pos hp0 hu0
  set S := Z.filter (fun Q => u < γ Q) with hS
  set T := Z.filter (fun Q => ¬ u < γ Q) with hT
  set nS : ℕ := ∑ Q ∈ S, m Q with hnS
  set nT : ℕ := ∑ Q ∈ T, m Q with hnT
  have hsplit : (∑ Q ∈ Z, m Q) = nS + nT := by
    rw [hnS, hnT, hS, hT, Finset.sum_filter_add_sum_filter_not]
  set PS : ℝ := ∏ Q ∈ S, γ Q ^ m Q with hPS
  set PT : ℝ := ∏ Q ∈ T, γ Q ^ m Q with hPT
  have hSZ : ∀ Q ∈ S, Q ∈ Z := fun Q hQ => (Finset.mem_filter.1 hQ).1
  have hTZ : ∀ Q ∈ T, Q ∈ Z := fun Q hQ => (Finset.mem_filter.1 hQ).1
  have hPS1 : PS ≤ 1 := by
    refine Finset.prod_le_one₀ (fun Q hQ => pow_nonneg (hp0.trans (hγ Q (hSZ Q hQ)).1).le _)
      fun Q hQ => ?_
    exact pow_le_one₀ (hp0.trans (hγ Q (hSZ Q hQ)).1).le (hγ Q (hSZ Q hQ)).2.le
  have hPS1' : S.Nonempty → PS < 1 := by
    rintro ⟨Q0, hQ0⟩
    rw [hPS, ← Finset.mul_prod_erase _ _ hQ0]
    have h1 : γ Q0 ^ m Q0 < 1 :=
      pow_lt_one₀ (hp0.trans (hγ Q0 (hSZ Q0 hQ0)).1).le (hγ Q0 (hSZ Q0 hQ0)).2
        (hm Q0 (hSZ Q0 hQ0)).ne'
    have h2 : ∏ Q ∈ S.erase Q0, γ Q ^ m Q ≤ 1 := by
      refine Finset.prod_le_one₀
        (fun Q hQ => pow_nonneg (hp0.trans (hγ Q (hSZ Q (Finset.mem_of_mem_erase hQ))).1).le _)
        fun Q hQ => ?_
      exact pow_le_one₀ (hp0.trans (hγ Q (hSZ Q (Finset.mem_of_mem_erase hQ))).1).le
        (hγ Q (hSZ Q (Finset.mem_of_mem_erase hQ))).2.le
    have h3 : 0 ≤ ∏ Q ∈ S.erase Q0, γ Q ^ m Q :=
      Finset.prod_nonneg fun Q hQ =>
        pow_nonneg (hp0.trans (hγ Q (hSZ Q (Finset.mem_of_mem_erase hQ))).1).le _
    calc γ Q0 ^ m Q0 * ∏ Q ∈ S.erase Q0, γ Q ^ m Q ≤ γ Q0 ^ m Q0 * 1 :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (hp0.trans (hγ Q0 (hSZ Q0 hQ0)).1).le _)
      _ < 1 := by rw [mul_one]; exact h1
  have hPT0 : 0 < PT := Finset.prod_pos fun Q hQ => pow_pos (hp0.trans (hγ Q (hTZ Q hQ)).1) _
  have hPTp : p ^ nT ≤ PT := by
    rw [hPT, hnT, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun Q _ => pow_nonneg hp0.le _) fun Q hQ =>
      pow_le_pow_left₀ hp0.le (hγ Q (hTZ Q hQ)).1.le _
  have hPTp' : T.Nonempty → p ^ nT < PT := by
    rintro ⟨Q0, hQ0⟩
    rw [hPT, hnT, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_lt_prod_of_nonempty₀ (fun Q _ => pow_pos hp0 _)
      (fun Q hQ => pow_lt_pow_left₀ (hγ Q (hTZ Q hQ)).1 hp0.le (hm Q (hTZ Q hQ)).ne') ⟨Q0, hQ0⟩
  have hprod1 : (∏ Q ∈ Z, (max (γ Q) u) ^ m Q) = PS * u ^ nT := by
    rw [← Finset.prod_filter_mul_prod_filter_not Z (fun Q => u < γ Q), ← hS, ← hT, hPS, hnT,
      ← Finset.prod_pow_eq_pow_sum]
    congr 1
    · exact Finset.prod_congr rfl fun Q hQ => by rw [max_eq_left (Finset.mem_filter.1 hQ).2.le]
    · exact Finset.prod_congr rfl fun Q hQ => by
        rw [max_eq_right (not_lt.1 (Finset.mem_filter.1 hQ).2)]
  have hprod2 : (∏ Q ∈ Z, (max 1 (u / γ Q)) ^ m Q) = u ^ nT * PT⁻¹ := by
    rw [← Finset.prod_filter_mul_prod_filter_not Z (fun Q => u < γ Q), ← hS, ← hT, hPT, hnT,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    have hS1 : ∏ Q ∈ S, (max 1 (u / γ Q)) ^ m Q = 1 := by
      refine Finset.prod_eq_one fun Q hQ => ?_
      have hγ0 : 0 < γ Q := hp0.trans (hγ Q (hSZ Q hQ)).1
      rw [max_eq_left ((div_le_one hγ0).2 (Finset.mem_filter.1 hQ).2.le), one_pow]
    rw [hS1, one_mul]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    have hγ0 : 0 < γ Q := hp0.trans (hγ Q (hTZ Q hQ)).1
    rw [max_eq_right ((one_le_div hγ0).2 (not_lt.1 (Finset.mem_filter.1 hQ).2)), div_pow,
      div_eq_mul_inv]
  have hB1 : H ≤ u ^ (a - (nS : ℤ)) * PS := by
    rw [hprod1, hsplit] at h1
    calc H ≤ u ^ (a - ((nS + nT : ℕ) : ℤ)) * (PS * u ^ nT) := h1
      _ = u ^ (a - (nS : ℤ)) * PS := by
          rw [← zpow_natCast u nT, Nat.cast_add]
          rw [show a - ((nS : ℤ) + (nT : ℤ)) = (a - (nS : ℤ)) - (nT : ℤ) by ring, zpow_sub₀ hu0.ne']
          field_simp
  have hB2 : H ≤ C * (p / u) ^ (a' - (nT : ℤ)) * (p ^ nT * PT⁻¹) := by
    rw [hprod2] at h2
    calc H ≤ C * (p / u) ^ a' * (u ^ nT * PT⁻¹) := h2
      _ = C * (p / u) ^ (a' - (nT : ℤ)) * (p ^ nT * PT⁻¹) := by
          rw [zpow_sub₀ hpu0.ne', zpow_natCast, div_pow]
          field_simp
  have hq1 : p ^ nT * PT⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hPT0, one_mul]; exact hPTp
  have hq1' : T.Nonempty → p ^ nT * PT⁻¹ < 1 := fun hT' => by
    rw [mul_inv_lt_iff₀ hPT0, one_mul]; exact hPTp' hT'
  have hq0 : 0 ≤ p ^ nT * PT⁻¹ := mul_nonneg (pow_nonneg hp0.le _) (inv_nonneg.2 hPT0.le)
  have hPS0 : 0 ≤ PS :=
    Finset.prod_nonneg fun Q hQ => pow_nonneg (hp0.trans (hγ Q (hSZ Q hQ)).1).le _
  have hnSa' : (nS : ℤ) + (nT : ℤ) = a + a' := by rw [← hn, hsplit]; push_cast; ring
  by_cases hcase : (nS : ℤ) ≤ a
  · have hua : u ^ (a - (nS : ℤ)) ≤ 1 := zpow_le_one₀ hu0 hu1.le (by omega)
    have hH1 : H ≤ 1 := hB1.trans (by nlinarith [zpow_nonneg hu0.le (a - (nS : ℤ))])
    refine ⟨hH1, fun hstrict => ?_⟩
    by_cases hlt : (nS : ℤ) < a
    · have hua' : u ^ (a - (nS : ℤ)) < 1 := zpow_lt_one₀ hu0 hu1 (by omega)
      calc H ≤ u ^ (a - (nS : ℤ)) * PS := hB1
        _ ≤ u ^ (a - (nS : ℤ)) * 1 := mul_le_mul_of_nonneg_left hPS1 (zpow_nonneg hu0.le _)
        _ < 1 := by rw [mul_one]; exact hua'
    · have heq : (nS : ℤ) = a := le_antisymm hcase (not_lt.1 hlt)
      by_cases hSne : S.Nonempty
      · calc H ≤ u ^ (a - (nS : ℤ)) * PS := hB1
          _ ≤ 1 * PS := mul_le_mul_of_nonneg_right hua hPS0
          _ < 1 := by rw [one_mul]; exact hPS1' hSne
      · have hnS0 : nS = 0 := by
          rw [hnS]; exact Finset.sum_eq_zero fun Q hQ => (hSne ⟨Q, hQ⟩).elim
        have ha'T : a' - (nT : ℤ) = 0 := by omega
        rw [ha'T, zpow_zero, mul_one] at hB2
        by_cases hTne : T.Nonempty
        · calc H ≤ C * (p ^ nT * PT⁻¹) := hB2
            _ ≤ 1 * (p ^ nT * PT⁻¹) := mul_le_mul_of_nonneg_right hC1 hq0
            _ < 1 := by rw [one_mul]; exact hq1' hTne
        · have hnT0 : nT = 0 := by
            rw [hnT]; exact Finset.sum_eq_zero fun Q hQ => (hTne ⟨Q, hQ⟩).elim
          have hC : C < 1 := by
            rcases hstrict with hC | hpos
            · exact hC
            · exfalso; omega
          calc H ≤ C * (p ^ nT * PT⁻¹) := hB2
            _ ≤ C * 1 := mul_le_mul_of_nonneg_left hq1 hC0.le
            _ < 1 := by rw [mul_one]; exact hC
  · have hexp : 0 < a' - (nT : ℤ) := by omega
    have hlt : (p / u) ^ (a' - (nT : ℤ)) < 1 := zpow_lt_one₀ hpu0 hpu1 hexp
    have hH : H < 1 := by
      calc H ≤ C * (p / u) ^ (a' - (nT : ℤ)) * (p ^ nT * PT⁻¹) := hB2
        _ ≤ 1 * (p / u) ^ (a' - (nT : ℤ)) * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hC1 (zpow_nonneg hpu0.le _)) hq1 hq0
            exact mul_nonneg zero_le_one (zpow_nonneg hpu0.le _)
        _ < 1 := by rw [one_mul, mul_one]; exact hlt
    exact ⟨hH.le, fun _ => hH⟩

/-- **Two-end bound on an annulus.** Let `μ` be an absolute value on `L` with
`A = {a | μ a ≤ 1}`, and let `F / L` have principal divisors (every nonzero function has a
divisor, of degree zero). Let `An`, `An'` be annuli with the same places and the same nonzero
modulus `π`, whose coordinates multiply to `π`, attached to charts `C` at `x` and `C'` at `x'`,
with the coordinate of `An` taking two distinct absolute values on the annulus. Let `h` be
integral for `C` with nonzero reduction there and without poles on the annulus, and let `c' ∈ A`
be nonzero with `h / c'` integral for `C'` with nonzero reduction there. Then the orders at `x`
and `x'` of the two reductions have nonnegative sum, `μ (h(R)) ≤ 1` at every place `R` of the
annulus (strictly if `μ c' < 1` or the sum is positive), and if `μ c' = 1` and both orders vanish
then `h` has order zero and `μ (h(R)) = 1` at every place `R` of the annulus. -/
public theorem Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (_hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar')
    (hatt' : An'.IsAttached C' x')
    (hwide : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An.dom),
      μ (Q₁.evalAt (An.isRational Q₁ hQ₁) An.param) ≠
        μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers)
    (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h) :
    0 ≤ x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ∧
    (∀ (R : Place L F) (hR : R ∈ An.dom), μ (R.evalAt (An.isRational R hR) h) ≤ 1 ∧
      ((μ c' < 1 ∨
          0 < x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩)) →
        μ (R.evalAt (An.isRational R hR) h) < 1)) ∧
    ((μ c' = 1 ∧ x.ord (C.residue ⟨h, hC⟩) = 0 ∧
        x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0) →
      ∀ (R : Place L F) (hR : R ∈ An.dom),
        R.ord h = 0 ∧ μ (R.evalAt (An.isRational R hR) h) = 1) := by
  classical
  set h' : F := (algebraMap L F c')⁻¹ * h with hh'_def
  set a : ℤ := x.ord (C.residue ⟨h, hC⟩) with ha_def
  set a' : ℤ := x'.ord (C'.residue ⟨h', hC'⟩) with ha'_def
  set z : F := An.param with hz_def
  set z' : F := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ_def
  have hattC := hatt
  have hattC' := hatt'
  obtain ⟨hxnode, hzC, hzord, hlawC⟩ := hatt
  obtain ⟨hx'node, hz'C', hz'ord, hlawC'⟩ := hatt'
  have hh0 : h ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hC⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hh'0 : h' ≠ 0 := mul_ne_zero (inv_ne_zero ((map_ne_zero _).2 hc'0)) hh0
  have hπA : π ∈ A := An.modulus.2
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 :=
    abv_lt_one_of_mem_maximalIdeal_vs μ hμA hπA (by simpa [hπ_def] using An.modulus_mem)
  have hμc'1 : μ c' ≤ 1 := (hμA _).1 hc'A
  have hμc'0 : 0 < μ c' := μ.pos hc'0
  have hz'0 : z' ≠ 0 := by
    intro h0
    apply hmod0
    have : algebraMap L F π = 0 := by rw [← htwo, h0, zero_mul]
    exact (map_eq_zero _).1 this
  have hzbar0 : C.residue ⟨z, hzC⟩ ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hzord
    exact zero_ne_one hzord
  have hz'bar0 : C'.residue ⟨z', hz'C'⟩ ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hz'ord
    exact zero_ne_one hz'ord
  -- The values of the coordinate on the annulus, extended by `0` to the other places.
  set cz : Place L F → L := fun Q => if hQ : Q ∈ An.dom then Q.evalAt (An.isRational Q hQ) z else 0
    with hcz_def
  have hcz : ∀ Q (hQ : Q ∈ An.dom), Q.evalAt (An.isRational Q hQ) z = cz Q := fun Q hQ => by
    simp only [hcz_def, dite_eq_left hQ]
  have hdomfacts : ∀ Q ∈ An.dom, z ∈ Q.toValuationSubring ∧ z' ∈ Q.toValuationSubring ∧
      (∃ hzA : cz Q ∈ A, (⟨cz Q, hzA⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
      cz Q ≠ 0 ∧ 0 < μ (cz Q) ∧ μ (cz Q) < 1 ∧ μ π < μ (cz Q) ∧
      (∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ μ (m : L) < 1 ∧ π = cz Q * m) := by
    intro Q hQ
    obtain ⟨hzreg, hrest⟩ := An.mem_dom Q hQ
    rw [← hz_def, ← hπ_def, hcz Q hQ] at hrest
    obtain ⟨⟨hzA, hzmax⟩, hzne, m, hm, hπm⟩ := hrest
    obtain ⟨hz'reg, -⟩ := An'.mem_dom Q (hdom ▸ hQ)
    have hμm : μ (m : L) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA m.2 (by simpa using hm)
    have hμz : μ (cz Q) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
    have hπlt : μ π < μ (cz Q) := by
      rw [hπm, map_mul]
      calc μ (cz Q) * μ (m : L) < μ (cz Q) * 1 := mul_lt_mul_of_pos_left hμm (μ.pos hzne)
        _ = μ (cz Q) := mul_one _
    exact ⟨hzreg, hz'reg, ⟨hzA, hzmax⟩, hzne, μ.pos hzne, hμz, hπlt, m, hm, hμm, hπm⟩
  have hcA : ∀ Q ∈ An.dom, cz Q ∈ A := fun Q hQ => by
    obtain ⟨-, -, ⟨h1, -⟩, -⟩ := hdomfacts Q hQ
    exact h1
  have hcmax : ∀ Q (hQ : Q ∈ An.dom), (⟨cz Q, hcA Q hQ⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    fun Q hQ => by
      obtain ⟨-, -, ⟨h1, h2⟩, -⟩ := hdomfacts Q hQ
      exact h2
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) h hh0
  set Z : Finset (Place L F) := D.support.filter (fun Q => Q ∈ An.dom) with hZ_def
  have hZ : ∀ Q, Q ∈ Z ↔ Q ∈ An.dom ∧ 0 < Q.ord h := by
    intro Q
    rw [hZ_def, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    constructor
    · rintro ⟨hne, hQ⟩
      exact ⟨hQ, lt_of_le_of_ne (hpole Q hQ) (Ne.symm hne)⟩
    · rintro ⟨hQ, hpos⟩
      exact ⟨hpos.ne', hQ⟩
  have hZdom : ∀ Q ∈ Z, Q ∈ An.dom := fun Q hQ => ((hZ Q).1 hQ).1
  set m : Place L F → ℕ := fun Q => (Q.ord h).toNat with hm_def
  have hmQ : ∀ Q ∈ Z, ((m Q : ℕ) : ℤ) = Q.ord h := by
    intro Q hQ
    exact Int.toNat_of_nonneg ((hZ Q).1 hQ).2.le
  have hmpos : ∀ Q ∈ Z, 0 < m Q := by
    intro Q hQ
    have := ((hZ Q).1 hQ).2
    rw [← hmQ Q hQ] at this
    exact_mod_cast this
  set n : ℕ := ∑ Q ∈ Z, m Q with hn_def
  have hordh : ∀ R ∈ An.dom, R ∉ Z → R.ord h = 0 := by
    intro R hR hRZ
    have := hpole R hR
    by_contra hne
    exact hRZ ((hZ R).2 ⟨hR, lt_of_le_of_ne this (Ne.symm hne)⟩)
  have hc0 : ∀ Q ∈ Z, cz Q ≠ 0 := fun Q hQ => (hdomfacts Q (hZdom Q hQ)).2.2.2.1
  set v : Place L F → F := fun Q => algebraMap L F (cz Q) - z with hv_def
  have hv0 : ∀ Q ∈ Z, v Q ≠ 0 := by
    intro Q hQ h0
    have h1 := An.ord_param_sub Q (hZdom Q hQ)
    have : z - algebraMap L F (cz Q) = -(v Q) := by rw [hv_def]; ring
    rw [← hz_def, hcz Q (hZdom Q hQ), this, h0, neg_zero, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hvord : ∀ Q ∈ Z, ∀ R ∈ An.dom, R.ord (v Q) = if R = Q then 1 else 0 := by
    intro Q hQ R hR
    have hQd := hZdom Q hQ
    have hRrat := An.isRational R hR
    obtain ⟨hzR, -, -, hzRne, -⟩ := hdomfacts R hR
    obtain ⟨-, -, ⟨hzQA, hzQmax⟩, hzQne, -, -, -, mQ, hmQmax, hμmQ, hπmQ⟩ := hdomfacts Q hQd
    split_ifs with hRQ
    · subst hRQ
      have h1 := An.ord_param_sub R hQd
      rw [← hz_def, hcz R hQd] at h1
      have : v R = -(z - algebraMap L F (cz R)) := by rw [hv_def]; ring
      rw [this, Place.ord_neg']
      exact h1
    · have hvR : v Q ∈ R.toValuationSubring := sub_mem (R.algebraMap_mem' _) hzR
      apply R.ord_eq_zero_of_evalAt_ne_zero hRrat hvR
      rw [hv_def, R.evalAt_sub hRrat (R.algebraMap_mem' _) hzR, R.evalAt_algebraMap hRrat,
        hcz R hR]
      intro h0
      apply hRQ
      have hval : cz R = cz Q := (sub_eq_zero.1 h0).symm
      obtain ⟨P0, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨cz Q, hzQA⟩ hzQmax
        (by simpa using hzQne) ⟨mQ, hmQmax, by simpa [hπ_def] using hπmQ⟩
      have e1 := huniq R ⟨hR, by simpa [hz_def] using (hcz R hR).trans hval⟩
      have e2 := huniq Q ⟨hQd, by simpa [hz_def] using hcz Q hQd⟩
      exact e1.trans e2.symm
  have hvR : ∀ Q ∈ Z, ∀ R ∈ An.dom, v Q ∈ R.toValuationSubring := fun Q hQ R hR =>
    sub_mem (R.algebraMap_mem' _) (hdomfacts R hR).1
  have hvC : ∀ Q ∈ Z, v Q ∈ C.integers := fun Q hQ =>
    sub_mem ((C.algebraMap_mem_iff _).2 (hcA Q (hZdom Q hQ))) hzC
  have hvres : ∀ Q (hQ : Q ∈ Z), C.residue ⟨v Q, hvC Q hQ⟩ = -C.residue ⟨z, hzC⟩ := by
    intro Q hQ
    have e : (⟨v Q, hvC Q hQ⟩ : C.integers)
        = ⟨algebraMap L F ((⟨cz Q, hcA Q (hZdom Q hQ)⟩ : A) : L),
            (C.algebraMap_mem_iff _).mpr (⟨cz Q, hcA Q (hZdom Q hQ)⟩ : A).2⟩ - ⟨z, hzC⟩ :=
      Subtype.ext rfl
    rw [e, map_sub, C.residue_algebraMap,
      residue_eq_zero_of_mem_maximalIdeal' _ (hcmax Q (hZdom Q hQ)), map_zero, zero_sub]
  have hvres0 : ∀ Q (hQ : Q ∈ Z), C.residue ⟨v Q, hvC Q hQ⟩ ≠ 0 := fun Q hQ => by
    rw [hvres Q hQ]; exact neg_ne_zero.2 hzbar0
  set w : Place L F → F := fun Q => if Q ∈ Z then (v Q)⁻¹ else 1 with hw_def
  have hwZ : ∀ Q ∈ Z, w Q = (v Q)⁻¹ := fun Q hQ => by simp [hw_def, hQ]
  have hw0 : ∀ Q, w Q ≠ 0 := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hwZ Q hQ]; exact inv_ne_zero (hv0 Q hQ)
    · simp [hw_def, hQ]
  have hwC : ∀ Q, w Q ∈ C.integers := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hwZ Q hQ]
      exact inv_mem_of_isUnit' (hvC Q hQ) (C.isUnit_of_residue_ne_zero' (hvC Q hQ) (hvres0 Q hQ))
    · simp only [hw_def, hQ, ite_false]; exact one_mem _
  have hwres : ∀ Q, C.residue ⟨w Q, hwC Q⟩ = if Q ∈ Z then (-C.residue ⟨z, hzC⟩)⁻¹ else 1 := by
    intro Q
    by_cases hQ : Q ∈ Z
    · rw [ite_eq_left hQ]
      have hwi : (v Q)⁻¹ ∈ C.integers := (hwZ Q hQ) ▸ hwC Q
      have e : (⟨w Q, hwC Q⟩ : C.integers) = ⟨(v Q)⁻¹, hwi⟩ := Subtype.ext (hwZ Q hQ)
      rw [e, C.residue_inv' (hvC Q hQ) (hvres0 Q hQ) hwi, hvres Q hQ]
    · rw [ite_eq_right hQ]
      have e : (⟨w Q, hwC Q⟩ : C.integers) = 1 := Subtype.ext (by simp [hw_def, hQ])
      rw [e, map_one]
  have hword : ∀ Q ∈ Z, ∀ R ∈ An.dom, R.ord (w Q) = -(if R = Q then 1 else 0) := by
    intro Q hQ R hR
    rw [hwZ Q hQ, Place.ord_inv, hvord Q hQ R hR]
  set gC : F := h * ∏ Q ∈ Z, w Q ^ m Q with hgC_def
  have hgC0 : gC ≠ 0 := mul_ne_zero hh0 (Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (hw0 Q))
  have hgCmem : gC ∈ C.integers := mul_mem hC (prod_mem fun Q _ => pow_mem (hwC Q) _)
  have hprodmem : (∏ Q ∈ Z, w Q ^ m Q) ∈ C.integers := prod_mem fun Q _ => pow_mem (hwC Q) _
  have hprodres : C.residue ⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ = ((-C.residue ⟨z, hzC⟩)⁻¹) ^ n := by
    have e : (⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ : C.integers) =
        ∏ Q ∈ Z, (⟨w Q, hwC Q⟩ : C.integers) ^ m Q := by
      apply Subtype.ext
      push_cast
      rfl
    rw [e, map_prod]
    simp_rw [map_pow, hwres]
    rw [hn_def, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun Q hQ => by rw [ite_eq_left hQ]
  have hgCres : C.residue ⟨gC, hgCmem⟩ = C.residue ⟨h, hC⟩ * ((-C.residue ⟨z, hzC⟩)⁻¹) ^ n := by
    have e : (⟨gC, hgCmem⟩ : C.integers) = ⟨h, hC⟩ * ⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, hprodres]
  have hgCres0 : C.residue ⟨gC, hgCmem⟩ ≠ 0 := by
    rw [hgCres]
    exact mul_ne_zero hres (pow_ne_zero _ (inv_ne_zero (neg_ne_zero.2 hzbar0)))
  have hgCord : x.ord (C.residue ⟨gC, hgCmem⟩) = a - n := by
    rw [hgCres, x.ord_mul hres (pow_ne_zero _ (inv_ne_zero (neg_ne_zero.2 hzbar0))), ← ha_def,
      x.ord_pow', x.ord_inv, x.ord_neg', hzord]
    ring
  have hgCzf : ∀ R ∈ An.dom, R.ord gC = 0 := by
    intro R hR
    rw [hgC_def, R.ord_mul hh0 (Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (hw0 Q)),
      R.ord_prod' _ _ (fun Q _ => pow_ne_zero _ (hw0 Q))]
    simp_rw [R.ord_pow']
    have hsum : ∑ Q ∈ Z, (m Q : ℤ) * R.ord (w Q) = -(if R ∈ Z then (m R : ℤ) else 0) := by
      rw [Finset.sum_congr rfl fun Q hQ => by rw [hword Q hQ R hR]]
      simp_rw [mul_neg, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_neg_distrib, Finset.sum_ite_eq Z R (fun Q => (m Q : ℤ))]
    rw [hsum]
    by_cases hRZ : R ∈ Z
    · rw [ite_eq_left hRZ, hmQ R hRZ]; ring
    · rw [ite_eq_right hRZ, hordh R hR hRZ]; ring
  have hslopeC : ∀ R (hR : R ∈ An.dom),
      μ (R.evalAt (An.isRational R hR) gC) = μ (cz R) ^ (a - (n : ℤ)) := by
    intro R hR
    obtain ⟨-, -, h3⟩ :=
      abv_evalAt_eq_zpow_of_isAttached μ hμA An C x hattC gC hgCmem hgCres0 hgCzf R hR
    rw [h3, hgCord, ← hz_def, hcz R hR]
  have hz'unit : IsUnit (⟨z', hz'C'⟩ : C'.integers) := C'.isUnit_of_residue_ne_zero' hz'C' hz'bar0
  have hz'inv : z'⁻¹ ∈ C'.integers := inv_mem_of_isUnit' hz'C' hz'unit
  have hzeq : z = algebraMap L F π * z'⁻¹ := by
    rw [← htwo]; field_simp
  have htQ : ∀ Q ∈ Z, ∃ ht : z * algebraMap L F (cz Q)⁻¹ ∈ C'.integers,
      C'.residue ⟨_, ht⟩ = 0 := by
    intro Q hQ
    obtain ⟨-, -, -, -, -, -, -, mQ, hmQmax, -, hπmQ⟩ := hdomfacts Q (hZdom Q hQ)
    have hπc : π * (cz Q)⁻¹ = (mQ : L) := by
      rw [hπmQ, mul_comm (cz Q) (mQ : L), mul_inv_cancel_right₀ (hc0 Q hQ)]
    have e1 : z * algebraMap L F (cz Q)⁻¹ = algebraMap L F (mQ : L) * z'⁻¹ := by
      nth_rewrite 1 [hzeq]
      rw [← hπc, map_mul]
      ring
    have hmem : algebraMap L F (mQ : L) * z'⁻¹ ∈ C'.integers :=
      mul_mem ((C'.algebraMap_mem_iff _).2 mQ.2) hz'inv
    refine ⟨e1 ▸ hmem, ?_⟩
    have e2 : (⟨z * algebraMap L F (cz Q)⁻¹, e1 ▸ hmem⟩ : C'.integers)
        = ⟨algebraMap L F (mQ : L), (C'.algebraMap_mem_iff _).mpr mQ.2⟩ * ⟨z'⁻¹, hz'inv⟩ :=
      Subtype.ext e1
    rw [e2, map_mul, C'.residue_algebraMap,
      residue_eq_zero_of_mem_maximalIdeal' _ (by simpa using hmQmax),
      map_zero, zero_mul]
  set v' : Place L F → F := fun Q => 1 - z * algebraMap L F (cz Q)⁻¹ with hv'_def
  have hv'C : ∀ Q ∈ Z, v' Q ∈ C'.integers := fun Q hQ => sub_mem (one_mem _) (htQ Q hQ).1
  have hv'res : ∀ Q (hQ : Q ∈ Z), C'.residue ⟨v' Q, hv'C Q hQ⟩ = 1 := by
    intro Q hQ
    obtain ⟨ht, htres⟩ := htQ Q hQ
    have e : (⟨v' Q, hv'C Q hQ⟩ : C'.integers) = 1 - ⟨_, ht⟩ := Subtype.ext rfl
    rw [e, map_sub, map_one, htres, sub_zero]
  have hv'w : ∀ Q ∈ Z, v' Q = algebraMap L F (cz Q)⁻¹ * v Q := by
    intro Q hQ
    rw [hv'_def, hv_def]
    simp only []
    rw [map_inv₀]
    field_simp [(map_ne_zero (algebraMap L F)).2 (hc0 Q hQ)]
  have hv'0 : ∀ Q ∈ Z, v' Q ≠ 0 := fun Q hQ => by
    rw [hv'w Q hQ]
    exact mul_ne_zero ((map_ne_zero (algebraMap L F)).2 (inv_ne_zero (hc0 Q hQ))) (hv0 Q hQ)
  set w' : Place L F → F := fun Q => if Q ∈ Z then (v' Q)⁻¹ else 1 with hw'_def
  have hw'Z : ∀ Q ∈ Z, w' Q = (v' Q)⁻¹ := fun Q hQ => by simp [hw'_def, hQ]
  have hw'w : ∀ Q, w' Q = (if Q ∈ Z then algebraMap L F (cz Q) else 1) * w Q := by
    intro Q
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ, hwZ Q hQ, ite_eq_left hQ, hv'w Q hQ, mul_inv, map_inv₀, inv_inv]
    · simp [hw'_def, hw_def, hQ]
  have hw'0 : ∀ Q, w' Q ≠ 0 := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ]; exact inv_ne_zero (hv'0 Q hQ)
    · simp [hw'_def, hQ]
  have hw'C : ∀ Q, w' Q ∈ C'.integers := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ]
      exact inv_mem_of_isUnit' (hv'C Q hQ)
        (C'.isUnit_of_residue_ne_zero' (hv'C Q hQ) (by rw [hv'res Q hQ]; exact one_ne_zero))
    · simp only [hw'_def, hQ, ite_false]; exact one_mem _
  have hw'res : ∀ Q, C'.residue ⟨w' Q, hw'C Q⟩ = 1 := by
    intro Q
    by_cases hQ : Q ∈ Z
    · have hwi : (v' Q)⁻¹ ∈ C'.integers := (hw'Z Q hQ) ▸ hw'C Q
      have e : (⟨w' Q, hw'C Q⟩ : C'.integers) = ⟨(v' Q)⁻¹, hwi⟩ := Subtype.ext (hw'Z Q hQ)
      rw [e, C'.residue_inv' (hv'C Q hQ) (by rw [hv'res Q hQ]; exact one_ne_zero) hwi,
        hv'res Q hQ, inv_one]
    · have e : (⟨w' Q, hw'C Q⟩ : C'.integers) = 1 := Subtype.ext (by simp [hw'_def, hQ])
      rw [e, map_one]
  set gC' : F := h' * ∏ Q ∈ Z, w' Q ^ m Q with hgC'_def
  have hgC'mem : gC' ∈ C'.integers := mul_mem hC' (prod_mem fun Q _ => pow_mem (hw'C Q) _)
  have hprodmem' : (∏ Q ∈ Z, w' Q ^ m Q) ∈ C'.integers := prod_mem fun Q _ => pow_mem (hw'C Q) _
  have hprodres' : C'.residue ⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ = 1 := by
    have e : (⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ : C'.integers) =
        ∏ Q ∈ Z, (⟨w' Q, hw'C Q⟩ : C'.integers) ^ m Q := by
      apply Subtype.ext
      push_cast
      rfl
    rw [e, map_prod]
    simp_rw [map_pow, hw'res, one_pow]
    exact Finset.prod_const_one
  have hgC'res : C'.residue ⟨gC', hgC'mem⟩ = C'.residue ⟨h', hC'⟩ := by
    have e : (⟨gC', hgC'mem⟩ : C'.integers) = ⟨h', hC'⟩ * ⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, hprodres', mul_one]
  have hgC'res0 : C'.residue ⟨gC', hgC'mem⟩ ≠ 0 := by rw [hgC'res]; exact hres'
  set κ : L := c'⁻¹ * ∏ Q ∈ Z, cz Q ^ m Q with hκ_def
  have hκ0 : κ ≠ 0 := mul_ne_zero (inv_ne_zero hc'0)
    (Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (hc0 Q hQ))
  have hgC'eq : gC' = algebraMap L F κ * gC := by
    have hprod : (∏ Q ∈ Z, w' Q ^ m Q) =
        algebraMap L F (∏ Q ∈ Z, cz Q ^ m Q) * ∏ Q ∈ Z, w Q ^ m Q := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun Q hQ => ?_
      rw [hw'w Q, ite_eq_left hQ, mul_pow, map_pow]
    rw [hgC'_def, hgC_def, hh'_def, hprod, hκ_def, map_mul, map_inv₀]
    ring
  have hgC'zf : ∀ R ∈ An'.dom, R.ord gC' = 0 := by
    intro R hR
    rw [hdom] at hR
    rw [hgC'eq, R.ord_mul ((map_ne_zero _).2 hκ0) hgC0, R.ord_algebraMap, hgCzf R hR, add_zero]
  have hgC'ord : x'.ord (C'.residue ⟨gC', hgC'mem⟩) = a' := by rw [hgC'res]
  have hslopeC' : ∀ R (hR : R ∈ An.dom),
      μ (R.evalAt (An.isRational R hR) gC') = μ (R.evalAt (An.isRational R hR) z') ^ a' := by
    intro R hR
    obtain ⟨-, -, h3⟩ := abv_evalAt_eq_zpow_of_isAttached μ hμA An' C' x' hattC' gC' hgC'mem
      hgC'res0 hgC'zf R
      (hdom ▸ hR)
    rw [h3, hgC'ord]
  have hgCreg : ∀ R ∈ An.dom, gC ∈ R.toValuationSubring := fun R hR =>
    R.mem_of_ord_nonneg hgC0 (hgCzf R hR).symm.le
  have hprofile : ∀ R ∈ An.dom,
      μ (cz R) ^ (a - (n : ℤ) + a') = μ π ^ a' * (μ κ)⁻¹ := by
    intro R hR
    have hRrat := An.isRational R hR
    obtain ⟨hzR, hz'R, -, hzRne, hu0, hu1, hπu, -⟩ := hdomfacts R hR
    have hprod : R.evalAt hRrat z' * cz R = π := by
      rw [← hcz R hR, ← R.evalAt_mul hRrat hz'R hzR, htwo, R.evalAt_algebraMap hRrat]
    have hz'val : μ (R.evalAt hRrat z') = μ π * (μ (cz R))⁻¹ := by
      rw [← hprod, map_mul, mul_inv_cancel_right₀ hu0.ne']
    have h1 := hslopeC R hR
    have h2 := hslopeC' R hR
    rw [hz'val] at h2
    have h3 : R.evalAt hRrat gC' = κ * R.evalAt hRrat gC := by
      rw [hgC'eq, R.evalAt_mul hRrat (R.algebraMap_mem' _) (hgCreg R hR),
        R.evalAt_algebraMap hRrat]
    rw [h3, map_mul, h1, mul_zpow, inv_zpow, ← div_eq_mul_inv] at h2
    have hua' : μ (cz R) ^ a' ≠ 0 := zpow_ne_zero _ hu0.ne'
    have hμκ0 : μ κ ≠ 0 := (μ.pos hκ0).ne'
    rw [eq_div_iff hua'] at h2
    rw [zpow_add₀ hu0.ne', eq_mul_inv_iff_mul_eq₀ hμκ0]
    calc μ (cz R) ^ (a - (n : ℤ)) * μ (cz R) ^ a' * μ κ
        = μ κ * μ (cz R) ^ (a - (n : ℤ)) * μ (cz R) ^ a' := by ring
      _ = μ π ^ a' := h2
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hexp : a - (n : ℤ) + a' = 0 := by
    by_contra hne0
    apply hne
    have hu1 := (hdomfacts Q₁ hQ₁).2.2.2.2.1
    have hu2 := (hdomfacts Q₂ hQ₂).2.2.2.2.1
    have h12 : μ (cz Q₁) ^ (a - (n : ℤ) + a') = μ (cz Q₂) ^ (a - (n : ℤ) + a') := by
      rw [hprofile Q₁ hQ₁, hprofile Q₂ hQ₂]
    rw [hcz Q₁ hQ₁, hcz Q₂ hQ₂]
    exact (zpow_left_inj₀ hu1.le hu2.le hne0).1 h12
  have hn : (n : ℤ) = a + a' := by omega
  refine ⟨by omega, ?_, ?_⟩
  · intro R hR
    have hRrat := An.isRational R hR
    obtain ⟨hzR, hz'R, -, hzRne, hu0, hu1, hπu, -⟩ := hdomfacts R hR
    have hfacC : gC * ∏ Q ∈ Z, v Q ^ m Q = h := by
      rw [hgC_def, mul_assoc, ← Finset.prod_mul_distrib]
      rw [Finset.prod_congr rfl (fun Q hQ => by
        rw [hwZ Q hQ, ← mul_pow, inv_mul_cancel₀ (hv0 Q hQ), one_pow])]
      simp
    have hvpowR : ∀ Q ∈ Z, v Q ^ m Q ∈ R.toValuationSubring := fun Q hQ => pow_mem (hvR Q hQ R hR) _
    have hprodR : (∏ Q ∈ Z, v Q ^ m Q) ∈ R.toValuationSubring := prod_mem hvpowR
    have hprodval := R.evalAt_prod hRrat Z (fun Q => v Q ^ m Q) hvpowR
    have hevalv : ∀ Q ∈ Z, R.evalAt hRrat (v Q) = cz Q - cz R := fun Q hQ => by
      rw [hv_def, R.evalAt_sub hRrat (R.algebraMap_mem' _) hzR, R.evalAt_algebraMap hRrat,
        hcz R hR]
    have hμh1 : μ (R.evalAt hRrat h) =
        μ (cz R) ^ (a - (n : ℤ)) * ∏ Q ∈ Z, μ (cz Q - cz R) ^ m Q := by
      rw [← hfacC, R.evalAt_mul hRrat (hgCreg R hR) hprodR, map_mul, hslopeC R hR, hprodval,
        map_prod]
      congr 1
      exact Finset.prod_congr rfl fun Q hQ => by
        rw [R.evalAt_pow hRrat (hvR Q hQ R hR), map_pow, hevalv Q hQ]
    have hbound1 : μ (R.evalAt hRrat h) ≤ μ (cz R) ^ (a - ((∑ Q ∈ Z, m Q : ℕ) : ℤ)) *
        ∏ Q ∈ Z, (max (μ (cz Q)) (μ (cz R))) ^ m Q := by
      rw [hμh1, ← hn_def]
      refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg hu0.le _)
      exact Finset.prod_le_prod₀ (fun Q _ => pow_nonneg (μ.nonneg _) _) fun Q hQ =>
        pow_le_pow_left₀ (μ.nonneg _) (abv_sub_le_max μ hμA _ _) _
    have hfacC' : algebraMap L F c' * (gC' * ∏ Q ∈ Z, v' Q ^ m Q) = h := by
      have : gC' * ∏ Q ∈ Z, v' Q ^ m Q = h' := by
        rw [hgC'_def, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_congr rfl (fun Q hQ => by
          rw [hw'Z Q hQ, ← mul_pow, inv_mul_cancel₀ (hv'0 Q hQ), one_pow])]
        simp
      rw [this, hh'_def, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 hc'0), one_mul]
    have hv'R : ∀ Q ∈ Z, v' Q ∈ R.toValuationSubring := fun Q hQ =>
      sub_mem (one_mem _) (mul_mem hzR (R.algebraMap_mem' _))
    have hv'powR : ∀ Q ∈ Z, v' Q ^ m Q ∈ R.toValuationSubring := fun Q hQ => pow_mem (hv'R Q hQ) _
    have hprodR' : (∏ Q ∈ Z, v' Q ^ m Q) ∈ R.toValuationSubring := prod_mem hv'powR
    have hprodval' := R.evalAt_prod hRrat Z (fun Q => v' Q ^ m Q) hv'powR
    have hgC'reg : gC' ∈ R.toValuationSubring := by
      rw [hgC'eq]; exact mul_mem (R.algebraMap_mem' _) (hgCreg R hR)
    have hevalv' : ∀ Q ∈ Z, R.evalAt hRrat (v' Q) = 1 - cz R * (cz Q)⁻¹ := fun Q hQ => by
      rw [hv'_def, R.evalAt_sub hRrat (one_mem _) (mul_mem hzR (R.algebraMap_mem' _)),
        R.evalAt_one hRrat, R.evalAt_mul hRrat hzR (R.algebraMap_mem' _),
        R.evalAt_algebraMap hRrat, hcz R hR]
    have hprodQ : R.evalAt hRrat z' * cz R = π := by
      rw [← hcz R hR, ← R.evalAt_mul hRrat hz'R hzR, htwo, R.evalAt_algebraMap hRrat]
    have hz'val : μ (R.evalAt hRrat z') = μ π / μ (cz R) := by
      rw [← hprodQ, map_mul, mul_div_cancel_right₀ _ hu0.ne']
    have hμh2 : μ (R.evalAt hRrat h) = μ c' * (μ π / μ (cz R)) ^ a' *
        ∏ Q ∈ Z, μ (1 - cz R * (cz Q)⁻¹) ^ m Q := by
      rw [← hfacC', R.evalAt_mul hRrat (R.algebraMap_mem' _) (mul_mem hgC'reg hprodR'),
        R.evalAt_algebraMap hRrat, R.evalAt_mul hRrat hgC'reg hprodR', map_mul, map_mul,
        hslopeC' R hR,
        hz'val, hprodval', map_prod, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun Q hQ => by
        rw [R.evalAt_pow hRrat (hv'R Q hQ), map_pow, hevalv' Q hQ]
    have hbound2 : μ (R.evalAt hRrat h) ≤ μ c' * (μ π / μ (cz R)) ^ a' *
        ∏ Q ∈ Z, (max 1 (μ (cz R) / μ (cz Q))) ^ m Q := by
      rw [hμh2]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (μ.nonneg _) (zpow_nonneg (div_nonneg hμπ0.le hu0.le) _))
      refine Finset.prod_le_prod₀ (fun Q _ => pow_nonneg (μ.nonneg _) _) fun Q hQ => ?_
      refine pow_le_pow_left₀ (μ.nonneg _) ?_ _
      have := abv_sub_le_max μ hμA (1 : L) (cz R * (cz Q)⁻¹)
      rw [map_one, map_mul, map_inv₀] at this
      rw [div_eq_mul_inv]
      exact this
    have hγ : ∀ Q ∈ Z, μ π < μ (cz Q) ∧ μ (cz Q) < 1 := fun Q hQ => by
      obtain ⟨-, -, -, -, -, h7, h8, -⟩ := hdomfacts Q (hZdom Q hQ)
      exact ⟨h8, h7⟩
    have hncast : ((∑ Q ∈ Z, m Q : ℕ) : ℤ) = a + a' := by rw [← hn_def]; exact hn
    exact two_end_profile_bound Z m (fun Q => μ (cz Q)) (μ π) (μ (cz R)) (μ c')
      (μ (R.evalAt hRrat h))
      a a' hμπ0 hπu hu1 hγ hmpos hμc'0 hμc'1 hncast hbound1 hbound2
  · rintro ⟨hμc', ha0, ha'0⟩ R hR
    have hn0 : n = 0 := by omega
    have hZe : Z = ∅ := by
      by_contra hZne
      obtain ⟨Q, hQ⟩ := Finset.nonempty_iff_ne_empty.2 hZne
      have : 0 < n := by
        rw [hn_def]
        exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨Q, hQ, hmpos Q hQ⟩
      omega
    have hRZ : R ∉ Z := by rw [hZe]; exact Finset.notMem_empty _
    refine ⟨hordh R hR hRZ, ?_⟩
    have hgCh : gC = h := by rw [hgC_def, hZe, Finset.prod_empty, mul_one]
    have := hslopeC R hR
    rw [hgCh, hn0] at this
    rw [this, ha0]
    simp

/-- **Maximum principle on an annulus attached at both ends.** In the setting of
`Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends`, a nonzero function `g`
without poles on the annulus, integral for `C`, and integral for `C'` after dividing by a nonzero
constant `b`, satisfies `μ (g(R)) ≤ max 1 (μ b)` at every place `R` of the annulus, with strict
inequality when `μ b ≠ 1`. -/
public theorem Annulus.abv_evalAt_le_max_of_isAttached_both_ends
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar')
    (hatt' : An'.IsAttached C' x')
    (hwide : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An.dom),
      μ (Q₁.evalAt (An.isRational Q₁ hQ₁) An.param) ≠
        μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0) (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ (R : Place L F) (hR : R ∈ An.dom), μ (R.evalAt (An.isRational R hR) g) ≤ max 1 (μ b) ∧
      (μ b ≠ 1 → μ (R.evalAt (An.isRational R hR) g) < max 1 (μ b)) := by
  classical
  obtain ⟨-, hzC, hzord, -⟩ := id hatt
  obtain ⟨-, hz'C', hz'ord, -⟩ := id hatt'
  set z := An.param with hz_def
  set z' := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hbL : algebraMap L F b ≠ 0 := (map_ne_zero _).2 hb0
  set g' : F := (algebraMap L F b)⁻¹ * g with hg'
  have hg'0 : g' ≠ 0 := mul_ne_zero (inv_ne_zero hbL) hg0
  have hdomR : ∀ R (hR : R ∈ An.dom),
      z ∈ R.toValuationSubring ∧ z' ∈ R.toValuationSubring ∧
      R.evalAt (An.isRational R hR) z ≠ 0 ∧ R.evalAt (An.isRational R hR) z' ≠ 0 ∧
      R.evalAt (An.isRational R hR) z' * R.evalAt (An.isRational R hR) z = π := by
    intro R hR
    have hrat := An.isRational R hR
    obtain ⟨hzR, -, hzR0, -⟩ := An.mem_dom R hR
    obtain ⟨hz'R, -, hz'R0, -⟩ := An'.mem_dom R (hdom ▸ hR)
    have hprod : R.evalAt hrat z' * R.evalAt hrat z = π := by
      rw [← R.evalAt_mul hrat hz'R hzR, htwo, R.evalAt_algebraMap hrat]
    exact ⟨hzR, hz'R, hzR0, hz'R0, hprod⟩
  have hwide' : ∃ (Q₁ : Place L F) (hQ₁ : Q₁ ∈ An'.dom) (Q₂ : Place L F) (hQ₂ : Q₂ ∈ An'.dom),
      μ (Q₁.evalAt (An'.isRational Q₁ hQ₁) An'.param) ≠
        μ (Q₂.evalAt (An'.isRational Q₂ hQ₂) An'.param) := by
    obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
    refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
    have key : ∀ R (hR : R ∈ An.dom), μ (R.evalAt (An.isRational R hR) An'.param) *
        μ (R.evalAt (An.isRational R hR) z) = μ π := by
      intro R hR
      obtain ⟨-, -, -, -, hp⟩ := hdomR R hR
      rw [← map_mul]; exact congrArg μ hp
    intro heq; apply hne
    have h1 := key Q₁ hQ₁
    have h2 := key Q₂ hQ₂
    rw [heq] at h1
    have h12 := h1.trans h2.symm
    have hne0 : μ (Q₂.evalAt (An.isRational Q₂ hQ₂) An'.param) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h2; exact hμπ0.ne h2
    exact mul_left_cancel₀ hne0 h12
  obtain ⟨c₁, hc₁g, hc₁res⟩ := C.exists_smul_mem g hg0
  obtain ⟨c₂, hc₂g, hc₂res⟩ := C'.exists_smul_mem g' hg'0
  set h₀ : F := c₁ • g with hh₀
  set h₁ : F := c₂ • g' with hh₁
  have hsm₁ : h₀ = algebraMap L F c₁ * g := Algebra.smul_def _ _
  have hsm₂ : h₁ = algebraMap L F c₂ * g' := Algebra.smul_def _ _
  have hc₁0 : c₁ ≠ 0 := by
    intro h0; apply hc₁res
    have : (⟨h₀, hc₁g⟩ : C.integers) = 0 := Subtype.ext (by change c₁ • g = 0; rw [h0, zero_smul])
    rw [this, map_zero]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0; apply hc₂res
    have : (⟨h₁, hc₂g⟩ : C'.integers) = 0 := Subtype.ext (by change c₂ • g' = 0; rw [h0, zero_smul])
    rw [this, map_zero]
  have hu₁ : IsUnit (⟨h₀, hc₁g⟩ : C.integers) := C.isUnit_of_residue_ne_zero' hc₁g hc₁res
  have hu₂ : IsUnit (⟨h₁, hc₂g⟩ : C'.integers) := C'.isUnit_of_residue_ne_zero' hc₂g hc₂res
  have hc₁invA : c₁⁻¹ ∈ A := by
    have hinv : h₀⁻¹ ∈ C.integers := inv_mem_of_isUnit' hc₁g hu₁
    have hprod : g * h₀⁻¹ = algebraMap L F c₁⁻¹ := by
      rw [hsm₁, map_inv₀]; field_simp
    have : algebraMap L F c₁⁻¹ ∈ C.integers := by rw [← hprod]; exact mul_mem hgC hinv
    exact (C.algebraMap_mem_iff _).1 this
  have hc₂invA : c₂⁻¹ ∈ A := by
    have hinv : h₁⁻¹ ∈ C'.integers := inv_mem_of_isUnit' hc₂g hu₂
    have hprod : g' * h₁⁻¹ = algebraMap L F c₂⁻¹ := by
      rw [hsm₂, map_inv₀]; field_simp
    have : algebraMap L F c₂⁻¹ ∈ C'.integers := by rw [← hprod]; exact mul_mem hgC' hinv
    exact (C'.algebraMap_mem_iff _).1 this
  have hμc₁ : 1 ≤ μ c₁ := by
    have h1 : μ c₁⁻¹ ≤ 1 := (hμA _).1 hc₁invA
    rw [map_inv₀] at h1; exact (inv_le_one₀ (μ.pos hc₁0)).1 h1
  have hμc₂ : 1 ≤ μ c₂ := by
    have h1 : μ c₂⁻¹ ≤ 1 := (hμA _).1 hc₂invA
    rw [map_inv₀] at h1; exact (inv_le_one₀ (μ.pos hc₂0)).1 h1
  set c'' : L := c₁ * b * c₂⁻¹ with hc''
  have hc''0 : c'' ≠ 0 := mul_ne_zero (mul_ne_zero hc₁0 hb0) (inv_ne_zero hc₂0)
  have key₁ : (algebraMap L F c'')⁻¹ * h₀ = h₁ := by
    rw [hsm₁, hsm₂, hg', hc'', map_mul, map_mul, map_inv₀]
    have h1 : algebraMap L F c₁ ≠ 0 := (map_ne_zero _).2 hc₁0
    have h2 : algebraMap L F c₂ ≠ 0 := (map_ne_zero _).2 hc₂0
    field_simp
  have key₂ : (algebraMap L F c''⁻¹)⁻¹ * h₁ = h₀ := by
    rw [map_inv₀, inv_inv, ← key₁, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 hc''0),
      one_mul h₀]
  have hh₀0 : h₀ ≠ 0 := by rw [hsm₁]; exact mul_ne_zero ((map_ne_zero _).2 hc₁0) hg0
  have hh₁0 : h₁ ≠ 0 := by rw [hsm₂]; exact mul_ne_zero ((map_ne_zero _).2 hc₂0) hg'0
  have hordh₀ : ∀ R ∈ An.dom, R.ord h₀ = R.ord g := by
    intro R hR; rw [hsm₁, R.ord_mul ((map_ne_zero _).2 hc₁0) hg0, Place.ord_algebraMap, zero_add]
  have hordh₁ : ∀ R ∈ An.dom, R.ord h₁ = R.ord g := by
    intro R hR
    rw [hsm₂, hg', R.ord_mul ((map_ne_zero _).2 hc₂0) hg'0, Place.ord_algebraMap, zero_add,
      R.ord_mul (inv_ne_zero hbL) hg0, Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  have hpole₀ : ∀ R ∈ An.dom, 0 ≤ R.ord h₀ := fun R hR => by rw [hordh₀ R hR]; exact hpole R hR
  have hpole₁ : ∀ R ∈ An'.dom, 0 ≤ R.ord h₁ := fun R hR => by
    rw [hordh₁ R (hdom ▸ hR)]; exact hpole R (hdom ▸ hR)
  have hval : ∀ R (hR : R ∈ An.dom), g ∈ R.toValuationSubring ∧
      μ (R.evalAt (An.isRational R hR) h₀) = μ c₁ * μ (R.evalAt (An.isRational R hR) g) ∧
        μ (R.evalAt (An.isRational R hR) h₁) =
          μ c₂ * (μ b)⁻¹ * μ (R.evalAt (An.isRational R hR) g) := by
    intro R hR
    have hrat := An.isRational R hR
    have hgR : g ∈ R.toValuationSubring := R.mem_of_ord_nonneg hg0 (hpole R hR)
    refine ⟨hgR, ?_, ?_⟩
    · rw [hsm₁, R.evalAt_mul hrat (R.algebraMap_mem' _) hgR, R.evalAt_algebraMap hrat, map_mul]
    · rw [hsm₂, hg', ← mul_assoc, ← map_inv₀, ← map_mul,
        R.evalAt_mul hrat (R.algebraMap_mem' _) hgR, R.evalAt_algebraMap hrat, map_mul, map_mul,
        map_inv₀]
  intro R hR
  have hRrat := An.isRational R hR
  obtain ⟨hgR, hv₀, hv₁⟩ := hval R hR
  have hμb0 : 0 < μ b := μ.pos hb0
  have hμc₁0 : 0 < μ c₁ := μ.pos hc₁0
  have hμc₂0 : 0 < μ c₂ := μ.pos hc₂0
  by_cases hle : μ c'' ≤ 1
  · have hc''A : c'' ∈ A := (hμA _).2 hle
    have hC'₀ : (algebraMap L F c'')⁻¹ * h₀ ∈ C'.integers := by rw [key₁]; exact hc₂g
    have e1 : (⟨_, hC'₀⟩ : C'.integers) = ⟨h₁, hc₂g⟩ := Subtype.ext key₁
    have hres'₀ : C'.residue ⟨_, hC'₀⟩ ≠ 0 := by rw [e1]; exact hc₂res
    obtain ⟨-, hb', -⟩ := Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
      μ hμA An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide h₀ hc₁g hc₁res c'' hc''0 hc''A
      hC'₀ hres'₀ hpole₀
    obtain ⟨hle1, hstrict⟩ := hb' R hR
    have hg1 : μ (R.evalAt hRrat g) ≤ 1 := by
      calc μ (R.evalAt hRrat g) = 1 * μ (R.evalAt hRrat g) := (one_mul _).symm
        _ ≤ μ c₁ * μ (R.evalAt hRrat g) := mul_le_mul_of_nonneg_right hμc₁ (μ.nonneg _)
        _ = μ (R.evalAt hRrat h₀) := hv₀.symm
        _ ≤ 1 := hle1
    refine ⟨hg1.trans (le_max_left _ _), fun hb1 => ?_⟩
    rcases hμc₁.lt_or_eq with hgt1 | heq1
    · by_cases hg00 : R.evalAt hRrat g = 0
      · rw [hg00, map_zero]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
      · have hpos : 0 < μ (R.evalAt hRrat g) := μ.pos hg00
        calc μ (R.evalAt hRrat g) = 1 * μ (R.evalAt hRrat g) := (one_mul _).symm
          _ < μ c₁ * μ (R.evalAt hRrat g) := mul_lt_mul_of_pos_right hgt1 hpos
          _ = μ (R.evalAt hRrat h₀) := hv₀.symm
          _ ≤ 1 := hle1
          _ ≤ max 1 (μ b) := le_max_left _ _
    · rcases lt_or_gt_of_ne hb1 with hblt | hbgt
      · have hc''lt : μ c'' < 1 := by
          rw [hc'', map_mul, map_mul, map_inv₀, ← heq1, one_mul]
          calc μ b * (μ c₂)⁻¹ ≤ μ b * 1 := by
                apply mul_le_mul_of_nonneg_left _ hμb0.le
                exact inv_le_one_of_one_le₀ hμc₂
            _ = μ b := mul_one _
            _ < 1 := hblt
        have h1 : μ (R.evalAt hRrat h₀) < 1 := hstrict (Or.inl hc''lt)
        rw [hv₀, ← heq1, one_mul] at h1
        exact h1.trans_le (le_max_left _ _)
      · exact hg1.trans_lt (lt_max_of_lt_right hbgt)
  · push Not at hle
    set d : L := c''⁻¹ with hd
    have hd0 : d ≠ 0 := inv_ne_zero hc''0
    have hμd : μ d < 1 := by rw [hd, map_inv₀]; exact inv_lt_one_of_one_lt₀ hle
    have hdA : d ∈ A := (hμA _).2 hμd.le
    have hC₁ : (algebraMap L F d)⁻¹ * h₁ ∈ C.integers := by rw [key₂]; exact hc₁g
    have e2 : (⟨_, hC₁⟩ : C.integers) = ⟨h₀, hc₁g⟩ := Subtype.ext key₂
    have hres₁ : C.residue ⟨_, hC₁⟩ ≠ 0 := by rw [e2]; exact hc₁res
    have hmod0' : ((An'.modulus : L)) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : An.param * An'.param = algebraMap L F (An'.modulus : L) := by
      rw [mul_comm, htwo, hmod]
    obtain ⟨-, hb', -⟩ := Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
      μ hμA An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide' h₁ hc₂g hc₂res d
      hd0 hdA hC₁ hres₁ hpole₁
    obtain ⟨-, hstrict⟩ := hb' R (hdom ▸ hR)
    have h1 : μ (R.evalAt hRrat h₁) < 1 := hstrict (Or.inl hμd)
    rw [hv₁] at h1
    have hglt : μ (R.evalAt hRrat g) < μ b := by
      have h2 : μ c₂ * (μ b)⁻¹ * μ (R.evalAt hRrat g) * (μ b * (μ c₂)⁻¹) < 1 * (μ b * (μ c₂)⁻¹) :=
        mul_lt_mul_of_pos_right h1 (mul_pos hμb0 (inv_pos.2 hμc₂0))
      have h3 :
          μ c₂ * (μ b)⁻¹ * μ (R.evalAt hRrat g) * (μ b * (μ c₂)⁻¹) = μ (R.evalAt hRrat g) := by
        field_simp
      rw [h3, one_mul] at h2
      calc μ (R.evalAt hRrat g) < μ b * (μ c₂)⁻¹ := h2
        _ ≤ μ b * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hμc₂) hμb0.le
        _ = μ b := mul_one _
    exact ⟨hglt.le.trans (le_max_right _ _), fun _ => hglt.trans_le (le_max_right _ _)⟩

end AlgebraicCurve
