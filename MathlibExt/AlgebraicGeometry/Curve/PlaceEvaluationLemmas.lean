/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files of the FLT project
(https://github.com/anthropics/fermats-last-theorem):
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`;
`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`;
`Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`;
`Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean`;
`Theorems/Thm_AlgebraicCurve_N.lean` and `P2M/Sol/S_AlgebraicCurve_N.lean`
for each `N` in:
`Divisor_evalFun_add`;
`Place_evalAt_ne_zero`;
`Place_isRational_iff_deg_eq_one`;
`Place_evalAt_mul`;
`Divisor_evalFun_mul`;
`Place_eq_ord_of_addHom_of_nonneg_iff`;
`Divisor_evalFun_single_sub_single`;
`Place_evalAt_inv`;
`Place_evalAt_zpow`;
`Divisor_evalFun_zpow_left`;
`Divisor_evalFun_zsmul`;
`Place_adicValuation_isRankOneDiscrete`;
`Place_adicValuation_isTrivialOn`;
`Place_evalAt_algebraMap`;
`Place_evalAt_congr`;
`Place_ord_algebraMap`;
`Place_ord_eq_neg_log_of_valuationSubring_eq`;
`Theorems/Thm_N.lean` and `P2M/Sol/S_N.lean` for each `N` in:
`Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap`;
`Algebra_norm_of_subsingleton`;
`Algebra_norm_prod`.
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

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation
public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationOrd
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

/-!
# Rules for evaluation at rational places

`AlgebraicCurve.Place.evalAt` and `CurveDivisor.evalFun` (in `Curve/PlaceEvaluation`) evaluate a
function of a function field `F / K` at a rational place and on a divisor supported on rational
places. This file proves how these evaluations interact with products, inverses and powers of
functions, and with sums and multiples of divisors (constants are in
`Curve/PlaceEvaluationOrd`).

## Main results

* `AlgebraicCurve.Place.evalAt_ne_zero`, `AlgebraicCurve.Place.evalAt_inv`,
  `AlgebraicCurve.Place.evalAt_zpow`: at a rational place where a nonzero `f` has order zero, the
  value of `f` is nonzero and evaluation commutes with inverses and integer powers.
* `AlgebraicCurve.Place.evalAt_congr`: two functions whose difference vanishes at the place have
  the same value.
* `CurveDivisor.evalFun_add`, `CurveDivisor.evalFun_mul`, `CurveDivisor.evalFun_zpow_left`,
  `CurveDivisor.evalFun_zsmul`, `CurveDivisor.evalFun_single_sub_single`: evaluation on sums and
  multiples of divisors, and of products and powers of functions.
* `AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff`: a map `F → ℤ` that sends products of
  nonzero elements to sums, takes the value `1` at a nonzero element, and is nonnegative at a
  nonzero `x` exactly when `x` lies in the valuation ring of a place agrees with the order
  function of that place on nonzero elements.
* `Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap`: if `a - μ` is nilpotent in a free
  finite algebra `A` over a domain `R`, the norm of `a` is `μ ^ [A : R]`.
-/

@[expose] public section

noncomputable section

open IsLocalRing WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt hv f ≠ 0 := by
  have hmem : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg hf h.ge
  have hunit : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [h, zpow_zero, mul_one] at hu
    have huf : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [huf]
    exact u.isUnit
  have hres : residue v.toValuationSubring (⟨f, hmem⟩ : v.toValuationSubring) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr hunit
  intro h0
  have key := v.algebraMap_evalAt hv hmem
  rw [h0, map_zero] at key
  exact hres key.symm

theorem evalAt_inv (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt hv f⁻¹ = (v.evalAt hv f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul hv (v.mem_of_ord_nonneg hf h.ge) (v.mem_of_ord_nonneg hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one hv] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem evalAt_zpow (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) :
    v.evalAt hv (f ^ n) = v.evalAt hv f ^ n := by
  have hpow : ∀ m : ℕ, v.evalAt hv (f ^ m) = v.evalAt hv f ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hm : v.ord (f ^ (m : ℤ)) = 0 := by rw [v.ord_zpow, h, mul_zero]
      rw [pow_succ, v.evalAt_mul hv ?_ (v.mem_of_ord_nonneg hf h.ge), ih, pow_succ]
      have : (f ^ m : F) = f ^ (m : ℤ) := by rw [zpow_natCast]
      rw [this]
      exact v.mem_of_ord_nonneg (zpow_ne_zero _ hf) hm.ge
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine v.evalAt_inv hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

theorem evalAt_congr (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) (h : f - g = 0 ∨ 0 < v.ord (f - g)) :
    v.evalAt hv f = v.evalAt hv g := by
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h]
  have hsub : f - g ∈ v.toValuationSubring := sub_mem hf hg
  have hmax : ∀ {x : F} (hx : x ∈ v.toValuationSubring), 0 < v.ord x →
      (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    intro x hx hpos
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    rw [v.mem_maximalIdeal_iff_adicValuation_lt_one]
    have hne : v.adicValuation x ≠ 0 := v.adicValuation_ne_zero hx0
    rw [← exp_log hne, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
    have : v.ord x = -log (v.adicValuation x) := rfl
    omega
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ = ⟨f - g, hsub⟩ := rfl
    rw [this]
    exact hmax hsub h
  have hres : residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring)
      = residue v.toValuationSubring (⟨g, hg⟩ : v.toValuationSubring) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [v.evalAt_of_mem hv hf, v.evalAt_of_mem hv hg, hres]

theorem eq_ord_of_addHom_of_nonneg_iff (w : Place K F) (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y) (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring)) {x : F} (hx : x ≠ 0) :
    φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone
  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega
  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring
  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega
  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega
  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel
  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Place

end AlgebraicCurve

namespace CurveDivisor

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalFun_eq_prod (f : F) (D : Divisor K F) (hD : ∀ v ∈ D.support, v.IsRational)
    (ev : Place K F → K) (hev : ∀ v (hv : v.IsRational), v ∈ D.support → v.evalAt hv f = ev v) :
    evalFun f D hD = D.prod fun v n => ev v ^ n := by
  rw [evalFun_def, Finsupp.prod, ← Finset.prod_attach D.support]
  exact Finset.prod_congr rfl fun v _ => by rw [hev v (hD v v.2) v.2]

theorem evalFun_add (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, v.IsRational)
    (hE : ∀ v ∈ E.support, v.IsRational) (hDE : ∀ v ∈ (D + E).support, v.IsRational)
    (hD0 : ∀ v (hv : v.IsRational), v ∈ D.support → v.evalAt hv f ≠ 0)
    (hE0 : ∀ v (hv : v.IsRational), v ∈ E.support → v.evalAt hv f ≠ 0) :
    evalFun f (D + E) hDE = evalFun f D hD * evalFun f E hE := by
  classical
  have hev : ∀ (D : Divisor K F) v (hv : v.IsRational), v ∈ D.support →
      v.evalAt hv f = if h : v.IsRational then v.evalAt h f else 0 :=
    fun _ v hv _ => by rw [dite_eq_left hv]
  rw [evalFun_eq_prod f _ hDE _ (hev _), evalFun_eq_prod f D hD _ (hev D),
    evalFun_eq_prod f E hE _ (hev E)]
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => zpow_add₀ ?_ b₁ b₂)
  rcases Finset.mem_union.mp hv with h | h
  · rw [dite_eq_left (hD v h)]
    exact hD0 v _ h
  · rw [dite_eq_left (hE v h)]
    exact hE0 v _ h

theorem evalFun_mul {f g : F} {D : Divisor K F} (hD : ∀ v ∈ D.support, v.IsRational)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) :
    evalFun (f * g) D hD = evalFun f D hD * evalFun g D hD := by
  simp only [evalFun_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Place.evalAt_mul _ (hD v v.2) (hf v v.2) (hg v v.2), mul_zpow]

theorem evalFun_single_sub_single (f : F) {v₁ v₂ : Place K F} (hv₁ : v₁.IsRational)
    (hv₂ : v₂.IsRational) (h₁ : v₁.evalAt hv₁ f ≠ 0) (h₂ : v₂.evalAt hv₂ f ≠ 0)
    (hD : ∀ v ∈ (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1) : Divisor K F).support,
      v.IsRational) :
    evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) hD
      = v₁.evalAt hv₁ f / v₂.evalAt hv₂ f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ) (v : Place K F),
      v ∈ (Finsupp.single w n).support → v = w := fun w n v hv =>
    Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
  have hr : ∀ (w : Place K F) (hw : w.IsRational) (n : ℤ),
      ∀ v ∈ (Finsupp.single w n : Divisor K F).support, v.IsRational := fun w hw n v hv =>
    hsupp w n v hv ▸ hw
  rw [evalFun_add f (hr v₁ hv₁ 1) (hr v₂ hv₂ (-1)) hD
      (fun v _ hv => by obtain rfl := hsupp _ _ v hv; exact h₁)
      (fun v _ hv => by obtain rfl := hsupp _ _ v hv; exact h₂),
    evalFun_single f v₁ hv₁, evalFun_single f v₂ hv₂, zpow_one, zpow_neg_one, div_eq_mul_inv]

theorem evalFun_zpow_left {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ)
    (hD : ∀ v ∈ D.support, v.IsRational) (hord : ∀ v ∈ D.support, v.ord f = 0) :
    evalFun (f ^ n) D hD = evalFun f D hD ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Place.evalAt_zpow _ (hD v v.2) hf (hord v v.2) n, ← zpow_mul, ← zpow_mul, mul_comm]

theorem evalFun_zsmul (f : F) (D : Divisor K F) (n : ℤ) (hD : ∀ v ∈ D.support, v.IsRational)
    (hnD : ∀ v ∈ (n • D).support, v.IsRational) :
    evalFun f (n • D) hnD = evalFun f D hD ^ n := by
  classical
  have hev : ∀ (D : Divisor K F) v (hv : v.IsRational), v ∈ D.support →
      v.evalAt hv f = if h : v.IsRational then v.evalAt h f else 0 :=
    fun _ v hv _ => by rw [dite_eq_left hv]
  rw [evalFun_eq_prod f _ hnD _ (hev _), evalFun_eq_prod f D hD _ (hev D),
    Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    Finsupp.prod, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

end CurveDivisor

theorem Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R]
    [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R}
    (h : IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]
