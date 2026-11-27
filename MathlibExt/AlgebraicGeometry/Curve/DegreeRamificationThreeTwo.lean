/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two.lean`,
`P2M/Sol/S_AlgebraicCurve_six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.lean`
and
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean`
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

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOverOfTranscendental
import Mathlib.Tactic.LinearCombination
import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentity
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd

/-!
# Degrees of divisors over `K(y)` with ramification orders three and two

Let `F / K` be a field extension and `y : F` transcendental over `K` with `F` finite and
separable over `K(y)`.

* The pole divisor of `y`, with coefficient `max 0 (-ord_v y)` at each place `v`, has degree
  `[F : K(y)]`. It is the pullback of the place at infinity of `K(y)`, so this is the fundamental
  identity.
* If `K` is algebraically closed, every zero of `y` has order `3` and every zero of `y - 1728`
  has order `2`, then for every nonnegative integer `m` the divisor `D` with coefficient
  `⌊2 m ord_v y / 3⌋` at the zeros of `y`, `⌊m ord_v (y - 1728) / 2⌋` at the zeros of `y - 1728`,
  `m ord_v y` at the poles of `y` and `0` elsewhere satisfies `6 deg D = m [F : K(y)]`.

## Main statements

* `AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord_of_isSeparable`
* `AlgebraicCurve.six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two`
-/

@[expose] public section

noncomputable section

open IntermediateField

namespace AlgebraicCurve

section Ord

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem ord_pos_iff {f : F} (hf : f ≠ 0) : 0 < w.ord f ↔ w.adicValuation f < 1 := by
  rw [Place.ord, neg_pos, ← WithZero.log_one,
    WithZero.log_lt_log (w.adicValuation_ne_zero hf) one_ne_zero]

private theorem ord_neg_iff {f : F} (hf : f ≠ 0) : w.ord f < 0 ↔ 1 < w.adicValuation f := by
  rw [Place.ord, neg_lt_zero, ← WithZero.log_one,
    WithZero.log_lt_log one_ne_zero (w.adicValuation_ne_zero hf)]

private theorem adicValuation_algebraMap {c : K} (hc : c ≠ 0) :
    w.adicValuation (algebraMap K F c) = 1 := by
  apply le_antisymm (w.adicValuation_algebraMap_le_one c)
  have h1 : w.adicValuation (algebraMap K F c) * w.adicValuation (algebraMap K F c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  have h2 := w.adicValuation_algebraMap_le_one c⁻¹
  by_contra h
  rw [not_le] at h
  have : w.adicValuation (algebraMap K F c) * w.adicValuation (algebraMap K F c⁻¹) < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h h2 zero_le zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

private theorem ord_sub_algebraMap_eq_zero_of_ord_pos {t : F} (ht : t ≠ 0) {c : K} (hc : c ≠ 0)
    (h : 0 < w.ord t) : w.ord (t - algebraMap K F c) = 0 := by
  have hv : w.adicValuation t < w.adicValuation (algebraMap K F c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w ht).1 h
  rw [Place.ord, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hv,
    adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

private theorem ord_sub_algebraMap_eq_of_ord_neg {t : F} (ht : t ≠ 0) (c : K)
    (h : w.ord t < 0) : w.ord (t - algebraMap K F c) = w.ord t := by
  have hv : w.adicValuation (algebraMap K F c) < w.adicValuation t :=
    lt_of_le_of_lt (w.adicValuation_algebraMap_le_one c) ((ord_neg_iff w ht).1 h)
  rw [Place.ord, Place.ord, Valuation.map_sub_eq_of_lt_left _ hv]

private theorem ord_eq_zero_of_ord_sub_algebraMap_pos {t : F} {c : K} (hc : c ≠ 0)
    (htc : t - algebraMap K F c ≠ 0) (h : 0 < w.ord (t - algebraMap K F c)) : w.ord t = 0 := by
  have hv : w.adicValuation (t - algebraMap K F c) < w.adicValuation (algebraMap K F c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w htc).1 h
  have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
  rw [Place.ord, this, Valuation.map_add_eq_of_lt_right _ hv, adicValuation_algebraMap w hc,
    WithZero.log_one, neg_zero]

private theorem ord_eq_of_ord_sub_algebraMap_neg {t : F} (c : K) (htc : t - algebraMap K F c ≠ 0)
    (h : w.ord (t - algebraMap K F c) < 0) : w.ord t = w.ord (t - algebraMap K F c) := by
  have := ord_sub_algebraMap_eq_of_ord_neg w htc (-c) h
  rwa [map_neg, sub_neg_eq_add, sub_add_cancel] at this

end Ord

section PoleDivisor

open RationalFunctionField

private theorem ord_placeInfty_X (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  rw [ord_placeInfty (K := K) RatFunc.X_ne_zero, RatFunc.intDegree_X]

private theorem ord_X_nonneg_of_ne_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, rfl⟩ | hw
  · rw [← RatFunc.algebraMap_X]
    exact Place.ord_nonneg_of_mem _ (algebraMap_mem_ofHeightOneSpectrum K w Polynomial.X)
  · exact absurd hw hu

/-- Over a finite separable extension `F` of `RatFunc K`, the pole divisor of `X` is the pullback
of the place at infinity, so its degree is `[F : RatFunc K]`. -/
private theorem degree_eq_finrank_ratFunc {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [HasPrincipalDivisors K F] (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = max 0 (-v.ord (algebraMap (RatFunc K) F RatFunc.X))) :
    Divisor.degree D = (Module.finrank (RatFunc K) F : ℤ) := by
  classical
  have : SumRamificationInertia K (RatFunc K) F :=
    ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩
  have hDe : D = Divisor.pullback F (Finsupp.single (placeInfty K) 1) := by
    ext w
    have he : (1 : ℤ) ≤ w.ramificationIndex (RatFunc K) := by
      exact_mod_cast w.ramificationIndex_pos (F := RatFunc K)
    rw [hD, Divisor.pullback_apply, Place.ord_restrict, Finsupp.single_apply]
    split_ifs with h
    · rw [← h, ord_placeInfty_X, mul_neg_one, neg_neg, mul_one]
      exact max_eq_right (by omega)
    · have := ord_X_nonneg_of_ne_placeInfty (Ne.symm h)
      have : 0 ≤ (w.ramificationIndex (RatFunc K) : ℤ) * (w.restrict (RatFunc K)).ord RatFunc.X :=
        mul_nonneg (by omega) this
      rw [mul_zero]
      exact max_eq_left (by omega)
  rw [hDe, Divisor.degree_pullback, Divisor.degree_single, deg_placeInfty]
  push_cast
  ring

-- The upstream theorem `AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord` assumes
-- `[IsCurveOver K F]` and a finite-dimensional `LSpace 0` instead of separability; neither
-- statement implies the other, so this one records its separability hypothesis in its name.
/-- **Degree of the pole divisor of a separating element.** If `x : F` is transcendental over `K`
and `F` is finite and separable over `K(x)`, then the pole divisor of `x` has degree
`[F : K(x)]`. -/
theorem Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord_of_isSeparable {K F : Type*} [Field K]
    [Field F] [Algebra K F] {x : F} (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ F]
    [Algebra.IsSeparable K⟮x⟯ F] (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank K⟮x⟯ F : ℤ) := by
  have : IsCurveOver K F := isCurveOver_of_transcendental hx inferInstance inferInstance
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have hX : algebraMap (RatFunc K) F RatFunc.X = x := by
    change ((RatFunc.algEquivOfTranscendental x hx RatFunc.X : K⟮x⟯) : F) = x
    rw [RatFunc.algEquivOfTranscendental_X]
  have hrank : Module.finrank K⟮x⟯ F = Module.finrank (RatFunc K) F :=
    Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  rw [hrank]
  exact degree_eq_finrank_ratFunc D fun v => by rw [hX]; exact hD v

end PoleDivisor

/-- **Degrees of divisors with ramification orders three and two.** Let `k` be algebraically
closed and `y : F` transcendental over `k` with `F` finite and separable over `k(y)`, such that
every zero of `y` has order `3` and every zero of `y - 1728` has order `2`. Let `m` be a
nonnegative integer. If `D` has coefficient `⌊2 m ord_w y / 3⌋` at the zeros of `y`,
`⌊m ord_w (y - 1728) / 2⌋` at the zeros of `y - 1728`, `m ord_w y` at the poles of `y` and `0` at
every other place, then `6 deg D = m [F : k(y)]`. -/
theorem six_mul_degree_eq_mul_finrank_of_forall_eq_weightFloor_of_ord_eq_three_two
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (y : F) (hy : Transcendental k y)
    (hfin : FiniteDimensional k⟮y⟯ F) (hsep : Algebra.IsSeparable k⟮y⟯ F)
    (h0 : ∀ w : Place k F, 0 < w.ord y → w.ord y = 3)
    (h1728 : ∀ w : Place k F, 0 < w.ord (y - 1728) → w.ord (y - 1728) = 2)
    (m : ℕ) (D : Divisor k F)
    (hD : ∀ w : Place k F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)) :
    6 * D.degree = (m : ℤ) * (Module.finrank k⟮y⟯ F : ℤ) := by
  classical
  have : IsCurveOver k F := isCurveOver_of_transcendental hy hfin hsep
  have hdeg1 : ∀ v : Place k F, v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  set n : ℤ := (Module.finrank k⟮y⟯ F : ℤ) with hn
  have hc : (1728 : F) = algebraMap k F 1728 := (map_ofNat (algebraMap k F) 1728).symm
  have hD' : ∀ w : Place k F, D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
      + (if 0 < w.ord (y - algebraMap k F 1728) then
          ((m : ℤ) * w.ord (y - algebraMap k F 1728)) / 2 else 0)
      + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := fun w => by rw [← hc]; exact hD w
  have h1728' : ∀ w : Place k F, 0 < w.ord (y - algebraMap k F 1728) →
      w.ord (y - algebraMap k F 1728) = 2 := fun w => by rw [← hc]; exact h1728 w
  have hy0 : y ≠ 0 := fun h => hy (h ▸ isAlgebraic_zero)
  have hyc : y - algebraMap k F 1728 ≠ 0 := fun h => hy (by
    rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap (1728 : k))
  obtain ⟨Dj, hDj, hDj0⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := F) y hy0
  obtain ⟨Dc, hDc, hDc0⟩ :=
    HasPrincipalDivisors.exists_divisor (K := k) (F := F) (y - algebraMap k F 1728) hyc
  set S0 := Dj.support.filter (fun v => 0 < v.ord y) with hS0def
  set S1 := Dc.support.filter (fun v => 0 < v.ord (y - algebraMap k F 1728)) with hS1def
  set T := Dj.support.filter (fun v => v.ord y < 0) with hTdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord y := fun v => by
    rw [hS0def, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_gt h, h⟩⟩
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (y - algebraMap k F 1728) := fun v => by
    rw [hS1def, Finset.mem_filter, Finsupp.mem_support_iff, hDc v]
    exact ⟨And.right, fun h => ⟨ne_of_gt h, h⟩⟩
  have hT : ∀ v, v ∈ T ↔ v.ord y < 0 := fun v => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_lt h, h⟩⟩
  let P : Divisor k F := ∑ v ∈ T, Finsupp.single v (-(v.ord y))
  have hP : ∀ v : Place k F, P v = max 0 (-v.ord y) := by
    intro v
    simp only [P, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' T v]
    by_cases hv : v ∈ T
    · rw [ite_eq_left hv, max_eq_right]; have := (hT v).1 hv; omega
    · rw [ite_eq_right hv, max_eq_left]; have := (hT v).not.1 hv; omega
  have hPdeg := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord_of_isSeparable hy P hP
  have hPdeg' : Divisor.degree P = ∑ v ∈ T, -(v.ord y) := by
    simp only [P, map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
  have hTsum : ∑ v ∈ T, v.ord y = -n := by
    have : ∑ v ∈ T, -(v.ord y) = n := hPdeg'.symm.trans hPdeg
    rw [Finset.sum_neg_distrib] at this
    linarith
  have hdegsum : ∀ E : Divisor k F, Divisor.degree E = ∑ v ∈ E.support, E v := by
    intro E
    conv_lhs => rw [← Finsupp.sum_single E]
    rw [Finsupp.sum, map_sum]
    simp only [Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
  have hsupp_j : Dj.support = S0 ∪ T := by
    ext v
    rw [Finset.mem_union, hS0, hT, Finsupp.mem_support_iff, hDj v]
    constructor
    · intro h; rcases lt_trichotomy (v.ord y) 0 with h' | h' | h'
      · exact Or.inr h'
      · exact absurd h' h
      · exact Or.inl h'
    · rintro (h | h) <;> omega
  have hdisj_0T : Disjoint S0 T := by
    rw [Finset.disjoint_left]; intro v h0' hT'
    have := (hS0 v).1 h0'; have := (hT v).1 hT'; omega
  have hS0sum : ∑ v ∈ S0, v.ord y = n := by
    have h := hdegsum Dj
    rw [hDj0, hsupp_j, Finset.sum_union hdisj_0T] at h
    simp only [hDj] at h
    linarith
  have hnpos : 0 < n := by
    have : 0 < Module.finrank k⟮y⟯ F := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  by_cases hk : (1728 : k) = 0
  · exfalso
    have hS0ne : S0.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty] at hS0sum
      linarith
    obtain ⟨v, hv⟩ := hS0ne
    have hv3 := h0 v ((hS0 v).1 hv)
    have hyy : y - algebraMap k F 1728 = y := by rw [hk, map_zero, sub_zero]
    have hv2 := h1728' v (by rw [hyy]; exact (hS0 v).1 hv)
    rw [hyy] at hv2
    omega
  have hzero_c : ∀ v : Place k F, 0 < v.ord y → v.ord (y - algebraMap k F 1728) = 0 :=
    fun v hv => ord_sub_algebraMap_eq_zero_of_ord_pos v hy0 hk hv
  have hpole_c : ∀ v : Place k F, v.ord y < 0 → v.ord (y - algebraMap k F 1728) = v.ord y :=
    fun v hv => ord_sub_algebraMap_eq_of_ord_neg v hy0 1728 hv
  have hzero_j : ∀ v : Place k F, 0 < v.ord (y - algebraMap k F 1728) → v.ord y = 0 :=
    fun v hv => ord_eq_zero_of_ord_sub_algebraMap_pos v hk hyc hv
  have hpole_j : ∀ v : Place k F, v.ord (y - algebraMap k F 1728) < 0 →
      v.ord y = v.ord (y - algebraMap k F 1728) :=
    fun v hv => ord_eq_of_ord_sub_algebraMap_neg v 1728 hyc hv
  have hsupp_c : Dc.support = S1 ∪ T := by
    ext v
    rw [Finset.mem_union, hS1, hT, Finsupp.mem_support_iff, hDc v]
    constructor
    · intro h; rcases lt_trichotomy (v.ord (y - algebraMap k F 1728)) 0 with h' | h' | h'
      · right; rw [hpole_j v h']; exact h'
      · exact absurd h' h
      · exact Or.inl h'
    · rintro (h | h)
      · exact ne_of_gt h
      · rw [hpole_c v h]; exact ne_of_lt h
  have hdisj_1T : Disjoint S1 T := by
    rw [Finset.disjoint_left]; intro v h1 hT'
    have := (hS1 v).1 h1; have := hzero_j v this; have := (hT v).1 hT'; omega
  have hS1sum : ∑ v ∈ S1, v.ord (y - algebraMap k F 1728) = n := by
    have h := hdegsum Dc
    rw [hDc0, hsupp_c, Finset.sum_union hdisj_1T] at h
    simp only [hDc] at h
    have : ∑ v ∈ T, v.ord (y - algebraMap k F 1728) = ∑ v ∈ T, v.ord y :=
      Finset.sum_congr rfl fun v hv => hpole_c v ((hT v).1 hv)
    linarith
  have hcnt0 : 3 * (S0.card : ℤ) = n := by
    rw [← hS0sum, show ∑ v ∈ S0, v.ord y = ∑ v ∈ S0, (3 : ℤ) from
      Finset.sum_congr rfl fun v hv => h0 v ((hS0 v).1 hv)]
    simp only [Finset.sum_const]; ring
  have hcnt1 : 2 * (S1.card : ℤ) = n := by
    rw [← hS1sum, show ∑ v ∈ S1, v.ord (y - algebraMap k F 1728) = ∑ v ∈ S1, (2 : ℤ) from
      Finset.sum_congr rfl fun v hv => h1728' v ((hS1 v).1 hv)]
    simp only [Finset.sum_const]; ring
  have hDval : ∀ v : Place k F, D v =
      (if v ∈ S0 then 2 * (m : ℤ) else 0) + (if v ∈ S1 then (m : ℤ) else 0) +
        (if v ∈ T then (m : ℤ) * v.ord y else 0) := by
    intro v
    rw [hD' v]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · by_cases h : 0 < v.ord y
      · rw [ite_eq_left h, ite_eq_left ((hS0 v).2 h), h0 v h]; omega
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hS0 v).1 h'))]
    · by_cases h : 0 < v.ord (y - algebraMap k F 1728)
      · rw [ite_eq_left h, ite_eq_left ((hS1 v).2 h), h1728' v h]; omega
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hS1 v).1 h'))]
    · by_cases h : v.ord y < 0
      · rw [ite_eq_left h, ite_eq_left ((hT v).2 h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hT v).1 h'))]
  have hDsupp : D.support ⊆ S0 ∪ S1 ∪ T := by
    intro v hv
    rw [Finsupp.mem_support_iff, hDval v] at hv
    rw [Finset.mem_union, Finset.mem_union]
    by_contra hnot
    simp only [not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hv
    exact hv (by ring)
  have hDdeg : Divisor.degree D = ∑ v ∈ S0 ∪ S1 ∪ T, D v := by
    rw [hdegsum D]
    exact Finset.sum_subset hDsupp (fun v _ hv => by rwa [Finsupp.mem_support_iff, not_not] at hv)
  have hsumD : ∑ v ∈ S0 ∪ S1 ∪ T, D v =
      ∑ v ∈ S0 ∪ S1 ∪ T, ((if v ∈ S0 then 2 * (m : ℤ) else 0) + (if v ∈ S1 then (m : ℤ) else 0) +
        (if v ∈ T then (m : ℤ) * v.ord y else 0)) := Finset.sum_congr rfl fun v _ => hDval v
  have hA : ∑ v ∈ S0 ∪ S1 ∪ T, (if v ∈ S0 then 2 * (m : ℤ) else 0) = 2 * (m : ℤ) * S0.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (by intro v hv; simp [hv]), Finset.sum_const]
    simp only [nsmul_eq_mul]; ring
  have hB : ∑ v ∈ S0 ∪ S1 ∪ T, (if v ∈ S1 then (m : ℤ) else 0) = (m : ℤ) * S1.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (by intro v hv; simp [hv]), Finset.sum_const]
    simp only [nsmul_eq_mul]; ring
  have hC : ∑ v ∈ S0 ∪ S1 ∪ T, (if v ∈ T then (m : ℤ) * v.ord y else 0) =
      (m : ℤ) * ∑ v ∈ T, v.ord y := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (by intro v hv; simp [hv]), Finset.mul_sum]
  rw [hDdeg, hsumD, Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC, hTsum]
  linear_combination (4 * (m : ℤ)) * hcnt0 + (3 * (m : ℤ)) * hcnt1

end AlgebraicCurve
