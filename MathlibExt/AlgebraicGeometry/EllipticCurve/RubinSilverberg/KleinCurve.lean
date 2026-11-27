/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero.lean`
and
`P2M/Sol/S_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero.lean`
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
framework; the statement is reused here with that machinery removed and the
names restated in Mathlib style. The integrality and degree steps of the proof
are adapted from the source; its icosahedral-symmetry step is replaced by the
fifth-root-of-unity substitution and the coefficient comparison below.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The `3`-division polynomial of the Klein curve has no rational root

Let `K` be a field of characteristic zero containing a primitive fifth root of unity. Over
the rational function field `K(u)`, the `3`-division polynomial `Ψ₃` of `kleinCurve u` has no
root. Equivalently, `kleinCurve u` has no `K(u)`-rational `3`-torsion `x`-coordinate.

## Proof

Up to the factor `2304`, `Ψ₃(x) = 6912 x⁴ - 288 H x² + 32 T x - H²` with `H = H(u)`,
`T = T(u)`. This is monic up to a constant over `K[u]`, so a root in `K(u)` lies in `K[u]`
(as `K[u]` is integrally closed), and comparing degrees it has degree at most `10`. Since `H`
and `T` are polynomials in `u⁵`, the substitution `u ↦ ζ u` permutes the at most four roots
and has order `5`, so it fixes each root; hence a root is `a + b u⁵ + c u¹⁰`. Comparing the
coefficients of `u⁰`, `u⁵`, `u¹⁰`, `u¹⁵` gives four polynomial equations in `a`, `b`, `c`
which generate the unit ideal, a contradiction.
-/

@[expose] public section

open Polynomial

namespace RubinSilverberg

section rel

variable {R : Type*} [CommRing R]

/-- `2304 · Ψ₃(w)` of `kleinCurve`, written in terms of `H` and `T`. -/
private def rel (H T w : R) : R := 6912 * w ^ 4 - 288 * H * w ^ 2 + 32 * T * w - H ^ 2

private theorem map_rel {S F : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (H T w : R) : f (rel H T w) = rel (f H) (f T) (f w) := by
  simp [rel, map_ofNat]

private theorem kleinH_eq_of_pow_five_eq {u v : R} (h : u ^ 5 = v ^ 5) : kleinH u = kleinH v := by
  have e : ∀ x : R,
      kleinH x = (x ^ 5) ^ 4 - 228 * (x ^ 5) ^ 3 + 494 * (x ^ 5) ^ 2 + 228 * x ^ 5 + 1 :=
    fun x ↦ by unfold kleinH; ring
  rw [e, e, h]

private theorem kleinT_eq_of_pow_five_eq {u v : R} (h : u ^ 5 = v ^ 5) : kleinT u = kleinT v := by
  have e : ∀ x : R, kleinT x = (x ^ 5) ^ 6 + 522 * (x ^ 5) ^ 5 - 10005 * (x ^ 5) ^ 4
      - 10005 * (x ^ 5) ^ 2 - 522 * x ^ 5 + 1 :=
    fun x ↦ by unfold kleinT; ring
  rw [e, e, h]

end rel

private theorem psi3_eval_mul {F : Type*} [Field F] [CharZero F] (u x : F) :
    2304 * ((kleinCurve u).Ψ₃).eval x = rel (kleinH u) (kleinT u) x := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, kleinCurve, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  rw [rel]
  field_simp
  ring

section integrality

variable {K : Type*} [Field K]

private theorem algebraMap_kleinH_X :
    algebraMap K[X] (RatFunc K) (kleinH X) = kleinH (RatFunc.X : RatFunc K) := by
  rw [map_kleinH, RatFunc.algebraMap_X]

private theorem algebraMap_kleinT_X :
    algebraMap K[X] (RatFunc K) (kleinT X) = kleinT (RatFunc.X : RatFunc K) := by
  rw [map_kleinT, RatFunc.algebraMap_X]

/-- A root in `K(u)` of `rel H T` is a polynomial, since `K[u]` is integrally closed. -/
private theorem exists_poly_of_rel_eq_zero [CharZero K] (x : RatFunc K)
    (hx : rel (kleinH (RatFunc.X : RatFunc K)) (kleinT RatFunc.X) x = 0) :
    ∃ w : K[X], algebraMap K[X] (RatFunc K) w = x := by
  set q : (K[X])[X] := X ^ 4 + Polynomial.C (-(Polynomial.C (24 : K)⁻¹ * kleinH X)) * X ^ 2
      + Polynomial.C (Polynomial.C (216 : K)⁻¹ * kleinT X) * X
      + Polynomial.C (-(Polynomial.C (6912 : K)⁻¹ * kleinH X ^ 2)) with hq
  have hmonic : q.Monic := by
    rw [hq]; monicity!
  have hint : IsIntegral K[X] x := by
    refine ⟨q, hmonic, ?_⟩
    rw [← aeval_def, hq]
    have hC : ∀ c : K, algebraMap K[X] (RatFunc K) (Polynomial.C c) = algebraMap K (RatFunc K) c :=
      fun c ↦ by rw [RatFunc.algebraMap_C]; rfl
    simp only [map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C, algebraMap_kleinH_X,
      algebraMap_kleinT_X, hC, map_inv₀, map_ofNat]
    rw [rel] at hx
    field_simp
    linear_combination 5184 * hx
  exact (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (K := RatFunc K)).mp hint

private theorem natDegree_kleinH_X_le : (kleinH (X : K[X])).natDegree ≤ 20 := by
  unfold kleinH; compute_degree

private theorem natDegree_kleinT_X_le : (kleinT (X : K[X])).natDegree ≤ 30 := by
  unfold kleinT; compute_degree

private theorem kleinH_X_ne_zero : kleinH (X : K[X]) ≠ 0 := fun h ↦ by
  have h0 : (kleinH (X : K[X])).coeff 0 = 1 := by simp [kleinH]
  rw [h, coeff_zero] at h0
  exact zero_ne_one h0

private theorem natDegree_le_ten [CharZero K] (w : K[X]) (hw : rel (kleinH X) (kleinT X) w = 0) :
    w.natDegree ≤ 10 := by
  by_contra hd
  push Not at hd
  set d := w.natDegree with hd_def
  have heq : C (6912 : K) * w ^ 4 = 288 * kleinH X * w ^ 2 - 32 * kleinT X * w + kleinH X ^ 2 := by
    rw [rel] at hw
    rw [show (C (6912 : K) : K[X]) = 6912 from map_ofNat C 6912]
    linear_combination hw
  have hL : (C (6912 : K) * w ^ 4).natDegree = 4 * d := by
    rw [natDegree_C_mul (by norm_num), natDegree_pow, hd_def, mul_comm]
  have hH := natDegree_kleinH_X_le (K := K)
  have hT := natDegree_kleinT_X_le (K := K)
  have h288 : ((288 : K[X]) * kleinH X * w ^ 2).natDegree ≤ 20 + 2 * d := by
    calc ((288 : K[X]) * kleinH X * w ^ 2).natDegree
        ≤ ((288 : K[X]) * kleinH X).natDegree + (w ^ 2).natDegree := natDegree_mul_le
      _ ≤ ((288 : K[X]).natDegree + (kleinH X).natDegree) + (w ^ 2).natDegree := by
          gcongr; exact natDegree_mul_le
      _ ≤ (0 + 20) + 2 * d := by
          gcongr
          · simp
          · rw [natDegree_pow]
  have h32 : ((32 : K[X]) * kleinT X * w).natDegree ≤ 30 + d := by
    calc ((32 : K[X]) * kleinT X * w).natDegree
        ≤ ((32 : K[X]) * kleinT X).natDegree + w.natDegree := natDegree_mul_le
      _ ≤ ((32 : K[X]).natDegree + (kleinT X).natDegree) + w.natDegree := by
          gcongr; exact natDegree_mul_le
      _ ≤ (0 + 30) + d := by gcongr; simp
  have hH2 : (kleinH (X : K[X]) ^ 2).natDegree ≤ 40 := by
    rw [natDegree_pow]; omega
  have hR : (288 * kleinH X * w ^ 2 - 32 * kleinT X * w + kleinH X ^ 2 : K[X]).natDegree ≤
      max (max (20 + 2 * d) (30 + d)) 40 :=
    (natDegree_add_le _ _).trans
      (max_le_max ((natDegree_sub_le _ _).trans (max_le_max h288 h32)) hH2)
  rw [← heq, hL] at hR
  omega

end integrality

section symmetry

variable {K : Type*} [Field K]

/-- The quartic `6912 Y⁴ - 288 H Y² + 32 T Y - H²` over `K[u]`. -/
private noncomputable def quartic (H T : K[X]) : (K[X])[X] :=
  C 6912 * X ^ 4 - C (288 * H) * X ^ 2 + C (32 * T) * X - C (H ^ 2)

private theorem eval_quartic (H T w : K[X]) : (quartic H T).eval w = rel H T w := by
  simp only [quartic, rel, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]

private theorem quartic_ne_zero [CharZero K] (H T : K[X]) : quartic H T ≠ 0 := fun h ↦ by
  have h4 : (quartic H T).coeff 4 = 6912 := by
    simp only [quartic, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  rw [h, coeff_zero] at h4
  exact (by norm_num : (0 : K[X]) ≠ 6912) h4

private theorem natDegree_quartic_le (H T : K[X]) : (quartic H T).natDegree ≤ 4 := by
  unfold quartic; compute_degree

private theorem comp_C_mul_X_comp (w : K[X]) (a b : K) :
    (w.comp (C a * X)).comp (C b * X) = w.comp (C (a * b) * X) := by
  rw [comp_assoc, mul_comp, C_comp, X_comp, map_mul, mul_assoc]

private theorem iterate_comp (ζ : K) (w : K[X]) (n : ℕ) :
    (fun v : K[X] ↦ v.comp (C ζ * X))^[n] w = w.comp (C (ζ ^ n) * X) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, comp_C_mul_X_comp, pow_succ]

/-- The substitution `u ↦ ζ u` fixes each polynomial root of `rel H T`. -/
private theorem comp_eq_self [CharZero K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {w : K[X]}
    (hw : rel (kleinH X) (kleinT X) w = 0) : w.comp (C ζ * X) = w := by
  classical
  set f : K[X] → K[X] := fun v ↦ v.comp (C ζ * X) with hf
  have hit : ∀ (n : ℕ) (v : K[X]), f^[n] v = v.comp (C (ζ ^ n) * X) :=
    fun n v ↦ iterate_comp ζ v n
  have h5 : ∀ v, f^[5] v = v := fun v ↦ by rw [hit, hζ.pow_eq_one]; simp
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (g := f^[4]) fun v ↦ by
      rw [← Function.iterate_succ_apply, h5]
  have hpow : (C ζ * X : K[X]) ^ 5 = X ^ 5 := by
    rw [mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]
  have hH : (kleinH (X : K[X])).comp (C ζ * X) = kleinH X := by
    rw [← coe_compRingHom_apply, map_kleinH, coe_compRingHom_apply, X_comp,
      kleinH_eq_of_pow_five_eq hpow]
  have hT : (kleinT (X : K[X])).comp (C ζ * X) = kleinT X := by
    rw [← coe_compRingHom_apply, map_kleinT, coe_compRingHom_apply, X_comp,
      kleinT_eq_of_pow_five_eq hpow]
  have hrel : ∀ v, rel (kleinH X) (kleinT X) v = 0 → rel (kleinH X) (kleinT X) (f v) = 0 := by
    intro v hv
    have := congrArg (compRingHom (C ζ * X)) hv
    rw [map_rel, map_zero] at this
    simpa only [coe_compRingHom_apply, hH, hT] using this
  set RF : Finset K[X] := (quartic (kleinH X) (kleinT X)).roots.toFinset with hRF
  have mem_RF : ∀ v, v ∈ RF ↔ rel (kleinH X) (kleinT X) v = 0 := fun v ↦ by
    rw [hRF, Multiset.mem_toFinset, mem_roots (quartic_ne_zero _ _), IsRoot.def, eval_quartic]
  have hcardRF : RF.card ≤ 4 :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_quartic_le _ _))
  have hrelit : ∀ n : ℕ, rel (kleinH X) (kleinT X) (f^[n] w) = 0 := fun n ↦ by
    induction n with
    | zero => simpa using hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hrel _ ih
  have hmaps : ∀ i ∈ Finset.range 5, f^[i] w ∈ RF := fun i _ ↦ (mem_RF _).mpr (hrelit i)
  have hcard : RF.card < (Finset.range 5).card := by
    rw [Finset.card_range]; omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hper : ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ f^[k] w = w := by
    rw [Finset.mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, by omega, ?_⟩
      apply hinj.iterate i
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]; exact heq.symm
    · refine ⟨i - j, by omega, by omega, ?_⟩
      apply hinj.iterate j
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]; exact heq
  obtain ⟨k, hk1, hk4, hk⟩ := hper
  change f w = w
  interval_cases k
  · simpa using hk
  · have h4 : f^[4] w = w := by
      rw [show 4 = 2 + 2 from rfl, Function.iterate_add_apply, hk, hk]
    have : f^[5] w = f w := by
      rw [show 5 = 1 + 4 from rfl, Function.iterate_add_apply, h4]; rfl
    rw [← this, h5]
  · have h6 : f^[6] w = w := by
      rw [show 6 = 3 + 3 from rfl, Function.iterate_add_apply, hk, hk]
    have : f^[6] w = f w := by
      rw [show 6 = 1 + 5 from rfl, Function.iterate_add_apply, h5]; rfl
    rw [← this, h6]
  · have : f^[5] w = f w := by
      rw [show 5 = 1 + 4 from rfl, Function.iterate_add_apply, hk]; rfl
    rw [← this, h5]

/-- A polynomial root of `rel H T` has the shape `a + b u⁵ + c u¹⁰`. -/
private theorem shape [CharZero K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {w : K[X]}
    (hw : rel (kleinH X) (kleinT X) w = 0) :
    w = C (w.coeff 0) + C (w.coeff 5) * X ^ 5 + C (w.coeff 10) * X ^ 10 := by
  have hdeg := natDegree_le_ten w hw
  have hz : ∀ i, ¬ 5 ∣ i → w.coeff i = 0 := fun i hi ↦ by
    have h := congrArg (fun p : K[X] ↦ p.coeff i) (comp_eq_self hζ hw)
    simp only [comp_C_mul_X_coeff] at h
    have hne : ζ ^ i ≠ 1 := fun h1 ↦ hi ((hζ.pow_eq_one_iff_dvd i).mp h1)
    have : w.coeff i * (ζ ^ i - 1) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  ext n
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge 10 n with hn | hn
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hn)]
    simp [show n ≠ 0 by omega, show n ≠ 5 by omega, show n ≠ 10 by omega]
  · interval_cases n <;> simp [hz]

end symmetry

section coefficients

variable {K : Type*} [Field K]

/-- The expansion of `rel H T (a + b u⁵ + c u¹⁰)` in powers of `u⁵`. -/
private theorem rel_shape (a b c : K) :
    rel (kleinH X) (kleinT X) (C a + C b * X ^ 5 + C c * X ^ 10) =
      C (6912 * a ^ 4 - 288 * a ^ 2 + 32 * a - 1)
      + C (27648 * a ^ 3 * b - 65664 * a ^ 2 - 576 * a * b - 16704 * a + 32 * b - 456) * X ^ 5
      + C (27648 * a ^ 3 * c + 41472 * a ^ 2 * b ^ 2 - 142272 * a ^ 2 - 131328 * a * b
          - 576 * a * c - 320160 * a - 288 * b ^ 2 - 16704 * b + 32 * c - 52972) * X ^ 10
      + C (82944 * a ^ 2 * b * c + 65664 * a ^ 2 + 27648 * a * b ^ 3 - 284544 * a * b
          - 131328 * a * c - 65664 * b ^ 2 - 576 * b * c - 320160 * b - 16704 * c
          - 224808) * X ^ 15
      + C (41472 * a ^ 2 * c ^ 2 - 288 * a ^ 2 + 82944 * a * b ^ 2 * c + 131328 * a * b
          - 284544 * a * c - 320160 * a + 6912 * b ^ 4 - 142272 * b ^ 2 - 131328 * b * c
          - 288 * c ^ 2 - 320160 * c - 140070) * X ^ 20
      + C (82944 * a * b * c ^ 2 - 576 * a * b + 131328 * a * c + 16704 * a
          + 27648 * b ^ 3 * c + 65664 * b ^ 2 - 284544 * b * c - 320160 * b - 65664 * c ^ 2
          + 224808) * X ^ 25
      + C (27648 * a * c ^ 3 - 576 * a * c + 32 * a + 41472 * b ^ 2 * c ^ 2 - 288 * b ^ 2
          + 131328 * b * c + 16704 * b - 142272 * c ^ 2 - 320160 * c - 52972) * X ^ 30
      + C (27648 * b * c ^ 3 - 576 * b * c + 32 * b + 65664 * c ^ 2 + 16704 * c + 456) * X ^ 35
      + C (6912 * c ^ 4 - 288 * c ^ 2 + 32 * c - 1) * X ^ 40 := by
  simp only [rel, kleinH, kleinT, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

/-- The coefficients of `u⁰`, `u⁵`, `u¹⁰`, `u¹⁵` of `rel H T (a + b u⁵ + c u¹⁰)` cannot all
vanish: the four polynomials generate the unit ideal of `ℚ[a, b, c]`. -/
private theorem rel_shape_ne_zero [CharZero K] (a b c : K) :
    rel (kleinH X) (kleinT X) (C a + C b * X ^ 5 + C c * X ^ 10) ≠ 0 := by
  intro h
  rw [rel_shape] at h
  have e : ∀ n, (0 : K[X]).coeff n = 0 := fun _ ↦ coeff_zero _
  have h0 := e 0
  have h1 := e 5
  have h2 := e 10
  have h3 := e 15
  rw [← h] at h0 h1 h2 h3
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have : (3538944 : K) = 0 := by
    linear_combination
      (174885120 * a ^ 2 * b + 97360128 * a ^ 2 * c - 131241600 * a * b ^ 2
        + 1410048 * a * b * c - 558213312 * a * b + 53753280 * a * c - 916351152 * a
        + 2177280 * b ^ 3 + 10901664 * b ^ 2 - 13824 * b * c - 26203072 * b + 3294368 * c
        - 183728332) * h0
      + (-43721280 * a ^ 3 + 69320448 * a ^ 2 * b - 632448 * a ^ 2 * c + 139553328 * a ^ 2
        - 964224 * a * b ^ 2 + 17432064 * a * b + 105408 * a * c + 57923044 * a
        + 80352 * b ^ 2 + 1591056 * b - 4392 * c + 4509325) * h1
      + (-24340032 * a ^ 3 + 279936 * a ^ 2 * b - 13438320 * a ^ 2 - 39744 * a * b
        - 1818572 * a + 1368 * b - 34805) * h2
      + (-20736 * a ^ 2 + 3456 * a - 144) * h3
  norm_num at this

end coefficients

/-- Over `K(u)`, with `K` of characteristic zero containing a primitive fifth root of unity,
the `3`-division polynomial of `kleinCurve u` has no root. -/
theorem kleinCurve_Psi3_eval_ne_zero {K : Type*} [Field K] [CharZero K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) (x : RatFunc K) :
    ((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by
  intro hx0
  have hx : rel (kleinH (RatFunc.X : RatFunc K)) (kleinT RatFunc.X) x = 0 := by
    rw [← psi3_eval_mul, hx0, mul_zero]
  obtain ⟨w, rfl⟩ := exists_poly_of_rel_eq_zero x hx
  have hwP : rel (kleinH X) (kleinT X) w = 0 := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    rw [map_rel, algebraMap_kleinH_X, algebraMap_kleinT_X, hx, map_zero]
  rw [shape hζ hwP] at hwP
  exact rel_shape_ne_zero _ _ _ hwP

end RubinSilverberg
