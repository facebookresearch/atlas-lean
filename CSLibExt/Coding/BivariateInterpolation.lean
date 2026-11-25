/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.GuruswamiSudan
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Sqrt
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# Bivariate interpolation: closed-form degree choices

This module turns the Guruswami-Sudan interpolation step
`Cslib.CodingTheory.GuruswamiSudan.exists_interpolant` into corollaries
with explicit degree bounds. Given `n` points `(αᵢ, yᵢ)` over a field
and a degree bound `k`, it produces a nonzero bivariate interpolant of
`(1, k - 1)`-weighted degree at most `D` vanishing at every point,
first with the linear choice `D = n` coming from the weighted-monomial
count (`exists_bivariate_interpolant`), then with the sharper
square-root choice `D = ⌈√(2 * (k - 1) * n)⌉`
(`exists_bivariate_interpolant_sqrt`), and finally transported to
`MvPolynomial` (`exists_bivariate_interpolant_mvPolynomial`). The
weighted-monomial counting bounds are `card_weighted_monomials_ge` and
`two_mul_card_weighted_monomials_ge`; `hasRootMult_one_iff` identifies
vanishing with root multiplicity one.

## References

The square-root degree choice and the counting estimate behind it are
the multiplicity-one case of the interpolation analysis in
V. Guruswami, A. Rudra, and M. Sudan, *Essential Coding Theory*, draft
of August 26, 2025, Section 12.2, equations (12.8)-(12.9); the same
edition is cited throughout `CSLibExt.Coding.GuruswamiSudan`.
-/

@[expose] public section

namespace Cslib.CodingTheory.BivariateInterpolation

open Polynomial Finset BigOperators

/-- Vanishing at `(a, b)` is the multiplicity-one case of root multiplicity. -/
theorem hasRootMult_one_iff (F : Type*) [Field F] (Q : F[X][X])
    (a b : F) :
    Cslib.CodingTheory.GuruswamiSudan.HasRootMult Q a b 1 ↔
      (Q.eval (C b)).eval a = 0 := by
  unfold Cslib.CodingTheory.GuruswamiSudan.HasRootMult
  unfold Cslib.CodingTheory.GuruswamiSudan.pointIdeal
  rw [pow_one (Ideal.span ({C (X - C a), X - C (C b)} : Set F[X][X]))]
  constructor
  · intro h
    let φ : F[X][X] →+* F :=
      (Polynomial.evalRingHom a).comp (Polynomial.evalRingHom (C b))
    have hsub : ({C (X - C a), X - C (C b)} : Set F[X][X])
        ⊆ RingHom.ker φ := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · apply RingHom.mem_ker.mpr
        show ((C (X - C a)).eval (C b)).eval a = 0
        rw [Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, sub_self]
      · apply RingHom.mem_ker.mpr
        show ((X - C (C b)).eval (C b)).eval a = 0
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_self, Polynomial.eval_zero]
    have hker : Ideal.span ({C (X - C a), X - C (C b)} : Set F[X][X])
        ≤ RingHom.ker φ := Ideal.span_le.mpr hsub
    exact RingHom.mem_ker.mp (hker h)
  · intro h
    have hQ := Polynomial.modByMonic_add_div Q (X - C (C b))
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hQ
    have hQ' : Q = (X - C (C b))
        * (Polynomial.divByMonic Q (X - C (C b))) + C (Q.eval (C b)) :=
      hQ.symm.trans (add_comm _ _)
    set r : F[X] := Q.eval (C b) with hr_def
    have hr := Polynomial.modByMonic_add_div r (X - C a)
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, h, Polynomial.C_0,
      zero_add] at hr
    have hr' : r = (X - C a) * (Polynomial.divByMonic r (X - C a)) :=
      hr.symm
    have hg1 : C (X - C a)
        ∈ Ideal.span ({C (X - C a), X - C (C b)} : Set F[X][X]) :=
      Ideal.subset_span (by simp)
    have hg2 : X - C (C b)
        ∈ Ideal.span ({C (X - C a), X - C (C b)} : Set F[X][X]) :=
      Ideal.subset_span (by simp)
    rw [hQ', hr', Polynomial.C_mul, mul_comm (X - C (C b)) _,
      mul_comm (C (X - C a)) _]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg2)
      (Ideal.mul_mem_left _ _ hg1)

/-- The weighted monomial count is at least `D + 1` (the `j = 0` row). -/
theorem card_weighted_monomials_ge (w D : ℕ) :
    D + 1 ≤ (((range (D + 1) ×ˢ range (D + 1)).filter
      fun ij : ℕ × ℕ => ij.1 + w * ij.2 ≤ D).card) := by
  have he : Function.Injective (fun i : ℕ => (i, 0)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hsub : (range (D + 1)).map ⟨(fun i : ℕ => (i, 0)), he⟩ ⊆
      (range (D + 1) ×ˢ range (D + 1)).filter
        fun ij : ℕ × ℕ => ij.1 + w * ij.2 ≤ D := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_filter, Finset.mem_product]
    simp only [Finset.mem_range]
    change (i < D + 1 ∧ 0 < D + 1) ∧ i + w * 0 ≤ D
    exact ⟨⟨hi, Nat.succ_pos D⟩, by omega⟩
  calc D + 1 = ((range (D + 1)).map ⟨(fun i : ℕ => (i, 0)), he⟩).card := by
        rw [Finset.card_map, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

private theorem sum_two_mul_succ_sub (D : ℕ) :
    ∑ i ∈ range (D + 1), 2 * (D - i + 1) = (D + 1) * (D + 2) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have hlast : 2 * (D + 1 - (D + 1) + 1) = 2 := by omega
    have hterm : ∀ i ∈ range (D + 1),
        2 * (D + 1 - i + 1) = 2 * (D - i + 1) + 2 := by
      intro i hi
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hlast]
    have htwo : ∑ _i ∈ range (D + 1), 2 = (D + 1) * 2 := by simp
    rw [htwo, ih]
    ring

/-- Lower bound on the weighted monomial count from the row sums. -/
theorem two_mul_card_weighted_monomials_ge (w D : ℕ) (hw : 0 < w) :
    D * (D + 2) ≤ 2 * w * (((range (D + 1) ×ˢ range (D + 1)).filter
      fun ij : ℕ × ℕ => ij.1 + w * ij.2 ≤ D).card) := by
  have hcard : (((range (D + 1) ×ˢ range (D + 1)).filter
        fun ij : ℕ × ℕ => ij.1 + w * ij.2 ≤ D).card)
      = ∑ i ∈ range (D + 1), ((D - i) / w + 1) := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    show (∑ j ∈ range (D + 1), (if i + w * j ≤ D then 1 else 0))
      = (D - i) / w + 1
    rw [← Finset.card_filter]
    change ((({j ∈ range (D + 1) | i + w * j ≤ D}).card)) = (D - i) / w + 1
    have hiD : i ≤ D := by
      rw [Finset.mem_range] at hi
      omega
    have hm : (D - i) / w < D + 1 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hiff : ∀ j : ℕ, (i + w * j ≤ D) ↔ (j ≤ (D - i) / w) := by
      intro j
      rw [Nat.le_div_iff_mul_le hw, mul_comm j w]
      omega
    have hset : ({j ∈ range (D + 1) | i + w * j ≤ D})
        = range ((D - i) / w + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [hiff j]
      omega
    rw [hset, Finset.card_range]
  have hterm : ∀ i ∈ range (D + 1),
      2 * (D - i + 1) ≤ 2 * w * ((D - i) / w + 1) := by
    intro i _
    have hle : D - i + 1 ≤ w * ((D - i) / w + 1) := by
      rw [Nat.left_distrib]
      have hdiv : w * ((D - i) / w) + (D - i) % w = D - i :=
        Nat.div_add_mod _ _
      have hmod : (D - i) % w < w := Nat.mod_lt _ hw
      omega
    rw [Nat.mul_assoc]
    omega
  have hsum : D * (D + 2) ≤ ∑ i ∈ range (D + 1), 2 * (D - i + 1) := by
    rw [sum_two_mul_succ_sub D]
    have he : (D + 1) * (D + 2) = D * (D + 2) + (D + 2) := by
      rw [Nat.right_distrib]
      omega
    omega
  rw [hcard, Finset.mul_sum]
  exact le_trans hsum (Finset.sum_le_sum hterm)

/-- A nonzero interpolant of `(1, k - 1)`-degree at most `n` exists. -/
theorem exists_bivariate_interpolant (F : Type*) [Field F] (n : ℕ)
    (α y : Fin n → F) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ Q : F[X][X], Q ≠ 0 ∧
      Cslib.CodingTheory.GuruswamiSudan.WeightedDegLE (k - 1) n Q ∧
      ∀ i, (Q.eval (C (y i))).eval (α i) = 0 := by
  have hcount : n * (1 * (1 + 1) / 2)
      < (((range (n + 1) ×ˢ range (n + 1)).filter
        fun ij : ℕ × ℕ => ij.1 + (k - 1) * ij.2 ≤ n).card) := by
    have heq : n * (1 * (1 + 1) / 2) = n := by simp
    have hle := card_weighted_monomials_ge (k - 1) n
    omega
  obtain ⟨Q, hQ0, hQdeg, hQvan⟩ :=
    Cslib.CodingTheory.GuruswamiSudan.exists_interpolant α y (k - 1) n 1
      hcount
  exact ⟨Q, hQ0, hQdeg,
    fun i => (hasRootMult_one_iff F Q (α i) (y i)).mp (hQvan i)⟩

def ceilSqrt (x : ℕ) : ℕ :=
  if Nat.sqrt x ^ 2 = x then Nat.sqrt x else Nat.sqrt x + 1

private theorem ceilSqrt_sq_eq (x : ℕ) (h : Nat.sqrt x ^ 2 = x) :
    ceilSqrt x ^ 2 = x := by
  unfold ceilSqrt
  simp [h]

private theorem ceilSqrt_lt_sq (x : ℕ) (h : Nat.sqrt x ^ 2 ≠ x) :
    x < ceilSqrt x ^ 2 := by
  unfold ceilSqrt
  simp [h]
  have hlt : Nat.sqrt x < Nat.sqrt x + 1 := by omega
  have hub : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.sqrt_lt.mp hlt
  rw [pow_two]
  exact hub

private theorem ceilSqrt_le (x : ℕ) : x ≤ ceilSqrt x ^ 2 := by
  by_cases h : Nat.sqrt x ^ 2 = x
  · have heq := ceilSqrt_sq_eq x h
    omega
  · have hlt := ceilSqrt_lt_sq x h
    omega

private theorem ceilSqrt_pos (x : ℕ) (hx : 0 < x) : 0 < ceilSqrt x := by
  unfold ceilSqrt
  split_ifs with h
  · by_contra hz
    have h0 : Nat.sqrt x = 0 := by omega
    rw [h0] at h
    simp at h
    omega
  · omega

/-- Interpolant with `D` the source ceiling choice `⌈√(2 * (k - 1) * n)⌉`,
via the (12.8)-(12.9) estimate through `two_mul_card_weighted_monomials_ge`. -/
theorem exists_bivariate_interpolant_sqrt (F : Type*) [Field F] (n : ℕ)
    (α y : Fin n → F) (k : ℕ) (hk : 2 ≤ k) :
    ∃ Q : F[X][X], Q ≠ 0 ∧
      Cslib.CodingTheory.GuruswamiSudan.WeightedDegLE (k - 1)
        (ceilSqrt (2 * (k - 1) * n)) Q ∧
      ∀ i, (Q.eval (C (y i))).eval (α i) = 0 := by
  have hw : 0 < k - 1 := by omega
  set D : ℕ := ceilSqrt (2 * (k - 1) * n) with hD
  have hcount : n * (1 * (1 + 1) / 2)
      < (((range (D + 1) ×ˢ range (D + 1)).filter
        fun ij : ℕ × ℕ => ij.1 + (k - 1) * ij.2 ≤ D).card) := by
    have heq : n * (1 * (1 + 1) / 2) = n := by simp
    by_cases hn : n = 0
    · subst hn
      rw [heq]
      have hle := card_weighted_monomials_ge (k - 1) D
      omega
    · have hn_pos : 0 < n := by omega
      have hL := two_mul_card_weighted_monomials_ge (k - 1) D hw
      have hXpos : 0 < 2 * (k - 1) * n :=
        Nat.mul_pos (Nat.mul_pos (show (0 : ℕ) < 2 by omega) hw) hn_pos
      have hDpos : 0 < D := by
        rw [hD]
        exact ceilSqrt_pos _ hXpos
      have hle : 2 * (k - 1) * n ≤ D ^ 2 := by
        rw [hD]
        exact ceilSqrt_le _
      have hsq : 2 * (k - 1) * n ≤ D * D := by
        rw [pow_two] at hle
        exact hle
      have hmul : D * D < D * (D + 2) := by
        have he : D * (D + 2) = D * D + D * 2 := Nat.left_distrib _ _ _
        omega
      have hnc : n < (((range (D + 1) ×ˢ range (D + 1)).filter
          fun ij : ℕ × ℕ => ij.1 + (k - 1) * ij.2 ≤ D).card) := by
        have hchain : 2 * (k - 1) * n < 2 * (k - 1) *
            (((range (D + 1) ×ˢ range (D + 1)).filter
              fun ij : ℕ × ℕ => ij.1 + (k - 1) * ij.2 ≤ D).card) :=
          lt_of_le_of_lt hsq (lt_of_lt_of_le hmul hL)
        by_contra hcon
        have hle : (((range (D + 1) ×ˢ range (D + 1)).filter
            fun ij : ℕ × ℕ => ij.1 + (k - 1) * ij.2 ≤ D).card) ≤ n := by
          omega
        have hmul_le := Nat.mul_le_mul_left (2 * (k - 1)) hle
        omega
      omega
  obtain ⟨Q, hQ0, hQdeg, hQvan⟩ :=
    Cslib.CodingTheory.GuruswamiSudan.exists_interpolant α y (k - 1) D 1
      hcount
  exact ⟨Q, hQ0, hQdeg,
    fun i => (hasRootMult_one_iff F Q (α i) (y i)).mp (hQvan i)⟩

/-- `exists_bivariate_interpolant` transported along
`Polynomial.Bivariate.equivMvPolynomial`. -/
theorem exists_bivariate_interpolant_mvPolynomial (F : Type*) [Field F]
    (n : ℕ) (α y : Fin n → F) (k : ℕ) (hk : 1 ≤ k) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ d ∈ Q.support, d 0 + (k - 1) * d 1 ≤ n) ∧
      ∀ i, MvPolynomial.eval ![α i, y i] Q = 0 := by
  obtain ⟨Q', hQ0, hQdeg, hQvan⟩ :=
    exists_bivariate_interpolant F n α y k hk
  unfold Cslib.CodingTheory.GuruswamiSudan.WeightedDegLE at hQdeg
  refine ⟨(Polynomial.Bivariate.equivMvPolynomial F) Q', ?_, ?_, ?_⟩
  · intro hcon
    apply hQ0
    exact AlgEquiv.injective _ (hcon.trans (map_zero _).symm)
  · intro d hd
    have hmem := MvPolynomial.mem_support_iff.mp hd
    have hgen : ∀ (p : F[X][X]) (e : Fin 2 →₀ ℕ),
        ((Polynomial.Bivariate.equivMvPolynomial F) p).coeff e
        = (p.coeff (e 1)).coeff (e 0) := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        intro e
        simp [map_add, hp, hq, Polynomial.coeff_add]
      | monomial n a =>
        intro e
        induction a using Polynomial.induction_on' with
        | add p q hp hq =>
          simp [map_add, Polynomial.coeff_add, hp, hq]
        | monomial m r =>
          have houter : (monomial n) ((monomial m) r : F[X])
              = C ((monomial m) r) * X ^ n := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial]
          have hinner : (monomial m) r = C r * X ^ m := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial]
          rw [houter, hinner]
          simp only [map_mul, map_pow,
            Polynomial.Bivariate.equivMvPolynomial_C_C,
            Polynomial.Bivariate.equivMvPolynomial_C_X,
            Polynomial.Bivariate.equivMvPolynomial_X]
          have hX1 : (MvPolynomial.X (R := F) (1 : Fin 2)) ^ n
              = MvPolynomial.monomial (Finsupp.single (1 : Fin 2) n)
                (1 : F) := by
            have h := MvPolynomial.C_mul_X_pow_eq_monomial (s := (1 : Fin 2))
              (a := (1 : F)) (n := n)
            simpa using h
          have hMv : MvPolynomial.C r * MvPolynomial.X (0 : Fin 2) ^ m
              * MvPolynomial.X (1 : Fin 2) ^ n
              = MvPolynomial.monomial
                (Finsupp.single (0 : Fin 2) m
                  + Finsupp.single (1 : Fin 2) n) r := by
            rw [hX1, MvPolynomial.C_mul_X_pow_eq_monomial,
              MvPolynomial.monomial_mul_monomial, mul_one]
          rw [hMv, MvPolynomial.coeff_monomial]
          have hC : Polynomial.C (Polynomial.C r) * Polynomial.C Polynomial.X ^ m
              = Polynomial.C ((monomial m) r : F[X]) := by
            rw [hinner, map_mul, map_pow]
          have hP : Polynomial.C ((monomial m) r : F[X]) * Polynomial.X ^ n
              = (monomial n) ((monomial m) r : F[X]) := by
            rw [Polynomial.C_mul_X_pow_eq_monomial]
          have hRHS : ((Polynomial.C (Polynomial.C r) * Polynomial.C Polynomial.X ^ m
              * Polynomial.X ^ n).coeff (e 1)).coeff (e 0)
              = (((monomial n) ((monomial m) r : F[X])).coeff (e 1)).coeff
                (e 0) := by
            rw [hC, hP]
          rw [hRHS, Polynomial.coeff_monomial_apply]
          have hd0 : (Finsupp.single (0 : Fin 2) m
              + Finsupp.single (1 : Fin 2) n) 0 = m := by
            simp
          have hd1 : (Finsupp.single (0 : Fin 2) m
              + Finsupp.single (1 : Fin 2) n) 1 = n := by
            simp
          by_cases hn : n = e 1
          · rw [ite_eq_left hn, Polynomial.coeff_monomial_apply]
            by_cases hm : m = e 0
            · have heq : Finsupp.single (0 : Fin 2) m
                  + Finsupp.single (1 : Fin 2) n = e := by
                ext i
                fin_cases i
                · simp [hm]
                · simp [hn]
              rw [ite_eq_left heq, ite_eq_left hm]
            · have hne : Finsupp.single (0 : Fin 2) m
                  + Finsupp.single (1 : Fin 2) n ≠ e := by
                intro hcon
                apply hm
                rw [← hd0, hcon]
              rw [ite_eq_right hne, ite_eq_right hm]
          · rw [ite_eq_right hn, Polynomial.coeff_zero]
            have hne : Finsupp.single (0 : Fin 2) m
                + Finsupp.single (1 : Fin 2) n ≠ e := by
              intro hcon
              apply hn
              rw [← hd1, hcon]
            rw [ite_eq_right hne]
    have hcoeff : ((Polynomial.Bivariate.equivMvPolynomial F) Q').coeff d
        = (Q'.coeff (d 1)).coeff (d 0) := hgen Q' d
    rw [hcoeff] at hmem
    exact hQdeg (d 1) (d 0) hmem
  · intro i
    have hequiv : (Polynomial.Bivariate.equivMvPolynomial F) Q'
        = Polynomial.aevalAeval (MvPolynomial.X 0) (MvPolynomial.X 1) Q' :=
      rfl
    have heval : MvPolynomial.eval ![α i, y i]
        ((Polynomial.Bivariate.equivMvPolynomial F) Q')
        = MvPolynomial.aeval ![α i, y i]
          ((Polynomial.Bivariate.equivMvPolynomial F) Q' : MvPolynomial (Fin 2) F) := by
      rw [← MvPolynomial.coe_aeval_eq_eval]
      rfl
    rw [heval, hequiv]
    have hcomp : MvPolynomial.aeval ![α i, y i]
        (Polynomial.aevalAeval (MvPolynomial.X 0) (MvPolynomial.X 1) Q'
          : MvPolynomial (Fin 2) F)
        = Polynomial.aevalAeval (α i) (y i) Q' := by
      let f : F[X][X] →ₐ[F] F :=
        (MvPolynomial.aeval ![α i, y i]).comp
          (Polynomial.aevalAeval (MvPolynomial.X 0) (MvPolynomial.X 1))
      have hf : f Q' = MvPolynomial.aeval ![α i, y i]
          (Polynomial.aevalAeval (MvPolynomial.X 0) (MvPolynomial.X 1) Q'
            : MvPolynomial (Fin 2) F) := rfl
      have hCX : f (Polynomial.C Polynomial.X) = α i := by
        simp [f]
      have hY : f Polynomial.X = y i := by
        simp [f]
      have heq : f = Polynomial.aevalAeval (α i) (y i) := by
        have h := (Polynomial.aevalAevalEquiv F F).right_inv f
        simp [Polynomial.aevalAevalEquiv, hCX, hY] at h
        exact h.symm
      rw [← hf, heq]
    rw [hcomp]
    have hcoe := Polynomial.coe_aevalAeval_eq_evalEval (α i) (y i)
    have hfun := congrFun hcoe Q'
    rw [hfun]
    exact hQvan i

end Cslib.CodingTheory.BivariateInterpolation
