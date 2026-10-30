/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexCounterexample
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# From the parity model to the current series on `K₄`

The even and odd parts of the current series are `cosh` and `sinh`, so a sum of current weights
grouped by edge parity equals `cosh^|E|` times the parity polynomial at `tanh`. This carries the
`K₄` counterexample of `SupportLexCounterexample` from the parity model to the current series.

## i. Overview

For a single edge, `∑_{k even} x^k/k! = cosh x` and `∑_{k odd} x^k/k! = sinh x`. Summing a
predicate `P` of the odd-multiplicity edge set over all currents therefore gives
`cosh(x)^|E| · ∑_{A : P A} tanh(x)^|A|` (`shb_paritySeriesMass_eq_cosh_mul_polynomial`). The ratio
of two such masses is independent of the `cosh` factor, so the direct-path weight of the current
series at `x` equals the parity-model weight at `t = tanh x`. Taking `x = artanh (2/3)` transfers
the strict inequality of the parity model.

Headline fidelity: `shb_supportLex_realParity_P3_counterexample` and
`shb_supportLex_series_P3_counterexample` are proved unconditionally.

## ii. Key results

- `shb_paritySeriesMass_eq_cosh_mul_polynomial`, `shb_paritySeriesMassOn_eq_cosh_mul_polynomial` :
  current series grouped by parity = `cosh^|E|` × parity polynomial at `tanh` (unconditional)
- `shbK4DirectRhoSeries_eq_polynomial` : the series ratio equals the polynomial ratio at `tanh`
- `shb_supportLex_series_P3_counterexample` : domain monotonicity fails for the current series on
  `K₄` at `x = artanh (2/3)` (unconditional)

## iii. Table of contents

- A. Even and odd current series
- B. Parity masses as polynomials in `tanh`
- C. The `K₄` masses as real polynomials
- D. The `K₄` masses as current series

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982)
  1–48
-/
@[expose] public section

open Finset

namespace StatMech.Sharpness

/-! ## A. Even and odd current series -/

/-- The even part `∑_k x^{2k}/(2k)!` of the single-edge current series. -/
noncomputable def shbEvenCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k) / (2 * k).factorial

/-- The odd part `∑_k x^{2k+1}/(2k+1)!` of the single-edge current series. -/
noncomputable def shbOddCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k + 1) / (2 * k + 1).factorial

lemma shb_evenCurrentSeries_eq_cosh (x : ℝ) :
    shbEvenCurrentSeries x = Real.cosh x := by
  unfold shbEvenCurrentSeries
  exact (Real.cosh_eq_tsum x).symm

lemma shb_oddCurrentSeries_eq_sinh (x : ℝ) :
    shbOddCurrentSeries x = Real.sinh x := by
  unfold shbOddCurrentSeries
  exact (Real.sinh_eq_tsum x).symm

/-! ## B. Parity masses as polynomials in `tanh` -/

/-- The current-series mass of the currents on `E` whose odd-multiplicity edge set satisfies `P`:
`∑_{A : P A} ∏_{e ∈ A} sinh-part · ∏_{e ∉ A} cosh-part`. -/
noncomputable def shbParitySeriesMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then
      ∏ e : E, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0

/-- The parity polynomial `∑_{A : P A} t^|A|` over all edge subsets `A`. -/
def shbParityPolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then t ^ A.card else 0

private lemma shb_sinh_eq_cosh_mul_tanh (x : ℝ) :
    Real.sinh x = Real.cosh x * Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- A parity-grouped current-series mass is `cosh^|E|` times the parity polynomial at `tanh`. -/
theorem shb_paritySeriesMass_eq_cosh_mul_polynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) :
    shbParitySeriesMass P x =
      Real.cosh x ^ Fintype.card E * shbParityPolynomial P (Real.tanh x) := by
  unfold shbParitySeriesMass shbParityPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A
  · rw [ite_eq_left hP, ite_eq_left hP]
    simp_rw [shb_evenCurrentSeries_eq_cosh, shb_oddCurrentSeries_eq_sinh,
      shb_sinh_eq_cosh_mul_tanh]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset E)) (fun e ↦ e ∈ A)
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_univ] at hcard
    rw [mul_pow]
    calc
      Real.cosh x ^ A.card * Real.tanh x ^ A.card *
            Real.cosh x ^ ((Finset.univ.filter fun e ↦ ¬ e ∈ A).card) =
          (Real.cosh x ^ A.card *
              Real.cosh x ^ ((Finset.univ.filter fun e ↦ ¬ e ∈ A).card)) *
            Real.tanh x ^ A.card := by ring
      _ = Real.cosh x ^
              (A.card + (Finset.univ.filter fun e ↦ ¬ e ∈ A).card) *
            Real.tanh x ^ A.card := by rw [pow_add]
      _ = Real.cosh x ^ Fintype.card E * Real.tanh x ^ A.card := by rw [hcard]
  · rw [ite_eq_right hP, ite_eq_right hP, mul_zero]

/-- `shbParitySeriesMass` with edges restricted to the finite set `S`. -/
noncomputable def shbParitySeriesMassOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ S.powerset,
    if P A then
      ∏ e ∈ S, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0

/-- `shbParityPolynomial` with edges restricted to the finite set `S`. -/
def shbParityPolynomialOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, if P A then t ^ A.card else 0

lemma shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) :
    shbParitySeriesMassOn S P x =
      Real.cosh x ^ S.card * shbParityPolynomialOn S P (Real.tanh x) := by
  unfold shbParitySeriesMassOn shbParityPolynomialOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A
  · rw [ite_eq_left hP, ite_eq_left hP]
    simp_rw [shb_evenCurrentSeries_eq_cosh, shb_oddCurrentSeries_eq_sinh,
      shb_sinh_eq_cosh_mul_tanh]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.prod_const]
    have hsub : A ⊆ S := Finset.mem_powerset.mp hA
    rw [Finset.inter_eq_right.mpr hsub]
    have hcard := Finset.card_filter_add_card_filter_not
      (s := S) (fun e ↦ e ∈ A)
    simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub] at hcard
    rw [mul_pow]
    calc
      Real.cosh x ^ A.card * Real.tanh x ^ A.card *
            Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card) =
          (Real.cosh x ^ A.card *
              Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card)) *
            Real.tanh x ^ A.card := by ring
      _ = Real.cosh x ^
              (A.card + (S.filter fun e ↦ ¬ e ∈ A).card) *
            Real.tanh x ^ A.card := by rw [pow_add]
      _ = Real.cosh x ^ S.card * Real.tanh x ^ A.card := by rw [hcard]
  · rw [ite_eq_right hP, ite_eq_right hP, mul_zero]

/-! ## C. The `K₄` masses as real polynomials -/

/-- The real-valued direct fiber mass of `SupportLexCounterexample`. -/
def shbK4DirectFiberPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  ∑ A ∈ shbK4Configs E, if shbK4SelectsDirect03 A then t ^ A.card else 0

/-- The real-valued vacuum mass of `SupportLexCounterexample`. -/
def shbK4VacuumPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  ∑ A ∈ shbK4Configs E, if shbK4Boundary A = ∅ then t ^ A.card else 0

lemma shbK4DirectFiberMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectFiberMass E t : ℝ) = shbK4DirectFiberPolynomial E t := by
  unfold shbK4DirectFiberMass shbK4DirectFiberPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4SelectsDirect03 A <;> simp [h]

lemma shbK4VacuumMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4VacuumMass E t : ℝ) = shbK4VacuumPolynomial E t := by
  unfold shbK4VacuumMass shbK4VacuumPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4Boundary A = ∅ <;> simp [h]

/-- The real-valued parity model of the direct-path backbone weight. -/
noncomputable def shbK4DirectRhoPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  shbK4DirectFiberPolynomial E t / shbK4VacuumPolynomial E t

lemma shbK4DirectRho_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectRho E t : ℝ) = shbK4DirectRhoPolynomial E t := by
  rw [shbK4DirectRho, shbK4DirectRhoPolynomial, Rat.cast_div,
    shbK4DirectFiberMass_cast, shbK4VacuumMass_cast]

/-- The parity-model counterexample to domain monotonicity, over `ℝ`. -/
theorem shb_supportLex_realParity_P3_counterexample :
    shbK4DirectRhoPolynomial shbK4H (2 / 3) <
      shbK4DirectRhoPolynomial shbK4G (2 / 3) := by
  have h := shb_supportLex_edgeDomain_P3_counterexample
  have hH := shbK4DirectRho_cast shbK4H (2 / 3)
  have hG := shbK4DirectRho_cast shbK4G (2 / 3)
  norm_num at hH hG
  rw [← hH, ← hG]
  exact_mod_cast h

lemma shb_tanh_artanh_two_thirds :
    Real.tanh (Real.artanh (2 / 3)) = (2 / 3 : ℝ) := by
  rw [Real.tanh_artanh]
  norm_num

/-! ## D. The `K₄` masses as current series -/

/-- The current-series mass of the configurations on `E` selecting the direct edge `03`. -/
noncomputable def shbK4DirectFiberSeriesMass
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbParitySeriesMassOn E shbK4SelectsDirect03 x

/-- The current-series mass of the sourceless currents on `E`. -/
noncomputable def shbK4VacuumSeriesMass
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbParitySeriesMassOn E (fun A ↦ shbK4Boundary A = ∅) x

lemma shbK4DirectFiberSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectFiberSeriesMass E x =
      Real.cosh x ^ E.card * shbK4DirectFiberPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E shbK4SelectsDirect03 x

lemma shbK4VacuumSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4VacuumSeriesMass E x =
      Real.cosh x ^ E.card * shbK4VacuumPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E (fun A ↦ shbK4Boundary A = ∅) x

/-- The current-series direct-path backbone weight on `E`. -/
noncomputable def shbK4DirectRhoSeries
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbK4DirectFiberSeriesMass E x / shbK4VacuumSeriesMass E x

lemma shbK4DirectRhoSeries_eq_polynomial
    (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectRhoSeries E x =
      shbK4DirectRhoPolynomial E (Real.tanh x) := by
  rw [shbK4DirectRhoSeries, shbK4DirectFiberSeriesMass_eq,
    shbK4VacuumSeriesMass_eq, shbK4DirectRhoPolynomial]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.cosh_pos x).ne')

/-- Domain monotonicity fails for the current-series direct-path weight on `K₄ \ 12 ⊆ K₄` at
`x = artanh (2/3)`. -/
theorem shb_supportLex_series_P3_counterexample :
    shbK4DirectRhoSeries shbK4H (Real.artanh (2 / 3)) <
      shbK4DirectRhoSeries shbK4G (Real.artanh (2 / 3)) := by
  rw [shbK4DirectRhoSeries_eq_polynomial,
    shbK4DirectRhoSeries_eq_polynomial, shb_tanh_artanh_two_thirds]
  exact shb_supportLex_realParity_P3_counterexample

end StatMech.Sharpness
