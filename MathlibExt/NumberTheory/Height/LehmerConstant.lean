/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.Reverse

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.ComputeDegree

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.LehmerConstant

/-!
# Lehmer's Mahler measure constant

For an integer polynomial `f`, its Mahler measure is
`M(f) = |a| * ∏ᵢ max (1, |αᵢ|)`, where `a` is the leading coefficient and
the `αᵢ` are the complex roots of `f` counted with multiplicity. This is
`Polynomial.mapMahlerMeasure (Int.castRingHom ℂ)` in Mathlib, whose root
product formula is `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`.

Lehmer's constant (catalogue constant C40a) is the infimum of the Mahler
measures strictly larger than `1` among integer polynomials:
`L = inf {M(f) | f ∈ ℤ[X], 1 < M(f)}`. Lehmer's 1933 question asks whether
Mahler measures accumulate at `1`, equivalently whether `L = 1`; this file
proves that equivalence together with the elementary bounds `1 ≤ L ≤ 2`.
This file also certifies the Mahler measure bound for Lehmer's example polynomial and
uses it to prove `L ≤ 1176281/1000000`. Smyth's nonreciprocal lower bound remains a
proof request in the wanted file.

Source: Optimization Problems, constants/40a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`d89b66d6b78a2de211675ee1e2deb67f427fc66a3d051adad8a740a28397e3e6`.
-/

/-- **Mahler measure of an integer polynomial.** The Mahler measure of $f \in \mathbb{Z}[X]$
is the Mahler measure of its image in $\mathbb{C}[X]$. It equals
$|a| \prod_i \max(1, |\alpha_i|)$, where $a$ is the leading coefficient of $f$ and the
$\alpha_i$ are the complex roots of $f$ counted with multiplicity. -/
noncomputable def intMahlerMeasure (f : Polynomial ℤ) : ℝ :=
  f.mapMahlerMeasure (Int.castRingHom ℂ)

theorem intMahlerMeasure_nonneg (f : Polynomial ℤ) :
    0 ≤ intMahlerMeasure f :=
  Polynomial.mahlerMeasure_nonneg _

/-- **Nonzero integer polynomials have Mahler measure at least one.** If
$f \in \mathbb{Z}[X]$ is a nonzero polynomial, then its Mahler measure satisfies $M(f) \ge 1$.

Indeed, $M(f) = |a| \prod_i \max(1, |\alpha_i|)$, where the leading coefficient $a$ of $f$ is a
nonzero integer and the $\alpha_i$ are the complex roots of $f$ counted with multiplicity, so
every factor is at least $1$. -/
theorem one_le_intMahlerMeasure {f : Polynomial ℤ} (hf : f ≠ 0) :
    1 ≤ intMahlerMeasure f := by
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  calc
    (1 : ℝ) ≤ ‖f.leadingCoeff‖ := by
      rw [Int.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hlc
    _ ≤ intMahlerMeasure f :=
      Polynomial.leadingCoeff_le_mapMahlerMeasure _ _ Complex.isometry_intCast

theorem intMahlerMeasure_mul (f g : Polynomial ℤ) :
    intMahlerMeasure (f * g) = intMahlerMeasure f * intMahlerMeasure g := by
  simp only [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_mul,
    Polynomial.mahlerMeasure_mul]

theorem intMahlerMeasure_C (a : ℤ) :
    intMahlerMeasure (C a) = ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_C,
    Polynomial.mahlerMeasure_const]
  simp

/-- **Mahler measure of a monic linear integer polynomial.** For every integer $a$, the
Mahler measure of the integer polynomial $X - a$ is $\max(1, |a|)$. -/
theorem intMahlerMeasure_X_sub_C (a : ℤ) :
    intMahlerMeasure (X - C a) = max 1 ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.mahlerMeasure_X_sub_C]
  simp

theorem intMahlerMeasure_X : intMahlerMeasure (X : Polynomial ℤ) = 1 := by
  have h : (X : Polynomial ℤ) = X - C (0 : ℤ) := by simp
  rw [h, intMahlerMeasure_X_sub_C]
  simp

/-- **Mahler measure of $X - 1$.** The integer polynomial $X - 1$ has Mahler measure $1$.

Since $1$ is not strictly larger than $1$, this value is excluded from the set whose
infimum is Lehmer's constant. -/
theorem intMahlerMeasure_X_sub_one :
    intMahlerMeasure (X - C (1 : ℤ)) = 1 := by
  rw [intMahlerMeasure_X_sub_C]
  simp

/-- **Mahler measure of $X - 2$.** The integer polynomial $X - 2$ has Mahler measure $2$.

Since $2 > 1$, this value lies in the set whose infimum is Lehmer's constant. -/
theorem intMahlerMeasure_X_sub_two :
    intMahlerMeasure (X - C (2 : ℤ)) = 2 := by
  rw [intMahlerMeasure_X_sub_C]
  norm_num

/-- **Mahler measures above one.** This is the set of real numbers of the form $M(f)$, where
$f \in \mathbb{Z}[X]$ is an integer polynomial whose Mahler measure $M(f)$ is strictly larger
than $1$. -/
def mahlerMeasuresAboveOne : Set ℝ :=
  {y | ∃ f : Polynomial ℤ, 1 < intMahlerMeasure f ∧ y = intMahlerMeasure f}

/-- **Lehmer's constant.** Writing $M(f)$ for the Mahler measure of an integer polynomial $f$,
Lehmer's constant is
$C_{40a} = \inf \{M(f) : f \in \mathbb{Z}[X],\ M(f) > 1\}$,
the infimum of the Mahler measures of integer polynomials that are strictly larger than $1$. -/
noncomputable def lehmerConstant : ℝ :=
  sInf mahlerMeasuresAboveOne

theorem mahlerMeasuresAboveOne_nonempty : mahlerMeasuresAboveOne.Nonempty :=
  ⟨2, X - C (2 : ℤ), by rw [intMahlerMeasure_X_sub_two]; norm_num,
    intMahlerMeasure_X_sub_two.symm⟩

theorem mahlerMeasuresAboveOne_bddBelow : BddBelow mahlerMeasuresAboveOne :=
  ⟨1, by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf⟩

/-- **Lehmer's constant bounds every Mahler measure above $1$.** For every integer polynomial
$f$ whose Mahler measure is strictly larger than $1$, Lehmer's constant is at most the Mahler
measure of $f$. -/
theorem lehmerConstant_le_intMahlerMeasure {f : Polynomial ℤ}
    (hf : 1 < intMahlerMeasure f) : lehmerConstant ≤ intMahlerMeasure f :=
  csInf_le mahlerMeasuresAboveOne_bddBelow ⟨f, hf, rfl⟩

/-- **Lehmer's constant is at least one.** Lehmer's constant $L$, the infimum of the Mahler
measures strictly larger than $1$ of polynomials in $\mathbb{Z}[X]$, satisfies $1 \le L$.

This is the lower bound recorded in the catalogue for the constant $C_{40a}$. -/
theorem one_le_lehmerConstant : 1 ≤ lehmerConstant :=
  le_csInf mahlerMeasuresAboveOne_nonempty (by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf)

/-- **Lehmer's constant is at most $2$.** Lehmer's constant $C_{40a}$ satisfies
$C_{40a} \le 2$.

The witness is the integer polynomial $X - 2$, whose Mahler measure is $2$. -/
theorem lehmerConstant_le_two : lehmerConstant ≤ 2 := by
  rw [← intMahlerMeasure_X_sub_two]
  exact lehmerConstant_le_intMahlerMeasure (by
    rw [intMahlerMeasure_X_sub_two]; norm_num)

/-- **Lehmer's question.** The proposition that there are integer polynomials with
Mahler measure arbitrarily close to $1$ from above: for every real $\varepsilon > 0$ there is a
polynomial $f \in \mathbb{Z}[X]$ whose Mahler measure $M(f)$ satisfies $1 < M(f) < 1 + \varepsilon$.

Lehmer asked in 1933 whether this proposition holds. -/
def LehmerQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : Polynomial ℤ,
    1 < intMahlerMeasure f ∧ intMahlerMeasure f < 1 + ε

/-- **Lehmer's question in terms of Lehmer's constant.** Lehmer's constant equals $1$ if and
only if Lehmer's question has a positive answer, that is, for every $\varepsilon > 0$ there is
an integer polynomial whose Mahler measure lies strictly between $1$ and $1 + \varepsilon$. -/
theorem lehmerConstant_eq_one_iff : lehmerConstant = 1 ↔ LehmerQuestion := by
  constructor
  · intro hL ε hε
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := exists_lt_of_csInf_lt
      mahlerMeasuresAboveOne_nonempty (show lehmerConstant < 1 + ε by linarith)
    exact ⟨f, hf, hy⟩
  · intro hQ
    apply le_antisymm _ one_le_lehmerConstant
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf1, hf2⟩ := hQ ε hε
    linarith [lehmerConstant_le_intMahlerMeasure hf1]

/-- **Lehmer's polynomial.** Lehmer's polynomial is the integer polynomial
$X^{10} + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1$.

Lehmer found it in 1933. Its Mahler measure $1.176280\ldots$ is still the smallest known
Mahler measure larger than $1$. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

private noncomputable def lehmerTrace : ℝ[X] :=
  X ^ 5 + (X ^ 4 - C 5 * X ^ 3 - C 5 * X ^ 2 + C 4 * X + C 3)

private theorem lehmerTrace_monic : lehmerTrace.Monic := by
  unfold lehmerTrace
  apply monic_X_pow_add
  compute_degree!

private theorem lehmerTrace_natDegree : lehmerTrace.natDegree = 5 := by
  unfold lehmerTrace
  compute_degree!

-- A monic quintic with five distinct roots is the product of their linear factors.
private theorem lehmerTrace_eq_prod {s : Finset ℝ} (hs : s.card = 5)
    (hroot : ∀ y ∈ s, lehmerTrace.eval y = 0) : lehmerTrace = ∏ y ∈ s, (X - C y) := by
  have hdvd : (∏ y ∈ s, (X - C y)) ∣ lehmerTrace := by
    refine Finset.prod_dvd_of_coprime ?_ (fun y hy => dvd_iff_isRoot.mpr (hroot y hy))
    intro a _ b _ hab
    exact pairwise_coprime_X_sub_C Function.injective_id hab
  have hmonic : (∏ y ∈ s, (X - C y)).Monic :=
    monic_prod_of_monic _ _ (fun y _ => monic_X_sub_C y)
  have hdegree : (∏ y ∈ s, (X - C y)).natDegree = 5 := by
    rw [natDegree_prod _ _ (fun y _ => (monic_X_sub_C y).ne_zero)]
    simpa using hs
  simpa only [lehmerTrace_monic.leadingCoeff, map_one, one_mul] using
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmonic hdvd
      (lehmerTrace_natDegree.trans hdegree.symm).le

-- Substituting x + x⁻¹ recovers the reciprocal polynomial after clearing x⁻⁵.
private theorem eval_lehmerPolynomial_eq_trace (x : ℝ) (hx : x ≠ 0) :
    (lehmerPolynomial.map (Int.castRingHom ℝ)).eval x =
      x ^ 5 * lehmerTrace.eval (x + x⁻¹) := by
  delta lehmerPolynomial
  simp [lehmerTrace]
  field_simp
  ring

private noncomputable def lehmerQuadratic (y : ℝ) : ℂ[X] :=
  X ^ 2 - C (y : ℂ) * X + 1

private theorem map_lehmerPolynomial_eq_prod {s : Finset ℝ} (hs : s.card = 5)
    (htrace : lehmerTrace = ∏ y ∈ s, (X - C y)) :
    lehmerPolynomial.map (Int.castRingHom ℂ) = ∏ y ∈ s, lehmerQuadratic y := by
  have hreal : lehmerPolynomial.map (Int.castRingHom ℝ) =
      ∏ y ∈ s, ((X : ℝ[X]) ^ 2 - C y * X + 1) := by
    apply Polynomial.funext
    intro x
    by_cases hx : x = 0
    · subst x
      delta lehmerPolynomial
      simp [eval_prod]
    rw [eval_lehmerPolynomial_eq_trace x hx, htrace, eval_prod, ← hs, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, eval_prod]
    apply Finset.prod_congr rfl
    intro y _
    simp
    field_simp
    ring
  simpa [lehmerQuadratic, Polynomial.map_prod, Polynomial.map_map, RingHom.eq_intCast'] using
    congrArg (Polynomial.map Complex.ofRealHom) hreal

private theorem lehmerQuadratic_factor {y : ℝ} {u v : ℂ}
    (hsum : u + v = (y : ℂ)) (hprod : u * v = 1) :
    lehmerQuadratic y = (X - C u) * (X - C v) := by
  calc
    lehmerQuadratic y = X ^ 2 - (C u + C v) * X + C u * C v := by
      rw [← map_add, ← map_mul, hsum, hprod, map_one, lehmerQuadratic]
    _ = (X - C u) * (X - C v) := by ring

-- For a trace in [-2, 2], the two roots are conjugates on the unit circle.
private theorem mahlerMeasure_lehmerQuadratic_of_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc (-2) 2) :
    (lehmerQuadratic y).mahlerMeasure = 1 := by
  have hy₁ : -2 ≤ y := hy.1
  have hy₂ : y ≤ 2 := hy.2
  have hrad : 0 ≤ 4 - y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy₂) (show 0 ≤ 2 + y by linarith)]
  let z : ℂ := ⟨y / 2, √(4 - y ^ 2) / 2⟩
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply]
    change (y / 2) * (y / 2) + (√(4 - y ^ 2) / 2) * (√(4 - y ^ 2) / 2) = 1
    nlinarith [Real.sq_sqrt hrad]
  have hz : ‖z‖ = 1 := by rw [Complex.norm_def, hsq, Real.sqrt_one]
  have hsum : z + (starRingEnd ℂ) z = (y : ℂ) := by
    rw [Complex.add_conj]
    congr 1
    change 2 * (y / 2) = y
    ring
  have hprod : z * (starRingEnd ℂ) z = 1 := by rw [Complex.mul_conj, hsq, Complex.ofReal_one]
  rw [lehmerQuadratic_factor hsum hprod, mahlerMeasure_mul, mahlerMeasure_X_sub_C,
    mahlerMeasure_X_sub_C, Complex.norm_conj, hz, max_self, mul_one]

-- The other quadratic has reciprocal positive real roots, one of which exceeds one.
private theorem mahlerMeasure_lehmerQuadratic_of_reciprocal {r : ℝ} (hr : 1 < r) :
    (lehmerQuadratic (r + r⁻¹)).mahlerMeasure = r := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hprod : (r : ℂ) * (↑(r⁻¹) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr₀.ne', Complex.ofReal_one]
  rw [lehmerQuadratic_factor (Complex.ofReal_add r r⁻¹).symm hprod, mahlerMeasure_mul,
    mahlerMeasure_X_sub_C, mahlerMeasure_X_sub_C, Complex.norm_of_nonneg hr₀.le,
    Complex.norm_of_nonneg (inv_nonneg.mpr hr₀.le), max_eq_right hr.le,
    max_eq_left (inv_le_one_of_one_le₀ hr.le), mul_one]

private theorem intMahlerMeasure_lehmerPolynomial_mem_Ioo :
    intMahlerMeasure lehmerPolynomial ∈ Set.Ioo 1 (1176281 / 1000000) := by
  classical
  -- Four sign changes in (-2, 2) give the four unit-circle traces.
  obtain ⟨a, ha, ha₀⟩ := intermediate_value_Ioo (f := lehmerTrace.eval)
    (a := -2) (b := -7 / 4) (by norm_num) lehmerTrace.continuous.continuousOn
    (show 0 ∈ Set.Ioo _ _ by constructor <;> norm_num [lehmerTrace])
  obtain ⟨b, hb, hb₀⟩ := intermediate_value_Ioo' (f := lehmerTrace.eval)
    (a := -7 / 4) (b := -1) (by norm_num) lehmerTrace.continuous.continuousOn
    (show 0 ∈ Set.Ioo _ _ by constructor <;> norm_num [lehmerTrace])
  obtain ⟨c, hc, hc₀⟩ := intermediate_value_Ioo (f := lehmerTrace.eval)
    (a := -1) (b := 0) (by norm_num) lehmerTrace.continuous.continuousOn
    (show 0 ∈ Set.Ioo _ _ by constructor <;> norm_num [lehmerTrace])
  obtain ⟨d, hd, hd₀⟩ := intermediate_value_Ioo' (f := lehmerTrace.eval)
    (a := 0) (b := 1) (by norm_num) lehmerTrace.continuous.continuousOn
    (show 0 ∈ Set.Ioo _ _ by constructor <;> norm_num [lehmerTrace])
  -- Locate the larger real root directly in x, so its trace is r + r⁻¹ > 2.
  let p := lehmerPolynomial.map (Int.castRingHom ℝ)
  obtain ⟨r, hr, hr₀⟩ := intermediate_value_Ioo (f := p.eval)
    (a := 1) (b := 1176281 / 1000000) (by norm_num) p.continuous.continuousOn
    (show 0 ∈ Set.Ioo _ _ by
      dsimp only [p]
      delta lehmerPolynomial
      constructor <;> norm_num)
  have hrpos : 0 < r := zero_lt_one.trans hr.1
  let e := r + r⁻¹
  have he : 2 < e := by
    have hmul : r⁻¹ * r = 1 := inv_mul_cancel₀ hrpos.ne'
    have hsq : 0 < (r - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hr.1.ne')
    exact lt_of_mul_lt_mul_right (show 2 * r < e * r by dsimp [e]; nlinarith) hrpos.le
  have he₀ : lehmerTrace.eval e = 0 := by
    change (lehmerPolynomial.map (Int.castRingHom ℝ)).eval r = 0 at hr₀
    rw [eval_lehmerPolynomial_eq_trace r hrpos.ne'] at hr₀
    exact (mul_eq_zero.mp hr₀).resolve_left (pow_ne_zero _ hrpos.ne')
  have hab : a < b := ha.2.trans hb.1
  have hbc : b < c := hb.2.trans hc.1
  have hcd : c < d := hc.2.trans hd.1
  have hde : d < e := hd.2.trans ((by norm_num : (1 : ℝ) < 2).trans he)
  let s : Finset ℝ := {a, b, c, d}
  have hs : s.card = 4 := by
    simp [s, Finset.card_insert_of_notMem, hab.ne, (hab.trans hbc).ne,
      (hab.trans (hbc.trans hcd)).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne]
  have hes : e ∉ s := by
    simp [s, hde.ne', (hcd.trans hde).ne', (hbc.trans (hcd.trans hde)).ne',
      (hab.trans (hbc.trans (hcd.trans hde))).ne']
  have hcard : (insert e s).card = 5 := by rw [Finset.card_insert_of_notMem hes, hs]
  have hroots : ∀ y ∈ insert e s, lehmerTrace.eval y = 0 := by
    intro y hy
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    exacts [he₀, ha₀, hb₀, hc₀, hd₀]
  have hunit : ∀ y ∈ s, (lehmerQuadratic y).mahlerMeasure = 1 := by
    intro y hy
    apply mahlerMeasure_lehmerQuadratic_of_mem_Icc
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    all_goals constructor <;> linarith [ha.1, hb.1, hc.1, hd.1, ha.2, hb.2, hc.2, hd.2]
  have hprod : ∀ t : Finset ℝ,
      (∏ y ∈ t, lehmerQuadratic y).mahlerMeasure = ∏ y ∈ t, (lehmerQuadratic y).mahlerMeasure := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert y t hy ih => simp [Finset.prod_insert hy, mahlerMeasure_mul, ih]
  have hm : intMahlerMeasure lehmerPolynomial = r := by
    rw [intMahlerMeasure, Polynomial.mapMahlerMeasure,
      map_lehmerPolynomial_eq_prod hcard (lehmerTrace_eq_prod hcard hroots), hprod,
      Finset.prod_insert hes, mahlerMeasure_lehmerQuadratic_of_reciprocal hr.1,
      Finset.prod_eq_one hunit, mul_one]
  rwa [hm]

/-- **Mahler measure of Lehmer's polynomial.** The Mahler measure of Lehmer's polynomial is at most
$1176281/1000000 = 1.176281$.

Source: Lehmer (1933), the Mahler measure of Lehmer's polynomial is
`1.176280818...`, hence at most `1.176281`. -/
theorem intMahlerMeasure_lehmerPolynomial_le :
    intMahlerMeasure lehmerPolynomial ≤ 1176281 / 1000000 :=
  intMahlerMeasure_lehmerPolynomial_mem_Ioo.2.le

/-- **Lehmer's upper bound for Lehmer's constant.** Lehmer's constant is at most
$1176281/1000000 = 1.176281$.

Source: Lehmer (1933), catalogue upper bound `C₄₀ₐ ≤ 1.176280...`
from the Mahler measure of Lehmer's polynomial, rounded up at the sixth
decimal place. -/
theorem lehmer1933UpperBound_wanted : lehmerConstant ≤ 1176281 / 1000000 :=
  (lehmerConstant_le_intMahlerMeasure intMahlerMeasure_lehmerPolynomial_mem_Ioo.1).trans
    intMahlerMeasure_lehmerPolynomial_le

/-- **Smyth's polynomial.** Smyth's polynomial is $X^3 - X - 1 \in \mathbb{Z}[X]$.

Its Mahler measure is the plastic number $\theta_0 = 1.324717\ldots$, the real root of
$X^3 - X - 1$. Smyth proved in 1971 that every polynomial $f \in \mathbb{Z}[X]$ with
$f(0) \neq 0$ that is nonreciprocal (reversing its coefficients gives neither $f$ nor $-f$)
has Mahler measure at least $\theta_0$. -/
noncomputable def smythPolynomial : Polynomial ℤ :=
  X ^ 3 - X - 1

/-- **Reciprocal polynomial.** An integer polynomial $f$ is reciprocal when reversing its
coefficients gives $f$ or $-f$, that is, when $X^d f(1/X) = f$ or $X^d f(1/X) = -f$, where $d$
is the degree of $f$, taken to be $0$ when $f = 0$. -/
def IsReciprocal (f : Polynomial ℤ) : Prop :=
  f.reverse = f ∨ f.reverse = -f

theorem isReciprocal_one : IsReciprocal (1 : Polynomial ℤ) := by
  left
  simp [Polynomial.reverse]

end MathlibExt.NumberTheory.LehmerConstant
