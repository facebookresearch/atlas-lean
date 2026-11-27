/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Neighbours in the polynomial Farey series

This module defines the polynomial Farey series and its degree neighbours, proves
the neighbour criterion in terms of a nonzero constant determinant, and counts the
neighbours of a given denominator degree over a prime field.

## References

* Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
  *An Interpretation of Continued Fractions and Farey Graphs in the Field of Rational Functions*,
  INTEGERS 26 (2026), Article A3, pp. 1–14, Theorem 3 (neighbour count) and
  Definitions 1–3 and Theorem 2 (the series and neighbour criterion).
* William A. Webb, *The Farey Series of polynomials over a finite field*,
  Elemente der Mathematik 41 (1986), pp. 6–11, Lemma 1 and Theorems 1 and 2.
  This is the original source for the determinant parametrization and the two results above.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- **Farey series over a field.** Let $F$ be a field and $n$ a natural number. The Farey series
$\mathcal{F}_n$ of order $n$ over $F$ is the set of pairs $(u, v)$ of polynomials in $F[x]$, read
as the fraction $u / v$, such that $\deg u < \deg v \le n$, $u$ and $v$ are coprime, and $v$ is
monic. Here $\deg 0 = -\infty$, so $u = 0$ is allowed.

Each fraction is thus represented by exactly one such pair.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1 (quoted from [6], there over
`𝔽_{p^r}`). -/
public def polyFareySeries (n : ℕ) : Set (F[X] × F[X]) :=
  {w | w.1.degree < w.2.degree ∧ w.2.natDegree ≤ n ∧ IsCoprime w.1 w.2 ∧ w.2.Monic}

/-- **The fraction of a pair of polynomials.** Let $F$ be a field. The value of a pair $(u, v)$ of
polynomials in $F[x]$ is the rational function $u / v$ in the field $F(x)$ of rational functions
over $F$ (it is $0$ when $v = 0$).

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public noncomputable def polyFrac (w : F[X] × F[X]) : RatFunc F :=
  algebraMap F[X] (RatFunc F) w.1 / algebraMap F[X] (RatFunc F) w.2

/-- **Degree neighbours in the polynomial Farey series.** Let $F$ be a field, let $n \in \mathbb N$,
and let $\mathcal F_n$ be the Farey series of order $n$ over $F$. For pairs $(u, v)$ and $(h, k)$
of polynomials over $F$, read as the fractions $u/v$ and $h/k$, the fraction $h/k$ is a
$(\deg k)$-neighbour of $u/v$ in $\mathcal F_n$ when both fractions lie in $\mathcal F_n$,
$h/k \ne u/v$ as rational functions, and $|u/v - h/k| \le |u/v - h'/k'|$ for every
$h'/k' \in \mathcal F_n$ with $\deg k' = \deg k$ and $h'/k' \ne u/v$. Here $|\cdot|$ is the
valuation of $F(X)$ at infinity, which orders nonzero rational functions $f/g$ by
$\deg f - \deg g$ and puts $0$ below every nonzero value.

The fraction $u/v$ itself is excluded from the comparison, as the paper's counts (Theorem 3 with
$t = 0$, Figure 1) require.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 2 (quoted from [6]). -/
public def IsPolyFareyDegNeighbor [DecidableEq (RatFunc F)] (n : ℕ) (w z : F[X] × F[X]) :
    Prop :=
  w ∈ polyFareySeries n ∧ z ∈ polyFareySeries n ∧ polyFrac z ≠ polyFrac w ∧
    ∀ z' ∈ polyFareySeries n, z'.2.natDegree = z.2.natDegree → polyFrac z' ≠ polyFrac w →
    RatFunc.inftyValuation F (polyFrac w - polyFrac z) ≤
      RatFunc.inftyValuation F (polyFrac w - polyFrac z')

/-- **Neighbouring fractions in the polynomial Farey series.** Let $F$ be a field and let
$n \in \mathbb N$. Two pairs $(u, v)$ and $(h, k)$ of polynomials over $F$, read as the fractions
$u/v$ and $h/k$, are neighbours in the Farey series $\mathcal F_n$ of order $n$ over $F$ when
$u/v$ is a $(\deg v)$-neighbour of $h/k$ in $\mathcal F_n$ and $h/k$ is a $(\deg k)$-neighbour of
$u/v$ in $\mathcal F_n$. In particular, both fractions then lie in $\mathcal F_n$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 3 (quoted from [6]). -/
public def ArePolyFareyNeighbors [DecidableEq (RatFunc F)] (n : ℕ) (w z : F[X] × F[X]) :
    Prop :=
  IsPolyFareyDegNeighbor n z w ∧ IsPolyFareyDegNeighbor n w z

private theorem frac_sub (w z : F[X] × F[X]) (hw : w.2 ≠ 0) (hz : z.2 ≠ 0) :
    polyFrac w - polyFrac z =
      algebraMap F[X] (RatFunc F) (w.1 * z.2 - z.1 * w.2) /
        algebraMap F[X] (RatFunc F) (w.2 * z.2) := by
  have hw' : algebraMap F[X] (RatFunc F) w.2 ≠ 0 := by simpa using hw
  have hz' : algebraMap F[X] (RatFunc F) z.2 ≠ 0 := by simpa using hz
  simp only [polyFrac, map_sub, map_mul]
  field_simp

private theorem frac_ne_iff (w z : F[X] × F[X]) (hw : w.2 ≠ 0) (hz : z.2 ≠ 0) :
    polyFrac w ≠ polyFrac z ↔ w.1 * z.2 - z.1 * w.2 ≠ 0 := by
  rw [← sub_ne_zero, frac_sub w z hw hz, div_ne_zero_iff]
  rw [and_iff_left (RatFunc.algebraMap_ne_zero (mul_ne_zero hw hz))]
  constructor
  · intro h he
    apply h
    rw [he, map_zero]
  · exact RatFunc.algebraMap_ne_zero

private theorem distance (w z : F[X] × F[X]) [DecidableEq (RatFunc F)]
    (hw : w.2 ≠ 0) (hz : z.2 ≠ 0) (hne : polyFrac w ≠ polyFrac z) :
    RatFunc.inftyValuation F (polyFrac w - polyFrac z) =
      WithZero.exp ((w.1 * z.2 - z.1 * w.2).natDegree -
        (w.2.natDegree : ℤ) - z.2.natDegree) := by
  have hd := (frac_ne_iff w z hw hz).mp hne
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_ne_zero F
      (sub_ne_zero.mpr hne),
    frac_sub w z hw hz,
    RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hd)
      (RatFunc.algebraMap_ne_zero (mul_ne_zero hw hz)),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
    natDegree_mul hw hz, Nat.cast_add]
  congr 1
  omega

private theorem determinant_one_coprime (u v a b : F[X]) (h : u * b - a * v = 1) :
    IsCoprime a b := by
  refine ⟨-v, u, ?_⟩
  linear_combination h

private theorem small_bezout (u v : F[X]) (huv : u.degree < v.degree)
    (hv : v.Monic) (hc : IsCoprime u v) (hd : 0 < v.natDegree) :
    ∃ a b : F[X], a.degree < v.degree ∧ b.degree < v.degree ∧ u * b - a * v = 1 := by
  obtain ⟨s, t, hst⟩ := hc
  let b := s % v
  let a := -(t + u * (s / v))
  have hb : b.degree < v.degree := degree_mod_lt s hv.ne_zero
  have hdet : u * b - a * v = 1 := by
    have hm := EuclideanDomain.div_add_mod s v
    dsimp only [a, b]
    linear_combination hst + u * hm
  have ha : a.degree < v.degree := by
    by_cases ha0 : a = 0
    · simpa [ha0] using (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hv.ne_zero))
    have hav : a * v = u * b - 1 := by linear_combination -hdet
    have hbound : (a * v).natDegree ≤ max (u.natDegree + b.natDegree) 0 := by
      rw [hav]
      exact (natDegree_sub_le _ _).trans (max_le_max natDegree_mul_le (by simp))
    have hu0 : u ≠ 0 := by
      intro hu0
      have hzero : (a * v).natDegree = 0 := by simp [hav, hu0]
      rw [natDegree_mul ha0 hv.ne_zero] at hzero
      omega
    have hb0 : b ≠ 0 := by
      intro hb0
      have hzero : (a * v).natDegree = 0 := by simp [hav, hb0]
      rw [natDegree_mul ha0 hv.ne_zero] at hzero
      omega
    have huNat := natDegree_lt_natDegree hu0 huv
    have hbNat := natDegree_lt_natDegree hb0 hb
    rw [natDegree_mul ha0 hv.ne_zero] at hbound
    apply degree_lt_degree
    omega
  exact ⟨a, b, ha, hb, hdet⟩

private theorem zero_of_degree_zero (n : ℕ) (w : F[X] × F[X])
    (hw : w ∈ polyFareySeries n) (hd : w.2.natDegree = 0) : w = (0, 1) := by
  have hv : w.2 = 1 := hw.2.2.2.natDegree_eq_zero.mp hd
  have hu : w.1 = 0 := by
    have h := hw.1
    rw [hv, degree_one] at h
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro i
    simpa using (degree_lt_iff_coeff_zero w.1 0).mp h i (Nat.zero_le i)
  exact Prod.ext hu hv

private theorem competitor (n e : ℕ) (w : F[X] × F[X]) (hw : w ∈ polyFareySeries n)
    (hle : w.2.natDegree ≤ e) (he : 0 < e) (hen : e ≤ n) :
    ∃ z ∈ polyFareySeries n, z.2.natDegree = e ∧ w.1 * z.2 - z.1 * w.2 = 1 := by
  by_cases hd : w.2.natDegree = 0
  · have hw0 := zero_of_degree_zero n w hw hd
    subst w
    refine ⟨(-1, X ^ e), ?_, by simp, by simp⟩
    refine ⟨?_, by simpa using hen, ?_, monic_X_pow e⟩
    · simp only [degree_neg, degree_one, degree_X_pow]
      exact WithBot.coe_lt_coe.mpr he
    · exact determinant_one_coprime 0 1 (-1) (X ^ e) (by simp)
  obtain ⟨a, b, ha, hb, hdet⟩ := small_bezout w.1 w.2 hw.1 hw.2.2.2 hw.2.2.1
    (Nat.pos_of_ne_zero hd)
  let t : F[X] := X ^ (e - w.2.natDegree)
  have ht : t.Monic := monic_X_pow _
  have htv : (t * w.2).degree = (e : WithBot ℕ) := by
    rw [degree_mul, degree_eq_natDegree ht.ne_zero, degree_eq_natDegree hw.2.2.2.ne_zero]
    dsimp only [t]
    rw [natDegree_X_pow, ← Nat.cast_add, Nat.sub_add_cancel hle]
  have hvle : w.2.degree ≤ (t * w.2).degree := by
    rw [htv, degree_eq_natDegree hw.2.2.2.ne_zero]
    exact WithBot.coe_le_coe.mpr hle
  have hb' : b.degree < (t * w.2).degree := hb.trans_le hvle
  have hk : (b + t * w.2).Monic := (ht.mul hw.2.2.2).add_of_right hb'
  have hkdeg : (b + t * w.2).degree = (e : WithBot ℕ) :=
    (degree_add_eq_right_of_degree_lt hb').trans htv
  have htu : (t * w.1).degree < (e : WithBot ℕ) := by
    by_cases hu : w.1 = 0
    · simp [hu]
    rw [degree_eq_natDegree (mul_ne_zero ht.ne_zero hu), natDegree_mul ht.ne_zero hu]
    have h := natDegree_lt_natDegree hu hw.1
    dsimp only [t]
    rw [natDegree_X_pow]
    have hlt : e - w.2.natDegree + w.1.natDegree < e := by omega
    exact_mod_cast hlt
  have hnum : (a + t * w.1).degree < (b + t * w.2).degree := by
    rw [hkdeg]
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt (ha.trans_le (hvle.trans_eq htv)) htu)
  have hdet' : w.1 * (b + t * w.2) - (a + t * w.1) * w.2 = 1 := by
    linear_combination hdet
  refine ⟨(a + t * w.1, b + t * w.2), ?_, ?_, hdet'⟩
  · exact ⟨hnum, (natDegree_eq_of_degree_eq_some hkdeg).le.trans hen,
      determinant_one_coprime _ _ _ _ hdet', hk⟩
  · exact natDegree_eq_of_degree_eq_some hkdeg

private theorem directed_of_constant (n : ℕ) (w z : F[X] × F[X])
    [DecidableEq (RatFunc F)] (hw : w ∈ polyFareySeries n) (hz : z ∈ polyFareySeries n)
    (hdet : (w.1 * z.2 - z.1 * w.2).degree = 0) : IsPolyFareyDegNeighbor n w z := by
  have hd : w.1 * z.2 - z.1 * w.2 ≠ 0 := by
    intro h
    simp [h] at hdet
  have hne := (frac_ne_iff w z hw.2.2.2.ne_zero hz.2.2.2.ne_zero).mpr hd
  refine ⟨hw, hz, hne.symm, ?_⟩
  intro z' hz' hdeg hne'
  rw [distance w z hw.2.2.2.ne_zero hz.2.2.2.ne_zero hne,
    distance w z' hw.2.2.2.ne_zero hz'.2.2.2.ne_zero hne'.symm, WithZero.exp_le_exp]
  have hzero : (w.1 * z.2 - z.1 * w.2).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le (n := 0) hdet.le)
  rw [hzero, hdeg]
  omega

private theorem constant_of_directed (n : ℕ) (w z : F[X] × F[X])
    [DecidableEq (RatFunc F)] (h : IsPolyFareyDegNeighbor n w z)
    (hle : w.2.natDegree ≤ z.2.natDegree) : (w.1 * z.2 - z.1 * w.2).degree = 0 := by
  have he : 0 < z.2.natDegree := by
    by_contra he
    have hz0 : z.2.natDegree = 0 := by omega
    have hw0 : w.2.natDegree = 0 := by omega
    have hw := zero_of_degree_zero n w h.1 hw0
    have hz := zero_of_degree_zero n z h.2.1 hz0
    exact h.2.2.1 (by rw [hw, hz])
  obtain ⟨z', hz', hdeg, hdet⟩ := competitor n z.2.natDegree w h.1 hle he h.2.1.2.1
  have hne' : polyFrac w ≠ polyFrac z' :=
    (frac_ne_iff w z' h.1.2.2.2.ne_zero hz'.2.2.2.ne_zero).mpr (by rw [hdet]; exact one_ne_zero)
  have hcomp := h.2.2.2 z' hz' hdeg hne'.symm
  rw [distance w z h.1.2.2.2.ne_zero h.2.1.2.2.2.ne_zero h.2.2.1.symm,
    distance w z' h.1.2.2.2.ne_zero hz'.2.2.2.ne_zero hne', hdet, natDegree_one,
    hdeg, WithZero.exp_le_exp] at hcomp
  have hd := (frac_ne_iff w z h.1.2.2.2.ne_zero h.2.1.2.2.2.ne_zero).mp h.2.2.1.symm
  have hn : (w.1 * z.2 - z.1 * w.2).natDegree = 0 := by omega
  rw [degree_eq_natDegree hd, hn, Nat.cast_zero]

/-- **Neighbour criterion for the polynomial Farey series.** Let $F$ be a field, let
$n \in \mathbb N$, and let $(u, v)$ and $(h, k)$ be elements of the Farey series $\mathcal F_n$ of
order $n$ over $F$, read as the fractions $u/v$ and $h/k$. Then $u/v$ and $h/k$ are neighbours in
$\mathcal F_n$ if and only if the polynomial $uk - hv$ has degree $0$, that is, $uk - hv$ is a
nonzero constant.

The paper, quoting [6], works over $\mathbb F_{p^r}$; here the field $F$ is arbitrary.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 2 (`integers-2026-A3-thm-2`). -/
public theorem arePolyFareyNeighbors_iff [DecidableEq (RatFunc F)] (n : ℕ)
    {w z : F[X] × F[X]} (hw : w ∈ polyFareySeries n) (hz : z ∈ polyFareySeries n) :
    ArePolyFareyNeighbors n w z ↔ (w.1 * z.2 - z.1 * w.2).degree = 0 := by
  have hswap : z.1 * w.2 - w.1 * z.2 = -(w.1 * z.2 - z.1 * w.2) := by ring
  constructor
  · intro h
    rcases le_total w.2.natDegree z.2.natDegree with hle | hle
    · exact constant_of_directed n w z h.2 hle
    · have hc := constant_of_directed n z w h.1 hle
      simpa only [hswap, degree_neg] using hc
  · intro hdet
    refine ⟨directed_of_constant n z w hz hw ?_, directed_of_constant n w z hw hz hdet⟩
    simpa only [hswap, degree_neg] using hdet

-- A nonzero constant determinant gives both properness and coprimality.
private theorem mem_polyFareySeries_of_det {n : ℕ} {w z : F[X] × F[X]}
    (hw : w ∈ polyFareySeries n) (hq : 0 < w.2.natDegree)
    (hz : z.2.Monic) (hzn : z.2.natDegree ≤ n) {c : F} (hc : c ≠ 0)
    (hdet : w.1 * z.2 - z.1 * w.2 = C c) : z ∈ polyFareySeries n := by
  refine ⟨?_, hzn, ?_, hz⟩
  · by_cases hz0 : z.1 = 0
    · simpa [hz0] using bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hz.ne_zero)
    have hu : w.1.natDegree < w.2.natDegree := by
      by_cases hu0 : w.1 = 0
      · simpa [hu0] using hq
      · exact natDegree_lt_natDegree hu0 hw.1
    have heq : z.1 * w.2 = w.1 * z.2 - C c := by linear_combination -hdet
    have hbound : (z.1 * w.2).natDegree ≤ max (w.1.natDegree + z.2.natDegree) 0 := by
      rw [heq]
      exact (natDegree_sub_le _ _).trans (max_le_max natDegree_mul_le (by simp))
    rw [natDegree_mul hz0 hw.2.2.2.ne_zero] at hbound
    exact degree_lt_degree (by omega)
  · refine ⟨-C c⁻¹ * w.2, C c⁻¹ * w.1, ?_⟩
    calc
      _ = C c⁻¹ * (w.1 * z.2 - z.1 * w.2) := by ring
      _ = 1 := by rw [hdet, ← map_mul, inv_mul_cancel₀ hc, map_one]

private theorem neighbor_det {n : ℕ} [DecidableEq (RatFunc F)] {w z : F[X] × F[X]}
    (hw : w ∈ polyFareySeries n) (hz : z ∈ polyFareySeries n)
    (h : ArePolyFareyNeighbors n w z) : ∃ c : F, c ≠ 0 ∧ w.1 * z.2 - z.1 * w.2 = C c := by
  have hd := (arePolyFareyNeighbors_iff n hw hz).mp h
  refine ⟨_, ?_, eq_C_of_degree_eq_zero hd⟩
  intro hc
  have he := eq_C_of_degree_eq_zero hd
  rw [hc, map_zero] at he
  simp [he] at hd

-- The determinant-one pair and the original pair are a basis for polynomial pairs.
private theorem neighbor_coordinates {w z : F[X] × F[X]} {a b : F[X]} {c : F}
    (hab : w.1 * b - a * w.2 = 1) (hdet : w.1 * z.2 - z.1 * w.2 = C c) :
    ∃ m : F[X], z = (C c * a + m * w.1, C c * b + m * w.2) := by
  refine ⟨b * z.1 - a * z.2, Prod.ext ?_ ?_⟩
  · dsimp
    linear_combination a * hdet - z.1 * hab
  · dsimp
    linear_combination b * hdet - z.2 * hab

private theorem degree_scaled_lt_mul {v b m : F[X]} (hv : v ≠ 0) (hb : b.degree < v.degree)
    (hm : m ≠ 0) (c : F) : (C c * b).degree < (m * v).degree := by
  have hle : v.degree ≤ (m * v).degree := by
    rw [degree_eq_natDegree hv, degree_eq_natDegree (mul_ne_zero hm hv), natDegree_mul hm hv]
    exact WithBot.coe_le_coe.mpr (Nat.le_add_left _ _)
  have hc : (C c * b).degree ≤ b.degree := by
    simpa only [smul_eq_C_mul] using degree_smul_le c b
  exact (hc.trans_lt hb).trans_le hle

private theorem unique_smaller_neighbor {n : ℕ} [DecidableEq (RatFunc F)] {w : F[X] × F[X]}
    (hw : w ∈ polyFareySeries n) (hq : 0 < w.2.natDegree) {a b : F[X]}
    (hb : b.degree < w.2.degree) (hab : w.1 * b - a * w.2 = 1) :
    ∃! z, z ∈ polyFareySeries n ∧ z.2.natDegree < w.2.natDegree ∧ ArePolyFareyNeighbors n w z := by
  have hv := hw.2.2.2.ne_zero
  have hb0 : b ≠ 0 := by
    intro he
    have h : a * w.2 = -1 := by rw [he, mul_zero, zero_sub, neg_eq_iff_eq_neg] at hab; exact hab
    have ha0 : a ≠ 0 := by rintro rfl; simp at h
    have hn := congrArg natDegree h
    rw [natDegree_mul ha0 hv, natDegree_neg, natDegree_one] at hn
    omega
  have hbc := leadingCoeff_ne_zero.mpr hb0
  let c := b.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero hbc
  let z : F[X] × F[X] := (C c * a, C c * b)
  have hzmonic : z.2.Monic := by
    change (C c * b).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hbc]
  have hzd : z.2.natDegree < w.2.natDegree := by
    exact natDegree_lt_natDegree hzmonic.ne_zero (by simpa only [z, degree_C_mul hc] using hb)
  have hzdet : w.1 * z.2 - z.1 * w.2 = C c := by
    dsimp only [z, Prod.fst, Prod.snd]
    linear_combination C c * hab
  have hz := mem_polyFareySeries_of_det hw hq hzmonic (hzd.le.trans hw.2.1) hc hzdet
  refine ⟨z, ⟨hz, hzd, (arePolyFareyNeighbors_iff n hw hz).mpr (by rw [hzdet, degree_C hc])⟩, ?_⟩
  rintro y ⟨hy, hyd, hyn⟩
  obtain ⟨d, hd, hdet⟩ := neighbor_det hw hy hyn
  obtain ⟨m, rfl⟩ := neighbor_coordinates hab hdet
  have hm : m = 0 := by
    by_contra hm
    change (C d * b + m * w.2).natDegree < w.2.natDegree at hyd
    rw [natDegree_add_eq_right_of_degree_lt (degree_scaled_lt_mul hv hb hm d),
      natDegree_mul hm hv] at hyd
    omega
  have hd' := hy.2.2.2.leadingCoeff
  change (C d * b + m * w.2).leadingCoeff = 1 at hd'
  rw [hm, zero_mul, add_zero, leadingCoeff_mul, leadingCoeff_C] at hd'
  have hdc : d = c := by
    calc
      d = (d * b.leadingCoeff) * c := by
        dsimp only [c]
        rw [mul_assoc, mul_inv_cancel₀ hbc, mul_one]
      _ = c := by rw [hd', one_mul]
  simp [hm, hdc, z]

private noncomputable def monicOfDegreeEquiv (t : ℕ) :
    {m : F[X] // IsMonicOfDegree m t} ≃ (Fin t → F) :=
  (Equiv.ofBijective (fun r : degreeLT F t =>
    (⟨r.val + X ^ t, by
      have hlt : r.val.degree < (X ^ t : F[X]).degree := by
        rw [degree_X_pow]
        exact mem_degreeLT.mp r.property
      exact ⟨(natDegree_add_eq_right_of_degree_lt hlt).trans (natDegree_X_pow t),
        (monic_X_pow t).add_of_right hlt⟩⟩ : {m : F[X] // IsMonicOfDegree m t})) (by
    constructor
    · intro r s h
      exact Subtype.ext (add_right_cancel (congrArg Subtype.val h))
    · intro m
      have hp : m.val.degree = (X ^ t : F[X]).degree := by
        rw [degree_eq_natDegree m.property.ne_zero, m.property.natDegree_eq, degree_X_pow]
      have hlt : (m.val - X ^ t).degree < m.val.degree :=
        degree_sub_lt_left hp m.property.ne_zero
          (m.property.leadingCoeff_eq.trans (monic_X_pow t).leadingCoeff.symm)
      have hr : m.val - X ^ t ∈ degreeLT F t := mem_degreeLT.mpr (by simpa [hp] using hlt)
      exact ⟨⟨m.val - X ^ t, hr⟩, Subtype.ext (sub_add_cancel _ _)⟩)).symm.trans
    (degreeLTEquiv F t).toEquiv

private noncomputable def largerNeighborEquiv {n t : ℕ} [DecidableEq (RatFunc F)]
    {w : F[X] × F[X]} (hw : w ∈ polyFareySeries n) (hq : 0 < w.2.natDegree)
    (ht : w.2.natDegree + t ≤ n) {a b : F[X]} (hb : b.degree < w.2.degree)
    (hab : w.1 * b - a * w.2 = 1) :
    ({c : F // c ≠ 0} × {m : F[X] // IsMonicOfDegree m t}) ≃
      {z // z ∈ polyFareySeries n ∧ z.2.natDegree = w.2.natDegree + t ∧
        ArePolyFareyNeighbors n w z} := by
  have hv := hw.2.2.2
  let pair (c : F) (m : F[X]) := (C c * a + m * w.1, C c * b + m * w.2)
  have hdet (c : F) (m : F[X]) : w.1 * (pair c m).2 - (pair c m).1 * w.2 = C c := by
    dsimp only [pair, Prod.fst, Prod.snd]
    linear_combination C c * hab
  have hdegree (c : F) {m : F[X]} (hm : m ≠ 0) :
      (pair c m).2.natDegree = w.2.natDegree + m.natDegree := by
    change (C c * b + m * w.2).natDegree = _
    rw [natDegree_add_eq_right_of_degree_lt (degree_scaled_lt_mul hv.ne_zero hb hm c),
      natDegree_mul hm hv.ne_zero, add_comm]
  have hlc (c : F) {m : F[X]} (hm : m ≠ 0) : (pair c m).2.leadingCoeff = m.leadingCoeff := by
    change (C c * b + m * w.2).leadingCoeff = _
    rw [leadingCoeff_add_of_degree_lt (degree_scaled_lt_mul hv.ne_zero hb hm c),
      leadingCoeff_mul_monic hv]
  refine Equiv.ofBijective (fun ⟨c, m⟩ => ⟨pair c m, ?_⟩) ⟨?_, ?_⟩
  · have hm := m.property.ne_zero
    have hmonic : (pair c m).2.Monic := (hlc c hm).trans m.property.leadingCoeff_eq
    have hd := (hdegree c hm).trans (congrArg (w.2.natDegree + ·) m.property.natDegree_eq)
    have hz := mem_polyFareySeries_of_det hw hq hmonic (hd.trans_le ht) c.property (hdet c m)
    exact ⟨hz, hd, (arePolyFareyNeighbors_iff n hw hz).mpr (by rw [hdet, degree_C c.property])⟩
  · rintro ⟨c, m⟩ ⟨d, k⟩ he
    have he' : pair c m = pair d k := congrArg Subtype.val he
    have hcd : (c : F) = d := by
      apply C_injective
      rw [← hdet c m, he', hdet]
    have hmk := congrArg Prod.snd he'
    change C c.val * b + m.val * w.2 = C d.val * b + k.val * w.2 at hmk
    rw [hcd] at hmk
    exact Prod.ext (Subtype.ext hcd)
      (Subtype.ext (mul_right_cancel₀ hv.ne_zero (add_left_cancel hmk)))
  · rintro ⟨z, hz, hzd, hzneigh⟩
    obtain ⟨c, hc, hzc⟩ := neighbor_det hw hz hzneigh
    obtain ⟨m, rfl⟩ := neighbor_coordinates hab hzc
    change (pair c m).2.natDegree = w.2.natDegree + t at hzd
    have hm : m ≠ 0 := by
      rintro rfl
      have hlt : (pair c 0).2.natDegree < w.2.natDegree :=
        natDegree_lt_natDegree hz.2.2.2.ne_zero (by simp [pair, degree_C_mul hc, hb])
      omega
    have hmd : m.natDegree = t := Nat.add_left_cancel ((hdegree c hm).symm.trans hzd)
    have hmonic : m.Monic := (hlc c hm).symm.trans hz.2.2.2.leadingCoeff
    exact ⟨(⟨c, hc⟩, ⟨m, hmd, hmonic⟩), rfl⟩

/-- **Number of neighbours of a polynomial Farey fraction.** Let $p$ be a prime, let
$n \in \mathbb{N}$, and let $u / v$ be a fraction of the Farey series $\mathcal{F}_n$ over
$\mathbb{F}_p$ with $q = \deg v \ge 1$. Then for every $t \in \mathbb{N}$ with $q + t \le n$,
exactly $(p - 1) p^t$ fractions $h / k \in \mathcal{F}_n$ with $\deg k = q + t$ are neighbours
of $u / v$ in $\mathcal{F}_n$, and exactly one fraction $h / k \in \mathcal{F}_n$ with
$\deg k < q$ is a neighbour of $u / v$ in $\mathcal{F}_n$.

Compared with the paper, $t$ is restricted to $q + t \le n$ (there are no fractions of larger
degree in $\mathcal{F}_n$), the hypothesis $q \ge 1$ is added (for $0 / 1$ there is no neighbour
of degree less than $0$), and the field is the prime field $\mathbb{F}_p$, the case of the
paper's count $(p - 1) p^t$ and of its Example 2.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 3 (`integers-2026-A3-thm-3`). -/
public theorem polyFarey_neighbor_count (p : ℕ) [Fact p.Prime]
    [DecidableEq (RatFunc (ZMod p))] (n : ℕ) {w : (ZMod p)[X] × (ZMod p)[X]}
    (hw : w ∈ polyFareySeries (F := ZMod p) n) (hq : 1 ≤ w.2.natDegree) :
    (∀ t : ℕ, w.2.natDegree + t ≤ n →
      Set.ncard {z | z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree = w.2.natDegree + t ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z} = (p - 1) * p ^ t) ∧
      ∃! z, z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree < w.2.natDegree ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z := by
  obtain ⟨a, b, _, hb, hab⟩ := small_bezout w.1 w.2 hw.1 hw.2.2.2 hw.2.2.1 hq
  refine ⟨?_, unique_smaller_neighbor hw hq hb hab⟩
  intro t ht
  let e := largerNeighborEquiv hw hq ht hb hab
  have hc : Nat.card {c : ZMod p // c ≠ 0} = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun c : ZMod p => c = 0),
      ZMod.card, Fintype.card_subtype_eq]
  change Nat.card {z // z ∈ polyFareySeries n ∧ z.2.natDegree = w.2.natDegree + t ∧
    ArePolyFareyNeighbors n w z} = _
  rw [← Nat.card_congr e, Nat.card_prod, hc,
    Nat.card_congr (monicOfDegreeEquiv (F := ZMod p) t), Nat.card_eq_fintype_card,
    Fintype.card_pi_const, ZMod.card]

end

end MetaMathlibExt
