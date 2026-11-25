/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial continued fractions and determinant-one Farey paths

We define finite continued fractions with polynomial partial quotients and prove
`MetaMathlibExt.polyContFract_of_farey_path_det_one`, the signed convergent formula
for Farey paths with increasing denominator degrees and adjacent determinants one.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- **Finite continued fraction with polynomial partial quotients.** Let $F$ be a field, let
$a_0, a_1, a_2, \ldots$ be polynomials in $F[X]$ and let $n \in \mathbb{N}$. The continued
fraction $[a_0; a_1, \ldots, a_n]$ is the generalized continued fraction over the field $F(X)$ of
rational functions with integral part $a_0$ and, for $1 \le i \le n$, an $i$th term with partial
numerator $1$ and partial denominator $a_i$; it has no further terms. For $i \ge 0$ write $A_i$
and $B_i$ for the numerator and denominator of its $i$th convergent $A_i / B_i$. Thus, with
$A_{-1} = 1$ and $B_{-1} = 0$, we have $A_0 = a_0$, $B_0 = 1$, and $A_{i+1} = a_{i+1} A_i + A_{i-1}$
and $B_{i+1} = a_{i+1} B_i + B_{i-1}$ for $0 \le i < n$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public noncomputable def polyContFract (a : ℕ → F[X]) (n : ℕ) :
    GenContFract (RatFunc F) :=
  ⟨algebraMap F[X] (RatFunc F) (a 0),
    Stream'.Seq.ofList
      ((List.range n).map fun i => ⟨1, algebraMap F[X] (RatFunc F) (a (i + 1))⟩)⟩

/-- **Integral part of a polynomial continued fraction.** Let $F$ be a field, let $n \in \mathbb N$,
and let $a_0, a_1, \dots, a_n \in F[X]$. The integral part (head term) of the continued fraction
$[a_0, a_1, \dots, a_n]$ over $F(X)$ is $a_0$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_h (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).h = algebraMap F[X] (RatFunc F) (a 0) := rfl

/-- **Terms of a polynomial continued fraction.** Let $F$ be a field, let $a_0, a_1, \ldots$ be
polynomials in $F[X]$ and let $n \in \mathbb{N}$. For every $i \in \mathbb{N}$, the term of index
$i$ (counting from $0$) of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ is the
pair with partial numerator $1$ and partial denominator $a_{i+1}$ if $i < n$, and does not exist
if $i \ge n$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_s_get? (a : ℕ → F[X]) (n i : ℕ) :
    (polyContFract a n).s.get? i =
      if i < n then some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 1))⟩ else none := by
  simp [polyContFract, Stream'.Seq.ofList_get?, List.getElem?_map]
  split_ifs <;> simp_all

/-- **Zeroth convergent numerator of a polynomial continued fraction.** Let $F$ be a field,
let $a_0, a_1, \ldots$ be polynomials in $F[X]$ and let $n \in \mathbb{N}$. The numerator $A_0$
of the zeroth convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ is
$a_0$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_nums_zero (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).nums 0 = algebraMap F[X] (RatFunc F) (a 0) := by
  simp [GenContFract.zeroth_num_eq_h, polyContFract_h]

/-- **Zeroth convergent denominator of a polynomial continued fraction.** Let $F$ be a field,
let $a_0, a_1, \ldots$ be polynomials in $F[X]$ and let $n \in \mathbb{N}$. The denominator $B_0$
of the zeroth convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ is $1$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_dens_zero (a : ℕ → F[X]) (n : ℕ) :
    (polyContFract a n).dens 0 = 1 := by
  simp [GenContFract.zeroth_den_eq_one]

/-- **First convergent numerator of a polynomial continued fraction.** Let $F$ be a field,
let $a_0, a_1, \ldots$ be polynomials in $F[X]$ and let $n \ge 1$. The numerator $A_1$ of the
first convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ is
$a_1 a_0 + 1$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_nums_one (a : ℕ → F[X]) {n : ℕ} (hn : 0 < n) :
    (polyContFract a n).nums 1 = algebraMap F[X] (RatFunc F) (a 1 * a 0 + 1) := by
  rw [GenContFract.first_num_eq (gp := ⟨1, algebraMap F[X] (RatFunc F) (a 1)⟩)
    (by simp [polyContFract_s_get?, hn])]
  simp [polyContFract_h]

/-- **First convergent denominator of a polynomial continued fraction.** Let $F$ be a field,
let $a_0, a_1, \ldots$ be polynomials in $F[X]$ and let $n \ge 1$. The denominator $B_1$ of the
first convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ is $a_1$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Section 1. -/
public theorem polyContFract_dens_one (a : ℕ → F[X]) {n : ℕ} (hn : 0 < n) :
    (polyContFract a n).dens 1 = algebraMap F[X] (RatFunc F) (a 1) := by
  rw [GenContFract.first_den_eq (gp := ⟨1, algebraMap F[X] (RatFunc F) (a 1)⟩)
    (by simp [polyContFract_s_get?, hn])]

/-- **Farey paths of polynomials with all determinants 1.** Let $F$ be a field, let
$n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$ and that
for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = 1$. Let
$a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$, $a_1 = v_1$ and
$a_i = (-1)^{i+1} (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is nonconstant
for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator $B_i$ of the
$i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ are
$A_i = \varepsilon_i u_i$ and $B_i = \varepsilon_i v_i$, where $\varepsilon_i = 1$ if
$i \equiv 0, 1 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 2, 3 \pmod 4$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 3. -/
public theorem polyContFract_of_farey_path_det_one
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = 1)
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) * v i) := by
  let sign (i : ℕ) : F := if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1
  let cross (i : ℕ) : F[X] := u (i + 2) * v i - u i * v (i + 2)
  have hquot (i : ℕ) (hi : i + 2 ≤ n) : a (i + 2) = C ((-1) ^ (i + 3)) * cross i :=
    ha (i + 2) (by omega) hi
  -- The adjacent determinants give the coordinates of the next pair in the preceding basis.
  have hstep (i : ℕ) (hi : i + 2 ≤ n) :
      u (i + 2) + u i = cross i * u (i + 1) ∧
      v (i + 2) + v i = cross i * v (i + 1) := by
    have hprev : u (i + 1) * v i - u i * v (i + 1) = 1 := hdet (i + 1) (by omega) (by omega)
    have hcurr : u (i + 2) * v (i + 1) - u (i + 1) * v (i + 2) = 1 :=
      hdet (i + 2) (by omega) hi
    dsimp only [cross]
    constructor
    · linear_combination -u (i + 2) * hprev - u i * hcurr
    · linear_combination -v (i + 2) * hprev - v i * hcurr
  have hsign (i : ℕ) :
      sign (i + 2) = (-1) ^ (i + 3) * sign (i + 1) ∧ sign i = -sign (i + 2) := by
    simp only [sign, neg_one_pow_eq_ite, Nat.even_iff]
    constructor <;> split_ifs <;> (try simp only [one_mul, neg_one_mul, neg_neg]) <;> omega
  have hrec (i : ℕ) (hi : i + 2 ≤ n) {p q r : F[X]} (h : r + p = cross i * q) :
      a (i + 2) * (C (sign (i + 1)) * q) + C (sign i) * p = C (sign (i + 2)) * r := by
    have hscale : C ((-1) ^ (i + 3)) * C (sign (i + 1)) = C (sign (i + 2)) := by
      rw [← map_mul, ← (hsign i).1]
    calc
      _ = C (sign (i + 2)) * (cross i * q - p) := by
        rw [hquot i hi, (hsign i).2, map_neg, ← hscale]
        ring
      _ = _ := by rw [← h, add_sub_cancel_right]
  refine ⟨?_, ?_⟩
  · intro i hi hin
    obtain _ | _ | i := i
    · omega
    · simpa [natDegree_pos_iff_degree_pos, hv0, ha1] using hdeg 1 hi hin
    have hprev : (v i).degree < (v (i + 1)).degree := hdeg (i + 1) (by omega) (by omega)
    have hcurr : (v (i + 1)).degree < (v (i + 2)).degree := hdeg (i + 2) hi hin
    have hprod : (cross i * v (i + 1)).natDegree = (v (i + 2)).natDegree := by
      rw [← (hstep i hin).2]
      exact natDegree_add_eq_left_of_degree_lt (hprev.trans hcurr)
    have hlt := natDegree_lt_natDegree (ne_zero_of_degree_gt hprev) hcurr
    have hle : (cross i * v (i + 1)).natDegree ≤ (cross i).natDegree + (v (i + 1)).natDegree :=
      natDegree_mul_le
    rw [hquot i hin, natDegree_C_mul (by simp)]
    omega
  · change ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C (sign i) * u i) ∧
      (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C (sign i) * v i)
    intro i
    induction i using Nat.twoStepInduction with
    | zero => simp [sign, polyContFract_h, ha0, hv0]
    | one =>
      intro hi
      have hu1 : u 1 = v 1 * u 0 + 1 := by
        have h : u 1 * v 0 - u 0 * v 1 = 1 := hdet 1 le_rfl hi
        rw [hv0, mul_one] at h
        linear_combination h
      have hn : 0 < n := by omega
      simp [sign, polyContFract_nums_one a hn, polyContFract_dens_one a hn, ha0, ha1, hu1]
    | more i ih₀ ih₁ =>
      intro hi
      obtain ⟨hu₀, hv₀⟩ := ih₀ (by omega)
      obtain ⟨hu₁, hv₁⟩ := ih₁ (by omega)
      have hs : (polyContFract a n).s.get? (i + 1) =
          some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
        simp [polyContFract_s_get?, show i + 1 < n by omega]
      obtain ⟨hu, hv⟩ := hstep i hi
      constructor
      · rw [GenContFract.nums_recurrence hs hu₀ hu₁]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec i hi hu)
      · rw [GenContFract.dens_recurrence hs hv₀ hv₁]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec i hi hv)

end

end MetaMathlibExt
