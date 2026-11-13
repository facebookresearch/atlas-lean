/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.Translations
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Field.ZMod

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

/-- **Convergents of a polynomial continued fraction form a Farey path.** Let $F$ be a field, let
$n \in \mathbb N$, and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for
$1 \le i \le n$. Write $A_i$ and $B_i$ for the numerator and the denominator of the $i$th
convergent $A_i / B_i$ of the continued fraction $[a_0, a_1, \dots, a_n]$ over $F(X)$. Then for
every $i \le n$, $A_i$ and $B_i$ are polynomials in $F[X]$, $B_i \ne 0$, and $A_i$ and $B_i$ are
coprime in $F[X]$; and for $1 \le i \le n$, the polynomial $A_i B_{i-1} - A_{i-1} B_i$ is a unit
of $F[X]$, that is, a nonzero constant.

In the language of the paper, each convergent $A_i / B_i$ is a vertex of the Farey graph over $F$
and consecutive convergents are adjacent in it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 4. -/
public theorem_wanted polyContFract_convergents_farey_path (a : ℕ → F[X]) (n : ℕ)
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) :
    ∃ A B : ℕ → F[X], ∀ i ≤ n,
      (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i) ∧
      (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i) ∧
      B i ≠ 0 ∧ IsCoprime (A i) (B i) ∧
      (1 ≤ i → IsUnit (A i * B (i - 1) - A (i - 1) * B i))

/-- **Extending a Farey path extends the continued fraction.** Let $F$ be a field, let $n \ge 1$,
and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for $1 \le i \le n$. Let
$A_0, \dots, A_n, B_0, \dots, B_n \in F[X]$ be such that, for every $i \le n$, $A_i$ and $B_i$ are
the numerator and the denominator of the $i$th convergent of the continued fraction
$[a_0, a_1, \dots, a_n]$ over $F(X)$. Let $u, v \in F[X]$ be such that $u B_n - v A_n$ is a unit
of $F[X]$ (a nonzero constant) and $\deg B_n < \deg v$. Then there is a nonconstant polynomial
$b \in F[X]$ such that, in $F(X)$,
$$b = \frac{v A_{n-1} - u B_{n-1}}{u B_n - v A_n},$$
and the $(n+1)$st convergent of the continued fraction $[a_0, a_1, \dots, a_n, b]$ equals $u/v$.

Compared with the paper: the case $n = 0$, which needs $A_{-1} = 1$ and $B_{-1} = 0$, is excluded;
the paper's degree condition on the reduced denominator of $A_n / B_n$ is stated with $B_n$ itself
(the two agree, since $A_n / B_n$ is already in lowest terms); and the hypothesis that $u$ and $v$
are coprime is omitted, since adjacency implies it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 5. -/
public theorem_wanted polyContFract_extend_farey_path (a : ℕ → F[X]) {n : ℕ}
    (hn : 1 ≤ n) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree)
    (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (u v : F[X]) (hadj : IsUnit (u * B n - v * A n))
    (hdeg : (B n).degree < v.degree) :
    ∃ b : F[X], 0 < b.natDegree ∧
      algebraMap F[X] (RatFunc F) b =
        algebraMap F[X] (RatFunc F) (v * A (n - 1) - u * B (n - 1)) /
          algebraMap F[X] (RatFunc F) (u * B n - v * A n) ∧
      (polyContFract (Function.update a (n + 1) b) (n + 1)).convs (n + 1) =
        algebraMap F[X] (RatFunc F) u / algebraMap F[X] (RatFunc F) v

/-- **Continued fraction along a Farey path of polynomials.** Let $F$ be a field, let
$n \in \mathbb N$, let $u_i, v_i \in F[X]$ for $i \ge 0$, and let $c_i \in F$ for $i \ge 1$.
Suppose that $v_0 = 1$ and that for $1 \le i \le n$ we have $c_i \ne 0$,
$\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = c_i$. Let $a_0, a_1, \ldots \in F[X]$
satisfy $a_0 = u_0$, $a_1 = c_1^{-1} v_1$, $a_2 = -c_2^{-1} c_1 (u_2 v_0 - u_0 v_2)$ and, for
$3 \le i \le n$,
$$a_i = (-1)^{i+1}c_i^{-1}c_{i-1}(u_i v_{i-2} - u_{i-2} v_i)\prod_{j=1}^{i-2} c_j^{2(-1)^{i-j+1}}.$$
Then $a_i$ is nonconstant for $1 \le i \le n$. Moreover, for every $i \le n$ let
$t_i = \varepsilon_i \prod_{j=1}^{i} c_j^{(-1)^{i-j+1}}$, where $\varepsilon_i = 1$ if
$i \equiv 0, 1 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 2, 3 \pmod 4$. Then the numerator
$A_i$ and the denominator $B_i$ of the $i$th convergent of the continued fraction
$[a_0; a_1, \ldots, a_n]$ over $F(X)$ are $A_i = t_i u_i$ and $B_i = t_i v_i$, and this
convergent equals $u_i / v_i$.

The paper's coprimality hypothesis $(u_i, v_i) = 1$ is omitted: it follows from the determinant
condition.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6. -/
public theorem_wanted polyContFract_of_farey_path (u v : ℕ → F[X]) (c : ℕ → F) (n : ℕ)
    (hv0 : v 0 = 1) (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C (c i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = C (c 1)⁻¹ * v 1)
    (ha2 : a 2 = -C ((c 2)⁻¹ * c 1) * (u 2 * v 0 - u 0 * v 2))
    (ha : ∀ i, 3 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1) * (c i)⁻¹ * c (i - 1) *
        ∏ j ∈ Finset.Icc 1 (i - 2), c j ^ (2 * (-1 : ℤ) ^ (i - j + 1))) *
        (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, ∃ t : F,
        t = (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) *
          ∏ j ∈ Finset.Icc 1 i, c j ^ ((-1 : ℤ) ^ (i - j + 1)) ∧
        (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C t * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C t * v i) ∧
        (polyContFract a n).convs i =
          algebraMap F[X] (RatFunc F) (u i) / algebraMap F[X] (RatFunc F) (v i)

/-- **Farey paths of polynomials with alternating determinants starting at 1.** Let $F$ be a
field, let $n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$
and that for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and
$u_i v_{i-1} - u_{i-1} v_i = (-1)^{i-1}$. Let $a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$,
$a_1 = v_1$ and $a_i = (-1)^i (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is
nonconstant for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator
$B_i$ of the $i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$
are $A_i = u_i$ and $B_i = v_i$.

The paper presents the corollaries for $\mathbb{F}_2$ and $\mathbb{F}_3$; the statement holds
verbatim over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 1. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one_pow_pred
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C ((-1) ^ (i - 1)))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n → a i = C ((-1) ^ i) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (v i)

/-- **Farey paths of polynomials with alternating determinants starting at −1.** Let $F$ be a
field, let $n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$
and that for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and
$u_i v_{i-1} - u_{i-1} v_i = (-1)^i$. Let $a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$,
$a_1 = -v_1$ and $a_i = (-1)^i (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is
nonconstant for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator
$B_i$ of the $i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$
are $A_i = (-1)^i u_i$ and $B_i = (-1)^i v_i$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 2. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one_pow
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C ((-1) ^ i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = -v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n → a i = C ((-1) ^ i) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C ((-1) ^ i) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C ((-1) ^ i) * v i)

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
public theorem_wanted polyContFract_of_farey_path_det_one
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
          (C (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) * v i)

/-- **Farey paths of polynomials with all determinants −1.** Let $F$ be a field, let
$n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$ and that
for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = -1$. Let
$a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$, $a_1 = -v_1$ and
$a_i = (-1)^{i+1} (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is nonconstant
for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator $B_i$ of the
$i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ are
$A_i = \varepsilon_i u_i$ and $B_i = \varepsilon_i v_i$, where $\varepsilon_i = 1$ if
$i \equiv 0, 3 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 1, 2 \pmod 4$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 4. -/
public theorem_wanted polyContFract_of_farey_path_det_neg_one
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = -1)
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = -v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * v i)

/-- **Farey series over a field.** Let $F$ be a field and $n$ a natural number. The Farey series
$\mathcal{F}_n$ of order $n$ over $F$ is the set of pairs $(u, v)$ of polynomials in $F[x]$, read
as the fraction $u / v$, such that $\deg u < \deg v \le n$, $u$ and $v$ are coprime, and $v$ is
monic. Here $\deg 0 = -\infty$, so $u = 0$ is allowed.

Each fraction is thus represented by exactly one such pair.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1 (quoted from [6], there over `𝔽_{p^r}`). -/
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

/-- **The fraction $0/1$ lies in every Farey series.** For every field $F$ and every natural number
$n$, the pair $(0, 1)$, that is the fraction $0 / 1$, belongs to the Farey series $\mathcal{F}_n$
of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem zero_one_mem_polyFareySeries (n : ℕ) :
    ((0 : F[X]), (1 : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_zero_left.2 isUnit_one, monic_one⟩ <;> simp

/-- **The fraction 1/X in the polynomial Farey series.** Let $F$ be a field. For every natural
number $n \ge 1$, the pair $(1, X)$, that is, the fraction $1/X$, belongs to the Farey series
$\mathcal F_n$ of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem one_X_mem_polyFareySeries {n : ℕ} (hn : 1 ≤ n) :
    ((1 : F[X]), (X : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp [hn]

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

/-- **No fraction is its own degree neighbour.** Let $F$ be a field and let $n \in \mathbb N$. For
every pair $(u, v)$ of polynomials over $F$, the fraction $u/v$ is not a $(\deg v)$-neighbour of
itself in the Farey series $\mathcal F_n$ of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 2. -/
public theorem not_isPolyFareyDegNeighbor_self [DecidableEq (RatFunc F)] (n : ℕ)
    (w : F[X] × F[X]) : ¬ IsPolyFareyDegNeighbor n w w :=
  fun h => h.2.2.1 rfl

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

/-- **Neighbour criterion for the polynomial Farey series.** Let $F$ be a field, let
$n \in \mathbb N$, and let $(u, v)$ and $(h, k)$ be elements of the Farey series $\mathcal F_n$ of
order $n$ over $F$, read as the fractions $u/v$ and $h/k$. Then $u/v$ and $h/k$ are neighbours in
$\mathcal F_n$ if and only if the polynomial $uk - hv$ has degree $0$, that is, $uk - hv$ is a
nonzero constant.

The paper, quoting [6], works over $\mathbb F_{p^r}$; here the field $F$ is arbitrary.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 2 (`integers-2026-A3-thm-2`). -/
public theorem_wanted arePolyFareyNeighbors_iff [DecidableEq (RatFunc F)] (n : ℕ)
    {w z : F[X] × F[X]} (hw : w ∈ polyFareySeries n) (hz : z ∈ polyFareySeries n) :
    ArePolyFareyNeighbors n w z ↔ (w.1 * z.2 - z.1 * w.2).degree = 0

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
public theorem_wanted polyFarey_neighbor_count (p : ℕ) [Fact p.Prime]
    [DecidableEq (RatFunc (ZMod p))] (n : ℕ) {w : (ZMod p)[X] × (ZMod p)[X]}
    (hw : w ∈ polyFareySeries (F := ZMod p) n) (hq : 1 ≤ w.2.natDegree) :
    (∀ t : ℕ, w.2.natDegree + t ≤ n →
      Set.ncard {z | z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree = w.2.natDegree + t ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z} = (p - 1) * p ^ t) ∧
      ∃! z, z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree < w.2.natDegree ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z

end

end MetaMathlibExt
