/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.BinomialProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

/-!
# Binomial products of rational power series

`MetaMathlibExt.binomialProduct_rational` treats inputs whose numerator degrees are strictly
smaller than the lengths of their root lists, allowing repeated or zero roots.
`MetaMathlibExt.binomialProduct_rational_general` pads the root lists with zeros to handle
arbitrary numerator degrees. The forward shift acts on binomial convolution by the product
rule, so the recurrence for the convolution has the pairwise sums of the input parameters as
roots.
-/

namespace MetaMathlibExt

open PowerSeries

namespace binomialProduct_rational_general

variable {K : Type*} [Field K]

-- Applying one factor of the recurrence polynomial in the forward shift.
private def difference (a : K) : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun u k := u (k + 1) - a * u k
  map_add' u v := by ext k; simp; ring
  map_smul' c u := by ext k; simp; ring

private def recurrence : List K → (ℕ → K) →ₗ[K] (ℕ → K)
  | [] => LinearMap.id
  | a :: l => (recurrence l).comp (difference a)

private theorem recurrence_difference (l : List K) (a : K) (u : ℕ → K) :
    recurrence l (difference a u) = difference a (recurrence l u) := by
  induction l generalizing u with
  | nil => rfl
  | cons b l ih =>
    have h : difference b (difference a u) = difference a (difference b u) := by
      ext k
      change _ - b * _ = _ - a * _
      simp [difference]
      ring
    exact (congrArg (recurrence l) h).trans (ih _)

private theorem recurrence_prefix (p l : List K) {u : ℕ → K} (hu : recurrence l u = 0) :
    recurrence (p ++ l) u = 0 := by
  induction p generalizing u with
  | nil => exact hu
  | cons a p ih =>
    exact ih (u := difference a u) (by rw [recurrence_difference, hu, map_zero])

private def conv (u v : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : K) * (u i * v (n - i))

-- Pascal's identity splits the forward difference between the two factors.
private theorem difference_conv (a b : K) (u v : ℕ → K) :
    difference (a + b) (conv u v) = conv (difference a u) v + conv u (difference b v) := by
  funext n
  change conv u v (n + 1) - (a + b) * conv u v n = _
  simp only [conv, Pi.add_apply, difference, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_choose_succ_mul (fun i j ↦ u i * v j)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range_succ_iff.mp hi
  rw [show n + 1 - i = n - i + 1 by omega]
  ring

private def pairSums (as bs : List K) := as.flatMap fun a ↦ bs.map (a + ·)

-- Peel off the factors indexed by one row of the array of pairwise sums.
private theorem recurrence_row (a : K) (bs rest : List K) (u v : ℕ → K)
    (hv : recurrence bs v = 0)
    (hrest : ∀ w, recurrence bs w = 0 → recurrence rest (conv (difference a u) w) = 0) :
    recurrence (bs.map (a + ·) ++ rest) (conv u v) = 0 := by
  induction bs generalizing v with
  | nil =>
    obtain rfl : v = 0 := hv
    have h : conv u 0 = 0 := by funext k; simp [conv]
    rw [h, map_zero]
  | cons b bs ih =>
    change recurrence (bs.map (a + ·) ++ rest) (difference (a + b) (conv u v)) = 0
    rw [difference_conv, map_add, recurrence_prefix _ _ (hrest v hv), zero_add]
    apply ih (difference b v) hv
    intro w hw
    apply hrest
    change recurrence bs (difference b w) = 0
    rw [recurrence_difference, hw, map_zero]

private theorem recurrence_conv (as bs : List K) (u v : ℕ → K)
    (hu : recurrence as u = 0) (hv : recurrence bs v = 0) :
    recurrence (pairSums as bs) (conv u v) = 0 := by
  induction as generalizing u v with
  | nil =>
    obtain rfl : u = 0 := hu
    funext k
    simp [pairSums, recurrence, conv]
  | cons a as ih => exact recurrence_row a bs _ u v hv (fun w hw ↦ ih _ w hu hw)

private noncomputable def denominator (l : List K) : PowerSeries K :=
  (l.map fun a ↦ 1 - C a * X).prod

private noncomputable def tail (f : PowerSeries K) (N : ℕ) (k : ℕ) := coeff (k + N) f

-- Clearing a denominator factor advances the starting index by one.
private theorem recurrence_tail (l : List K) (f : PowerSeries K) (N : ℕ) :
    recurrence l (tail f N) = tail (f * denominator l) (N + l.length) := by
  induction l generalizing f N with
  | nil => simp [recurrence, denominator]
  | cons a l ih =>
    have h : difference a (tail f N) = tail (f * (1 - C a * X)) (N + 1) := by
      funext k
      change coeff (k + 1 + N) f - a * coeff (k + N) f = coeff (k + (N + 1)) _
      rw [mul_sub, mul_one, ← mul_assoc, map_sub, ← Nat.add_assoc, coeff_succ_mul_X, coeff_mul_C]
      rw [Nat.add_right_comm k 1 N, mul_comm a]
    change recurrence l (difference a (tail f N)) = _
    rw [h, ih]
    simp [denominator, mul_assoc, Nat.add_right_comm N 1, Nat.add_assoc]

end binomialProduct_rational_general

open binomialProduct_rational_general in
/-- **Binomial products of proper rational series.** Let $K$ be a field of characteristic $0$, let
$\alpha_1, \dots, \alpha_m, \beta_1, \dots, \beta_n \in K$, not necessarily distinct or nonzero,
and let $R$, $S$ be polynomials over $K$ with $\deg R < m$ and $\deg S < n$. If $A$, $B$ are power
series over $K$ with $A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and
$B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$, then there is a polynomial $T$ over $K$ with
$\deg T < mn$ such that

$$(A \odot B)(x) \prod_{i=1}^m \prod_{j=1}^n \bigl(1 - (\alpha_i + \beta_j) x\bigr) = T(x),$$

where $\odot$ is the binomial product.

Here $\deg 0 = -\infty$, so $T = 0$ when $mn = 0$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 6 (`jis-2024-24.1.3-thm-6`). -/
public theorem binomialProduct_rational {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) (R S : Polynomial K) (hR : R.degree < m) (hS : S.degree < n)
    (A B : PowerSeries K) (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree < (m * n : ℕ) ∧
      binomialProduct A B * ∏ i, ∏ j, (1 - C (α i + β j) * X) = (T : PowerSeries K) := by
  let as := List.ofFn α
  let bs := List.ofFn β
  have input {d : ℕ} (γ : Fin d → K) (P : Polynomial K) (F : PowerSeries K)
      (hd : P.degree < d) (hF : F * ∏ i, (1 - C (γ i) * X) = P) :
      recurrence (List.ofFn γ) (tail F 0) = 0 := by
    rw [recurrence_tail]
    funext k
    simp only [tail, denominator, List.map_ofFn, List.prod_ofFn, Function.comp_apply,
      List.length_ofFn, Nat.zero_add, hF, Polynomial.coeff_coe, Pi.zero_apply]
    exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp hd _ (by omega)
  have h := recurrence_conv as bs _ _ (input α R A hR hA) (input β S B hS hB)
  have hconv : conv (tail A 0) (tail B 0) = tail (binomialProduct A B) 0 := by
    funext k
    simp [conv, tail, coeff_binomialProduct, mul_assoc]
  rw [hconv, recurrence_tail] at h
  have length_pairs (l : List K) : (pairSums l bs).length = l.length * n := by
    induction l with
    | nil => simp [pairSums]
    | cons a l ih =>
      change (bs.map (a + ·) ++ pairSums l bs).length = _
      simp [ih, bs, Nat.succ_mul, Nat.add_comm]
  let F := binomialProduct A B * ∏ i, ∏ j, (1 - C (α i + β j) * X)
  have htail : tail F (m * n) = 0 := by
    simpa [length_pairs, as, bs, F, denominator, pairSums, List.flatMap_def, List.prod_flatten,
      List.map_ofFn, List.prod_ofFn, Function.comp_def] using h
  refine ⟨trunc (m * n) F, degree_trunc_lt _ _, ?_⟩
  change F = ↑(trunc (m * n) F)
  ext k
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hk
  · rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_not_gt hk)
    exact congrFun htail j

private theorem prod_padded {K M : Type*} [Field K] [CommMonoid M] (u : ℕ) {m : ℕ}
    (α : Fin m → K) (f : K → M) :
    (∏ i, f (Fin.append (fun _ : Fin u ↦ 0) α i)) = f 0 ^ u * ∏ i, f (α i) := by
  rw [Fin.prod_univ_add]
  simp

set_option linter.unusedVariables false in
/-- **Binomial products of arbitrary rational series.** Let $K$ be a field of characteristic $0$,
let $\alpha_1, \dots, \alpha_m$ and $\beta_1, \dots, \beta_n$ be nonzero elements of $K$, and let
$R$, $S$ be polynomials over $K$. Let $A$, $B$ be power series over $K$ with
$A(x) \prod_{i=1}^m (1 - \alpha_i x) = R(x)$ and $B(x) \prod_{j=1}^n (1 - \beta_j x) = S(x)$.
Put $u = \max(d_R + 1 - m, 0)$ and $v = \max(d_S + 1 - n, 0)$, where $d_R$ and $d_S$ are the
degrees of $R$ and $S$, the zero polynomial counting as degree $0$. Then there is a polynomial
$T$ over $K$ of degree less than $(u + m)(v + n)$ such that

$$(A \odot B)(x) \Big(\prod_{i=1}^m (1 - \alpha_i x)\Big)^{v}
\Big(\prod_{j=1}^n (1 - \beta_j x)\Big)^{u} \prod_{i=1}^m \prod_{j=1}^n (1 - (\alpha_i + \beta_j) x)
= T(x),$$

where $\odot$ is the binomial product.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 7 (`jis-2024-24.1.3-cor-7`). -/
public theorem binomialProduct_rational_general {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (α : Fin m → K) (β : Fin n → K) (hα : ∀ i, α i ≠ 0) (hβ : ∀ j, β j ≠ 0)
    (R S : Polynomial K) (A B : PowerSeries K)
    (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree <
        (((R.natDegree + 1 - m) + m) * ((S.natDegree + 1 - n) + n) : ℕ) ∧
      binomialProduct A B * ((∏ i, (1 - C (α i) * X)) ^ (S.natDegree + 1 - n) *
        (∏ j, (1 - C (β j) * X)) ^ (R.natDegree + 1 - m) *
        ∏ i, ∏ j, (1 - C (α i + β j) * X)) = (T : PowerSeries K) := by
  let u := R.natDegree + 1 - m
  let v := S.natDegree + 1 - n
  let α' := Fin.append (fun _ : Fin u ↦ (0 : K)) α
  let β' := Fin.append (fun _ : Fin v ↦ (0 : K)) β
  have bound (P : Polynomial K) (d : ℕ) : P.degree < ↑((P.natDegree + 1 - d) + d) := by
    have h : P.natDegree < (P.natDegree + 1 - d) + d := by omega
    exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr h)
  obtain ⟨T, hd, hT⟩ := binomialProduct_rational (u + m) (v + n) α' β' R S
    (bound R m) (bound S n) A B
    (by simpa only [α', prod_padded u α (fun a ↦ 1 - C a * X), map_zero, zero_mul, sub_zero,
      one_pow, one_mul] using hA)
    (by simpa only [β', prod_padded v β (fun b ↦ 1 - C b * X), map_zero, zero_mul, sub_zero,
      one_pow, one_mul] using hB)
  refine ⟨T, hd, ?_⟩
  rw [← hT]
  congr 1
  let factor (c : K) : PowerSeries K := 1 - C c * X
  change _ = ∏ i, ∏ j, factor (α' i + β' j)
  rw [prod_padded u α (fun a ↦ ∏ j, factor (a + β' j))]
  simp only [zero_add]
  rw [prod_padded v β factor]
  have row (a : K) : (∏ j, factor (a + β' j)) = factor a ^ v * ∏ j, factor (a + β j) := by
    simpa only [add_zero] using prod_padded v β (fun b ↦ factor (a + b))
  simp_rw [row]
  simp only [u, v, factor, map_zero, zero_mul, sub_zero, one_pow, one_mul,
    Finset.prod_mul_distrib, Finset.prod_pow]
  ac_rfl

end MetaMathlibExt
