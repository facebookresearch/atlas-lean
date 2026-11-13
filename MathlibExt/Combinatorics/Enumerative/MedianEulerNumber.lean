/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.EulerSeidelMatrix
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Median Euler numbers

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen53.tex> and
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **The list of the first Euler coefficients.** Let $\varepsilon_N$ be $1$ if $N$ is odd and $0$
if $N$ is even. For each natural number $n$, this is the list $[c_0, c_1, \dots, c_n]$ of integers
with $c_0 = 1$ and, for $1 \le N \le n$, $c_N = \varepsilon_N - \sum_j \binom{N}{j} c_{N-j}$, where
the sum runs over the even $j$ with $2 \le j \le N$. The Euler coefficient $E_n$ is its last entry
$c_n$. The list is built one entry at a time, so each step reuses the earlier values.

The recurrence comes from $\cosh x \cdot (\operatorname{sech} x + \tanh x) = 1 + \sinh x$.

Source: concept `jis_sem_0f85ae780217af7de3a4a1b6`; statements `jis_bdf7050da9616e789767cc45` and
`jis_acae886a10f953dc872dd3f5`. -/
def medianEulerCoefficients : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      let previous := medianEulerCoefficients n
      let N := n + 1
      let sum : ℤ :=
        ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (N + 1)),
          (N.choose j : ℤ) * previous.getD (N - j) 0
      previous ++ [(if N % 2 = 1 then 1 else 0) - sum]

/-- **Euler coefficients.** Let $\varepsilon_n$ be $1$ if $n$ is odd and $0$ if $n$ is even. The
Euler coefficients $E_n$ are the integers defined by $E_0 = 1$ and, for $n \ge 1$,
$E_n = \varepsilon_n - \sum_j \binom{n}{j} E_{n-j}$, where the sum runs over the even $j$ with
$2 \le j \le n$.

They are the coefficients in $\operatorname{sech} x + \tanh x = \sum_{n \ge 0} E_n x^n / n!$: the
recurrence compares coefficients in $\cosh x \cdot (\operatorname{sech} x + \tanh x) = 1 + \sinh x$.
The first values are $1, 1, -1, -2, 5, 16, -61$. -/
def medianEulerCoeff (n : ℕ) : ℤ :=
  (medianEulerCoefficients n).getD n 0

/-- **Initial row for the median Euler numbers.** Let $E_m$ denote the Euler coefficients. This is
the integer sequence $(a_m)_{m \ge 0}$ with $a_0 = 0$ and $a_m = E_m$ for $m \ge 1$. It is the
initial row of the Euler–Seidel matrix from which the median Euler numbers are read off. -/
def medianEulerInitialRow : ℕ → ℤ
  | 0 => 0
  | m + 1 => medianEulerCoeff (m + 1)

/-- **Median Euler numbers.** Let $E_m$ denote the Euler coefficients, and let $(a_n^k)$ be the
Euler–Seidel matrix of the initial row $a_0 = 0$, $a_m = E_m$ for $m \ge 1$, so that $a_n^0 = a_n$
and $a_n^{k+1} = a_n^k + a_{n+1}^k$. The median Euler number $R_n$ is the natural number
$|a_{n+1}^n|$. Equivalently, $R_n = \left|\sum_{i=0}^{n} \binom{n}{i} E_{n+1+i}\right|$.

The first values are $R_0 = 1$, $R_1 = 3$, $R_2 = 24$ and $R_3 = 402$. -/
def medianEulerNumber (n : ℕ) : ℕ :=
  (eulerSeidelMatrix medianEulerInitialRow (n + 1) n).natAbs

theorem medianEulerNumber_zero : medianEulerNumber 0 = 1 := by rfl
theorem medianEulerNumber_one : medianEulerNumber 1 = 3 := by rfl
theorem medianEulerNumber_two : medianEulerNumber 2 = 24 := by rfl
theorem medianEulerNumber_three : medianEulerNumber 3 = 402 := by rfl

end

-- Unfolding of one step of the coefficient recurrence.
open scoped BigOperators in
private theorem me_coeffs_succ (n : ℕ) : medianEulerCoefficients (n + 1)
    = medianEulerCoefficients n ++
      [(if (n + 1) % 2 = 1 then 1 else 0) -
        ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (n + 1 + 1)),
          ((n + 1).choose j : ℤ) * (medianEulerCoefficients n).getD (n + 1 - j) 0] := rfl

-- Length of the coefficient list.
private theorem me_coeffs_length (n : ℕ) :
    (medianEulerCoefficients n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [me_coeffs_succ, List.length_append, ih, List.length_cons, List.length_nil]

-- Prefix stability of the coefficient lists.
private theorem me_prefix : ∀ n k : ℕ, k ≤ n →
    (medianEulerCoefficients n).getD k 0 = medianEulerCoeff k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    rfl
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · rw [me_coeffs_succ,
        List.getD_append _ _ _ _ (by rw [me_coeffs_length]; omega)]
      exact ih k hkn
    · have hkn1 : k = n + 1 := by omega
      subst hkn1
      rfl

/-- **The zeroth Euler coefficient.** The Euler coefficient $E_0$ equals $1$. -/
public theorem medianEulerCoeff_zero : medianEulerCoeff 0 = 1 := rfl

open scoped BigOperators in
/-- **Recurrence for the Euler coefficients.** Let $E_m$ denote the Euler coefficients, and let
$\varepsilon_m$ be $1$ if $m$ is odd and $0$ if $m$ is even. For every natural number $n$,
$E_{n+1} = \varepsilon_{n+1} - \sum_j \binom{n+1}{j} E_{n+1-j}$, where the sum runs over the even
$j$ with $2 \le j \le n+1$.

It comes from comparing coefficients in
$\cosh x \cdot (\operatorname{sech} x + \tanh x) = 1 + \sinh x$. -/
public theorem medianEulerCoeff_succ (n : ℕ) : medianEulerCoeff (n + 1)
    = (if (n + 1) % 2 = 1 then 1 else 0) -
      ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (n + 1 + 1)),
        ((n + 1).choose j : ℤ) * medianEulerCoeff (n + 1 - j) := by
  have hsum : (∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0)
        (Finset.range (n + 1 + 1)),
        ((n + 1).choose j : ℤ) * (medianEulerCoefficients n).getD (n + 1 - j) 0)
      = ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (n + 1 + 1)),
        ((n + 1).choose j : ℤ) * medianEulerCoeff (n + 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have hle : n + 1 - j ≤ n := by omega
    rw [me_prefix n (n + 1 - j) hle]
  have hE : medianEulerCoeff (n + 1)
      = (medianEulerCoefficients (n + 1)).getD (n + 1) 0 := rfl
  rw [hE, me_coeffs_succ,
    List.getD_append_right _ _ _ _ (le_of_eq (me_coeffs_length n)),
    me_coeffs_length, Nat.sub_self, List.getD_cons_zero, hsum]

-- Parity convolution for the Euler coefficients.
open scoped BigOperators in
private theorem me_parity_conv (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℤ) * (1 + (-1 : ℤ) ^ k) * medianEulerCoeff (n - k))
    = if n = 0 then 2 else 1 - (-1 : ℤ) ^ n := by
  cases n with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, Nat.choose_self,
      Nat.cast_one, pow_zero, Nat.sub_self, medianEulerCoeff_zero, ite_eq_left rfl]
    norm_num
  | succ m =>
    rw [ite_eq_right (by omega)]
    have hterm2 : ∀ k : ℕ, ((m + 1).choose k : ℤ) * (1 + (-1 : ℤ) ^ k)
          * medianEulerCoeff (m + 1 - k)
        = if k % 2 = 0 then ((m + 1).choose k : ℤ) * 2 * medianEulerCoeff (m + 1 - k)
          else 0 := by
      intro k
      rcases Nat.even_or_odd k with hev | hodd
      · have hmod : k % 2 = 0 := Nat.even_iff.mp hev
        rw [Even.neg_one_pow hev, ite_eq_left hmod]
        ring
      · have hmod : k % 2 = 1 := Nat.odd_iff.mp hodd
        rw [Odd.neg_one_pow hodd, ite_eq_right (by omega)]
        ring
    have hfilter : Finset.filter (fun k => k % 2 = 0) (Finset.range (m + 1 + 1))
        = insert 0
          (Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (m + 1 + 1))) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hlt, hev⟩
        by_cases hj0 : j = 0
        · exact Or.inl hj0
        · exact Or.inr ⟨hlt, ⟨by omega, hev⟩⟩
      · rintro (rfl | ⟨hlt, h2, hmod⟩)
        · exact ⟨by omega, by decide⟩
        · exact ⟨hlt, hmod⟩
    have h0mem : (0 : ℕ) ∉ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0)
        (Finset.range (m + 1 + 1)) := by
      simp
    have h2 : (∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0)
          (Finset.range (m + 1 + 1)),
          ((m + 1).choose j : ℤ) * 2 * medianEulerCoeff (m + 1 - j))
        = 2 * ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0)
          (Finset.range (m + 1 + 1)),
          ((m + 1).choose j : ℤ) * medianEulerCoeff (m + 1 - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [hterm2]
    rw [← Finset.sum_filter, hfilter, Finset.sum_insert h0mem]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [h2, medianEulerCoeff_succ]
    rcases Nat.even_or_odd (m + 1) with hev | hodd
    · have h0 : (m + 1) % 2 = 0 := Nat.even_iff.mp hev
      have hmod : ¬ ((m + 1) % 2 = 1) := by omega
      rw [ite_eq_right hmod, Even.neg_one_pow hev]
      ring
    · have hmod : (m + 1) % 2 = 1 := Nat.odd_iff.mp hodd
      rw [ite_eq_left hmod, Odd.neg_one_pow hodd]
      ring

-- Coefficient of a product of two EGFs is the binomial convolution.
open scoped BigOperators in
-- (plain `--` comment above keeps `open ... in` parsing `private` cleanly)
private theorem me_coeff_mul_egf (f g : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.mk (fun k => f k / (k.factorial : ℚ)) *
        PowerSeries.mk (fun k => g k / (k.factorial : ℚ))) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * f k * g (n - k)) /
        (n.factorial : ℚ) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i _ * PowerSeries.coeff j _) n,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [PowerSeries.coeff_mk]
  have hkn : k ≤ n := by omega
  have hchoose : ((n.choose k : ℕ) : ℚ) * ((k.factorial : ℕ) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ) = ((n.factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hd1 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hd2 : ((((n - k).factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  linear_combination (-(f k * g (n - k))) * hchoose

-- EGF of `exp`: coefficients `1 / k!`.
private theorem me_exp_eq_mk : PowerSeries.exp ℚ =
    PowerSeries.mk fun k => 1 / (k.factorial : ℚ) := by
  ext n
  rw [PowerSeries.coeff_exp, PowerSeries.coeff_mk, Algebra.algebraMap_self_apply]

-- EGF of rescaled `exp`: coefficients `c ^ k / k!`.
private theorem me_rescale_exp_eq_mk (c : ℚ) :
    PowerSeries.rescale c (PowerSeries.exp ℚ) =
    PowerSeries.mk fun k => c ^ k / (k.factorial : ℚ) := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_mk,
    Algebra.algebraMap_self_apply]
  ring

-- Rescaling an EGF twists coefficients by `c ^ k`.
private theorem me_rescale_mk_egf (c : ℚ) (f : ℕ → ℚ) :
    PowerSeries.rescale c (PowerSeries.mk fun k => f k / (k.factorial : ℚ)) =
    PowerSeries.mk fun k => c ^ k * f k / (k.factorial : ℚ) := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  ring

open scoped BigOperators in
/-- **Exponential generating function of the Euler coefficients.** Let $E_n$ denote the Euler
coefficients, let $e^x$ be the exponential series, and let $e^{-x}$ be the series obtained from
it by replacing $x$ with $-x$. In the ring $\mathbb{Q}[[x]]$ of formal power series with rational
coefficients, $(e^x + e^{-x}) \sum_{n \ge 0} E_n x^n / n! = 2 + e^x - e^{-x}$.

Since $e^x + e^{-x} = 2 \cosh x$ and $2 + e^x - e^{-x} = 2 (1 + \sinh x)$, and $\cosh x$ is
invertible, this says that the exponential generating function of the $E_n$ is
$\operatorname{sech} x + \tanh x$. -/
public theorem medianEulerCoeff_egf :
    (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
      PowerSeries.mk (fun n => ((medianEulerCoeff n : ℤ) : ℚ) / (n.factorial : ℚ))
    = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) := by
  have hadd : PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)
      = PowerSeries.mk (fun k => (1 + (-1 : ℚ) ^ k) / (k.factorial : ℚ)) := by
    rw [me_rescale_exp_eq_mk, me_exp_eq_mk]
    ext k
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      add_div]
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat _ _).symm
  ext n
  rw [hadd,
    me_coeff_mul_egf (fun k => 1 + (-1 : ℚ) ^ k)
      (fun k => ((medianEulerCoeff k : ℤ) : ℚ)) n,
    h2, map_sub, map_add, PowerSeries.coeff_C, me_rescale_exp_eq_mk, me_exp_eq_mk,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (1 + (-1 : ℚ) ^ k)
        * ((medianEulerCoeff (n - k) : ℤ) : ℚ))
      = ((if n = 0 then (2 : ℤ) else 1 - (-1 : ℤ) ^ n : ℤ) : ℚ) := by
    exact_mod_cast me_parity_conv n
  rw [hsum]
  cases n with
  | zero =>
    rw [ite_eq_left rfl, ite_eq_left rfl, Int.cast_ofNat, Nat.factorial_zero,
      Nat.cast_one, pow_zero]
    norm_num
  | succ m =>
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    push_cast
    rw [sub_div, zero_add]

private theorem me_init_zero : medianEulerInitialRow 0 = 0 := rfl

private theorem me_init_succ (m : ℕ) :
    medianEulerInitialRow (m + 1) = medianEulerCoeff (m + 1) := rfl

-- Abbreviations for the EGFs of `E` and `a`.
private def meE : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((medianEulerCoeff n : ℤ) : ℚ) / (n.factorial : ℚ)

private def meA : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((medianEulerInitialRow n : ℤ) : ℚ) / (n.factorial : ℚ)

-- Auxiliary: `e * ē = 1`.
private theorem me_exp_mul_bar : PowerSeries.exp ℚ *
    PowerSeries.rescale (-1) (PowerSeries.exp ℚ) = 1 :=
  PowerSeries.exp_mul_exp_neg_eq_one

-- Auxiliary: rescaling `ē` by `-1` gives back `e`.
private theorem me_bar_bar :
    PowerSeries.rescale (-1) (PowerSeries.rescale (-1) (PowerSeries.exp ℚ))
    = PowerSeries.exp ℚ := by
  have h11 : (-1 : ℚ) * (-1) = 1 := by norm_num
  rw [PowerSeries.rescale_rescale, h11]
  simp

-- Auxiliary: `e ^ 2 = rescale 2 e`.
private theorem me_exp_sq :
    PowerSeries.exp ℚ ^ 2
    = PowerSeries.rescale 2 (PowerSeries.exp ℚ) := by
  have h := PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) 2
  simpa using h

private theorem me_egf_A_eq : meA = meE - 1 := by
  simp only [meA, meE]
  ext n
  rw [map_sub]
  cases n with
  | zero => simp [PowerSeries.coeff_mk, me_init_zero, medianEulerCoeff_zero]
  | succ m => simp [PowerSeries.coeff_mk, me_init_succ]

private theorem me_egf_identity_bar :
    (PowerSeries.rescale (-1) (PowerSeries.exp ℚ) + PowerSeries.exp ℚ) *
      PowerSeries.rescale (-1) meE
    = 2 + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ := by
  have hE : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
      = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) :=
    medianEulerCoeff_egf
  have hEr := congrArg (PowerSeries.rescale (-1)) hE
  rw [map_mul, map_add, me_bar_bar, map_sub, map_add, me_bar_bar] at hEr
  have h2r : PowerSeries.rescale (-1) (2 : PowerSeries ℚ) = 2 := map_ofNat _ _
  rw [h2r] at hEr
  exact hEr

-- Reflection `𝔄 * e + rescale (-1) 𝔄 = 0`.
private theorem me_egf_reflection :
    meA * PowerSeries.exp ℚ + PowerSeries.rescale (-1) meA = 0 := by
  have hE : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
      = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) :=
    medianEulerCoeff_egf
  have hAr : PowerSeries.rescale (-1) meA = PowerSeries.rescale (-1) meE - 1 := by
    have h := congrArg (PowerSeries.rescale (-1)) me_egf_A_eq
    rwa [map_sub, map_one] at h
  have hDne : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.coeff 0) hz
    simp only [map_add, PowerSeries.coeff_exp, PowerSeries.coeff_rescale, map_zero,
      Algebra.algebraMap_self_apply, pow_zero, one_mul, Nat.factorial_zero,
      Nat.cast_one, div_one, one_add_one_eq_two] at hc
    norm_num at hc
  have key : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
      (meA * PowerSeries.exp ℚ + PowerSeries.rescale (-1) meA) = 0 := by
    linear_combination
      (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
        PowerSeries.exp ℚ * me_egf_A_eq +
      PowerSeries.exp ℚ * hE +
      (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * hAr +
      me_egf_identity_bar - 2 * me_exp_mul_bar
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hDne
  · exact h

-- Linear `(𝔄 * rescale 2 e) + 𝔄 = 2 * (e - 1)`.
private theorem me_egf_linear :
    meA * PowerSeries.rescale 2 (PowerSeries.exp ℚ) + meA
    = 2 * (PowerSeries.exp ℚ - 1) := by
  have hE : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
      = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) :=
    medianEulerCoeff_egf
  have hmul : (PowerSeries.rescale 2 (PowerSeries.exp ℚ) + 1) * meE
      = PowerSeries.exp ℚ *
        (2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
    linear_combination PowerSeries.exp ℚ * hE - meE * me_exp_sq - meE * me_exp_mul_bar
  linear_combination
    (PowerSeries.rescale 2 (PowerSeries.exp ℚ) + 1) * me_egf_A_eq + hmul +
    me_exp_sq - me_exp_mul_bar

-- Auxiliary: rescaling commutes with differentiation up to `C a`.
private theorem me_deriv_rescale (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative (PowerSeries.rescale a f)
    = PowerSeries.C a * PowerSeries.rescale a (PowerSeries.derivative f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale]
  ring

-- Auxiliary: derivative of `ē`.
private theorem me_deriv_bar :
    PowerSeries.derivative (PowerSeries.rescale (-1) (PowerSeries.exp ℚ))
    = PowerSeries.C (-1) * PowerSeries.rescale (-1) (PowerSeries.exp ℚ) := by
  rw [me_deriv_rescale, PowerSeries.derivative_exp]

-- Auxiliary: the differentiated generating-function identity.
private theorem me_deriv_egf_identity :
    (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
        PowerSeries.derivative meE +
      (PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
    = PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) := by
  have hE : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
      = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) :=
    medianEulerCoeff_egf
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat _ _).symm
  have hCm1 : PowerSeries.C (-1 : ℚ) = -1 := by simp
  have hd := congrArg (⇑PowerSeries.derivative) hE
  simp only [Derivation.leibniz, map_add, map_sub, smul_eq_mul] at hd
  rw [PowerSeries.derivative_exp, me_deriv_bar, h2, PowerSeries.derivative_C,
    hCm1] at hd
  linear_combination hd

private theorem me_egf_riccati :
    2 * PowerSeries.derivative meE
    = PowerSeries.rescale (-1) meE * meE +
      PowerSeries.rescale (-1) meE * PowerSeries.rescale (-1) meE := by
  have hE : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE
      = 2 + PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ) :=
    medianEulerCoeff_egf
  have hDne : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.coeff 0) hz
    simp only [map_add, PowerSeries.coeff_exp, PowerSeries.coeff_rescale, map_zero,
      Algebra.algebraMap_self_apply, pow_zero, one_mul, Nat.factorial_zero,
      Nat.cast_one, div_one, one_add_one_eq_two] at hc
    norm_num at hc
  have key1 : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ 2 *
        (2 * PowerSeries.derivative meE)
      = 4 * (2 + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ) +
        8 * (PowerSeries.exp ℚ * PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - 1) := by
    linear_combination
      2 * (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
        me_deriv_egf_identity -
      2 * (PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * hE
  have key2 : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ 2 *
        (PowerSeries.rescale (-1) meE * meE +
          PowerSeries.rescale (-1) meE * PowerSeries.rescale (-1) meE)
      = 4 * (2 + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ) := by
    linear_combination
      ((PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * meE +
        (PowerSeries.rescale (-1) (PowerSeries.exp ℚ) + PowerSeries.exp ℚ) *
          PowerSeries.rescale (-1) meE +
        (2 + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ)) *
        me_egf_identity_bar +
      (2 + PowerSeries.rescale (-1) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ) * hE
  have key : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ 2 *
        (2 * PowerSeries.derivative meE)
      = (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ 2 *
        (PowerSeries.rescale (-1) meE * meE +
          PowerSeries.rescale (-1) meE * PowerSeries.rescale (-1) meE) := by
    linear_combination key1 - key2 + 8 * me_exp_mul_bar
  have hD2ne : (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hDne
  exact mul_left_cancel₀ hD2ne key

-- Reflection sum for the initial row.
open scoped BigOperators in
private theorem me_init_reflection (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
      ((m.choose i : ℤ) * medianEulerInitialRow i)
    = (-1 : ℤ) ^ (m + 1) * medianEulerInitialRow m := by
  have hcoeff := congrArg (PowerSeries.coeff m) me_egf_reflection
  rw [map_add, map_zero] at hcoeff
  simp only [meA, me_exp_eq_mk] at hcoeff
  rw [me_coeff_mul_egf (fun k => ((medianEulerInitialRow k : ℤ) : ℚ)) (fun _ => (1 : ℚ)) m,
    me_rescale_mk_egf, PowerSeries.coeff_mk] at hcoeff
  have hF : ((((m.factorial : ℕ)) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hmul := congrArg (· * ((m.factorial : ℕ) : ℚ)) hcoeff
  rw [add_mul, div_mul_cancel₀ _ hF, div_mul_cancel₀ _ hF, zero_mul] at hmul
  simp only [mul_one] at hmul
  have hQ : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) *
        ((medianEulerInitialRow i : ℤ) : ℚ))
      = (-1 : ℚ) ^ (m + 1) * ((medianEulerInitialRow m : ℤ) : ℚ) := by
    rw [pow_succ]
    linear_combination hmul
  exact_mod_cast hQ

-- Linear recurrence for the initial row.
open scoped BigOperators in
private theorem me_init_linear (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
      ((m.choose i : ℤ) * medianEulerInitialRow i * 2 ^ (m - i)))
      + medianEulerInitialRow m
    = if m = 0 then 0 else 2 := by
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat _ _).symm
  cases m with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, ite_eq_left rfl]
    simp [Nat.choose_self, me_init_zero]
  | succ m =>
    rw [ite_eq_right (by omega)]
    have hcoeff := congrArg (PowerSeries.coeff (m + 1)) me_egf_linear
    rw [map_add] at hcoeff
    simp only [meA, me_rescale_exp_eq_mk] at hcoeff
    rw [me_coeff_mul_egf (fun k => ((medianEulerInitialRow k : ℤ) : ℚ))
        (fun k => (2 : ℚ) ^ k) (m + 1), PowerSeries.coeff_mk] at hcoeff
    rw [h2, PowerSeries.coeff_C_mul, map_sub, me_exp_eq_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, ite_eq_right (by omega)] at hcoeff
    have hF : ((((m + 1).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m + 1)
    have hmul := congrArg (· * (((m + 1).factorial : ℕ) : ℚ)) hcoeff
    rw [add_mul, div_mul_cancel₀ _ hF, div_mul_cancel₀ _ hF, sub_zero, mul_assoc,
      one_div, inv_mul_cancel₀ hF, mul_one] at hmul
    have hQ : (∑ i ∈ Finset.range (m + 1 + 1), (m + 1).choose i *
          ((medianEulerInitialRow i : ℤ) : ℚ) * (2 : ℚ) ^ (m + 1 - i))
        + ((medianEulerInitialRow (m + 1) : ℤ) : ℚ) = 2 := by
      exact hmul
    exact_mod_cast hQ

-- Riccati recurrence for the Euler coefficients.
open scoped BigOperators in
private theorem me_coeff_riccati (n : ℕ) :
    2 * medianEulerCoeff (n + 1)
    = ∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℤ) * (((-1 : ℤ) ^ k + (-1 : ℤ) ^ n) *
        medianEulerCoeff k * medianEulerCoeff (n - k))) := by
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat _ _).symm
  have hcoeff := congrArg (PowerSeries.coeff n) me_egf_riccati
  rw [map_add] at hcoeff
  simp only [meE] at hcoeff
  rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mk] at hcoeff
  rw [me_rescale_mk_egf] at hcoeff
  rw [me_coeff_mul_egf (fun k => (-1 : ℚ) ^ k * ((medianEulerCoeff k : ℤ) : ℚ))
      (fun k => ((medianEulerCoeff k : ℤ) : ℚ)) n,
    me_coeff_mul_egf (fun k => (-1 : ℚ) ^ k * ((medianEulerCoeff k : ℤ) : ℚ))
      (fun k => (-1 : ℚ) ^ k * ((medianEulerCoeff k : ℤ) : ℚ)) n] at hcoeff
  have hS2 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
        ((-1 : ℚ) ^ k * ((medianEulerCoeff k : ℤ) : ℚ)) *
        ((-1 : ℚ) ^ (n - k) * ((medianEulerCoeff (n - k) : ℤ) : ℚ)))
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
        ((-1 : ℚ) ^ n * ((medianEulerCoeff k : ℤ) : ℚ) *
          ((medianEulerCoeff (n - k) : ℤ) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    have hpow : (-1 : ℚ) ^ k * (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hkn]
    linear_combination ((n.choose k : ℚ) * ((medianEulerCoeff k : ℤ) : ℚ) *
      ((medianEulerCoeff (n - k) : ℤ) : ℚ)) * hpow
  rw [hS2, ← add_div, ← Finset.sum_add_distrib] at hcoeff
  have hmerge : (∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℚ) * ((-1 : ℚ) ^ k * ((medianEulerCoeff k : ℤ) : ℚ)) *
          ((medianEulerCoeff (n - k) : ℤ) : ℚ) +
        (n.choose k : ℚ) * ((-1 : ℚ) ^ n * ((medianEulerCoeff k : ℤ) : ℚ) *
          ((medianEulerCoeff (n - k) : ℤ) : ℚ))))
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
        (((-1 : ℚ) ^ k + (-1 : ℚ) ^ n) * ((medianEulerCoeff k : ℤ) : ℚ) *
          ((medianEulerCoeff (n - k) : ℤ) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hmerge, Nat.factorial_succ] at hcoeff
  push_cast at hcoeff
  have hF : ((((n.factorial : ℕ))) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (((n : ℚ)) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hLHS : 2 * (((medianEulerCoeff (n + 1) : ℤ) : ℚ) / ((((n : ℚ)) + 1) *
      ((n.factorial : ℕ) : ℚ)) * ((((n : ℚ)) + 1)))
      = 2 * ((medianEulerCoeff (n + 1) : ℤ) : ℚ) / ((n.factorial : ℕ) : ℚ) := by
    field_simp
  rw [hLHS] at hcoeff
  have hmul := congrArg (· * ((n.factorial : ℕ) : ℚ)) hcoeff
  rw [div_mul_cancel₀ _ hF, div_mul_cancel₀ _ hF] at hmul
  have hQ : 2 * ((medianEulerCoeff (n + 1) : ℤ) : ℚ)
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
        (((-1 : ℚ) ^ k + (-1 : ℚ) ^ n) * ((medianEulerCoeff k : ℤ) : ℚ) *
          ((medianEulerCoeff (n - k) : ℤ) : ℚ)) := by
    exact hmul
  exact_mod_cast hQ

-- Antisymmetry of Euler–Seidel matrices under the reflection hypothesis.
open scoped BigOperators in
private theorem me_seidel_antisymm (a : ℕ → ℤ)
    (h : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℤ) * a i)
      = (-1 : ℤ) ^ (m + 1) * a m) (n k : ℕ) :
    eulerSeidelMatrix a n k = (-1 : ℤ) ^ (n + k + 1) * eulerSeidelMatrix a k n := by
  induction k generalizing n with
  | zero =>
    have h0 : eulerSeidelMatrix a n 0 = a n := rfl
    have hSn : eulerSeidelMatrix a 0 n
        = ∑ i ∈ Finset.range (n + 1), n.choose i • a (0 + i) :=
      eulerSeidelMatrix_eq_sum a 0 n
    have hsum : (∑ i ∈ Finset.range (n + 1), n.choose i • a (0 + i))
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * a i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [nsmul_eq_mul, zero_add]
    have hneg : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, rfl⟩
    have e : n + 0 + 1 = n + 1 := by omega
    rw [h0, hSn, hsum, h n, e, ← mul_assoc, hneg, one_mul]
  | succ k ih =>
    have hdef : eulerSeidelMatrix a n (k + 1)
        = eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k := rfl
    have hdef2 : eulerSeidelMatrix a k (n + 1)
        = eulerSeidelMatrix a k n + eulerSeidelMatrix a (k + 1) n := rfl
    have e2 : (n + 1) + k + 1 = (n + k + 1) + 1 := by omega
    have e3 : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
    rw [hdef, ih n, ih (n + 1), e2, e3, pow_succ, pow_succ]
    linear_combination (-(-1 : ℤ) ^ (n + k + 1)) * hdef2

-- Instance for the median Euler initial row.
private theorem me_seidel_antisymm_inst (n k : ℕ) :
    eulerSeidelMatrix medianEulerInitialRow n k
    = (-1 : ℤ) ^ (n + k + 1) * eulerSeidelMatrix medianEulerInitialRow k n :=
  me_seidel_antisymm medianEulerInitialRow me_init_reflection n k

-- Corollary: diagonal entries vanish.
private theorem me_seidel_diag_zero (n : ℕ) :
    eulerSeidelMatrix medianEulerInitialRow n n = 0 := by
  have h := me_seidel_antisymm_inst n n
  have he : (-1 : ℤ) ^ (n + n + 1) = -1 := Odd.neg_one_pow ⟨n, by omega⟩
  rw [he] at h
  linarith

-- Corollary: first row in terms of the initial row.
private theorem me_seidel_zero_left (m : ℕ) :
    eulerSeidelMatrix medianEulerInitialRow 0 m
    = (-1 : ℤ) ^ (m + 1) * medianEulerInitialRow m := by
  have h := me_seidel_antisymm_inst 0 m
  have hS0 : eulerSeidelMatrix medianEulerInitialRow m 0
      = medianEulerInitialRow m := rfl
  have e : 0 + m + 1 = m + 1 := by omega
  rw [e, hS0] at h
  exact h

-- Helper: the sign twist of one Riccati summand.
private theorem me_sign_factor (n k : ℕ) (hkn : k ≤ n) :
    (-1 : ℤ) ^ ((n + 1) / 2) * ((-1 : ℤ) ^ k + (-1 : ℤ) ^ n)
    = (if (n - k) % 2 = 0 then 2 else 0) *
      ((-1 : ℤ) ^ (k / 2) * (-1 : ℤ) ^ ((n - k) / 2)) := by
  by_cases hpar : (n - k) % 2 = 0
  · rw [ite_eq_left hpar]
    have hpm : (-1 : ℤ) ^ (n - k) = 1 := Even.neg_one_pow (Nat.even_iff.mpr hpar)
    have hkk : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hnpow : (-1 : ℤ) ^ n = (-1 : ℤ) ^ k := by
      conv_lhs => rw [hkk, pow_add, hpm, mul_one]
    rw [hnpow]
    have key : (-1 : ℤ) ^ ((n + 1) / 2) * (-1 : ℤ) ^ k
        = (-1 : ℤ) ^ (k / 2) * (-1 : ℤ) ^ ((n - k) / 2) := by
      obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k
      · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (n - k)
        · have e1 : (n + 1) / 2 = i + j := by omega
          have d1 : k / 2 = i := by omega
          have d2 : (n - k) / 2 = j := by omega
          rw [e1, d1, d2, hi]
          have h1 : (-1 : ℤ) ^ (2 * i) = 1 := Even.neg_one_pow ⟨i, by omega⟩
          rw [h1, mul_one, pow_add]
        · exfalso
          omega
      · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (n - k)
        · have e1 : (n + 1) / 2 = i + j + 1 := by omega
          have d1 : k / 2 = i := by omega
          have d2 : (n - k) / 2 = j := by omega
          rw [e1, d1, d2, hi]
          have h1 : (-1 : ℤ) ^ (2 * i + 1) = -1 := Odd.neg_one_pow ⟨i, rfl⟩
          rw [h1, pow_succ, pow_add]
          ring
        · exfalso
          omega
    linear_combination 2 * key
  · rw [ite_eq_right hpar]
    have hodd : Odd (n - k) := Nat.odd_iff.mpr (by omega)
    have hpm : (-1 : ℤ) ^ (n - k) = -1 := Odd.neg_one_pow hodd
    have hkk : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hnpow : (-1 : ℤ) ^ n = -(-1 : ℤ) ^ k := by
      conv_lhs => rw [hkk, pow_add, hpm, mul_neg, mul_one]
    rw [hnpow]
    ring

-- Sign of the Euler coefficients.
open scoped BigOperators in
private theorem me_coeff_sign (m : ℕ) :
    0 ≤ (-1 : ℤ) ^ (m / 2) * medianEulerCoeff m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      rw [Nat.zero_div, pow_zero, one_mul]
      rw [medianEulerCoeff_zero]
      norm_num
    | succ n =>
      have hR := me_coeff_riccati n
      have hmul := congrArg ((-1 : ℤ) ^ ((n + 1) / 2) * ·) hR
      simp only [Finset.mul_sum] at hmul
      have hLHS : (-1 : ℤ) ^ ((n + 1) / 2) * (2 * medianEulerCoeff (n + 1))
          = 2 * ((-1 : ℤ) ^ ((n + 1) / 2) * medianEulerCoeff (n + 1)) := by
        ring
      rw [hLHS] at hmul
      have hterm : ∀ k ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ ((n + 1) / 2) *
            ((n.choose k : ℤ) * (((-1 : ℤ) ^ k + (-1 : ℤ) ^ n) *
              medianEulerCoeff k * medianEulerCoeff (n - k)))
          = (n.choose k : ℤ) * (if (n - k) % 2 = 0 then (2 : ℤ) else 0) *
            (((-1 : ℤ) ^ (k / 2) * medianEulerCoeff k) *
              ((-1 : ℤ) ^ ((n - k) / 2) * medianEulerCoeff (n - k))) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hkn : k ≤ n := by omega
        linear_combination ((n.choose k : ℤ) * medianEulerCoeff k *
          medianEulerCoeff (n - k)) * (me_sign_factor n k hkn)
      rw [Finset.sum_congr rfl hterm] at hmul
      have hnn : 0 ≤ ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℤ) * (if (n - k) % 2 = 0 then (2 : ℤ) else 0) *
            (((-1 : ℤ) ^ (k / 2) * medianEulerCoeff k) *
              ((-1 : ℤ) ^ ((n - k) / 2) * medianEulerCoeff (n - k))) := by
        apply Finset.sum_nonneg
        intro k hk
        have hk1 : k < n + 1 := Finset.mem_range.mp hk
        have hnk1 : n - k < n + 1 := by omega
        have hc : (0 : ℤ) ≤ (n.choose k : ℤ) := Nat.cast_nonneg _
        have hcc : (0 : ℤ) ≤ (if (n - k) % 2 = 0 then 2 else 0) := by
          split <;> norm_num
        have hF1 : 0 ≤ (-1 : ℤ) ^ (k / 2) * medianEulerCoeff k := ih k hk1
        have hF2 : 0 ≤ (-1 : ℤ) ^ ((n - k) / 2) * medianEulerCoeff (n - k) :=
          ih (n - k) hnk1
        exact mul_nonneg (mul_nonneg hc hcc) (mul_nonneg hF1 hF2)
      linarith

-- Consequence: sign of the odd entries of the initial row.
private theorem me_init_odd_sign (p : ℕ) :
    0 ≤ (-1 : ℤ) ^ p * medianEulerInitialRow (2 * p + 1) := by
  have h1 : (2 * p + 1) / 2 = p := by omega
  have h := me_coeff_sign (2 * p + 1)
  rw [h1, ← me_init_succ] at h
  exact h

-- Helper: finite-sum congruence for `ZMOD 15`.
open scoped BigOperators in
private theorem me_modeq_sum15 {s : Finset ℕ} {f g : ℕ → ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD (15 : ℤ)]) :
    ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [ZMOD (15 : ℤ)] := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

-- Scalar congruence mod 3.
private theorem me_scalar3 (m : ℕ) :
    (8 * 10 ^ m - 5 * 2 ^ m - 3 ^ (m + 1) + 8 ^ (m + 1) - 3 : ℤ)
    ≡ 2 [ZMOD 3] := by
  have b8 : (8 : ℤ) ≡ 2 [ZMOD 3] := by decide
  have b10 : (10 : ℤ) ≡ 1 [ZMOD 3] := by decide
  have b5 : (5 : ℤ) ≡ 2 [ZMOD 3] := by decide
  have b3 : (3 : ℤ) ≡ 0 [ZMOD 3] := by decide
  have e1 : (8 * 10 ^ m : ℤ) ≡ 2 * 1 ^ m [ZMOD 3] := b8.mul (b10.pow m)
  have e2 : (5 * 2 ^ m : ℤ) ≡ 2 * 2 ^ m [ZMOD 3] := b5.mul (Int.ModEq.refl _)
  have e3 : ((3 : ℤ) ^ (m + 1)) ≡ 0 [ZMOD 3] := by
    rw [pow_succ']
    have h := b3.mul (Int.ModEq.refl ((3 : ℤ) ^ m))
    simpa using h
  have e4 : ((8 : ℤ) ^ (m + 1)) ≡ 2 ^ (m + 1) [ZMOD 3] := b8.pow _
  have e5 : (3 : ℤ) ≡ 0 [ZMOD 3] := b3
  have s := (((e1.sub e2).sub e3).add e4).sub e5
  have hrhs : (2 * 1 ^ m - 2 * 2 ^ m - 0 + 2 ^ (m + 1) - 0 : ℤ) = 2 := by
    rw [one_pow, pow_succ]
    ring
  rwa [hrhs] at s

private theorem me_scalar5 (m : ℕ) (hm : 1 ≤ m) :
    (8 * 10 ^ m - 5 * 2 ^ m - 3 ^ (m + 1) + 8 ^ (m + 1) - 3 : ℤ)
    ≡ 2 [ZMOD 5] := by
  have c8 : (8 : ℤ) ≡ 3 [ZMOD 5] := by decide
  have c5 : (5 : ℤ) ≡ 0 [ZMOD 5] := by decide
  have c10 : ((10 : ℤ) ^ m) ≡ 0 [ZMOD 5] := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [pow_succ']
    have h10 : (10 : ℤ) ≡ 0 [ZMOD 5] := by decide
    have h := h10.mul (Int.ModEq.refl ((10 : ℤ) ^ t))
    simpa using h
  have e1 : (8 * 10 ^ m : ℤ) ≡ 3 * 0 [ZMOD 5] := c8.mul c10
  have e2 : (5 * 2 ^ m : ℤ) ≡ 0 * 2 ^ m [ZMOD 5] := c5.mul (Int.ModEq.refl _)
  have e3 : ((3 : ℤ) ^ (m + 1)) ≡ 3 ^ (m + 1) [ZMOD 5] := Int.ModEq.refl _
  have e4 : ((8 : ℤ) ^ (m + 1)) ≡ 3 ^ (m + 1) [ZMOD 5] := c8.pow _
  have e5 : (3 : ℤ) ≡ 3 [ZMOD 5] := Int.ModEq.refl _
  have s := (((e1.sub e2).sub e3).add e4).sub e5
  have hrhs : (3 * 0 - 0 * 2 ^ m - 3 ^ (m + 1) + 3 ^ (m + 1) - 3 : ℤ) = -3 := by
    ring
  rw [hrhs] at s
  have hneg : (-3 : ℤ) ≡ 2 [ZMOD 5] := by decide
  exact s.trans hneg

-- Scalar congruence mod 15.
private theorem me_scalar15 (m : ℕ) (hm : 1 ≤ m) :
    (8 * 10 ^ m - 5 * 2 ^ m - 3 ^ (m + 1) + 8 ^ (m + 1) - 3 : ℤ)
    ≡ 2 [ZMOD 15] := by
  have h3 := me_scalar3 m
  have h5 := me_scalar5 m hm
  have hcop : Nat.Coprime (3 : ℤ).natAbs (5 : ℤ).natAbs := by decide
  have h := (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h3, h5⟩
  have hmul : (3 : ℤ) * 5 = 15 := by norm_num
  rwa [hmul] at h

-- Auxiliary: closed form of the full twisted binomial sum.
open scoped BigOperators in
private theorem me_full_binom (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1 + 1),
      ((t + 1).choose j : ℤ) * 2 ^ (t + 1 - j) * (8 ^ (j + 1) - 3)
    = 8 * 10 ^ (t + 1) - 3 * 3 ^ (t + 1) := by
  have e : ∀ j ∈ Finset.range (t + 1 + 1),
      ((t + 1).choose j : ℤ) * 2 ^ (t + 1 - j) * (8 ^ (j + 1) - 3)
      = 8 * (8 ^ j * 2 ^ (t + 1 - j) * ((t + 1).choose j : ℤ))
        - 3 * (1 ^ j * 2 ^ (t + 1 - j) * ((t + 1).choose j : ℤ)) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← add_pow, ← add_pow]
  norm_num

-- The mod-15 closed form for the Euler coefficients.
open scoped BigOperators in
private theorem me_coeff_modEq : ∀ m : ℕ, 1 ≤ m →
    medianEulerCoeff m ≡ (8 : ℤ) ^ (m + 1) - 3 [ZMOD 15] := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have hlin := me_init_linear (t + 1)
    rw [ite_eq_right (by omega : ¬ (t + 1 = 0))] at hlin
    rw [Finset.sum_range_succ] at hlin
    have htop : ((t + 1).choose (t + 1) : ℤ) * medianEulerInitialRow (t + 1)
        * 2 ^ (t + 1 - (t + 1)) = medianEulerInitialRow (t + 1) := by
      rw [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one]
    rw [htop] at hlin
    rw [Finset.sum_range_succ'] at hlin
    have hf0 : ((t + 1).choose 0 : ℤ) * medianEulerInitialRow 0 * 2 ^ (t + 1 - 0)
        = 0 := by
      simp [me_init_zero]
    rw [hf0] at hlin
    have hterm : ∀ i ∈ Finset.range t,
        ((t + 1).choose (i + 1) : ℤ) * medianEulerInitialRow (i + 1)
          * 2 ^ (t + 1 - (i + 1))
        ≡ ((t + 1).choose (i + 1) : ℤ) * 2 ^ (t + 1 - (i + 1))
          * (8 ^ (i + 1 + 1) - 3) [ZMOD 15] := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi1 : 1 ≤ i + 1 := by omega
      have him : i + 1 < t + 1 := by omega
      have hih := ih (i + 1) him hi1
      have ha : medianEulerInitialRow (i + 1) ≡ (8 : ℤ) ^ (i + 1 + 1) - 3
          [ZMOD 15] := by
        rw [me_init_succ]
        exact hih
      have h2 := ((Int.ModEq.refl ((t + 1).choose (i + 1) : ℤ)).mul ha).mul
        (Int.ModEq.refl ((2 : ℤ) ^ (t + 1 - (i + 1))))
      have heq : ((t + 1).choose (i + 1) : ℤ) * (8 ^ (i + 1 + 1) - 3)
          * 2 ^ (t + 1 - (i + 1))
          = ((t + 1).choose (i + 1) : ℤ) * 2 ^ (t + 1 - (i + 1))
            * (8 ^ (i + 1 + 1) - 3) := by
        ring
      rwa [heq] at h2
    have hsum0 := me_modeq_sum15 hterm
    have hG : (∑ i ∈ Finset.range t, ((t + 1).choose (i + 1) : ℤ)
          * 2 ^ (t + 1 - (i + 1)) * (8 ^ (i + 1 + 1) - 3))
        = 8 * 10 ^ (t + 1) - 3 * 3 ^ (t + 1) - 2 ^ (t + 1) * 5
          - (8 ^ (t + 1 + 1) - 3) := by
      have hfull := me_full_binom t
      have hp0 : (∑ j ∈ Finset.range (t + 1), ((t + 1).choose j : ℤ)
            * 2 ^ (t + 1 - j) * (8 ^ (j + 1) - 3))
          = (∑ i ∈ Finset.range t, ((t + 1).choose (i + 1) : ℤ)
              * 2 ^ (t + 1 - (i + 1)) * (8 ^ (i + 1 + 1) - 3))
            + ((t + 1).choose 0 : ℤ) * 2 ^ (t + 1 - 0) * (8 ^ (0 + 1) - 3) :=
        Finset.sum_range_succ' _ _
      have hpT : (∑ j ∈ Finset.range (t + 1 + 1), ((t + 1).choose j : ℤ)
            * 2 ^ (t + 1 - j) * (8 ^ (j + 1) - 3))
          = (∑ j ∈ Finset.range (t + 1), ((t + 1).choose j : ℤ)
              * 2 ^ (t + 1 - j) * (8 ^ (j + 1) - 3))
            + ((t + 1).choose (t + 1) : ℤ) * 2 ^ (t + 1 - (t + 1))
              * (8 ^ (t + 1 + 1) - 3) :=
        Finset.sum_range_succ _ _
      have hg0 : ((t + 1).choose 0 : ℤ) * 2 ^ (t + 1 - 0) * (8 ^ (0 + 1) - 3)
          = 2 ^ (t + 1) * 5 := by
        have e83 : (8 : ℤ) ^ (0 + 1) - 3 = 5 := by norm_num
        rw [Nat.choose_zero_right, Nat.cast_one, one_mul, e83, Nat.sub_zero]
      have hgT : ((t + 1).choose (t + 1) : ℤ) * 2 ^ (t + 1 - (t + 1))
          * (8 ^ (t + 1 + 1) - 3) = 8 ^ (t + 1 + 1) - 3 := by
        rw [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul,
          one_mul]
      rw [hpT, hp0] at hfull
      linear_combination hfull - hg0 - hgT
    rw [hG] at hsum0
    have hStep1 : (2 * medianEulerInitialRow (t + 1))
        ≡ 2 - (8 * 10 ^ (t + 1) - 3 * 3 ^ (t + 1) - 2 ^ (t + 1) * 5
          - (8 ^ (t + 1 + 1) - 3)) [ZMOD 15] := by
      have heq : 2 * medianEulerInitialRow (t + 1)
          = 2 - (∑ i ∈ Finset.range t, ((t + 1).choose (i + 1) : ℤ)
            * medianEulerInitialRow (i + 1) * 2 ^ (t + 1 - (i + 1))) := by
        linear_combination hlin
      rw [heq]
      exact (Int.ModEq.refl 2).sub hsum0
    have hStep2 : (2 - (8 * 10 ^ (t + 1) - 3 * 3 ^ (t + 1) - 2 ^ (t + 1) * 5
          - (8 ^ (t + 1 + 1) - 3)) : ℤ)
        ≡ 2 * (8 ^ (t + 1 + 1) - 3) [ZMOD 15] := by
      have hscalar' : (8 * 10 ^ (t + 1) - 5 * 2 ^ (t + 1) - 3 * 3 ^ (t + 1)
          + 8 ^ (t + 1 + 1) - 3 : ℤ) ≡ 2 [ZMOD 15] := by
        have hscalar := me_scalar15 (t + 1) (by omega)
        have hp3 : (3 : ℤ) ^ (t + 1 + 1) = 3 * 3 ^ (t + 1) := pow_succ' _ _
        rwa [hp3] at hscalar
      have h0 : ((8 * 10 ^ (t + 1) - 5 * 2 ^ (t + 1) - 3 * 3 ^ (t + 1)
          + 8 ^ (t + 1 + 1) - 3) - 2 : ℤ) ≡ 0 [ZMOD 15] := by
        simpa using hscalar'.sub (Int.ModEq.refl 2)
      have hfin := (Int.ModEq.refl (2 * (8 ^ (t + 1 + 1) - 3))).sub h0
      rw [sub_zero] at hfin
      have hring : (2 - (8 * 10 ^ (t + 1) - 3 * 3 ^ (t + 1) - 2 ^ (t + 1) * 5
          - (8 ^ (t + 1 + 1) - 3)) : ℤ)
          = 2 * (8 ^ (t + 1 + 1) - 3)
            - ((8 * 10 ^ (t + 1) - 5 * 2 ^ (t + 1) - 3 * 3 ^ (t + 1)
              + 8 ^ (t + 1 + 1) - 3) - 2) := by
        ring
      rw [hring]
      exact hfin
    have h2a := hStep1.trans hStep2
    have hcancel := Int.ModEq.cancel_left_div_gcd (show (0 : ℤ) < 15 by norm_num)
      h2a
    have hgcd : (15 : ℤ) / Int.gcd 15 2 = 15 := by decide
    rw [hgcd] at hcancel
    rw [me_init_succ] at hcancel
    exact hcancel

-- Scalar congruence mod 3: both sides vanish for `n ≥ 1`.
private theorem me_seidel_scalar3 (n : ℕ) (hn : 1 ≤ n) :
    (8 ^ (n + 2) * 9 ^ n - 3 * 2 ^ n : ℤ) ≡ ((-3 : ℤ)) ^ n [ZMOD 3] := by
  have hA0 : ((8 : ℤ) ^ (n + 2) * 9 ^ n) ≡ 0 [ZMOD 3] := by
    have h9 : ((9 : ℤ) ^ n) ≡ 0 [ZMOD 3] := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [pow_succ']
      have h := (by decide : (9 : ℤ) ≡ 0 [ZMOD 3]).mul
        (Int.ModEq.refl ((9 : ℤ) ^ t))
      simpa using h
    have h := (Int.ModEq.refl ((8 : ℤ) ^ (n + 2))).mul h9
    simpa using h
  have hB0 : ((3 : ℤ) * 2 ^ n) ≡ 0 [ZMOD 3] := by
    have h := (by decide : (3 : ℤ) ≡ 0 [ZMOD 3]).mul
      (Int.ModEq.refl ((2 : ℤ) ^ n))
    simpa using h
  have hLHS0 : ((8 : ℤ) ^ (n + 2) * 9 ^ n - 3 * 2 ^ n) ≡ 0 [ZMOD 3] := by
    have h := hA0.sub hB0
    simpa using h
  have hRHS0 : (((-3 : ℤ)) ^ n) ≡ 0 [ZMOD 3] := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ']
    have h := (by decide : (-3 : ℤ) ≡ 0 [ZMOD 3]).mul
      (Int.ModEq.refl (((-3 : ℤ)) ^ t))
    simpa using h
  exact hLHS0.trans hRHS0.symm

-- Scalar congruence mod 5: both sides equal `2 ^ n`.
private theorem me_seidel_scalar5 (n : ℕ) :
    (8 ^ (n + 2) * 9 ^ n - 3 * 2 ^ n : ℤ) ≡ ((-3 : ℤ)) ^ n [ZMOD 5] := by
  have e4 : ((3 : ℤ) ^ (n + 2) * 4 ^ n) = 9 * 12 ^ n := by
    have h1 : (3 : ℤ) ^ (n + 2) = 9 * 3 ^ n := by
      rw [pow_add, pow_two]
      ring
    have h2 : ((9 * 3 ^ n) * 4 ^ n : ℤ) = 9 * ((3 * 4) ^ n) := by
      rw [mul_pow]
      ring
    have h34 : (3 : ℤ) * 4 = 12 := by norm_num
    rw [h1, h2, h34]
  have hA : ((8 : ℤ) ^ (n + 2) * 9 ^ n) ≡ 4 * 2 ^ n [ZMOD 5] := by
    have e1 : ((8 : ℤ) ^ (n + 2)) ≡ 3 ^ (n + 2) [ZMOD 5] :=
      (by decide : (8 : ℤ) ≡ 3 [ZMOD 5]).pow _
    have e2 : ((9 : ℤ) ^ n) ≡ 4 ^ n [ZMOD 5] :=
      (by decide : (9 : ℤ) ≡ 4 [ZMOD 5]).pow _
    have e3 := e1.mul e2
    rw [e4] at e3
    have e5 : ((9 : ℤ) * 12 ^ n) ≡ 4 * 2 ^ n [ZMOD 5] :=
      (by decide : (9 : ℤ) ≡ 4 [ZMOD 5]).mul
        ((by decide : (12 : ℤ) ≡ 2 [ZMOD 5]).pow n)
    exact e3.trans e5
  have hLHS : ((8 : ℤ) ^ (n + 2) * 9 ^ n - 3 * 2 ^ n) ≡ 2 ^ n [ZMOD 5] := by
    have hsub := hA.sub
      ((by decide : (3 : ℤ) ≡ 3 [ZMOD 5]).mul (Int.ModEq.refl ((2 : ℤ) ^ n)))
    have hrr : ((4 * 2 ^ n - 3 * 2 ^ n : ℤ)) = 2 ^ n := by ring
    rwa [hrr] at hsub
  have hRHS : (((-3 : ℤ)) ^ n) ≡ 2 ^ n [ZMOD 5] :=
    (by decide : (-3 : ℤ) ≡ 2 [ZMOD 5]).pow n
  exact hLHS.trans hRHS.symm

-- Scalar congruence mod 15.
private theorem me_seidel_scalar15 (n : ℕ) (hn : 1 ≤ n) :
    (8 ^ (n + 2) * 9 ^ n - 3 * 2 ^ n : ℤ) ≡ ((-3 : ℤ)) ^ n [ZMOD 15] := by
  have h3 := me_seidel_scalar3 n hn
  have h5 := me_seidel_scalar5 n
  have hcop : Nat.Coprime (3 : ℤ).natAbs (5 : ℤ).natAbs := by decide
  have h := (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h3, h5⟩
  have hmul : (3 : ℤ) * 5 = 15 := by norm_num
  rwa [hmul] at h

-- The Seidel entry mod 15.
open scoped BigOperators in
private theorem me_seidel_modEq (n : ℕ) (hn : 1 ≤ n) :
    eulerSeidelMatrix medianEulerInitialRow (n + 1) n
    ≡ ((-3 : ℤ)) ^ n [ZMOD 15] := by
  have hclosed := eulerSeidelMatrix_eq_sum medianEulerInitialRow (n + 1) n
  simp only [nsmul_eq_mul] at hclosed
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((n.choose i : ℤ)) * medianEulerInitialRow (n + 1 + i)
      ≡ ((n.choose i : ℤ)) * (8 ^ (n + 1 + i + 1) - 3) [ZMOD 15] := by
    intro i hi
    have hi1 : 1 ≤ n + 1 + i := by omega
    have hih := me_coeff_modEq (n + 1 + i) hi1
    have he : n + 1 + i = (n + i) + 1 := by omega
    rw [he] at hih ⊢
    have ha : medianEulerInitialRow ((n + i) + 1)
        ≡ (8 : ℤ) ^ (((n + i) + 1) + 1) - 3 [ZMOD 15] := by
      rw [me_init_succ]
      exact hih
    exact (Int.ModEq.refl _).mul ha
  have hsum := me_modeq_sum15 hterm
  have hSeq : eulerSeidelMatrix medianEulerInitialRow (n + 1) n
      ≡ (∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℤ)) * (8 ^ (n + 1 + i + 1) - 3)) [ZMOD 15] := by
    rw [hclosed]
    exact hsum
  have hC : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℤ))) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hclosed2 : (∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℤ)) * (8 ^ (n + 1 + i + 1) - 3))
      = 8 ^ (n + 2) * 9 ^ n - 3 * 2 ^ n := by
    have e : ∀ i ∈ Finset.range (n + 1),
        ((n.choose i : ℤ)) * (8 ^ (n + 1 + i + 1) - 3)
        = 8 ^ (n + 2) * (8 ^ i * 1 ^ (n - i) * ((n.choose i : ℤ)))
          - 3 * ((n.choose i : ℤ)) := by
      intro i _
      have hexp : n + 1 + i + 1 = (n + 2) + i := by omega
      rw [hexp, pow_add]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have bp := add_pow (8 : ℤ) 1 n
    rw [← bp]
    have hC3 : (∑ i ∈ Finset.range (n + 1), 3 * ((n.choose i : ℤ)))
        = 3 * 2 ^ n := by
      rw [← Finset.mul_sum, hC]
    rw [hC3]
    norm_num
  rw [hclosed2] at hSeq
  have hscalar := me_seidel_scalar15 n hn
  exact hSeq.trans hscalar

-- Auxiliary: diagonal entries of an antisymmetric Seidel matrix vanish.
private theorem me_diag_zero (a : ℕ → ℤ)
    (hA : ∀ n k : ℕ, eulerSeidelMatrix a n k
      = (-1 : ℤ) ^ (n + k + 1) * eulerSeidelMatrix a k n)
    (r : ℕ) : eulerSeidelMatrix a r r = 0 := by
  have h := hA r r
  have he : (-1 : ℤ) ^ (r + r + 1) = -1 := Odd.neg_one_pow ⟨r, by omega⟩
  rw [he] at h
  linarith

-- Step `Ev`: descending along the even antidiagonal, using `Q` one level down.
private theorem me_ev_step (a : ℕ → ℤ) (p j : ℕ) (hp : 1 ≤ p)
    (hjp : j + 1 ≤ p)
    (hQprev : ∀ j' k' : ℕ, j' + k' = 2 * (p - 1) + 1 → j' ≤ p - 1 →
      0 ≤ (-1 : ℤ) ^ (p - 1) * eulerSeidelMatrix a j' k')
    (hnext : 0 ≤ (-1 : ℤ) ^ (p + 1) *
      eulerSeidelMatrix a (j + 1) (2 * p - (j + 1))) :
    0 ≤ (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j (2 * p - j) := by
  have eK : (2 * p - j - 1) + 1 = 2 * p - j := by omega
  have hdef : eulerSeidelMatrix a j (2 * p - j)
      = eulerSeidelMatrix a j (2 * p - j - 1)
        + eulerSeidelMatrix a (j + 1) (2 * p - j - 1) := by
    have hrfl : eulerSeidelMatrix a j ((2 * p - j - 1) + 1)
        = eulerSeidelMatrix a j (2 * p - j - 1)
          + eulerSeidelMatrix a (j + 1) (2 * p - j - 1) := rfl
    rwa [eK] at hrfl
  have hpp : (-1 : ℤ) ^ (p + 1) = (-1 : ℤ) ^ (p - 1) := by
    have e : p + 1 = (p - 1) + 2 := by omega
    rw [e, pow_add, pow_two]
    ring
  have hQterm : 0 ≤ (-1 : ℤ) ^ (p + 1) *
      eulerSeidelMatrix a j (2 * p - j - 1) := by
    have h1 : j + (2 * p - j - 1) = 2 * (p - 1) + 1 := by omega
    have h2 : j ≤ p - 1 := by omega
    have h3 := hQprev j (2 * p - j - 1) h1 h2
    rwa [← hpp] at h3
  have eK2 : 2 * p - (j + 1) = 2 * p - j - 1 := by omega
  rw [eK2] at hnext
  have key : (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j (2 * p - j)
      = (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j (2 * p - j - 1)
        + (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a (j + 1) (2 * p - j - 1) := by
    rw [← mul_add, ← hdef]
  rw [key]
  exact add_nonneg hQterm hnext

-- Step `Q`: ascending along the odd antidiagonal, using `Ev` at the same level.
private theorem me_q_step (a : ℕ → ℤ) (p j : ℕ) (hjp : j + 1 ≤ p)
    (hEv : ∀ j' k' : ℕ, j' + k' = 2 * p → j' ≤ p →
      0 ≤ (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j' k')
    (hprev : 0 ≤ (-1 : ℤ) ^ p * eulerSeidelMatrix a j (2 * p + 1 - j)) :
    0 ≤ (-1 : ℤ) ^ p * eulerSeidelMatrix a (j + 1) (2 * p + 1 - (j + 1)) := by
  have eK' : 2 * p + 1 - (j + 1) + 1 = 2 * p + 1 - j := by omega
  have hdef : eulerSeidelMatrix a j (2 * p + 1 - j)
      = eulerSeidelMatrix a j (2 * p + 1 - (j + 1))
        + eulerSeidelMatrix a (j + 1) (2 * p + 1 - (j + 1)) := by
    have hrfl : eulerSeidelMatrix a j ((2 * p + 1 - (j + 1)) + 1)
        = eulerSeidelMatrix a j (2 * p + 1 - (j + 1))
          + eulerSeidelMatrix a (j + 1) (2 * p + 1 - (j + 1)) := rfl
    rwa [eK'] at hrfl
  have hevT := hEv j (2 * p + 1 - (j + 1)) (by omega) (by omega)
  have hps : (-1 : ℤ) ^ (p + 1) = (-1 : ℤ) ^ p * (-1) := pow_succ _ _
  have key : (-1 : ℤ) ^ p * eulerSeidelMatrix a (j + 1) (2 * p + 1 - (j + 1))
      = (-1 : ℤ) ^ p * eulerSeidelMatrix a j (2 * p + 1 - j)
        + (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j (2 * p + 1 - (j + 1)) := by
    rw [hps]
    linear_combination (-(-1 : ℤ) ^ p) * hdef
  rw [key]
  exact add_nonneg hprev hevT

-- General: sign of median entries of an antisymmetric Euler–Seidel matrix.
private theorem me_seidel_median_sign_aux (a : ℕ → ℤ)
    (hA : ∀ n k : ℕ, eulerSeidelMatrix a n k
      = (-1 : ℤ) ^ (n + k + 1) * eulerSeidelMatrix a k n)
    (hB : ∀ p : ℕ, 0 ≤ (-1 : ℤ) ^ p * a (2 * p + 1))
    (n : ℕ) : 0 ≤ (-1 : ℤ) ^ n * eulerSeidelMatrix a (n + 1) n := by
  have hdiag : ∀ r : ℕ, eulerSeidelMatrix a r r = 0 :=
    fun r => me_diag_zero a hA r
  have hQall : ∀ p : ℕ, ∀ j k : ℕ, j + k = 2 * p + 1 → j ≤ p →
      0 ≤ (-1 : ℤ) ^ p * eulerSeidelMatrix a j k := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      have hEv1 : ∀ d : ℕ, d ≤ p →
          0 ≤ (-1 : ℤ) ^ (p + 1) *
            eulerSeidelMatrix a (p - d) (2 * p - (p - d)) := by
        intro d
        induction d with
        | zero =>
          intro _
          have e0 : 2 * p - (p - 0) = p := by omega
          rw [e0, Nat.sub_zero, hdiag]
          simp
        | succ d ihd =>
          intro hd
          have hp : 1 ≤ p := by omega
          have hprev := ihd (by omega : d ≤ p)
          have eJ : p - (d + 1) + 1 = p - d := by omega
          have hnext : 0 ≤ (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a
              (p - (d + 1) + 1) (2 * p - (p - (d + 1) + 1)) := by
            rw [← eJ] at hprev
            exact hprev
          have hjp : p - (d + 1) + 1 ≤ p := by omega
          have hQprev : ∀ j' k' : ℕ, j' + k' = 2 * (p - 1) + 1 → j' ≤ p - 1 →
              0 ≤ (-1 : ℤ) ^ (p - 1) * eulerSeidelMatrix a j' k' := by
            intro j' k' h1 h2
            exact ih (p - 1) (by omega) j' k' h1 h2
          exact me_ev_step a p (p - (d + 1)) hp hjp hQprev hnext
      have hEv2 : ∀ j k : ℕ, j + k = 2 * p → j ≤ p →
          0 ≤ (-1 : ℤ) ^ (p + 1) * eulerSeidelMatrix a j k := by
        intro j k hjk hjp
        have hk : k = 2 * p - j := by omega
        rw [hk]
        have h := hEv1 (p - j) (by omega)
        have e1 : p - (p - j) = j := by omega
        rw [e1] at h
        exact h
      have hQ1 : ∀ j : ℕ, j ≤ p →
          0 ≤ (-1 : ℤ) ^ p * eulerSeidelMatrix a j (2 * p + 1 - j) := by
        intro j
        induction j with
        | zero =>
          intro _
          have e0 : 2 * p + 1 - 0 = 2 * p + 1 := Nat.sub_zero _
          rw [e0]
          have hS0 := hA 0 (2 * p + 1)
          have hS00 : eulerSeidelMatrix a (2 * p + 1) 0 = a (2 * p + 1) := rfl
          have eexp : 0 + (2 * p + 1) + 1 = 2 * p + 2 := by omega
          rw [eexp] at hS0
          have hev : (-1 : ℤ) ^ (2 * p + 2) = 1 :=
            Even.neg_one_pow ⟨p + 1, by omega⟩
          rw [hev, hS00, one_mul] at hS0
          rw [hS0]
          exact hB p
        | succ j ihj =>
          intro hj
          have hprev := ihj (by omega : j ≤ p)
          exact me_q_step a p j hj hEv2 hprev
      intro j k hjk hjp
      have hk : k = 2 * p + 1 - j := by omega
      rw [hk]
      exact hQ1 j hjp
  have hQ := hQall n n (n + 1) (by omega) (le_refl n)
  have hdef : eulerSeidelMatrix a n (n + 1)
      = eulerSeidelMatrix a n n + eulerSeidelMatrix a (n + 1) n := rfl
  have heq : eulerSeidelMatrix a (n + 1) n
      = eulerSeidelMatrix a n (n + 1) - eulerSeidelMatrix a n n := by
    linear_combination -hdef
  rw [heq, hdiag n, sub_zero]
  exact hQ

-- Instance for the median Euler initial row.
private theorem me_median_sign (n : ℕ) :
    0 ≤ (-1 : ℤ) ^ n * eulerSeidelMatrix medianEulerInitialRow (n + 1) n :=
  me_seidel_median_sign_aux medianEulerInitialRow me_seidel_antisymm_inst
    me_init_odd_sign n

@[expose] public section

/-- **Median Euler numbers modulo three and five.** For every natural number $n \ge 1$, the median
Euler number $R_n$ is divisible by $3$, and $R_n / 3 \equiv 3^{n-1} \pmod 5$.

Proves `Wanted` entry `medianEulerNumber_div_three_and_modFive`.
-/
public theorem medianEulerNumber_div_three_and_modFive {n : ℕ} (hn : 1 ≤ n) :
    3 ∣ medianEulerNumber n ∧ Nat.ModEq 5 (medianEulerNumber n / 3) (3 ^ (n - 1)) := by
  have hR : medianEulerNumber n
      = (eulerSeidelMatrix medianEulerInitialRow (n + 1) n).natAbs := rfl
  have habs : ((-1 : ℤ) ^ n * eulerSeidelMatrix medianEulerInitialRow (n + 1) n).natAbs
      = (eulerSeidelMatrix medianEulerInitialRow (n + 1) n).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow,
      one_mul]
  have hRint : ((medianEulerNumber n : ℕ) : ℤ)
      = (-1 : ℤ) ^ n * eulerSeidelMatrix medianEulerInitialRow (n + 1) n := by
    have h := Int.natAbs_of_nonneg (me_median_sign n)
    rw [habs] at h
    rwa [hR]
  have h3n : ((-1 : ℤ) ^ n * eulerSeidelMatrix medianEulerInitialRow (n + 1) n)
      ≡ 3 ^ n [ZMOD 15] := by
    have hmul := (Int.ModEq.refl ((-1 : ℤ) ^ n)).mul (me_seidel_modEq n hn)
    have heq : ((-1 : ℤ) ^ n * (-3) ^ n) = 3 ^ n := by
      rw [← mul_pow, show (-1 : ℤ) * (-3) = 3 from by norm_num]
    rwa [heq] at hmul
  have hRmod : ((medianEulerNumber n : ℕ) : ℤ) ≡ 3 ^ n [ZMOD 15] := by
    rw [hRint]
    exact h3n
  have h15 : (15 : ℤ) = 3 * 5 := by norm_num
  have h3mod3 : ((medianEulerNumber n : ℕ) : ℤ) ≡ 3 ^ n [ZMOD 3] := by
    rw [h15] at hRmod
    exact hRmod.of_mul_right 5
  have hdvd3n : (3 : ℤ) ∣ 3 ^ n := dvd_pow_self 3 (by omega : n ≠ 0)
  have hdvdsub : (3 : ℤ) ∣ 3 ^ n - ((medianEulerNumber n : ℕ) : ℤ) :=
    Int.modEq_iff_dvd.mp h3mod3
  have hR3 : (3 : ℤ) ∣ ((medianEulerNumber n : ℕ) : ℤ) := by
    have h := hdvd3n.sub hdvdsub
    rwa [sub_sub_cancel] at h
  have hfst : 3 ∣ medianEulerNumber n := by
    exact_mod_cast hR3
  refine ⟨hfst, ?_⟩
  have hR3eq : medianEulerNumber n = 3 * (medianEulerNumber n / 3) :=
    (Nat.mul_div_cancel' hfst).symm
  have hcast : ((medianEulerNumber n : ℕ) : ℤ)
      = 3 * ((medianEulerNumber n / 3 : ℕ) : ℤ) := by
    exact_mod_cast hR3eq
  have hn1 : n = (n - 1) + 1 := by omega
  have hpow : (3 : ℤ) ^ n = 3 * 3 ^ (n - 1) := by
    conv_lhs => rw [hn1, pow_succ]
    ring
  rw [hcast, hpow] at hRmod
  have hcancel := Int.ModEq.cancel_left_div_gcd (show (0 : ℤ) < 15 by norm_num)
    hRmod
  have hgcd : (15 : ℤ) / Int.gcd 15 3 = 5 := by decide
  rw [hgcd] at hcancel
  rw [← Int.natCast_modEq_iff]
  push_cast
  exact hcancel

end

end MetaMathlibExt
