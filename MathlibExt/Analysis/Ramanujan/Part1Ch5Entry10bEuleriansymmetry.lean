/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry10bEuleriansymmetry

open scoped BigOperators
open Finset

noncomputable section

/-- **Even-index Euler numbers.** The integers $E_0, E_2, E_4, \dots$ defined recursively by
$E_0 = 1$ and $E_{2m} = -\sum_{k=0}^{m-1} \binom{2m}{2k} E_{2k}$ for $m \ge 1$; equivalently,
$\sum_{k=0}^{m} \binom{2m}{2k} E_{2k}$ is $1$ for $m = 0$ and $0$ for $m \ge 1$. The value at
$n$ is $E_{2n}$.

The first values are $E_0 = 1$, $E_2 = -1$, $E_4 = 5$, $E_6 = -61$; the absolute values are the
secant numbers. -/
def chapter5EulerEven (n : ℕ) : ℤ :=
  Nat.strongRec (motive := fun _ => ℤ)
    (fun m previous =>
      if m = 0 then 1
      else -∑ k : Fin m,
        (Nat.choose (2 * m) (2 * k.val) : ℤ) * previous k.val k.isLt) n

/-- **The initial even-index Euler number.** $E_0 = 1$. -/
theorem chapter5EulerEven_zero : chapter5EulerEven 0 = 1 := by
  unfold chapter5EulerEven
  rw [Nat.strongRec_eq]
  simp

/-- **Recursion for the even-index Euler numbers.** For every natural number $m \ge 1$,
$E_{2m} = -\sum_{k=0}^{m-1} \binom{2m}{2k} E_{2k}$. -/
theorem chapter5EulerEven_step (m : ℕ) (hm : m ≠ 0) :
    chapter5EulerEven m =
      -∑ k : Fin m, (Nat.choose (2 * m) (2 * k.val) : ℤ) * chapter5EulerEven k.val := by
  conv_lhs => unfold chapter5EulerEven; rw [Nat.strongRec_eq]
  simp only [hm, ↓reduceIte]
  rfl

/-- **Binomial recurrence for the even-index Euler numbers.** For every natural number $m$,
$\sum_{k=0}^{m} \binom{2m}{2k} E_{2k}$ is $1$ if $m = 0$ and $0$ if $m \ge 1$. -/
theorem chapter5EulerEven_recurrence (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k =
      if m = 0 then 1 else 0 := by
  cases m with
  | zero => simp [chapter5EulerEven_zero]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [Finset.sum_range_succ]
    have hlast : ((Nat.choose (2 * (m + 1)) (2 * (m + 1)) : ℕ) : ℤ) *
        chapter5EulerEven (m + 1) = chapter5EulerEven (m + 1) := by
      simp [Nat.choose_self]
    rw [hlast]
    have hstep := chapter5EulerEven_step (m + 1) (Nat.succ_ne_zero m)
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      ((Nat.choose (2 * (m+1)) (2 * k) : ℕ):ℤ) * chapter5EulerEven k)] at hstep
    linarith [hstep]

private theorem eulerEven_recurrenceQ (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) * ((chapter5EulerEven k : ℤ) : ℚ) =
      if m = 0 then 1 else 0 := by
  have h := chapter5EulerEven_recurrence m
  have h2 : ((∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k : ℤ) : ℚ) =
      ((if m = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by rw [h]
  rw [Int.cast_sum] at h2
  simp only [Int.cast_mul, Int.cast_natCast] at h2
  rw [h2]
  split <;> simp

private theorem sum_range_two_mul_succ (g : ℕ → ℚ) (m : ℕ)
    (hg : ∀ k, Odd k → g k = 0) :
    ∑ k ∈ Finset.range (2 * m + 1), g k = ∑ j ∈ Finset.range (m + 1), g (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    conv_lhs => rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, hg _ hodd, add_zero]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [ih]
    congr 1

private def eulerEGF : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then 0
    else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ))

private def coshPS : PowerSeries ℚ :=
  (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
    PowerSeries.C (2⁻¹ : ℚ)

private def sinhPS : PowerSeries ℚ :=
  (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
    PowerSeries.C (2⁻¹ : ℚ)

private theorem coeff_eulerEGF (n : ℕ) :
    PowerSeries.coeff n eulerEGF =
      if n % 2 = 1 then 0
      else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ)) := by
  simp [eulerEGF, PowerSeries.coeff_mk]

private theorem coeff_coshPS (n : ℕ) :
    PowerSeries.coeff n coshPS =
      (if n % 2 = 0 then (1 : ℚ) / (n.factorial : ℚ) else 0) := by
  unfold coshPS
  rw [PowerSeries.coeff_mul_C]
  have h1 : PowerSeries.coeff n
      (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      (1 : ℚ) / (n.factorial : ℚ) + (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
    have e1 : PowerSeries.coeff n (PowerSeries.exp ℚ) = (1 : ℚ) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_exp]; simp
    have e2 : PowerSeries.coeff n ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
        (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp [div_eq_mul_inv]
    rw [map_add, e1, e2]
  rw [h1]
  by_cases hn : n % 2 = 0
  · have hpow : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr hn)
    simp [hn, hpow]
    field_simp
    ring
  · have hodd : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    simp only [hn, hodd, ↓reduceIte]
    have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring

private theorem coeff_sinhPS (n : ℕ) :
    PowerSeries.coeff n sinhPS =
      (if n % 2 = 1 then (1 : ℚ) / (n.factorial : ℚ) else 0) := by
  unfold sinhPS
  rw [PowerSeries.coeff_mul_C]
  have h1 : PowerSeries.coeff n
      (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      (1 : ℚ) / (n.factorial : ℚ) - (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
    have e1 : PowerSeries.coeff n (PowerSeries.exp ℚ) = (1 : ℚ) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_exp]; simp
    have e2 : PowerSeries.coeff n ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
        (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp [div_eq_mul_inv]
    rw [map_sub, e1, e2]
  rw [h1]
  by_cases hn : n % 2 = 1
  · have hpow : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hn)
    simp [hn, hpow]
    field_simp
    ring
  · have hpow : (-1 : ℚ) ^ n = 1 := by
      have hev : Even n := Nat.even_iff.mpr (by omega)
      exact Even.neg_one_pow hev
    simp [hn, hpow]

private theorem euler_cosh : eulerEGF * coshPS = 1 := by
  ext n
  have hant : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff p.1 eulerEGF * PowerSeries.coeff p.2 coshPS) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS := by
    have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i eulerEGF * PowerSeries.coeff j coshPS) n
    simpa using h
  rw [PowerSeries.coeff_mul, hant, PowerSeries.coeff_one]
  by_cases hn : n % 2 = 1
  · have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ n := by omega
    by_cases hk2 : k % 2 = 1
    · rw [coeff_eulerEGF, ite_eq_left hk2, zero_mul]
    · have hnk : (n - k) % 2 = 1 := by omega
      have hne : ¬ ((n - k) % 2 = 0) := by omega
      rw [coeff_coshPS, ite_eq_right hne, mul_zero]
  · have hn0 : n % 2 = 0 := by omega
    -- n even; write n = 2 * (n/2)
    have hn2 : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.mpr hn0)).symm
    have hfact_n : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    -- restrict to even indices
    have hsum : ∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS =
        ∑ j ∈ Finset.range (n / 2 + 1),
          PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS := by
      have hnr : n + 1 = 2 * (n / 2) + 1 := by omega
      rw [hnr]
      apply sum_range_two_mul_succ
      intro k hkodd
      rw [coeff_eulerEGF, ite_eq_left (Nat.odd_iff.mp hkodd), zero_mul]
    rw [hsum]
    -- each term equals choose * Euler / n!
    have hterm : ∀ j ∈ Finset.range (n / 2 + 1),
        PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS =
        (((Nat.choose n (2 * j) : ℕ) : ℚ) * ((chapter5EulerEven j : ℤ) : ℚ)) /
          (n.factorial : ℚ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjn : 2 * j ≤ n := by omega
      have hj2 : (2 * j) / 2 = j := by omega
      have hjm : n - 2 * j = 2 * (n / 2 - j) := by omega
      have hmod1 : ¬ ((2 * j) % 2 = 1) := by omega
      have hmod2 : (n - 2 * j) % 2 = 0 := by omega
      rw [coeff_eulerEGF, ite_eq_right hmod1, coeff_coshPS, ite_eq_left hmod2, hj2]
      have hchoose := Nat.choose_mul_factorial_mul_factorial hjn
      have hfact1 : ((j.factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      -- (2j)! = j-th factorial appearing via hj2? need (2*j)! vs j! confusion:
      -- e_{2j} denominator is ((2*j)!), c denominator is ((n-2j)!).
      -- Combine into C(n,2j)/n!.
      have hcast : ((Nat.choose n (2 * j) : ℕ) : ℚ) * (((2 * j).factorial : ℕ) : ℚ) *
          (((n - 2 * j).factorial : ℕ) : ℚ) = ((n.factorial : ℕ) : ℚ) := by
        exact_mod_cast hchoose
      have hd1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * j)
      have hd2 : ((((n - 2 * j).factorial : ℕ)) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - 2 * j)
      have hAB : ((((2 * j).factorial : ℕ) : ℚ) * ((((n - 2 * j).factorial : ℕ)) : ℚ)) ≠ 0 :=
        mul_ne_zero hd1 hd2
      rw [div_mul_div_comm, mul_one, div_eq_div_iff hAB hfact_n]
      linear_combination -((chapter5EulerEven j : ℤ) : ℚ) * hcast
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_div]
    have hrec := eulerEven_recurrenceQ (n / 2)
    rw [← hn2] at hrec
    by_cases hm : n / 2 = 0
    · have hn00 : n = 0 := by omega
      subst hn00
      simp only [Nat.zero_div, zero_add, range_one, sum_singleton, mul_zero,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.factorial_zero, div_one,
        ↓reduceIte, Rat.intCast_eq_one_iff] at hrec ⊢
      rw [hrec]
    · have hn00 : n ≠ 0 := by omega
      simp only [hm, hn00, ↓reduceIte] at hrec ⊢
      rw [hrec]
      simp

-- Bernoulli / exponential facts
private theorem exp_neg_mul :
    PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) = 1 := by
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 (-1)
  have h1 : (1 : ℚ) + (-1) = 0 := by ring
  rw [h1] at h
  have hr1 : (PowerSeries.rescale (1 : ℚ)) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
    simp [PowerSeries.rescale_one]
  rw [hr1] at h
  have h0 : (PowerSeries.rescale (0 : ℚ)) (PowerSeries.exp ℚ) = 1 := by
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  rw [h0] at h
  exact h

private theorem exp_sq2 :
    PowerSeries.exp ℚ ^ 2 = (PowerSeries.rescale (2 : ℚ)) (PowerSeries.exp ℚ) := by
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 1
  have hr1 : (PowerSeries.rescale (1 : ℚ)) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
    simp [PowerSeries.rescale_one]
  rw [hr1] at h
  have h2 : (1 : ℚ) + 1 = 2 := by ring
  rw [h2] at h
  rw [sq]
  exact h

private theorem exp_four :
    PowerSeries.exp ℚ ^ 4 = (PowerSeries.rescale (4 : ℚ)) (PowerSeries.exp ℚ) := by
  have ha2 := exp_sq2
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 2 2
  have h22 : (2 : ℚ) + 2 = 4 := by ring
  rw [h22] at h
  have hp : (PowerSeries.exp ℚ : PowerSeries ℚ) ^ 4 = ((PowerSeries.exp ℚ) ^ 2) ^ 2 := by ring
  rw [hp, ha2, sq]
  exact h

private theorem cofactor2 (s u a f X : PowerSeries ℚ) :
    let A := a ^ 2 - 1
    let Bf := a ^ 4 - 1
    let R1 := s * Bf - 4 * X
    let R2 := u * A - 2 * X
    let R5 := a * f - 1
    let G := (X + s - u) * (a + f) - X * (a - f)
    let M := A * Bf
    G * M = (a + f) * A * R1 - (a + f) * Bf * R2 +
      (X * (2 * a * A ^ 2)) * R5 := by
  simp only
  ring

private theorem C4_eq : PowerSeries.C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat _ _
private theorem C2_eq : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat _ _

private def berB : PowerSeries ℚ := bernoulliPowerSeries ℚ
private def berB2 : PowerSeries ℚ := (PowerSeries.rescale 2) berB
private def berB4 : PowerSeries ℚ := (PowerSeries.rescale 4) berB
private def tanhPS : PowerSeries ℚ := sinhPS * eulerEGF

private theorem berB_coeff (n : ℕ) :
    PowerSeries.coeff n berB = bernoulli n / (n.factorial : ℚ) := by
  simp [berB, bernoulliPowerSeries]

private theorem berB2_rel :
    berB2 * ((PowerSeries.exp ℚ) ^ 2 - 1) = 2 * PowerSeries.X := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h2 : (PowerSeries.rescale (2 : ℚ))
        (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) =
      (PowerSeries.rescale (2 : ℚ)) PowerSeries.X := by rw [hB]
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h2
  rw [C2_eq] at h2
  have ha2 := exp_sq2
  rw [← ha2] at h2
  unfold berB2 berB
  exact h2

private theorem berB4_rel :
    berB4 * ((PowerSeries.exp ℚ) ^ 4 - 1) = 4 * PowerSeries.X := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h4 : (PowerSeries.rescale (4 : ℚ))
        (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) =
      (PowerSeries.rescale (4 : ℚ)) PowerSeries.X := by rw [hB]
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h4
  rw [C4_eq] at h4
  have ha4 := exp_four
  rw [← ha4] at h4
  unfold berB4 berB
  exact h4

private theorem exp_coeff_one : PowerSeries.coeff 1 (PowerSeries.exp ℚ) = 1 := by
  rw [PowerSeries.coeff_exp]; simp

private theorem A2_ne : (PowerSeries.exp ℚ) ^ 2 - 1 ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff 1) hz
  simp only [map_sub, map_zero, PowerSeries.coeff_one] at hc
  rw [exp_sq2, PowerSeries.coeff_rescale, exp_coeff_one] at hc
  norm_num at hc

private theorem A4_ne : (PowerSeries.exp ℚ) ^ 4 - 1 ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff 1) hz
  simp only [map_sub, map_zero, PowerSeries.coeff_one] at hc
  rw [exp_four, PowerSeries.coeff_rescale, exp_coeff_one] at hc
  norm_num at hc

private theorem M_ne : ((PowerSeries.exp ℚ) ^ 2 - 1) * ((PowerSeries.exp ℚ) ^ 4 - 1) ≠ 0 :=
  mul_ne_zero A2_ne A4_ne

private theorem hCinv : PowerSeries.C (2⁻¹ : ℚ) * (2 : PowerSeries ℚ) = 1 := by
  rw [← C2_eq, ← map_mul]
  have h12 : (2⁻¹ : ℚ) * 2 = 1 := by ring
  rw [h12, map_one]

private theorem hEf : eulerEGF *
    (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) = 2 := by
  have hcosh : eulerEGF * coshPS = 1 := euler_cosh
  unfold coshPS at hcosh
  have hEC : (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
      PowerSeries.C (2⁻¹ : ℚ) = 1 := by
    calc (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
            PowerSeries.C (2⁻¹ : ℚ)
        = eulerEGF * ((PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
            PowerSeries.C (2⁻¹ : ℚ)) := by ring
      _ = 1 := hcosh
  calc eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))
      = (eulerEGF * (PowerSeries.exp ℚ +
          (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) * 1 := by ring
    _ = (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
          (PowerSeries.C (2⁻¹ : ℚ) * 2) := by rw [← hCinv]
    _ = ((eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
          PowerSeries.C (2⁻¹ : ℚ)) * 2 := by ring
    _ = 2 := by rw [hEC]; ring

private theorem hTf :
    (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
    2 * tanhPS := by
  unfold tanhPS sinhPS
  calc (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF
      = ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          eulerEGF) * 1 := by ring
    _ = ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF) *
          (PowerSeries.C (2⁻¹ : ℚ) * 2) := by rw [← hCinv]
    _ = 2 * (((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) * eulerEGF) := by ring

private theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro hz
  rw [← C2_eq] at hz
  have hc := congrArg (PowerSeries.coeff 0) hz
  simp only [PowerSeries.coeff_C, map_zero] at hc
  simp at hc

private theorem G'_eq :
    (PowerSeries.X + berB4 - berB2) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) -
      PowerSeries.X * (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) = 0 := by
  have hR1 : berB4 * ((PowerSeries.exp ℚ) ^ 4 - 1) - 4 * PowerSeries.X = 0 := by
    rw [berB4_rel]; ring
  have hR2 : berB2 * ((PowerSeries.exp ℚ) ^ 2 - 1) - 2 * PowerSeries.X = 0 := by
    rw [berB2_rel]; ring
  have hR5 : PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) - 1 = 0 := by
    rw [exp_neg_mul]; ring
  have hcof := cofactor2 berB4 berB2 (PowerSeries.exp ℚ)
    ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) PowerSeries.X
  simp only at hcof
  rw [hR1, hR2, hR5] at hcof
  simp only [mul_zero, sub_zero, add_zero] at hcof
  have hM := M_ne
  have hGM : ((PowerSeries.X + berB4 - berB2) *
      (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) -
      PowerSeries.X * (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
      (((PowerSeries.exp ℚ) ^ 2 - 1) * ((PowerSeries.exp ℚ) ^ 4 - 1)) = 0 := hcof
  rcases mul_eq_zero.mp hGM with h | h
  · exact h
  · exact absurd h hM

private theorem bernoulli_tanh :
    PowerSeries.X * tanhPS = PowerSeries.X + berB4 - berB2 := by
  have hG := G'_eq
  have hE := congrArg (· * eulerEGF) hG
  rw [sub_mul, zero_mul] at hE
  have e1 : (PowerSeries.X + berB4 - berB2) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
      (PowerSeries.X + berB4 - berB2) * 2 := by
    have hrw : (PowerSeries.X + berB4 - berB2) *
          (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
        (PowerSeries.X + berB4 - berB2) *
          (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) := by
      ring
    rw [hrw, hEf]
  have e2 : PowerSeries.X *
        (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
      PowerSeries.X * (2 * tanhPS) := by
    have hrw : PowerSeries.X *
          (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
        PowerSeries.X *
          ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF) := by
      ring
    rw [hrw, hTf]
  rw [e1, e2] at hE
  have h3 : (2 : PowerSeries ℚ) *
      ((PowerSeries.X + berB4 - berB2) - PowerSeries.X * tanhPS) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h two_ne
  · have heq : PowerSeries.X + berB4 - berB2 = PowerSeries.X * tanhPS :=
      sub_eq_zero.mp h
    rw [heq]

-- Derivatives
private theorem derivative_rescale_q (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative ((PowerSeries.rescale a) f) =
      PowerSeries.C a * (PowerSeries.rescale a) (PowerSeries.derivative f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  ring

private theorem derivative_neg_exp :
    PowerSeries.derivative ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      PowerSeries.C (-1) * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) := by
  rw [derivative_rescale_q, PowerSeries.derivative_exp ℚ]

private theorem derivative_sinh : PowerSeries.derivative sinhPS = coshPS := by
  unfold sinhPS coshPS
  have hde : PowerSeries.derivative (PowerSeries.exp ℚ) = PowerSeries.exp ℚ :=
    PowerSeries.derivative_exp ℚ
  have hCm1 : PowerSeries.C (-1 : ℚ) = -1 := by simp
  have e1 : PowerSeries.derivative
        ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) =
      PowerSeries.C (2⁻¹ : ℚ) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) := by
    rw [Derivation.leibniz]
    simp only [PowerSeries.derivative_C, smul_eq_mul]
    rw [map_sub, hde, derivative_neg_exp, hCm1]
    ring
  rw [e1]
  ring

private theorem derivative_cosh : PowerSeries.derivative coshPS = sinhPS := by
  unfold sinhPS coshPS
  have hde : PowerSeries.derivative (PowerSeries.exp ℚ) = PowerSeries.exp ℚ :=
    PowerSeries.derivative_exp ℚ
  have hCm1 : PowerSeries.C (-1 : ℚ) = -1 := by simp
  have e1 : PowerSeries.derivative
        ((PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) =
      PowerSeries.C (2⁻¹ : ℚ) *
        (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) := by
    rw [Derivation.leibniz]
    simp only [PowerSeries.derivative_C, smul_eq_mul]
    rw [map_add, hde, derivative_neg_exp, hCm1]
    ring
  rw [e1]
  ring

private theorem cosh_sq_sub_sinh_sq : coshPS ^ 2 - sinhPS ^ 2 = 1 := by
  have haf := exp_neg_mul
  have h2C : (2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ) = 1 := by
    rw [mul_comm]; exact hCinv
  have hC : 4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2 = 1 := by
    have hrw : 4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2 =
        ((2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ)) *
          ((2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ)) := by ring
    rw [hrw, h2C, mul_one]
  have e : (coshPS ^ 2 - sinhPS ^ 2) =
      (PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
        (4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2) := by
    unfold coshPS sinhPS
    ring
  rw [e, haf, one_mul]
  exact hC

private theorem derivative_euler :
    PowerSeries.derivative eulerEGF = -(eulerEGF ^ 2 * sinhPS) := by
  have h1 : eulerEGF * coshPS = 1 := euler_cosh
  have hL : eulerEGF * sinhPS + coshPS * PowerSeries.derivative eulerEGF = 0 := by
    have h0 : PowerSeries.derivative (eulerEGF * coshPS) = 0 := by
      rw [h1, ← map_one PowerSeries.C]
      exact PowerSeries.derivative_C
    rw [Derivation.leibniz, derivative_cosh] at h0
    simp only [smul_eq_mul] at h0
    -- h0 : E * sinh + cosh * E' = 0 (up to order)
    linear_combination h0
  have h3 : eulerEGF ^ 2 * sinhPS + PowerSeries.derivative eulerEGF = 0 := by
    linear_combination eulerEGF * hL - PowerSeries.derivative eulerEGF * h1
  have hE' : PowerSeries.derivative eulerEGF = -(eulerEGF ^ 2 * sinhPS) := by
    linear_combination h3
  exact hE'

private theorem derivative_tanh : PowerSeries.derivative tanhPS = eulerEGF ^ 2 := by
  have h1 : eulerEGF * coshPS = 1 := euler_cosh
  have hE2 : eulerEGF ^ 2 * coshPS ^ 2 = 1 := by
    have hE2c : (eulerEGF * coshPS) ^ 2 = 1 := by rw [h1, one_pow]
    rwa [mul_pow] at hE2c
  have hsq2 : eulerEGF ^ 2 * coshPS ^ 2 - eulerEGF ^ 2 * sinhPS ^ 2 = eulerEGF ^ 2 := by
    have hsq := cosh_sq_sub_sinh_sq
    have hdist : eulerEGF ^ 2 * (coshPS ^ 2 - sinhPS ^ 2) = eulerEGF ^ 2 := by
      rw [hsq, mul_one]
    rwa [mul_sub] at hdist
  unfold tanhPS
  rw [Derivation.leibniz, derivative_sinh]
  simp only [smul_eq_mul]
  rw [derivative_euler, h1]
  linear_combination hsq2 - hE2

private theorem derivative_XT :
    PowerSeries.derivative (PowerSeries.X * tanhPS) =
      tanhPS + PowerSeries.X * eulerEGF ^ 2 := by
  rw [Derivation.leibniz, derivative_tanh]
  simp only [smul_eq_mul, PowerSeries.derivative_X, mul_one]
  ring

private theorem coeff_E_sq (m : ℕ) :
    PowerSeries.coeff (2 * m) (eulerEGF ^ 2) =
      (∑ k ∈ Finset.range (m + 1),
        ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
          ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
        ((2 * m).factorial : ℚ) := by
  have hant : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * m),
        PowerSeries.coeff p.1 eulerEGF * PowerSeries.coeff p.2 eulerEGF) =
      ∑ k ∈ Finset.range (2 * m + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (2 * m - k) eulerEGF := by
    have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i eulerEGF * PowerSeries.coeff j eulerEGF) (2 * m)
    simpa using h
  rw [sq, PowerSeries.coeff_mul, hant]
  have hsum : ∑ k ∈ Finset.range (2 * m + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (2 * m - k) eulerEGF =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (2 * m - 2 * j) eulerEGF := by
    apply sum_range_two_mul_succ
    intro k hkodd
    rw [coeff_eulerEGF, ite_eq_left (Nat.odd_iff.mp hkodd), zero_mul]
  rw [hsum]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (2 * m - 2 * j) eulerEGF =
        (((Nat.choose (2 * m) (2 * j) : ℕ) : ℚ) *
          ((chapter5EulerEven j : ℤ) : ℚ) * ((chapter5EulerEven (m - j) : ℤ) : ℚ)) /
          ((2 * m).factorial : ℚ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j ≤ m := by omega
    have h2jm : 2 * j ≤ 2 * m := by omega
    have hj2 : (2 * j) / 2 = j := by omega
    have hjm2 : (2 * m - 2 * j) / 2 = m - j := by omega
    have hmod1 : ¬ ((2 * j) % 2 = 1) := by omega
    have hmod2 : ¬ ((2 * m - 2 * j) % 2 = 1) := by omega
    rw [coeff_eulerEGF, ite_eq_right hmod1, hj2, coeff_eulerEGF, ite_eq_right hmod2, hjm2]
    have hchoose := Nat.choose_mul_factorial_mul_factorial h2jm
    have hcast : ((Nat.choose (2 * m) (2 * j) : ℕ) : ℚ) * (((2 * j).factorial : ℕ) : ℚ) *
        (((2 * m - 2 * j).factorial : ℕ) : ℚ) = (((2 * m).factorial : ℕ) : ℚ) := by
      exact_mod_cast hchoose
    have hd1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j)
    have hd2 : ((((2 * m - 2 * j).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m - 2 * j)
    have hfact : ((((2 * m).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m)
    have hAB : ((((2 * j).factorial : ℕ) : ℚ) * ((((2 * m - 2 * j).factorial : ℕ)) : ℚ)) ≠ 0 :=
      mul_ne_zero hd1 hd2
    rw [div_mul_div_comm, div_eq_div_iff hAB hfact]
    linear_combination -(((chapter5EulerEven j : ℤ) : ℚ) *
      ((chapter5EulerEven (m - j) : ℤ) : ℚ)) * hcast
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]

private theorem coeff_XT_bernoulli (n : ℕ) (_hn : 1 ≤ n) :
    PowerSeries.coeff (2 * n) (PowerSeries.X * tanhPS) =
      (((4 : ℚ) ^ (2 * n) - (2 : ℚ) ^ (2 * n)) * bernoulli (2 * n)) /
        (((2 * n).factorial : ℕ) : ℚ) := by
  have hXT := bernoulli_tanh
  have h21 : 2 * n ≠ 1 := by omega
  have hX0 : PowerSeries.coeff (2 * n) (PowerSeries.X : PowerSeries ℚ) = 0 := by
    rw [PowerSeries.coeff_X, ite_eq_right h21]
  have h4 : PowerSeries.coeff (2 * n) berB4 =
      (4 : ℚ) ^ (2 * n) * (bernoulli (2 * n) / (((2 * n).factorial : ℕ) : ℚ)) := by
    unfold berB4
    rw [PowerSeries.coeff_rescale, berB_coeff]
  have h2 : PowerSeries.coeff (2 * n) berB2 =
      (2 : ℚ) ^ (2 * n) * (bernoulli (2 * n) / (((2 * n).factorial : ℕ) : ℚ)) := by
    unfold berB2
    rw [PowerSeries.coeff_rescale, berB_coeff]
  have hcoeff : PowerSeries.coeff (2 * n) (PowerSeries.X * tanhPS) =
      PowerSeries.coeff (2 * n) (PowerSeries.X + berB4 - berB2) := by rw [hXT]
  rw [hcoeff]
  simp only [map_add, map_sub, hX0, h4, h2]
  ring

/-- **Bernoulli numbers as a convolution of even-index Euler numbers.** For every natural number
$n$, $2^{2n} (2^{2n} - 1) B_{2n} = 2n \sum_{k=0}^{n-1} \binom{2n-2}{2k} E_{2k} E_{2n-2k-2}$, where
$B_m$ are the Bernoulli numbers and $E_{2k}$ are the even-index Euler numbers.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5.
-/
theorem ramanujan_part1_ch5_entry10b_euleriansymmetry (n : ℕ) :
    (2 : ℚ) ^ (2 * n) * ((2 : ℚ) ^ (2 * n) - 1) * bernoulli (2 * n) =
      ((2 * n : ℕ) : ℚ) *
        ∑ k ∈ range n,
          (Nat.choose (2 * n - 2) (2 * k) : ℚ) *
            (chapter5EulerEven k : ℚ) *
              (chapter5EulerEven (n - k - 1) : ℚ) := by
  cases n with
  | zero =>
    simp [bernoulli_zero]
  | succ m =>
    have hFne : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * (m + 1))
    have hF2ne : ((((2 * m).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m)
    have hNNne : ((((2 * (m + 1) : ℕ)))) ≠ (0 : ℚ) := by
      exact_mod_cast (by omega : 2 * (m + 1) ≠ 0)
    have hN1ne : ((((2 * (m + 1) - 1 : ℕ)))) ≠ (0 : ℚ) := by
      exact_mod_cast (by omega : 2 * (m + 1) - 1 ≠ 0)
    -- Bernoulli side
    have cA : PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) =
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) :=
      coeff_XT_bernoulli (m + 1) (by omega)
    -- derivative equation at level 2(m+1)-1
    have hA' := derivative_XT
    have e_deriv : PowerSeries.coeff (2 * (m + 1) - 1)
          (PowerSeries.derivative (PowerSeries.X * tanhPS)) =
        PowerSeries.coeff (2 * (m + 1) - 1) tanhPS +
          PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) := by
      rw [hA']
      exact map_add _ _ _
    have cAd : PowerSeries.coeff (2 * (m + 1) - 1)
          (PowerSeries.derivative (PowerSeries.X * tanhPS)) =
        PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) *
          (((2 * (m + 1) : ℕ)) : ℚ) := by
      rw [PowerSeries.coeff_derivative]
      have h1 : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
      rw [h1]
      have hsub : ((2 * (m + 1) - 1 : ℕ) : ℚ) + 1 = ((2 * (m + 1) : ℕ) : ℚ) := by
        rw [Nat.cast_sub (show 1 ≤ 2 * (m + 1) by omega), Nat.cast_one, sub_add_cancel]
      rw [hsub]
    have cT : PowerSeries.coeff (2 * (m + 1) - 1) tanhPS =
        PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) := by
      have h := PowerSeries.coeff_succ_X_mul (2 * (m + 1) - 1) tanhPS
      have h1 : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
      rw [h1] at h
      exact h.symm
    have cE : PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) =
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
          ((((2 * m).factorial : ℕ)) : ℚ) := by
      have h0 : PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) =
          PowerSeries.coeff (2 * (m + 1) - 2) (eulerEGF ^ 2) := by
        have h := PowerSeries.coeff_succ_X_mul (2 * (m + 1) - 2) (eulerEGF ^ 2)
        have h1 : 2 * (m + 1) - 2 + 1 = 2 * (m + 1) - 1 := by omega
        rw [h1] at h
        exact h
      rw [h0]
      have hm2 : 2 * (m + 1) - 2 = 2 * m := by omega
      rw [hm2, coeff_E_sq]
    -- combined equation
    have eq : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) *
          ((((2 * (m + 1) : ℕ)))) =
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
            ((((2 * m).factorial : ℕ)) : ℚ) := by
      rw [← cA, ← cAd, ← cT, ← cE]
      exact e_deriv
    -- factorial relation
    have hfactQ : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) =
        ((((2 * (m + 1) : ℕ)))) * ((((2 * (m + 1) - 1 : ℕ)))) *
          ((((2 * m).factorial : ℕ)) : ℚ) := by
      have e1 : 2 * (m + 1) = 2 * m + 2 := by omega
      have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have hfactN : (2 * m + 2).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
        have s1 : 2 * m + 2 = (2 * m + 1) + 1 := by omega
        conv_lhs => rw [s1]
        rw [Nat.factorial_succ]
        have f2 : ((2 * m + 1)).factorial = (2 * m + 1) * (2 * m).factorial := by
          have t : 2 * m + 1 = (2 * m) + 1 := by omega
          conv_lhs => rw [t]
          rw [Nat.factorial_succ]
        rw [f2]
        ring
      rw [e2, e1]
      exact_mod_cast hfactN
    -- N - 1 = N1
    have hNN1 : ((((2 * (m + 1) : ℕ)) : ℚ)) - 1 =
        ((((2 * (m + 1) - 1 : ℕ)) : ℚ)) := by
      rw [Nat.cast_sub (show 1 ≤ 2 * (m + 1) by omega), Nat.cast_one]
    -- clear denominators
    have hP : (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ))))) *
          (((((2 * (m + 1)).factorial : ℕ)) : ℚ) * (((2 * m).factorial : ℕ) : ℚ)) =
        (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * (((2 * m).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            (((2 * (m + 1)).factorial : ℕ) : ℚ)) *
          (((2 * (m + 1)).factorial : ℕ) : ℚ) := by
      have eB : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) *
            ((((2 * (m + 1) : ℕ)))) =
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ))))) /
            (((2 * (m + 1)).factorial : ℕ) : ℚ) :=
        div_mul_eq_mul_div _ _ _
      have eA : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
            ((((2 * m).factorial : ℕ)) : ℚ) =
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * (((2 * m).factorial : ℕ) : ℚ) +
            (∑ k ∈ Finset.range (m + 1),
              ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
                ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
              (((2 * (m + 1)).factorial : ℕ) : ℚ)) /
            (((((2 * (m + 1)).factorial : ℕ)) : ℚ) * (((2 * m).factorial : ℕ) : ℚ)) := by
        rw [div_add_div _ _ hFne hF2ne]
        ring
      rw [eB, eA] at eq
      have h := (div_eq_div_iff hFne (mul_ne_zero hFne hF2ne)).mp eq
      linear_combination h
    -- factor out F
    have hX : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) *
          ((((2 * m).factorial : ℕ)) : ℚ) -
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * m).factorial : ℕ)) : ℚ) -
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
          (((2 * (m + 1)).factorial : ℕ) : ℚ) = 0 := by
      have hFX : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) *
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) *
            ((((2 * m).factorial : ℕ)) : ℚ) -
          ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * m).factorial : ℕ)) : ℚ) -
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            (((2 * (m + 1)).factorial : ℕ) : ℚ)) = 0 := by
        linear_combination hP
      rcases mul_eq_zero.mp hFX with h | h
      · exact absurd h hFne
      · exact h
    rw [hfactQ] at hX
    have hXf : ((((2 * m).factorial : ℕ)) : ℚ) *
        (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) -
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) -
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
          ((((2 * (m + 1) : ℕ)))) * ((((2 * (m + 1) - 1 : ℕ)))) ) = 0 := by
      linear_combination hX
    rcases mul_eq_zero.mp hXf with h | h
    · exact absurd h hF2ne
    · have hG0 : (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) -
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            ((((2 * (m + 1) : ℕ))))) * ((((2 * (m + 1) - 1 : ℕ)))) = 0 := by
        linear_combination h - (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1)))) * hNN1
      rcases mul_eq_zero.mp hG0 with h2 | h2
      · have hbS : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) =
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            ((((2 * (m + 1) : ℕ)))) :=
          sub_eq_zero.mp h2
        have h42 : (4 : ℚ) ^ (2 * (m + 1)) = (2 : ℚ) ^ (2 * (m + 1)) * (2 : ℚ) ^ (2 * (m + 1)) := by
          rw [show (4 : ℚ) = 2 * 2 from by ring, mul_pow]
        have hLHS : (2 : ℚ) ^ (2 * (m + 1)) *
              ((2 : ℚ) ^ (2 * (m + 1)) - 1) * bernoulli (2 * (m + 1)) =
            ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
              bernoulli (2 * (m + 1))) := by
          rw [h42]
          ring
        have hSsum : (∑ k ∈ Finset.range (m + 1),
              (Nat.choose (2 * (m + 1) - 2) (2 * k) : ℚ) *
                (chapter5EulerEven k : ℚ) *
                  (chapter5EulerEven ((m + 1) - k - 1) : ℚ)) =
            (∑ k ∈ Finset.range (m + 1),
              ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
                ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
          have e2 : (m + 1) - k - 1 = m - k := by omega
          rw [e1, e2]
        rw [hLHS, hSsum, hbS]
        ring
      · exact absurd h2 hN1ne

end
end Entry10bEuleriansymmetry
end MathlibExt.Analysis.Ramanujan.Part1Ch5
end
