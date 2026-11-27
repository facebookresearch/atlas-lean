/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliPoly
public import MathlibExt.NumberTheory.HeightOneMultipleZetaSeries

/-!
# Height one multiple zeta series weighted by powers of a natural number

The series $\sum_j \zeta(s, \{1\}^j) n^j$ is summable with sum
$\frac{1}{n!} \sum_{m=0}^{n} c(n, m) \zeta(s - m)$ for $\operatorname{Re} s > n + 1$,
and the series $\sum_j B_j^{(-n)}(-1) \zeta(s + n, \{1\}^j)$ is summable with sum
$\zeta(s)$ for $\operatorname{Re} s > 1$.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset Filter
open scoped Topology

/-- The elementary symmetric sum of the reciprocals of the first `a` positive
integers, as a rational number. -/
private noncomputable def elemSymm (a j : ℕ) : ℚ :=
  ∑ T ∈ (Finset.Icc 1 a).powersetCard j, ∏ m ∈ T, (1 / (m : ℚ))

private lemma elemSymm_nonneg (a j : ℕ) : 0 ≤ elemSymm a j := by
  unfold elemSymm
  positivity

private lemma elemSymm_eq_zero_of_lt {a j : ℕ} (h : a < j) : elemSymm a j = 0 := by
  have he : (Finset.Icc 1 a).powersetCard j = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    simp
    omega
  simp [elemSymm, he]

private lemma elemSymm_zero (a : ℕ) : elemSymm a 0 = 1 := by
  simp [elemSymm]

/-- The generating function of the elementary symmetric sums of reciprocals. -/
private lemma elemSymm_prod (a : ℕ) (t : ℚ) :
    ∑ j ∈ Finset.range (a + 1), elemSymm a j * t ^ j =
      ∏ m ∈ Finset.Icc 1 a, (1 + t / (m : ℚ)) := by
  have hprod : ∏ m ∈ Finset.Icc 1 a, (1 + t / (m : ℚ)) =
      ∑ T ∈ (Finset.Icc 1 a).powerset, ∏ m ∈ T, (t / (m : ℚ)) := by
    have hcomm : ∏ m ∈ Finset.Icc 1 a, (1 + t / (m : ℚ)) =
        ∏ m ∈ Finset.Icc 1 a, (t / (m : ℚ) + 1) := by
      apply Finset.prod_congr rfl
      intro m _
      rw [add_comm]
    rw [hcomm, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro T _
    simp
  rw [hprod, Finset.sum_powerset]
  simp only [Nat.card_Icc]
  rw [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j _
  unfold elemSymm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  have hcard : T.card = j := (Finset.mem_powersetCard.mp hT).2
  have hprod2 : ∏ m ∈ T, t / (m : ℚ) = t ^ j * ∏ m ∈ T, (1 / (m : ℚ)) := by
    have h1 : ∀ m : ℕ, t / (m : ℚ) = t * (1 / (m : ℚ)) := fun m => by
      rw [div_eq_mul_inv, one_div]
    simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_const, hcard]
  rw [hprod2, mul_comm]

private lemma prod_Icc_factorial (a t : ℕ) :
    ∏ m ∈ Finset.Icc 1 a, (((m : ℚ) + t) / (m : ℚ)) =
      ((a + t).factorial : ℚ) / ((a.factorial : ℚ) * (t.factorial : ℚ)) := by
  induction a with
  | zero =>
    have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by simp
    rw [hempty, Finset.prod_empty]
    simp only [zero_add, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [div_self (by positivity : ((t.factorial : ℚ)) ≠ 0)]
  | succ a ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ a + 1), ih]
    have h1 : (a.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (a + 1 : ℚ) ≠ 0 := by positivity
    rw [show a + 1 + t = (a + t) + 1 by omega, Nat.factorial_succ (a + t),
      Nat.factorial_succ a]
    push_cast
    field_simp
    ring

private lemma elemSymm_sum_factorial (a r : ℕ) :
    ∑ j ∈ Finset.range (a + 1), elemSymm a j * (r : ℚ) ^ j =
      ((a + r).factorial : ℚ) / ((a.factorial : ℚ) * (r.factorial : ℚ)) := by
  rw [elemSymm_prod]
  rw [← prod_Icc_factorial]
  apply Finset.prod_congr rfl
  intro m hm
  have h1m : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hm0 : (m : ℚ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  field_simp

private lemma elemSymm_sum_real (a n : ℕ) :
    ∑ j ∈ Finset.range (a + 1), (elemSymm a j : ℝ) * (n : ℝ) ^ j =
      (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ))) := by
  have hcast2 : ∑ j ∈ Finset.range (a + 1),
      (elemSymm a j : ℝ) * (n : ℝ) ^ j =
      ((∑ j ∈ Finset.range (a + 1), elemSymm a j * (n : ℚ) ^ j : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hcast2, elemSymm_sum_factorial]
  push_cast
  ring

private lemma stirlingFirst_eval (n : ℕ) (x : ℂ) :
    (ascPochhammer ℂ n).eval x =
      ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℂ) * x ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih]
    have hzero : (n : ℂ) * (Nat.stirlingFirst n 0 : ℂ) = 0 := by
      cases n with
      | zero => simp
      | succ k => simp [Nat.stirlingFirst_succ_zero]
    have hshift : ∑ m ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n (m + 1) : ℂ) * x ^ (m + 1) =
        (∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℂ) * x ^ m) -
          (Nat.stirlingFirst n 0 : ℂ) := by
      have h := Finset.sum_range_succ' (fun m => (Nat.stirlingFirst n m : ℂ) * x ^ m)
        (n + 1)
      have hz : (Nat.stirlingFirst n (n + 1) : ℂ) * x ^ (n + 1) = 0 := by
        simp [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]
      rw [Finset.sum_range_succ, hz, add_zero] at h
      have h2 : (∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℂ) * x ^ m) =
          (∑ m ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n (m + 1) : ℂ) * x ^ (m + 1)) +
            (Nat.stirlingFirst n 0 : ℂ) := by
        simpa using h
      rw [h2, add_sub_cancel_right]
    conv_rhs => rw [Finset.sum_range_succ']
    have h0 : (Nat.stirlingFirst (n + 1) 0 : ℂ) = 0 := by
      exact_mod_cast Nat.stirlingFirst_succ_zero n
    rw [h0]
    simp only [pow_zero, mul_one, add_zero]
    have step : ∀ m : ℕ, (Nat.stirlingFirst (n + 1) (m + 1) : ℂ) * x ^ (m + 1) =
        ((n : ℂ) * (Nat.stirlingFirst n (m + 1) : ℂ) +
          (Nat.stirlingFirst n m : ℂ)) * x ^ (m + 1) := fun m => by
      rw [Nat.stirlingFirst_succ_succ]
      push_cast
      ring
    simp_rw [step, add_mul, Finset.sum_add_distrib]
    have e1 : ∑ m ∈ Finset.range (n + 1),
          (n : ℂ) * (Nat.stirlingFirst n (m + 1) : ℂ) * x ^ (m + 1) =
        (n : ℂ) * ((∑ m ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n m : ℂ) * x ^ m) - (Nat.stirlingFirst n 0 : ℂ)) := by
      have hmul : ∑ m ∈ Finset.range (n + 1),
            (n : ℂ) * (Nat.stirlingFirst n (m + 1) : ℂ) * x ^ (m + 1) =
          (n : ℂ) * ∑ m ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n (m + 1) : ℂ) * x ^ (m + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      rw [hmul, hshift]
    have e2 : ∑ m ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n m : ℂ) * x ^ (m + 1) =
        (∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℂ) * x ^ m) * x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      rw [pow_succ]
      ring
    rw [e1, e2, mul_sub, hzero, sub_zero]
    ring

private lemma sum_stirlingSecond_factorial (n a : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (-1 : ℚ) ^ r * (Nat.stirlingSecond n r : ℚ) *
        ((a + r).factorial : ℚ) =
      (-1 : ℚ) ^ n * (a.factorial : ℚ) * ((a : ℚ) + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hD : ∑ r ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ r * ((r : ℚ) + 1) * (Nat.stirlingSecond n (r + 1) : ℚ) *
              ((a + r + 1).factorial : ℚ) +
            (-1 : ℚ) ^ r * (r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
              ((a + r).factorial : ℚ)) = 0 := by
      have hshift : ∑ r ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ r * ((r : ℚ) + 1) * (Nat.stirlingSecond n (r + 1) : ℚ) *
              ((a + r + 1).factorial : ℚ) =
          -∑ r ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ r * (r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
              ((a + r).factorial : ℚ) := by
        have hH : ∀ k : ℕ, (-1 : ℚ) ^ k * ((k : ℚ) + 1) *
              (Nat.stirlingSecond n (k + 1) : ℚ) * ((a + k + 1).factorial : ℚ) =
            -((-1 : ℚ) ^ (k + 1) * (((k + 1 : ℕ) : ℚ)) *
              (Nat.stirlingSecond n (k + 1) : ℚ) *
              ((a + (k + 1)).factorial : ℚ)) := by
          intro k
          rw [show a + (k + 1) = a + k + 1 by omega, pow_succ]
          push_cast
          ring
        have htop : (-1 : ℚ) ^ (n + 1) * ((n + 1 : ℕ) : ℚ) *
              (Nat.stirlingSecond n (n + 1) : ℚ) *
              ((a + (n + 1)).factorial : ℚ) = 0 := by
          simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
        have hzeroH : (-1 : ℚ) ^ 0 * ((0 : ℕ) : ℚ) *
              (Nat.stirlingSecond n 0 : ℚ) * ((a + 0).factorial : ℚ) = 0 := by simp
        have hsumH : ∑ k ∈ Finset.range (n + 2),
              (-1 : ℚ) ^ k * (k : ℚ) * (Nat.stirlingSecond n k : ℚ) *
                ((a + k).factorial : ℚ) =
            ∑ k ∈ Finset.range (n + 1),
              (-1 : ℚ) ^ k * (k : ℚ) * (Nat.stirlingSecond n k : ℚ) *
                ((a + k).factorial : ℚ) := by
          rw [Finset.sum_range_succ, htop, add_zero]
        have hsucc' := Finset.sum_range_succ'
          (fun k => (-1 : ℚ) ^ k * (k : ℚ) * (Nat.stirlingSecond n k : ℚ) *
            ((a + k).factorial : ℚ)) (n + 1)
        rw [hsumH, hzeroH, add_zero] at hsucc'
        rw [Finset.sum_congr rfl (fun r _ => hH r), Finset.sum_neg_distrib,
          ← hsucc']
      rw [Finset.sum_add_distrib, hshift]
      ring
    have hsplit : ∑ r ∈ Finset.range (n + 2),
          (-1 : ℚ) ^ r * (Nat.stirlingSecond (n + 1) r : ℚ) *
            ((a + r).factorial : ℚ) =
        ∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (r + 1) * (Nat.stirlingSecond (n + 1) (r + 1) : ℚ) *
            ((a + r + 1).factorial : ℚ) := by
      rw [Finset.sum_range_succ']
      have h0 : (-1 : ℚ) ^ 0 * (Nat.stirlingSecond (n + 1) 0 : ℚ) *
          ((a + 0).factorial : ℚ) = 0 := by
        have h00 : (Nat.stirlingSecond (n + 1) 0 : ℚ) = 0 := by
          exact_mod_cast Nat.stirlingSecond_succ_zero n
        rw [h00]
        simp
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro r _
      rw [show a + (r + 1) = a + r + 1 by omega]
    have hterm : ∀ r : ℕ, (-1 : ℚ) ^ (r + 1) *
          (Nat.stirlingSecond (n + 1) (r + 1) : ℚ) * ((a + r + 1).factorial : ℚ) =
        -((a : ℚ) + 1) * ((-1 : ℚ) ^ r * (Nat.stirlingSecond n r : ℚ) *
            ((a + r).factorial : ℚ)) -
          ((-1 : ℚ) ^ r * ((r : ℚ) + 1) * (Nat.stirlingSecond n (r + 1) : ℚ) *
              ((a + r + 1).factorial : ℚ) +
            (-1 : ℚ) ^ r * (r : ℚ) * (Nat.stirlingSecond n r : ℚ) *
              ((a + r).factorial : ℚ)) := by
      intro r
      rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ (a + r)]
      push_cast
      ring
    rw [hsplit]
    simp_rw [hterm, Finset.sum_sub_distrib, hD, sub_zero, ← Finset.mul_sum]
    rw [ih, pow_succ, pow_succ]
    ring

private lemma polyBernoulliPoly_neg (n j : ℕ) :
    polyBernoulliPoly j (-(n : ℤ)) (-1) =
      (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) *
          (r : ℚ) ^ j := by
  have hterm : ∀ i : ℕ, (j.choose i : ℚ) * polyBernoulli i (-(n : ℤ)) *
        (-1 : ℚ) ^ (j - i) =
      (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
        (j.choose i : ℚ) * ((-1 : ℚ) ^ r * (r.factorial : ℚ) *
          (Nat.stirlingSecond n r : ℚ) * ((r : ℚ) + 1) ^ i) *
          (-1 : ℚ) ^ (j - i) := by
    intro i
    rw [arakawa_kaneko_duality i n]
    have hY : ∀ r : ℕ, (-1 : ℚ) ^ r * (r.factorial : ℚ) *
          (Nat.stirlingSecond n r : ℚ) / (((r + 1 : ℕ) : ℚ) ^ (-(i : ℤ))) =
        (-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) *
          ((r : ℚ) + 1) ^ i := by
      intro r
      push_cast
      have hz : ((r : ℚ) + 1) ^ (-(i : ℤ)) = (((r : ℚ) + 1) ^ i)⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      rw [hz, div_inv_eq_mul]
    unfold polyBernoulli
    rw [Finset.sum_congr rfl (fun r _ => hY r)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  unfold polyBernoulliPoly
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    Finset.sum_comm]
  conv_rhs => rw [Finset.mul_sum]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have hinner : ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℚ) * (((r : ℚ) + 1) ^ i) * (-1 : ℚ) ^ (j - i) =
      (r : ℚ) ^ j := by
    have h := add_pow ((r : ℚ) + 1) (-1 : ℚ) j
    rw [show (r : ℚ) + 1 + -1 = (r : ℚ) by ring] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfactor : ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℚ) * ((-1 : ℚ) ^ r * (r.factorial : ℚ) *
          (Nat.stirlingSecond n r : ℚ) * ((r : ℚ) + 1) ^ i) *
          (-1 : ℚ) ^ (j - i) =
      ((-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ)) *
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℚ) * (((r : ℚ) + 1) ^ i) * (-1 : ℚ) ^ (j - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor, hinner]

/-- The summand of the double series for the first identity. -/
private noncomputable def heightOneTermNat (n : ℕ) (s : ℂ) (a j : ℕ) : ℂ :=
  ((a : ℂ) + 1) ^ (-s) * ((elemSymm a j : ℚ) : ℂ) * (n : ℂ) ^ j

/-- The summand of the double series for the second identity. -/
private noncomputable def heightOneTermPoly (n : ℕ) (s : ℂ) (a j : ℕ) : ℂ :=
  ((a : ℂ) + 1) ^ (-(s + n)) * ((elemSymm a j : ℚ) : ℂ) *
    ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ)

private lemma heightOne_eq_tsum_elemSymm (s : ℂ) (j : ℕ) :
    heightOneMultipleZeta s j =
      ∑' a : ℕ, ((a : ℂ) + 1) ^ (-s) * ((elemSymm a j : ℚ) : ℂ) := by
  unfold heightOneMultipleZeta elemSymm
  apply tsum_congr
  intro a
  rw [Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro m _
  simp

private lemma cpow_neg_sub_pow (x : ℂ) (hx : x ≠ 0) (s : ℂ) (m : ℕ) :
    x ^ (-s) * x ^ m = x ^ (-(s - m)) := by
  rw [← Complex.cpow_natCast, ← Complex.cpow_add (-s) (m : ℂ) hx]
  congr 1
  ring

private lemma hasSum_swap {F : ℕ → ℕ → ℂ} {rows cols : ℕ → ℂ} {s : ℂ}
    (hF : Summable (Function.uncurry F))
    (hr : ∀ a, HasSum (F a) (rows a))
    (hc : ∀ j, HasSum (fun a => F a j) (cols j))
    (hs : HasSum rows s) : HasSum cols s := by
  have hcols := hF.prod_symm.hasSum.prod_fiberwise hc
  have hrows := hF.hasSum.prod_fiberwise hr
  change HasSum cols (∑' ij, Function.uncurry F ((Equiv.prodComm ℕ ℕ) ij)) at hcols
  rwa [(Equiv.prodComm ℕ ℕ).tsum_eq (Function.uncurry F), hrows.unique hs] at hcols

private lemma summable_uncurry_of_finite_rows {F : ℕ → ℕ → ℂ}
    (hfin : ∀ a j, a < j → F a j = 0)
    (hrow : Summable (fun a => ∑ j ∈ Finset.range (a + 1), ‖F a j‖)) :
    Summable (Function.uncurry F) := by
  have hnorm : Summable (Function.uncurry (fun a j => ‖F a j‖)) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (F p.1 p.2))).2
    constructor
    · intro a
      apply summable_of_ne_finset_zero (s := Finset.range (a + 1))
      intro j hj
      change ‖F a j‖ = 0
      simp [hfin a j (by simpa using hj)]
    · apply hrow.congr
      intro a
      symm
      apply tsum_eq_sum
      intro j hj
      change ‖F a j‖ = 0
      simp [hfin a j (by simpa using hj)]
  exact hnorm.of_norm_bounded (fun p => le_rfl)

private lemma summable_of_row_bound {g : ℕ → ℝ} (hg : ∀ a, 0 ≤ g a) {σ : ℝ}
    (hσ : 1 < σ) (K : ℝ)
    (hbound : ∀ a, g a ≤ K * ((a : ℝ) + 1) ^ (-σ)) : Summable g := by
  have hsum : Summable (fun a : ℕ => K * ((a : ℝ) + 1) ^ (-σ)) := by
    have h := ((Real.summable_one_div_nat_add_rpow (1 : ℝ) σ).mpr hσ).mul_left K
    apply h.congr
    intro a
    have hpos : (0:ℝ) < (a:ℝ) + 1 := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    simp only [abs_of_pos hpos, one_div]
  exact Summable.of_nonneg_of_le hg hbound hsum

private lemma norm_heightOneTermNat (n : ℕ) (s : ℂ) (a j : ℕ) :
    ‖heightOneTermNat n s a j‖ =
      ((a : ℝ) + 1) ^ (-s.re) * (elemSymm a j : ℝ) * (n : ℝ) ^ j := by
  have hbase : ((a : ℂ) + 1) = (((a : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hE : ‖((elemSymm a j : ℚ) : ℂ)‖ = (elemSymm a j : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg]
    exact_mod_cast elemSymm_nonneg a j
  unfold heightOneTermNat
  rw [norm_mul, norm_mul, hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hE,
    norm_pow, Complex.norm_natCast]

private lemma factorial_ratio_le (a n : ℕ) :
    ((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ)) ≤
      ((a : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) := by
  have hchoose : ((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ)) =
      ((a + n).choose n : ℝ) := by
    have hfac : ((a + n).choose n : ℝ) * (n.factorial : ℝ) * (a.factorial : ℝ) =
        ((a + n).factorial : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ a + n by omega)
      rw [show a + n - n = a by omega] at h
      exact_mod_cast h
    have hpos : (a.factorial : ℝ) * (n.factorial : ℝ) ≠ 0 := by positivity
    rw [div_eq_iff hpos]
    calc ((a + n).factorial : ℝ) = ((a + n).choose n : ℝ) * (n.factorial : ℝ) *
          (a.factorial : ℝ) := hfac.symm
      _ = ((a + n).choose n : ℝ) * ((a.factorial : ℝ) * (n.factorial : ℝ)) := by ring
  rw [hchoose]
  have h1 := Nat.choose_le_pow_div (r := n) (n := a + n) (α := ℝ)
  have h2 : ((a : ℝ) + (n : ℝ)) ≤ ((a : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) n]
  have h3 : ((a : ℝ) + (n : ℝ)) ^ n ≤
      (((a : ℝ) + 1) * ((n : ℝ) + 1)) ^ n :=
    pow_le_pow_left₀ (by positivity) h2 n
  rw [mul_pow] at h3
  push_cast at h1
  exact h1.trans (by gcongr)

private lemma rowSum_heightOneTermNat (n a : ℕ) (s : ℂ) :
    ∑ j ∈ Finset.range (a + 1), heightOneTermNat n s a j =
      ((a : ℂ) + 1) ^ (-s) *
        (((a + n).factorial : ℂ) / ((a.factorial : ℂ) * (n.factorial : ℂ))) := by
  have hcast : ∑ j ∈ Finset.range (a + 1),
      ((elemSymm a j : ℚ) : ℂ) * (n : ℂ) ^ j =
      (((a + n).factorial : ℂ) / ((a.factorial : ℂ) * (n.factorial : ℂ))) := by
    have hcast2 : ∑ j ∈ Finset.range (a + 1),
        ((elemSymm a j : ℚ) : ℂ) * (n : ℂ) ^ j =
        ((∑ j ∈ Finset.range (a + 1), elemSymm a j * (n : ℚ) ^ j : ℚ) : ℂ) := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hcast2, elemSymm_sum_factorial]
    push_cast
    ring
  unfold heightOneTermNat
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hcast]

private lemma rowSum_heightOneTermNat_zeta (n a : ℕ) (s : ℂ) :
    ∑ j ∈ Finset.range (a + 1), heightOneTermNat n s a j =
      1 / (n.factorial : ℂ) * ∑ m ∈ Finset.range (n + 1),
        (Nat.stirlingFirst n m : ℂ) * ((a : ℂ) + 1) ^ (-(s - m)) := by
  have hx : ((a : ℂ) + 1) ≠ 0 := by
    have hcast : ((a : ℂ) + 1) = (((a + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast Nat.succ_ne_zero a
  have hpoch : ∀ k : ℕ, (ascPochhammer ℂ k).eval ((a : ℂ) + 1) =
      ((a + k).factorial : ℂ) / (a.factorial : ℂ) := by
    intro k
    induction k with
    | zero =>
      simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.add_zero]
      exact (div_self (by exact_mod_cast Nat.factorial_ne_zero a)).symm
    | succ k ih =>
      rw [ascPochhammer_succ_eval, ih]
      have hfact : (a.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero a
      rw [show a + (k + 1) = (a + k) + 1 by omega, Nat.factorial_succ (a + k)]
      push_cast
      field_simp
      ring
  have hratio : (((a + n).factorial : ℂ) / ((a.factorial : ℂ) * (n.factorial : ℂ))) =
      (1 / (n.factorial : ℂ)) * (ascPochhammer ℂ n).eval ((a : ℂ) + 1) := by
    rw [hpoch n]
    have h1 : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    have h2 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  rw [rowSum_heightOneTermNat, hratio, stirlingFirst_eval]
  have e : ((a : ℂ) + 1) ^ (-s) *
        ((1 / (n.factorial : ℂ)) *
          ∑ m ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n m : ℂ) * ((a : ℂ) + 1) ^ m) =
      1 / (n.factorial : ℂ) * ∑ m ∈ Finset.range (n + 1),
        (Nat.stirlingFirst n m : ℂ) * ((a : ℂ) + 1) ^ (-(s - m)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have h := cpow_neg_sub_pow ((a : ℂ) + 1) hx s m
    linear_combination (1 / (n.factorial : ℂ) * (Nat.stirlingFirst n m : ℂ)) * h
  exact e

private lemma hasSum_heightOneMultipleZeta_mul_nat_part1 (n : ℕ) (s : ℂ)
    (hs : (n : ℝ) + 1 < s.re) :
    HasSum (fun j : ℕ => heightOneMultipleZeta s j * (n : ℂ) ^ j)
      (1 / (n.factorial : ℂ) *
        ∑ m ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n m : ℂ) * riemannZeta (s - m)) := by
  have hfin : ∀ a j : ℕ, a < j → heightOneTermNat n s a j = 0 := by
    intro a j hj
    unfold heightOneTermNat
    rw [elemSymm_eq_zero_of_lt hj]
    simp
  have hrowsum : ∀ a : ℕ, ∑ j ∈ Finset.range (a + 1), ‖heightOneTermNat n s a j‖ =
      ((a : ℝ) + 1) ^ (-s.re) *
        (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ))) := by
    intro a
    have hsumR : ∑ j ∈ Finset.range (a + 1),
        (elemSymm a j : ℝ) * (n : ℝ) ^ j =
        (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ))) :=
      elemSymm_sum_real a n
    have hstep : ∀ j : ℕ, ‖heightOneTermNat n s a j‖ =
        ((a : ℝ) + 1) ^ (-s.re) * ((elemSymm a j : ℝ) * (n : ℝ) ^ j) := by
      intro j
      rw [norm_heightOneTermNat]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum, hsumR]
  have hbound : ∀ a : ℕ, ∑ j ∈ Finset.range (a + 1), ‖heightOneTermNat n s a j‖ ≤
      (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) *
        ((a : ℝ) + 1) ^ (-(s.re - (n : ℝ))) := by
    intro a
    rw [hrowsum]
    have hle := factorial_ratio_le a n
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hpow : ((a : ℝ) + 1) ^ (-s.re) *
          (((a : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) =
        (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) *
          ((a : ℝ) + 1) ^ (-(s.re - (n : ℝ))) := by
      rw [← Real.rpow_natCast ((a : ℝ) + 1) n, ← mul_div_assoc, ← mul_assoc,
        ← Real.rpow_add hpos,
        show -s.re + (n : ℝ) = -(s.re - (n : ℝ)) by ring, mul_div_assoc, mul_comm]
    calc ((a : ℝ) + 1) ^ (-s.re) *
            (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ)))
        ≤ ((a : ℝ) + 1) ^ (-s.re) *
            (((a : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) *
            ((a : ℝ) + 1) ^ (-(s.re - (n : ℝ))) := hpow
  have hF : Summable (Function.uncurry (heightOneTermNat n s)) :=
    summable_uncurry_of_finite_rows hfin
      (summable_of_row_bound (fun a => Finset.sum_nonneg
        (fun j _ => norm_nonneg _)) (by linarith : 1 < s.re - (n : ℝ))
        (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) hbound)
  have hr : ∀ a : ℕ, HasSum (heightOneTermNat n s a)
      (∑ j ∈ Finset.range (a + 1), heightOneTermNat n s a j) := by
    intro a
    have hnot : ∀ j ∉ Finset.range (a + 1), a < j := by
      intro j hj
      have h1 : ¬ j < a + 1 := fun h => hj (Finset.mem_range.mpr h)
      omega
    have hsum : Summable (heightOneTermNat n s a) :=
      summable_of_ne_finset_zero (s := Finset.range (a + 1))
        (fun j hj => hfin a j (hnot j hj))
    have h := hsum.hasSum
    rwa [tsum_eq_sum (fun j hj => hfin a j (hnot j hj))] at h
  have hc : ∀ j : ℕ, HasSum (fun a => heightOneTermNat n s a j)
      (heightOneMultipleZeta s j * (n : ℂ) ^ j) := by
    intro j
    have hfib : Summable (fun a => heightOneTermNat n s a j) :=
      hF.prod_symm.prod_factor j
    have htsum : (∑' a : ℕ, heightOneTermNat n s a j) =
        heightOneMultipleZeta s j * (n : ℂ) ^ j := by
      calc (∑' a : ℕ, heightOneTermNat n s a j) =
            ∑' a : ℕ, (((a : ℂ) + 1) ^ (-s) * ((elemSymm a j : ℚ) : ℂ)) *
              (n : ℂ) ^ j :=
          tsum_congr fun a => by unfold heightOneTermNat; ring
        _ = (∑' a : ℕ, ((a : ℂ) + 1) ^ (-s) * ((elemSymm a j : ℚ) : ℂ)) *
              (n : ℂ) ^ j := tsum_mul_right
        _ = heightOneMultipleZeta s j * (n : ℂ) ^ j := by
          rw [heightOne_eq_tsum_elemSymm]
    exact htsum ▸ hfib.hasSum
  have hzeta : ∀ m : ℕ, m ≤ n → HasSum
      (fun a : ℕ => ((a : ℂ) + 1) ^ (-(s - (m : ℂ)))) (riemannZeta (s - (m : ℂ))) := by
    intro m hm
    have hre : 1 < (s - (m : ℂ)).re := by
      have hre2 : (s - (m : ℂ)).re = s.re - (m : ℝ) := by simp
      rw [hre2]
      have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
      linarith
    have hsumm : Summable (fun a : ℕ => ((a : ℂ) + 1) ^ (-(s - (m : ℂ)))) := by
      have h1 : Summable (fun k : ℕ => 1 / (k : ℂ) ^ (s - (m : ℂ))) :=
        Complex.summable_one_div_nat_cpow.mpr hre
      have h2 := (summable_nat_add_iff
        (f := fun k : ℕ => 1 / (k : ℂ) ^ (s - (m : ℂ))) 1).mpr h1
      have hfun : (fun a : ℕ => ((a : ℂ) + 1) ^ (-(s - (m : ℂ)))) =
          (fun a : ℕ => 1 / (((a + 1 : ℕ)) : ℂ) ^ (s - (m : ℂ))) := by
        funext a
        rw [Complex.cpow_neg, one_div]
        push_cast
        ring
      rw [hfun]
      exact h2
    have htsum : (∑' a : ℕ, ((a : ℂ) + 1) ^ (-(s - (m : ℂ)))) =
        riemannZeta (s - (m : ℂ)) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
      apply tsum_congr
      intro a
      rw [Complex.cpow_neg, one_div]
    have hhas := hsumm.hasSum
    rwa [htsum] at hhas
  have hs : HasSum (fun a => ∑ j ∈ Finset.range (a + 1), heightOneTermNat n s a j)
      (1 / (n.factorial : ℂ) *
        ∑ m ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n m : ℂ) * riemannZeta (s - m)) := by
    have hsum := (hasSum_sum (fun m hm => (hzeta m
      (Nat.le_of_lt_succ (Finset.mem_range.mp hm))).mul_left
      (Nat.stirlingFirst n m : ℂ))).mul_left (1 / (n.factorial : ℂ))
    apply HasSum.congr_fun hsum
    intro a
    exact rowSum_heightOneTermNat_zeta n a s
  exact hasSum_swap hF hr hc hs

private lemma elemSymm_sum_polyBernoulli_rat (n a : ℕ) :
    ∑ j ∈ Finset.range (a + 1),
        polyBernoulliPoly j (-(n : ℤ)) (-1) * elemSymm a j = ((a : ℚ) + 1) ^ n := by
  have hper : ∀ j : ℕ, polyBernoulliPoly j (-(n : ℤ)) (-1) * elemSymm a j =
      (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ)) *
          (elemSymm a j * (r : ℚ) ^ j) := by
    intro j
    rw [polyBernoulliPoly_neg]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hswap : ∑ j ∈ Finset.range (a + 1),
        polyBernoulliPoly j (-(n : ℤ)) (-1) * elemSymm a j =
      (-1 : ℚ) ^ n * ∑ r ∈ Finset.range (n + 1),
        ((-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ)) *
          (∑ j ∈ Finset.range (a + 1), elemSymm a j * (r : ℚ) ^ j) := by
    rw [Finset.sum_congr rfl (fun j _ => hper j), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.mul_sum]
  have hterm : ∀ r : ℕ, ((-1 : ℚ) ^ r * (r.factorial : ℚ) *
        (Nat.stirlingSecond n r : ℚ)) *
        (∑ j ∈ Finset.range (a + 1), elemSymm a j * (r : ℚ) ^ j) =
      (-1 : ℚ) ^ r * (Nat.stirlingSecond n r : ℚ) * ((a + r).factorial : ℚ) /
        (a.factorial : ℚ) := by
    intro r
    rw [elemSymm_sum_factorial]
    have h1 : (r.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (a.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hswap, Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.sum_div,
    sum_stirlingSecond_factorial]
  have h2 : (a.factorial : ℚ) ≠ 0 := by positivity
  have hY2 : ((-1 : ℚ) ^ n * (a.factorial : ℚ) * ((a : ℚ) + 1) ^ n) /
      (a.factorial : ℚ) = (-1 : ℚ) ^ n * ((a : ℚ) + 1) ^ n := by
    rw [div_eq_iff h2]
    ring
  rw [hY2, ← mul_assoc, ← pow_add]
  have hev : Even (n + n) := ⟨n, by ring⟩
  rw [Even.neg_one_pow hev, one_mul]

private lemma elemSymm_sum_polyBernoulli (n a : ℕ) :
    ∑ j ∈ Finset.range (a + 1),
        ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) * ((elemSymm a j : ℚ) : ℂ) =
      ((a : ℂ) + 1) ^ n := by
  have h := elemSymm_sum_polyBernoulli_rat n a
  have hcast : ((∑ j ∈ Finset.range (a + 1),
        polyBernoulliPoly j (-(n : ℤ)) (-1) * elemSymm a j : ℚ) : ℂ) =
      ∑ j ∈ Finset.range (a + 1),
        ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) *
          ((elemSymm a j : ℚ) : ℂ) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [← hcast, h]
  push_cast
  ring

private lemma abs_polyBernoulliPoly_neg_le (n j : ℕ) :
    |polyBernoulliPoly j (-(n : ℤ)) (-1)| ≤
      (∑ r ∈ Finset.range (n + 1),
        (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ)) * (n : ℚ) ^ j := by
  have hfactor : ∀ r : ℕ, |(-1 : ℚ) ^ r * (r.factorial : ℚ) *
        (Nat.stirlingSecond n r : ℚ) * (r : ℚ) ^ j| =
      (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) * (r : ℚ) ^ j := by
    intro r
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
  calc |polyBernoulliPoly j (-(n : ℤ)) (-1)|
      = |∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) *
            (r : ℚ) ^ j| := by
        rw [polyBernoulliPoly_neg, abs_mul]
        simp
    _ ≤ ∑ r ∈ Finset.range (n + 1),
          |(-1 : ℚ) ^ r * (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) *
            (r : ℚ) ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ Finset.range (n + 1),
          (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) * (r : ℚ) ^ j := by
        apply Finset.sum_congr rfl
        intro r _
        exact hfactor r
    _ ≤ (∑ r ∈ Finset.range (n + 1),
          (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ)) * (n : ℚ) ^ j := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro r hr
        have hrle : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        have hpow : (r : ℚ) ^ j ≤ (n : ℚ) ^ j :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hrle) j
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

private lemma norm_heightOneTermPoly (n : ℕ) (s : ℂ) (a j : ℕ) :
    ‖heightOneTermPoly n s a j‖ =
      ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) * (elemSymm a j : ℝ) *
        |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| := by
  have hbase : ((a : ℂ) + 1) = (((a : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hE : ‖((elemSymm a j : ℚ) : ℂ)‖ = (elemSymm a j : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg]
    exact_mod_cast elemSymm_nonneg a j
  have hP : ‖((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ)‖ =
      |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  unfold heightOneTermPoly
  rw [norm_mul, norm_mul, hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hE, hP]
  congr 2

private lemma rowSum_heightOneTermPoly (n a : ℕ) (s : ℂ) :
    ∑ j ∈ Finset.range (a + 1), heightOneTermPoly n s a j = ((a : ℂ) + 1) ^ (-s) := by
  have hx : ((a : ℂ) + 1) ≠ 0 := by
    have hcast : ((a : ℂ) + 1) = (((a + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast Nat.succ_ne_zero a
  have hper : ∀ j : ℕ, heightOneTermPoly n s a j =
      ((a : ℂ) + 1) ^ (-(s + (n : ℂ))) *
        (((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) *
          ((elemSymm a j : ℚ) : ℂ)) := by
    intro j
    unfold heightOneTermPoly
    ring
  rw [Finset.sum_congr rfl (fun j _ => hper j), ← Finset.mul_sum,
    elemSymm_sum_polyBernoulli, ← Complex.cpow_natCast,
    ← Complex.cpow_add (-(s + (n : ℂ))) ((n : ℂ)) hx]
  congr 1
  ring

private lemma hasSum_heightOneMultipleZeta_mul_nat_part2 (n : ℕ) (s : ℂ)
    (hs : 1 < s.re) :
    HasSum (fun j : ℕ => (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
        heightOneMultipleZeta (s + n) j) (riemannZeta s) := by
  have hfin : ∀ a j : ℕ, a < j → heightOneTermPoly n s a j = 0 := by
    intro a j hj
    unfold heightOneTermPoly
    rw [elemSymm_eq_zero_of_lt hj]
    simp
  have hC : (0 : ℝ) ≤ ((∑ r ∈ Finset.range (n + 1),
      (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) := by
    positivity
  have habs : ∀ j : ℕ, |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| ≤
      ((∑ r ∈ Finset.range (n + 1),
        (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
        (n : ℝ) ^ j := by
    intro j
    have h := abs_polyBernoulliPoly_neg_le n j
    have hcast : |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| =
        ((|polyBernoulliPoly j (-(n : ℤ)) (-1)| : ℚ) : ℝ) := by
      rw [Rat.cast_abs]
    rw [hcast]
    exact_mod_cast h
  have hrowsum : ∀ a : ℕ, ∑ j ∈ Finset.range (a + 1), ‖heightOneTermPoly n s a j‖ =
      ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
        ∑ j ∈ Finset.range (a + 1),
          (elemSymm a j : ℝ) *
            |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| := by
    intro a
    have hstep : ∀ j : ℕ, ‖heightOneTermPoly n s a j‖ =
        ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
          ((elemSymm a j : ℝ) *
            |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)|) := by
      intro j
      rw [norm_heightOneTermPoly]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum]
  have hbound : ∀ a : ℕ, ∑ j ∈ Finset.range (a + 1), ‖heightOneTermPoly n s a j‖ ≤
      ((((∑ r ∈ Finset.range (n + 1),
        (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
          ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) *
        ((a : ℝ) + 1) ^ (-s.re) := by
    intro a
    rw [hrowsum]
    have hsumle : ∑ j ∈ Finset.range (a + 1),
          (elemSymm a j : ℝ) *
            |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)| ≤
        ((∑ r ∈ Finset.range (n + 1),
          (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
          (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ))) := by
      calc ∑ j ∈ Finset.range (a + 1),
              (elemSymm a j : ℝ) *
                |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)|
          ≤ ∑ j ∈ Finset.range (a + 1),
              (elemSymm a j : ℝ) *
                ((((∑ r ∈ Finset.range (n + 1),
                  (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ)) *
                  (n : ℝ) ^ j) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (habs j)
              (by exact_mod_cast elemSymm_nonneg a j)
        _ = ((∑ r ∈ Finset.range (n + 1),
              (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
              ∑ j ∈ Finset.range (a + 1), (elemSymm a j : ℝ) * (n : ℝ) ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = ((∑ r ∈ Finset.range (n + 1),
              (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
              (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ))) := by
            rw [elemSymm_sum_real]
    have hle := factorial_ratio_le a n
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hmerge : ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
          ((a : ℝ) + 1) ^ ((n : ℝ)) = ((a : ℝ) + 1) ^ (-s.re) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    have hpow : ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
          ((((∑ r ∈ Finset.range (n + 1),
            (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ)) *
            (((a : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) =
        ((((∑ r ∈ Finset.range (n + 1),
          (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
            ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) *
          ((a : ℝ) + 1) ^ (-s.re) := by
      rw [← Real.rpow_natCast ((a : ℝ) + 1) n, ← hmerge]
      ring
    calc ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
            ∑ j ∈ Finset.range (a + 1),
              (elemSymm a j : ℝ) *
                |((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℝ)|
        ≤ ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
            ((((∑ r ∈ Finset.range (n + 1),
              (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ)) *
              (((a + n).factorial : ℝ) / ((a.factorial : ℝ) * (n.factorial : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsumle
            (Real.rpow_nonneg (le_of_lt hpos) _)
      _ ≤ ((a : ℝ) + 1) ^ (-(s.re + (n : ℝ))) *
            ((((∑ r ∈ Finset.range (n + 1),
              (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ)) *
              (((a : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hC)
            (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = ((((∑ r ∈ Finset.range (n + 1),
            (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
              ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) *
            ((a : ℝ) + 1) ^ (-s.re) := hpow
  have hF : Summable (Function.uncurry (heightOneTermPoly n s)) :=
    summable_uncurry_of_finite_rows hfin
      (summable_of_row_bound (fun a => Finset.sum_nonneg
        (fun j _ => norm_nonneg _)) hs
        ((((∑ r ∈ Finset.range (n + 1),
          (r.factorial : ℚ) * (Nat.stirlingSecond n r : ℚ) : ℚ) : ℝ) *
            ((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) hbound)
  have hr : ∀ a : ℕ, HasSum (heightOneTermPoly n s a)
      (∑ j ∈ Finset.range (a + 1), heightOneTermPoly n s a j) := by
    intro a
    have hnot : ∀ j ∉ Finset.range (a + 1), a < j := by
      intro j hj
      have h1 : ¬ j < a + 1 := fun h => hj (Finset.mem_range.mpr h)
      omega
    have hsum : Summable (heightOneTermPoly n s a) :=
      summable_of_ne_finset_zero (s := Finset.range (a + 1))
        (fun j hj => hfin a j (hnot j hj))
    have h := hsum.hasSum
    rwa [tsum_eq_sum (fun j hj => hfin a j (hnot j hj))] at h
  have hc : ∀ j : ℕ, HasSum (fun a => heightOneTermPoly n s a j)
      ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
        heightOneMultipleZeta (s + n) j) := by
    intro j
    have hfib : Summable (fun a => heightOneTermPoly n s a j) :=
      hF.prod_symm.prod_factor j
    have htsum : (∑' a : ℕ, heightOneTermPoly n s a j) =
        (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
          heightOneMultipleZeta (s + n) j := by
      calc (∑' a : ℕ, heightOneTermPoly n s a j) =
            ∑' a : ℕ, (((a : ℂ) + 1) ^ (-(s + n)) * ((elemSymm a j : ℚ) : ℂ)) *
              ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) :=
          tsum_congr fun a => by unfold heightOneTermPoly; ring
        _ = (∑' a : ℕ, ((a : ℂ) + 1) ^ (-(s + n)) * ((elemSymm a j : ℚ) : ℂ)) *
              ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) := tsum_mul_right
        _ = heightOneMultipleZeta (s + n) j *
              ((polyBernoulliPoly j (-(n : ℤ)) (-1) : ℚ) : ℂ) := by
          rw [heightOne_eq_tsum_elemSymm]
        _ = (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
              heightOneMultipleZeta (s + n) j := mul_comm _ _
    exact htsum ▸ hfib.hasSum
  have hs : HasSum (fun a => ∑ j ∈ Finset.range (a + 1), heightOneTermPoly n s a j)
      (riemannZeta s) := by
    have hzeta0 : HasSum (fun a : ℕ => ((a : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
      have hsumm : Summable (fun a : ℕ => ((a : ℂ) + 1) ^ (-s)) := by
        have h1 : Summable (fun k : ℕ => 1 / (k : ℂ) ^ s) :=
          Complex.summable_one_div_nat_cpow.mpr hs
        have h2 := (summable_nat_add_iff
          (f := fun k : ℕ => 1 / (k : ℂ) ^ s) 1).mpr h1
        have hfun : (fun a : ℕ => ((a : ℂ) + 1) ^ (-s)) =
            (fun a : ℕ => 1 / (((a + 1 : ℕ)) : ℂ) ^ s) := by
          funext a
          rw [Complex.cpow_neg, one_div]
          push_cast
          ring
        rw [hfun]
        exact h2
      have htsum : (∑' a : ℕ, ((a : ℂ) + 1) ^ (-s)) = riemannZeta s := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
        apply tsum_congr
        intro a
        rw [Complex.cpow_neg, one_div]
      have hhas := hsumm.hasSum
      rwa [htsum] at hhas
    apply HasSum.congr_fun hzeta0
    intro a
    exact rowSum_heightOneTermPoly n a s
  exact hasSum_swap hF hr hc hs

/-- **Height one multiple zeta series weighted by powers of a natural number.** Let $n \ge 0$ be
an integer. Write $\zeta(s, \{1\}^j)$ for the height one multiple zeta function, $\zeta$ for the
Riemann zeta function, $c(n, m)$ for the unsigned Stirling numbers of the first kind and
$B_j^{(k)}(x)$ for the poly-Bernoulli polynomials. For every complex $s$ with
$\operatorname{Re} s > n + 1$, the series $\sum_{j \ge 0} \zeta(s, \{1\}^j) \, n^j$ (with $0^0 = 1$)
is summable with sum $\frac{1}{n!} \sum_{m=0}^{n} c(n, m) \, \zeta(s - m)$. For every complex $s$
with $\operatorname{Re} s > 1$, the series $\sum_{j \ge 0} B_j^{(-n)}(-1) \, \zeta(s + n, \{1\}^j)$
is summable with sum $\zeta(s)$.

The source states the second identity with $C_j^{(-n)} = B_j^{(-n)}(1)$, where its poly-Bernoulli
polynomials have the generating function with $e^{-xt}$; with the factor $e^{xt}$ used here this
coefficient is $B_j^{(-n)}(-1)$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 1 (`integers-2024-A43-cor-1`). -/
public theorem hasSum_heightOneMultipleZeta_mul_nat_pow (n : ℕ) :
    (∀ s : ℂ, (n : ℝ) + 1 < s.re →
      HasSum (fun j : ℕ => heightOneMultipleZeta s j * (n : ℂ) ^ j)
        (1 / (n.factorial : ℂ) *
          ∑ m ∈ Finset.range (n + 1), (n.stirlingFirst m : ℂ) * riemannZeta (s - m))) ∧
    ∀ s : ℂ, 1 < s.re →
      HasSum (fun j : ℕ => (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
        heightOneMultipleZeta (s + n) j) (riemannZeta s) :=
  ⟨fun s hs => hasSum_heightOneMultipleZeta_mul_nat_part1 n s hs,
    fun s hs => hasSum_heightOneMultipleZeta_mul_nat_part2 n s hs⟩

end

end MetaMathlibExt
