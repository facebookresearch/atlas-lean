/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Shifted alternating series of height one multiple zeta values

The shifted alternating series of height one multiple zeta values converges to a weighted
integral of the multiple Hurwitz zeta function.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Height one multiple zeta function.** For a complex number $s$ and an integer $j \ge 0$, the
height one multiple zeta function is
$$\zeta(s, \{1\}^j) = \sum_{n \ge 0} (n + 1)^{-s} \sum_{T} \prod_{m \in T} \frac{1}{m},$$
where $T$ runs over the $j$-element subsets of $\{1, \dots, n\}$. Writing $n_1 = n + 1$ and
$T = \{n_2, \dots, n_{j+1}\}$, this is
$\zeta(s, \{1\}^j) = \sum_{n_1 > \cdots > n_{j+1} \ge 1} n_1^{-s} (n_2 \cdots n_{j+1})^{-1}$, which
converges for $\operatorname{Re} s > 1$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public noncomputable def heightOneMultipleZeta (s : ℂ) (j : ℕ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) *
    ∑ T ∈ (Finset.Icc 1 n).powersetCard j, ∏ m ∈ T, (1 / (m : ℂ))

/-- **Height one multiple zeta function of depth one.** For every complex number $s$, the height
one multiple zeta function $\zeta(s, \{1\}^j)$ at $j = 0$ is the Dirichlet series of the Riemann
zeta function: $\zeta(s, \{1\}^0) = \sum_{n \ge 0} (n + 1)^{-s}$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public theorem heightOneMultipleZeta_zero (s : ℂ) :
    heightOneMultipleZeta s 0 = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) := by
  simp [heightOneMultipleZeta]

/-- **Multiple Hurwitz zeta function.** For complex numbers $r$ and $s$, the multiple Hurwitz zeta
function of order $r$, with Hurwitz parameter $a = 1$, is the Dirichlet series
$$\zeta_r(s) = \sum_{m \ge 0} \binom{m + r - 1}{m} (m + 1)^{-s},$$
where $\binom{m + r - 1}{m} = r (r + 1) \cdots (r + m - 1) / m!$. The series converges for
$\operatorname{Re} r < \operatorname{Re} s$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public noncomputable def multipleHurwitzZeta (r s : ℂ) : ℂ :=
  ∑' m : ℕ, (ascPochhammer ℂ m).eval r / (m.factorial : ℂ) * ((m : ℂ) + 1) ^ (-s)

/-- **Multiple Hurwitz zeta function of order zero.** For every complex number $s$, the multiple
Hurwitz zeta function of order $0$ is identically one: $\zeta_0(s) = 1$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public theorem multipleHurwitzZeta_zero (s : ℂ) : multipleHurwitzZeta 0 s = 1 := by
  rw [multipleHurwitzZeta, tsum_eq_single 0]
  · simp
  · intro m hm
    simp [hm]

open Finset Filter
open scoped Topology

-- The elementary symmetric sum in the reciprocals of the first a positive integers.
private noncomputable def harmonicCoeff (a p : ℕ) : ℝ :=
  ∑ T ∈ (Icc 1 a).powersetCard p, ∏ m ∈ T, (1 / (m : ℝ))

private lemma harmonicCoeff_nonneg (a p : ℕ) : 0 ≤ harmonicCoeff a p := by
  unfold harmonicCoeff
  positivity

private lemma harmonicCoeff_succ (a p : ℕ) :
    harmonicCoeff a (p + 1) = ∑ i ∈ range a, harmonicCoeff i p / (i + 1) := by
  induction a with
  | zero =>
    have he : (∅ : Finset ℕ).powersetCard (p + 1) = ∅ := powersetCard_eq_empty.mpr (by simp)
    simp [harmonicCoeff, he]
  | succ a ih =>
    have h : a + 1 ∉ Icc 1 a := by simp
    have hT {j T} (ht : T ∈ (Icc 1 a).powersetCard j) : a + 1 ∉ T :=
      fun ha => h ((mem_powersetCard.mp ht).1 ha)
    have hi : Icc 1 (a + 1) = insert (a + 1) (Icc 1 a) := by ext i; simp; omega
    rw [sum_range_succ, ← ih]
    unfold harmonicCoeff
    rw [hi, powersetCard_succ_insert h, sum_union, sum_image, sum_div]
    · congr 1
      apply sum_congr rfl
      intro T ht
      rw [prod_insert (hT ht), Nat.cast_add, Nat.cast_one]
      ring
    · intro T ht U hu he
      simpa [hT ht, hT hu] using congrArg (fun V : Finset ℕ => V.erase (a + 1)) he
    · rw [disjoint_left]
      rintro T ht him
      obtain ⟨U, _, rfl⟩ := mem_image.mp him
      exact hT ht (mem_insert_self ..)

-- The integer beta kernel and its two first differences.
private noncomputable def betaKernel (a b : ℕ) : ℝ :=
  (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial

private noncomputable def weight (a b : ℕ) : ℝ := betaKernel a b / (a + b + 2)

private lemma betaKernel_nonneg (a b : ℕ) : 0 ≤ betaKernel a b := by
  unfold betaKernel
  positivity

private lemma weight_nonneg (a b : ℕ) : 0 ≤ weight a b := by
  exact div_nonneg (betaKernel_nonneg ..) (by positivity)

private lemma betaKernel_symm (a b : ℕ) : betaKernel a b = betaKernel b a := by
  simp only [betaKernel, add_comm a b, mul_comm]

private lemma betaKernel_step (a b : ℕ) :
    betaKernel (a + 1) b = (a + 1) * weight a b := by
  unfold weight betaKernel
  rw [show a + 1 + b + 1 = (a + b + 1) + 1 by omega, Nat.factorial_succ (a + b + 1),
    Nat.factorial_succ a]
  push_cast
  field_simp
  ring

private lemma betaKernel_zero (a : ℕ) : betaKernel 0 a = 1 / (a + 1) := by
  simp [betaKernel, Nat.factorial_succ, mul_comm, div_mul_eq_div_div, Nat.factorial_ne_zero]

private lemma betaKernel_le (a b : ℕ) : betaKernel a b ≤ 1 / (b + 1) := by
  induction a with
  | zero => rw [betaKernel_zero]
  | succ a ih =>
    apply le_trans _ ih
    rw [betaKernel_step, weight, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [betaKernel_nonneg a b, mul_nonneg (betaKernel_nonneg a b) (Nat.cast_nonneg b)]

private lemma betaKernel_lim (a : ℕ) : Tendsto (betaKernel a) atTop (𝓝 0) :=
  squeeze_zero (betaKernel_nonneg a) (betaKernel_le a) tendsto_one_div_add_atTop_nhds_zero_nat

private lemma hasSum_difference {f g : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : ∀ i, f i = g i - g (i + 1)) (hg : Tendsto g atTop (𝓝 0)) :
    HasSum f (g 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hf]
  simpa only [h, sum_range_sub', sub_zero, Pi.sub_apply] using
    (tendsto_const_nhds (x := g 0)).sub hg

private noncomputable def pochCoeff (r : ℝ) (b : ℕ) : ℝ :=
  (ascPochhammer ℝ b).eval r / b.factorial

private lemma pochCoeff_step (r : ℝ) (b : ℕ) :
    pochCoeff r (b + 1) = pochCoeff r b * (r + b) / (b + 1) := by
  simp [pochCoeff, ascPochhammer_succ_eval, Nat.factorial_succ, div_eq_mul_inv]
  ring

private lemma pochCoeff_mem {r : ℝ} (hr : r ∈ Set.Icc 0 1) (b : ℕ) :
    pochCoeff r b ∈ Set.Icc 0 1 := by
  induction b with
  | zero => simp [pochCoeff]
  | succ b ih =>
    rw [pochCoeff_step]
    refine ⟨div_nonneg (mul_nonneg ih.1 (by linarith [hr.1, Nat.cast_nonneg (α := ℝ) b]))
      (by positivity), (div_le_iff₀ (by positivity)).2 ?_⟩
    calc
      pochCoeff r b * (r + b) ≤ 1 * (r + b) :=
        mul_le_mul_of_nonneg_right ih.2 (by linarith [hr.1, Nat.cast_nonneg (α := ℝ) b])
      _ ≤ _ := by linarith [hr.2]

private lemma hasSum_poch_weight {x : ℝ} (hx : x ∈ Set.Icc 0 1) (a : ℕ) :
    HasSum (fun b => pochCoeff (1 - x) b * weight a b) (1 / ((a + 1) * (a + 1 + x))) := by
  have hr : 1 - x ∈ Set.Icc 0 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd : 0 < (a : ℝ) + 1 + x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]
  let g b := pochCoeff (1 - x) b * betaKernel a b / (a + 1 + x)
  have hg : Tendsto g atTop (𝓝 0) := by
    apply squeeze_zero (fun b => div_nonneg (mul_nonneg (pochCoeff_mem hr b).1
      (betaKernel_nonneg ..)) hd.le) (fun b => div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (betaKernel_nonneg ..) (pochCoeff_mem hr b).2) hd.le)
    simpa using (betaKernel_lim a).div_const ((a : ℝ) + 1 + x)
  have h := hasSum_difference (g := g) (fun b => mul_nonneg (pochCoeff_mem hr b).1
    (weight_nonneg a b)) (fun b => by
      dsimp [g]
      rw [pochCoeff_step, betaKernel_symm a (b + 1), betaKernel_step]
      simp only [weight, betaKernel_symm b a, add_comm (b : ℝ) a]
      field_simp
      ring) hg
  simpa [g, pochCoeff, betaKernel_symm a 0, betaKernel_zero, div_eq_mul_inv, mul_comm] using h

private lemma transpose_nonneg {f : ℕ → ℕ → ℝ} {rows cols : ℕ → ℝ} {s : ℝ}
    (hf : ∀ i j, 0 ≤ f i j) (hr : ∀ i, HasSum (f i) (rows i))
    (hc : ∀ j, HasSum (fun i => f i j) (cols j)) (hs : HasSum rows s) : HasSum cols s := by
  have h : Summable (Function.uncurry f) := (summable_prod_of_nonneg
    (fun ij => hf ij.1 ij.2)).2 ⟨fun i => (hr i).summable,
      by simpa [(hr _).tsum_eq] using hs.summable⟩
  have hcols := h.prod_symm.hasSum.prod_fiberwise hc
  have hrows := h.hasSum.prod_fiberwise hr
  change HasSum cols (∑' ij, Function.uncurry f ((Equiv.prodComm ℕ ℕ) ij)) at hcols
  rwa [(Equiv.prodComm ℕ ℕ).tsum_eq (Function.uncurry f), hrows.unique hs] at hcols

private lemma hasSum_weight_tail (m b : ℕ) :
    HasSum (fun a => weight (a + m) b) (betaKernel m b / (b + 1)) := by
  let g a := betaKernel (a + m) b / (b + 1)
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa [g, betaKernel_symm b] using
      ((betaKernel_lim b).comp (tendsto_add_atTop_nat m)).div_const ((b : ℝ) + 1)
  simpa [g] using hasSum_difference (fun a => weight_nonneg (a + m) b) (g := g) (fun a => by
    dsimp [g]
    rw [show a + 1 + m = a + m + 1 by omega, betaKernel_step]
    unfold weight
    push_cast
    field_simp
    ring) hg

-- Adding a reciprocal to the subset sum contributes one further factor of 1 / (b + 1).
private lemma hasSum_harmonic_weight (p b : ℕ) :
    HasSum (fun a => harmonicCoeff a p * weight a b) (1 / (b + 1) ^ (p + 2)) := by
  induction p with
  | zero =>
    simpa [harmonicCoeff, betaKernel_zero, pow_two, div_eq_mul_inv] using hasSum_weight_tail 0 b
  | succ p ih =>
    let f i a := if i < a then harmonicCoeff i p / (i + 1) * weight a b else 0
    let rows i := harmonicCoeff i p * weight i b / (b + 1)
    have hr i : HasSum (f i) (rows i) := by
      have he : ∑ a ∈ range (i + 1), f i a = 0 := sum_eq_zero fun a ha => by
        simp [f, show ¬ i < a by have := mem_range.mp ha; omega]
      rw [← add_zero (rows i), ← he, ← hasSum_nat_add_iff (i + 1)]
      convert (hasSum_weight_tail (i + 1) b).mul_left (harmonicCoeff i p / (i + 1)) using 1
      · ext a
        simp [f, show i < a + (i + 1) by omega]
      · rw [betaKernel_step]
        dsimp [rows]
        field_simp
    have hc a : HasSum (fun i => f i a) (harmonicCoeff a (p + 1) * weight a b) := by
      rw [harmonicCoeff_succ, sum_mul]
      convert hasSum_sum_of_ne_finset_zero (s := range a) (f := fun i => f i a)
        (L := .unconditional ℕ) (fun i hi => by simp [f, mem_range.mpr.mt hi]) using 1
      exact sum_congr rfl fun i hi => by simp [f, mem_range.mp hi]
    apply transpose_nonneg (f := f) (rows := rows) (fun i a => ?_) hr hc
    · convert ih.div_const ((b : ℝ) + 1) using 1
      rw [show p + 1 + 2 = p + 2 + 1 by omega, pow_succ, div_div]
    · dsimp [f]
      split
      · exact mul_nonneg (div_nonneg (harmonicCoeff_nonneg ..) (by positivity)) (weight_nonneg ..)
      · rfl

private noncomputable def hurwitzSeries (r : ℝ) (p : ℕ) : ℝ :=
  ∑' b : ℕ, pochCoeff r b / (b + 1) ^ (p + 2)

-- Sum the nonnegative array of weighted beta kernels first over a and then over b.
private lemma kernel_expansion {x : ℝ} (hx : x ∈ Set.Icc 0 1) (p : ℕ) :
    HasSum (fun a : ℕ => harmonicCoeff a p / ((a + 1) * (a + 1 + x)))
      (hurwitzSeries (1 - x) p) := by
  let r := 1 - x
  have hr : r ∈ Set.Icc 0 1 := ⟨by dsimp [r]; linarith [hx.2], by dsimp [r]; linarith [hx.1]⟩
  have hp : Summable (fun b : ℕ => 1 / ((b : ℝ) + 1) ^ (p + 2)) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (p + 2)) 1).2
      (Real.summable_one_div_nat_pow.mpr (by omega))
  have hs : Summable (fun b : ℕ => pochCoeff r b / (b + 1) ^ (p + 2)) :=
    hp.of_nonneg_of_le (fun b => div_nonneg (pochCoeff_mem hr b).1 (by positivity))
      (fun b => div_le_div_of_nonneg_right (pochCoeff_mem hr b).2 (by positivity))
  apply transpose_nonneg (f := fun b a => pochCoeff r b * (harmonicCoeff a p * weight a b))
    (fun b a => mul_nonneg (pochCoeff_mem hr b).1
      (mul_nonneg (harmonicCoeff_nonneg ..) (weight_nonneg ..))) _ _ hs.hasSum
  · intro b
    simpa [div_eq_mul_inv] using (hasSum_harmonic_weight p b).mul_left (pochCoeff r b)
  · intro a
    simpa [r, mul_left_comm, div_eq_mul_inv] using (hasSum_poch_weight hx a).mul_left
      (harmonicCoeff a p)

-- At x = 0 the expansion provides a summable majorant for every zeta value used below.
private noncomputable def moment (p n : ℕ) : ℝ :=
  ∑' a : ℕ, harmonicCoeff a p / (a + 1) ^ (n + 2)

private lemma hasSum_moment (p n : ℕ) :
    HasSum (fun a : ℕ => harmonicCoeff a p / (a + 1) ^ (n + 2)) (moment p n) := by
  have h := (kernel_expansion (x := 0) (by simp) p).summable
  refine (h.of_nonneg_of_le (fun a => div_nonneg (harmonicCoeff_nonneg ..) (by positivity))
    (fun a => ?_)).hasSum
  simp only [add_zero, ← sq]
  apply div_le_div_of_nonneg_left (harmonicCoeff_nonneg ..) (by positivity)
  exact pow_le_pow_right₀ (by simp : (1 : ℝ) ≤ (a : ℝ) + 1) (by omega)

private noncomputable def partialPoly (p N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ range N, (-x) ^ n * moment p n

-- Sum the finite geometric progression at each a before estimating its remainder.
private lemma partial_error {x : ℝ} (hx : x ∈ Set.Icc 0 1) (p N : ℕ) :
    |hurwitzSeries (1 - x) p - partialPoly p N x| ≤ x ^ N * hurwitzSeries (1 - x) p := by
  let d (a : ℕ) : ℝ := a + 1
  let mass a := harmonicCoeff a p / (d a * (d a + x))
  have hd a : 0 < d a := by dsimp [d]; positivity
  have hdx a : 0 < d a + x := add_pos_of_pos_of_nonneg (hd a) hx.1
  have hmass a : 0 ≤ mass a := div_nonneg (harmonicCoeff_nonneg ..) (mul_pos (hd a) (hdx a)).le
  have hsum : HasSum mass (hurwitzSeries (1 - x) p) := kernel_expansion hx p
  have hfin := hasSum_sum (s := range N) (fun n _ => (hasSum_moment p n).mul_left ((-x) ^ n))
  have hrem : HasSum (fun a => mass a * (-x / d a) ^ N)
      (hurwitzSeries (1 - x) p - partialPoly p N x) := by
    apply (hsum.sub hfin).congr_fun
    intro a
    change mass a * (-x / d a) ^ N = mass a -
      ∑ n ∈ range N, (-x) ^ n * (harmonicCoeff a p / d a ^ (n + 2))
    have he n : (-x) ^ n * (harmonicCoeff a p / d a ^ (n + 2)) =
        (harmonicCoeff a p / d a ^ 2) * (-x / d a) ^ n := by
      simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
      ring
    simp_rw [he]
    rw [← mul_sum]
    have heq : mass a * (-x / d a - 1) = -(harmonicCoeff a p / d a ^ 2) := by
      dsimp only [mass]
      field_simp [(hd a).ne', (hdx a).ne']
      ring
    linear_combination -(mass a) * geom_sum_mul (-x / d a) N +
      (∑ n ∈ range N, (-x / d a) ^ n) * heq
  have hle a : |mass a * (-x / d a) ^ N| ≤ x ^ N * mass a := by
    rw [abs_mul, abs_of_nonneg (hmass a), abs_pow, abs_div, abs_neg, abs_of_nonneg hx.1,
      abs_of_pos (hd a), mul_comm]
    apply mul_le_mul_of_nonneg_right _ (hmass a)
    exact pow_le_pow_left₀ (div_nonneg hx.1 (hd a).le)
      (div_le_self hx.1 (by dsimp [d]; linarith [Nat.cast_nonneg (α := ℝ) a])) _
  have hm := hsum.mul_left (x ^ N)
  have habs := hm.summable.of_nonneg_of_le (fun a => abs_nonneg _) hle
  rw [← hrem.tsum_eq, ← hm.tsum_eq]
  exact (norm_tsum_le_tsum_norm (f := fun a => mass a * (-x / d a) ^ N) habs).trans
    (habs.tsum_le_tsum hle hm.summable)

private lemma hurwitzSeries_le {x : ℝ} (hx : x ∈ Set.Icc 0 1) (p : ℕ) :
    hurwitzSeries (1 - x) p ≤ moment p 0 := by
  have h := kernel_expansion hx p
  rw [← h.tsum_eq, ← (hasSum_moment p 0).tsum_eq]
  apply h.summable.tsum_le_tsum _ (hasSum_moment p 0).summable
  intro a
  apply div_le_div_of_nonneg_left (harmonicCoeff_nonneg ..) (by positivity)
  simp only [zero_add, pow_two]
  exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by positivity)

private lemma partial_tendsto {x : ℝ} (hx : x ∈ Set.Ico 0 1) (p : ℕ) :
    Tendsto (fun N => partialPoly p N x) atTop (𝓝 (hurwitzSeries (1 - x) p)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hx.2
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (by simpa using hpow.mul_const (hurwitzSeries (1 - x) p))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact partial_error ⟨hx.1, hx.2.le⟩ p N

private lemma partial_bound {x : ℝ} (hx : x ∈ Set.Icc 0 1) (p N : ℕ) :
    |partialPoly p N x| ≤ 2 * moment p 0 := by
  have hn : 0 ≤ hurwitzSeries (1 - x) p := by
    rw [← (kernel_expansion hx p).tsum_eq]
    exact tsum_nonneg fun a => div_nonneg (harmonicCoeff_nonneg ..)
      (mul_nonneg (by positivity) (add_nonneg (by positivity) hx.1))
  have he := (partial_error hx p N).trans
    (mul_le_of_le_one_left hn (pow_le_one₀ hx.1 hx.2))
  have hb := hurwitzSeries_le hx p
  rw [abs_le] at he ⊢
  constructor <;> linarith [he.1, he.2]

open MeasureTheory

private lemma integral_partial (q p N : ℕ) :
    (∫ r in (0 : ℝ)..1, (1 - r) ^ q * partialPoly p N (1 - r)) =
      ∑ n ∈ range N, (-1 : ℝ) ^ n / (q + n + 1) * moment p n := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun x => x ^ q * partialPoly p N x) 1
  simp only [sub_self, sub_zero] at h
  rw [h]
  simp only [partialPoly, mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable
    (by fun_prop) ..)]
  apply sum_congr rfl
  intro n _
  have he (x : ℝ) : x ^ q * ((-x) ^ n * moment p n) =
      x ^ (q + n) * ((-1) ^ n * moment p n) := by
    rw [show -x = -1 * x by ring, mul_pow, pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

private lemma tendsto_integral_real (q p : ℕ) :
    Tendsto (fun N => ∑ n ∈ range N, (-1 : ℝ) ^ n / (q + n + 1) * moment p n)
      atTop (𝓝 (∫ r in (0 : ℝ)..1, (1 - r) ^ q * hurwitzSeries r p)) := by
  simp_rw [← integral_partial]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * moment p 0)
  · exact Eventually.of_forall fun N => Continuous.aestronglyMeasurable (by
      unfold partialPoly
      fun_prop)
  · refine Eventually.of_forall fun N => ae_of_all _ fun r hr => ?_
    rw [Set.uIoc_of_le zero_le_one] at hr
    have hx : 1 - r ∈ Set.Icc 0 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hx.1 hx.2)).trans
      (partial_bound hx p N)
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun r hr => ?_
    rw [Set.uIoc_of_le zero_le_one] at hr
    have hx : 1 - r ∈ Set.Ico 0 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    simpa using (partial_tendsto hx p).const_mul ((1 - r) ^ q)

private lemma moment_eq (n p : ℕ) :
    (moment p n : ℂ) = heightOneMultipleZeta ((n + 2 : ℕ) : ℂ) p := by
  rw [moment, Complex.ofReal_tsum, heightOneMultipleZeta]
  apply tsum_congr
  intro a
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  simp [harmonicCoeff, div_eq_mul_inv, mul_comm]

private lemma hurwitzSeries_eq (r : ℝ) (p : ℕ) :
    (hurwitzSeries r p : ℂ) = multipleHurwitzZeta r ((p : ℂ) + 2) := by
  rw [hurwitzSeries, Complex.ofReal_tsum, multipleHurwitzZeta]
  apply tsum_congr
  intro b
  have hp : (((ascPochhammer ℝ b).eval r : ℝ) : ℂ) = (ascPochhammer ℂ b).eval (r : ℂ) := by
    induction b with
    | zero => simp
    | succ b ih => simp [ascPochhammer_succ_eval, ih]
  rw [show (p : ℂ) + 2 = ((p + 2 : ℕ) : ℂ) by push_cast; rfl, Complex.cpow_neg,
    Complex.cpow_natCast]
  simp [pochCoeff, hp, div_eq_mul_inv]

/-- **Shifted alternating series of height one multiple zeta values.** Let $k \ge -1$ and
$p \ge 0$ be integers, write $\zeta(s, \{1\}^p)$ for the height one multiple zeta function and
$\zeta_r(s)$ for the multiple Hurwitz zeta function of order $r$. Then the partial sums of the
series $\nu_{k,p} = \sum_{n \ge 2} \frac{(-1)^n \, \zeta(n, \{1\}^p)}{n + k}$ converge to
$\int_0^1 (1 - r)^{k+1} \, \zeta_r(p + 2) \, dr$.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 4 (`integers-2024-A43-thm-4`). -/
public theorem tendsto_alternating_heightOneMultipleZeta_integral (k : ℤ) (hk : -1 ≤ k)
    (p : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico 2 N,
        (-1 : ℂ) ^ n / ((n : ℂ) + k) * heightOneMultipleZeta n p)
      Filter.atTop
      (nhds (∫ r in (0 : ℝ)..1,
        (1 - (r : ℂ)) ^ (k + 1).toNat * multipleHurwitzZeta r ((p : ℂ) + 2))) := by
  let q := (k + 1).toNat
  have hq : (q : ℤ) = k + 1 := Int.toNat_of_nonneg (by omega)
  have hq' : (q : ℂ) = (k : ℂ) + 1 := by exact_mod_cast hq
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_integral_real q p)
  apply (tendsto_add_atTop_iff_nat 2).mp
  convert h using 1
  · ext N
    rw [sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Function.comp_apply, Complex.ofReal_sum]
    apply sum_congr rfl
    intro n _
    rw [Nat.add_comm 2 n, pow_add, ← moment_eq]
    push_cast
    rw [hq']
    ring
  · congr 1
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro r _
    simp [hurwitzSeries_eq, q]

end

end MetaMathlibExt
