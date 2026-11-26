/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import MathlibExt.NumberTheory.LurothConvergent
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lüroth well approximable sets without monotonicity

For each finite nonnegative lower order at infinity, we construct an approximation function
that increases on every tail and whose Lüroth well approximable set has Hausdorff dimension zero.
-/

namespace MetaMathlibExt

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

/-- **Lower order at infinity.** For $\psi : \mathbb{N} \to \mathbb{R}$, the lower order at infinity
of $1/\psi$ is
$$\tau_\psi = \liminf_{q \to \infty} \max\left(-\frac{\log \psi(q)}{\log q},\, 0\right),$$
with the liminf taken in $[0, \infty]$. Here $\log x$ means $\log |x|$ for $x \ne 0$ and
$\log 0 = 0$, and the ratio is read as $0$ when $\log q = 0$. For $\psi$ with values in $(0, 1]$
the ratio is nonnegative once $q \ge 2$, so the truncation at $0$ has no effect there, and
$\tau_\psi$ may be infinite.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public noncomputable def lowerOrderAtInfinity (ψ : ℕ → ℝ) : ℝ≥0∞ :=
  liminf (fun q : ℕ => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)) atTop

/-- **The order ratio of $q^{-\tau}$.** For every real $\tau$ and all sufficiently large natural
numbers $q$, $\max(0, -\log((q^{\tau})^{-1})/\log q) = \max(0, \tau)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public theorem orderRatio_rpow_inv (τ : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      ENNReal.ofReal (-Real.log (((q : ℝ) ^ τ)⁻¹) / Real.log q) = ENNReal.ofReal τ := by
  filter_upwards [eventually_ge_atTop 2] with q hq
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq').ne'
  rw [Real.log_inv, Real.log_rpow (by linarith), neg_neg, mul_div_assoc, div_self hlog,
    mul_one]

/-- **Lower order at infinity of a power function.** For a real number $\tau$, let
$\psi : \mathbb{N} \to \mathbb{R}$ be given by $\psi(q) = q^{-\tau}$ (the value at $q = 0$ does not
matter). Then the lower order at infinity of $1/\psi$ is $\tau_\psi = \max(\tau, 0)$, an element of
$[0, \infty]$; in particular $\tau_\psi = \tau$ when $\tau \ge 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, remark after Theorem 7. -/
public theorem lowerOrderAtInfinity_rpow_inv (τ : ℝ) :
    lowerOrderAtInfinity (fun q => ((q : ℝ) ^ τ)⁻¹) = ENNReal.ofReal τ := by
  rw [lowerOrderAtInfinity, liminf_congr (orderRatio_rpow_inv τ), liminf_const]

/-- **Recurrence for Lüroth denominators.** For every sequence of natural numbers
$d_0, d_1, d_2, \dots$ with Lüroth denominators $Q_0, Q_1, Q_2, \dots$ and every $n \ge 0$,
$$Q_{n+1} = Q_n (d_n - 1) d_{n+1}.$$

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public theorem lurothDenominator_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothDenominator d (n + 1) = lurothDenominator d n * (d n - 1) * d (n + 1) := by
  simp only [lurothDenominator, Finset.prod_range_succ]
  ring

/-- **Recurrence for Lüroth convergents.** For every sequence of natural numbers
$d_0, d_1, d_2, \dots$ with Lüroth denominators $Q_n$ and Lüroth convergents $x_n$, and every
$n \ge 0$, $x_{n+1} = x_n + 1/Q_{n+1}$, where $1/Q_{n+1}$ is read as $0$ if $Q_{n+1} = 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothConvergent_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothConvergent d (n + 1) =
      lurothConvergent d n + 1 / (lurothDenominator d (n + 1) : ℚ) := by
  rw [lurothConvergent, Finset.sum_range_succ, ← lurothConvergent]

/-- **Lüroth well approximable numbers.** For a function $\psi$ from the natural numbers to the
reals, $L(\psi)$ is the set of $x \in (0, 1]$ such that $|x - c_n(x)| < \psi(Q_n(x))/Q_n(x)$ for
infinitely many $n$, where $Q_n(x)$ and $c_n(x)$ are the $n$-th Lüroth denominator and the $n$-th
Lüroth convergent of the Lüroth digit sequence of $x$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothWellApproximableSet (ψ : ℕ → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ioc 0 1 ∧ ∃ᶠ n in atTop,
    |x - lurothConvergent (lurothDigitSeq x) n| <
      ψ (lurothDenominator (lurothDigitSeq x) n) / lurothDenominator (lurothDigitSeq x) n}

/-- **Lüroth well approximable numbers lie in $(0, 1]$.** For every function $\psi$ from the
natural numbers to the reals, the set $L(\psi)$ of Lüroth $\psi$-well approximable numbers is
contained in $(0, 1]$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothWellApproximableSet_subset_Ioc (ψ : ℕ → ℝ) :
    lurothWellApproximableSet ψ ⊆ Set.Ioc 0 1 :=
  fun _ hx => hx.1

end

namespace exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero

private noncomputable def approximationFunction (τ : ℝ) (q : ℕ) : ℝ :=
  if Even q then (((q : ℝ) + 1) ^ τ)⁻¹ * (1 / 2) ^ q else ((q : ℝ) ^ τ)⁻¹

private theorem approximationFunction_bounds (τ : ℝ) (hτ : 0 ≤ τ) (q : ℕ) :
    0 < approximationFunction τ q ∧ approximationFunction τ q ≤ 1 := by
  unfold approximationFunction
  split_ifs with he
  · have hbase : (1 : ℝ) ≤ (q : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    refine ⟨by positivity, ?_⟩
    exact (mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))).trans
        (inv_le_one_of_one_le₀ (Real.one_le_rpow hbase hτ))
  · have hne : q ≠ 0 := by
      rintro rfl
      exact he ⟨0, rfl⟩
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    exact ⟨inv_pos.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hq) _),
      inv_le_one_of_one_le₀ (Real.one_le_rpow hq hτ)⟩

private theorem approximationFunction_not_antitone (τ : ℝ) :
    ¬ ∃ N, AntitoneOn (approximationFunction τ) (Set.Ici N) := by
  rintro ⟨N, hN⟩
  let q := 2 * (N + 1)
  have he : Even q := even_iff_two_dvd.mpr ⟨N + 1, rfl⟩
  have ho : ¬ Even (q + 1) := Nat.not_even_two_mul_add_one (N + 1)
  have hq : N ≤ q := by dsimp [q]; omega
  have hpos : 0 < q := by dsimp [q]; omega
  have hlt : approximationFunction τ q < approximationFunction τ (q + 1) := by
    rw [approximationFunction, ite_eq_left he, approximationFunction, ite_eq_right ho, Nat.cast_add,
      Nat.cast_one]
    exact mul_lt_of_lt_one_right (by positivity) (pow_lt_one₀ (by norm_num) (by norm_num) hpos.ne')
  exact hlt.not_ge (hN hq (hq.trans (Nat.le_succ q)) (Nat.le_succ q))

private theorem approximationFunction_lowerOrder (τ : ℝ) (hτ : 0 ≤ τ) :
    lowerOrderAtInfinity (approximationFunction τ) = ENNReal.ofReal τ := by
  unfold lowerOrderAtInfinity
  apply le_antisymm
  · apply liminf_le_of_frequently_le'
    have hodd : ∃ᶠ q : ℕ in atTop, ¬ Even q :=
      frequently_atTop.mpr fun n => ⟨2 * n + 1, by omega, Nat.not_even_two_mul_add_one n⟩
    apply (hodd.and_eventually (orderRatio_rpow_inv τ)).mono
    intro q ⟨ho, hr⟩
    simpa only [approximationFunction, ite_eq_right ho, hr] using le_rfl (a := ENNReal.ofReal τ)
  · apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop 2, orderRatio_rpow_inv τ] with q hq hr
    have hq' : (1 : ℝ) < q := by exact_mod_cast hq
    have hψ : approximationFunction τ q ≤ ((q : ℝ) ^ τ)⁻¹ := by
      unfold approximationFunction
      split_ifs
      · calc
          _ ≤ (((q : ℝ) + 1) ^ τ)⁻¹ :=
            mul_le_of_le_one_right (by positivity)
              (pow_le_one₀ (by norm_num) (by norm_num))
          _ ≤ ((q : ℝ) ^ τ)⁻¹ := by
            apply inv_anti₀ (by positivity)
            exact Real.rpow_le_rpow (by positivity) (by linarith) hτ
      · exact le_rfl
    rw [← hr]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (neg_le_neg (Real.log_le_log (approximationFunction_bounds τ hτ q).1 hψ))
      (Real.log_pos hq').le)

private theorem denominator_pos {x : ℝ} (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    0 < lurothDenominator (lurothDigitSeq x) n := by
  by_contra! h
  have hz := Nat.eq_zero_of_le_zero h
  have he := lurothConvergent_lt_le x hx n
  simpa [hz, he.1.not_ge] using he.2

private theorem digit_ge_two {x : ℝ} (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    2 ≤ lurothDigitSeq x n := by
  have he := lurothConvergent_lt_le x hx n
  have hp := one_div_pos.mp (he.1.trans_le he.2)
  have hd := pos_of_mul_pos_left hp (Nat.cast_nonneg _)
  have hd' : (1 : ℝ) < lurothDigitSeq x n := sub_pos.mp hd
  exact_mod_cast hd'

private theorem index_le_denominator {x : ℝ} (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    n ≤ lurothDenominator (lurothDigitSeq x) n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hn := denominator_pos hx n
    rw [lurothDenominator_succ]
    calc
      n + 1 ≤ lurothDenominator (lurothDigitSeq x) n * 2 := by omega
      _ ≤ _ := by
        have := digit_ge_two hx n
        have := digit_ge_two hx (n + 1)
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega)) (by omega)

private theorem even_denominator_succ (d : ℕ → ℕ) (n : ℕ) :
    Even (lurothDenominator d (n + 1)) := by
  rw [even_iff_two_dvd, lurothDenominator, Finset.prod_range_succ]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.two_dvd_mul_sub_one _) _) _

private theorem convergent_numerator {x : ℝ} (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    ∃ p : ℕ, (lurothConvergent (lurothDigitSeq x) n : ℝ) =
      (p : ℝ) / lurothDenominator (lurothDigitSeq x) n := by
  let d := lurothDigitSeq x
  induction n with
  | zero => exact ⟨1, by simp [lurothConvergent]⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    let k := (d n - 1) * d (n + 1)
    have hk : lurothDenominator d (n + 1) = lurothDenominator d n * k := by
      rw [lurothDenominator_succ, mul_assoc]
    have hn : (0 : ℝ) < lurothDenominator d n := by exact_mod_cast denominator_pos hx n
    have hkpos : 0 < k := by
      dsimp [k, d]
      have := digit_ge_two hx n
      have := digit_ge_two hx (n + 1)
      exact Nat.mul_pos (by omega) (by omega)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
    refine ⟨p * k + 1, ?_⟩
    change (lurothConvergent d n : ℝ) = _ / lurothDenominator d n at hp
    change (lurothConvergent d (n + 1) : ℝ) = _ / lurothDenominator d (n + 1)
    rw [lurothConvergent_succ, Rat.cast_add, hp, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast, hk]
    push_cast
    field_simp

private theorem mem_tail_cover (ψ : ℕ → ℝ)
    (hψ : ∀ q, Even q → ψ q ≤ (1 / 2 : ℝ) ^ q) (N : ℕ) (x : ℝ)
    (hx : x ∈ lurothWellApproximableSet ψ) :
    ∃ q ≥ N, ∃ p : Fin (q + 1),
      x ∈ Set.Icc ((p : ℕ) / (q : ℝ)) ((p : ℕ) / (q : ℝ) + (1 / 2 : ℝ) ^ q) := by
  obtain ⟨n, hn, happ⟩ := frequently_atTop.mp hx.2 (max N 1)
  let q := lurothDenominator (lurothDigitSeq x) n
  have hqpos : (0 : ℝ) < q := by exact_mod_cast denominator_pos hx.1 n
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast denominator_pos hx.1 n
  have heven : Even q := by
    cases n with
    | zero => omega
    | succ n => exact even_denominator_succ _ n
  obtain ⟨p, hp⟩ := convergent_numerator hx.1 n
  have hbelow := (lurothConvergent_lt_le x hx.1 n).1
  rw [hp] at hbelow happ
  change 0 < x - (p : ℝ) / q at hbelow
  change |x - (p : ℝ) / q| < ψ q / q at happ
  have hp_le : p ≤ q := by
    have : (p : ℝ) / q ≤ 1 := (sub_pos.mp hbelow).le.trans hx.1.2
    exact_mod_cast (div_le_iff₀ hqpos).mp this |>.trans_eq (one_mul _)
  refine ⟨q, (le_max_left N 1).trans (hn.trans (index_le_denominator hx.1 n)),
    ⟨p, Nat.lt_succ_of_le hp_le⟩, (sub_pos.mp hbelow).le, ?_⟩
  rw [abs_of_pos hbelow] at happ
  have hrad : ψ q / q ≤ (1 / 2 : ℝ) ^ q :=
    (div_le_div_of_nonneg_right (hψ q heven) hqpos.le).trans
      (div_le_self (by positivity) hqone)
  exact (sub_le_iff_le_add.mp (happ.le.trans hrad)).trans_eq (add_comm _ _)

private theorem dimH_eq_zero_of_small_on_even (ψ : ℕ → ℝ)
    (hψ : ∀ q, Even q → ψ q ≤ (1 / 2 : ℝ) ^ q) :
    dimH (lurothWellApproximableSet ψ) = 0 := by
  apply bot_unique
  apply dimH_le
  intro s hs
  by_contra! hs0
  have hspos : (0 : ℝ) < s := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hs0)
  -- Cover by intervals at all denominators in a tail, with at most q + 1 intervals for q.
  let t (N : ℕ) (i : Σ k : ℕ, Fin (k + N + 1)) : Set ℝ :=
    let c : ℝ := (i.2 : ℕ) / ((i.1 + N : ℕ) : ℝ)
    Set.Icc c (c + (1 / 2 : ℝ) ^ (i.1 + N))
  let b := ENNReal.ofReal (1 / 2 : ℝ)
  have hb : b < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 (by norm_num)
  have hdiam (N : ℕ) (i : Σ k : ℕ, Fin (k + N + 1)) :
      Metric.ediam (t N i) = b ^ (i.1 + N) := by
    dsimp only [t]
    rw [Real.ediam_Icc, add_sub_cancel_left,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hcover (N : ℕ) : lurothWellApproximableSet ψ ⊆ ⋃ i, t N i := by
    intro x hx
    obtain ⟨q, hq, p, hp⟩ := mem_tail_cover ψ hψ N x hx
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hq
    exact Set.mem_iUnion.mpr ⟨⟨k, p⟩, hp⟩
  let r := (1 / 2 : ℝ) ^ (s : ℝ)
  let f (q : ℕ) : ℝ := ((q : ℝ) + 1) * r ^ q
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hspos
  have hf : Summable f := by
    simpa only [f, add_mul, one_mul, pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)).add
        (summable_geometric_of_lt_one hr0 hr1)
  have hsum (N : ℕ) :
      (∑' i, Metric.ediam (t N i) ^ (s : ℝ)) = ∑' k, ENNReal.ofReal (f (k + N)) := by
    rw [tsum_sigma']
    congr 1
    funext k
    simp only [hdiam, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← ENNReal.rpow_natCast_mul, mul_comm (↑(k + N) : ℝ), ENNReal.rpow_mul,
      ENNReal.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr0,
      ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      Nat.cast_add, Nat.cast_one]
    have hrb : b ^ (s : ℝ) = ENNReal.ofReal r :=
      ENNReal.ofReal_rpow_of_pos (by norm_num)
    rw [hrb]
  have hμ : μH[(s : ℝ)] (lurothWellApproximableSet ψ) ≤ 0 := by
    calc
      _ ≤ liminf (fun N => ∑' i, Metric.ediam (t N i) ^ (s : ℝ)) atTop :=
        Measure.hausdorffMeasure_le_liminf_tsum _ _
          (fun N => b ^ N) (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb) t
          (Eventually.of_forall fun N i => by
            rw [hdiam]
            exact pow_le_pow_right_of_le_one' hb.le (Nat.le_add_left _ _))
          (Eventually.of_forall hcover)
      _ = 0 := by
        simp only [hsum]
        exact (ENNReal.tendsto_sum_nat_add _ hf.tsum_ofReal_ne_top).liminf_eq
  exact ENNReal.top_ne_zero (le_antisymm (hs ▸ hμ) bot_le)

end exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero

/-- **Without monotonicity the Lüroth dimension can vanish.** For every real number $\tau \ge 0$
there is a function $\psi$ from the natural numbers to $(0, 1]$ such that: $\psi$ is not
non-increasing on $\{q : q \ge N\}$ for any $N$; the lower order at infinity
$\liminf_{q \to \infty} (-\log \psi(q) / \log q)$ of $1/\psi$ equals $\tau$; and the set
$L(\psi)$ of $x \in (0, 1]$ such that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely
many $n$, where $P_n(x)/Q_n(x)$ is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth
denominator, has Hausdorff dimension $0$.

Since $0 < 1/(1 + \tau)$, the Tan–Zhou conjecture fails without monotonicity.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 9. -/
public theorem exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero (τ : ℝ)
    (hτ : 0 ≤ τ) :
    ∃ ψ : ℕ → ℝ, (∀ q, 0 < ψ q ∧ ψ q ≤ 1) ∧ (¬ ∃ N, AntitoneOn ψ (Set.Ici N)) ∧
      lowerOrderAtInfinity ψ = ENNReal.ofReal τ ∧ dimH (lurothWellApproximableSet ψ) = 0 := by
  open exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero in
  refine ⟨approximationFunction τ, approximationFunction_bounds τ hτ,
    approximationFunction_not_antitone τ, approximationFunction_lowerOrder τ hτ, ?_⟩
  apply dimH_eq_zero_of_small_on_even
  intro q hq
  rw [approximationFunction, ite_eq_left hq]
  exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀
    (Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg _)) hτ))

end MetaMathlibExt
