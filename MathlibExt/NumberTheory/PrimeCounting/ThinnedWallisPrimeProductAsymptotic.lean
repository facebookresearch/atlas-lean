/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProductConstant
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Asymptotic for thinned Wallis-type prime products

Abel summation gives the limit of the prime reciprocal sum in each reduced residue class
minus its `log log x` main term. A summable logarithmic remainder gives the two class product
limits, and the Wallis factorization combines them into the thinned product asymptotic.

## References

* Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
  INTEGERS 26 (2026), Article A90, pp. 1–11, Sections 4–5, Theorems 1 and 2.
* K. S. Williams, *Mertens' Theorem for Arithmetic Progressions*, Journal of Number Theory 6
  (1974), 353–359, Theorem 1. We derive the convergence of the normalized first class product
  from the bounded weighted Mertens estimate, without using the explicit constant formula.
-/

open Filter MeasureTheory Set Topology

namespace MetaMathlibExt

open ArithmeticFunction

/-- The inclusive cutoff for primes in one residue class. -/
private noncomputable def classPrimes {q : ℕ} (a : ZMod q) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)

/-- A series over the selected primes converges along the inclusive real cutoff. -/
private lemma tendsto_sum_classPrimes {q : ℕ} (a : ZMod q) (u : ℕ → ℝ)
    (hu : Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then u n else 0)) :
    Tendsto (fun x => ∑ n ∈ classPrimes a x, u n) atTop
      (𝓝 (∑' n : ℕ, if n.Prime ∧ (n : ZMod q) = a then u n else 0)) := by
  refine (hu.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)).congr fun x => ?_
  exact (Finset.sum_filter _ _).symm

/-- The reciprocal-prime sum in a reduced residue class, centered by its main term, has a limit. -/
private lemma exists_tendsto_reciprocal_sub_log_log {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) : ∃ L : ℝ, Tendsto (fun x : ℝ =>
      (∑ p ∈ classPrimes a x, (1 : ℝ) / p) - Real.log (Real.log x) / q.totient) atTop (𝓝 L) := by
  let c (n : ℕ) : ℝ := (if n.Prime then vonMangoldt.residueClass a n else 0) / n
  let d (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt.residueClass a n) / n
  let A (t : ℝ) := ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n
  let M (t : ℝ) := Real.log t / (q.totient : ℝ)
  let E (t : ℝ) := A t - M t
  have hc0 : c 0 = 0 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c]
  have hc (n : ℕ) : 0 ≤ c n := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    split_ifs
    · exact vonMangoldt.residueClass_nonneg a n
    · exact le_rfl
  obtain ⟨B₀, hB₀⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le a ha
  let B := B₀ + ∑' n, d n
  have hB (t : ℝ) (ht : 2 ≤ t) : |E t| ≤ B := by
    have hd (n : ℕ) : 0 ≤ d n := by
      apply div_nonneg _ (Nat.cast_nonneg n)
      split_ifs
      · exact le_rfl
      · exact vonMangoldt.residueClass_nonneg a n
    have hpow := (vonMangoldt.summable_residueClass_non_primes_div a).sum_le_tsum
      (Finset.Icc 0 ⌊t⌋₊) (fun n _ => hd n)
    have hsplit : A t + ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, d n =
        ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, vonMangoldt.residueClass a n / (n : ℝ) := by
      dsimp only [A]
      rw [← Finset.sum_add_distrib, Finset.Icc_eq_cons_Ioc (Nat.zero_le _),
        Finset.sum_cons, hc0, show d 0 = 0 by simp [d], zero_add, zero_add]
      exact Finset.sum_congr rfl fun n _ => by by_cases hn : n.Prime <;> simp [c, d, hn]
    have h := abs_le.mp (hB₀ t (by linarith))
    rw [← hsplit] at h
    have hnonneg : 0 ≤ ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, d n := Finset.sum_nonneg fun n _ => hd n
    change (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, d n) ≤ ∑' n, d n at hpow
    change -B₀ ≤ A t + _ - M t ∧ A t + _ - M t ≤ B₀ at h
    rw [abs_le]
    dsimp only [E, B]
    constructor <;> linarith [h.1, h.2]
  let f (t : ℝ) : ℝ := (Real.log t)⁻¹
  let g (t : ℝ) : ℝ := -t⁻¹ / Real.log t ^ 2
  let H (t : ℝ) : ℝ := Real.log (Real.log t) / q.totient
  have htpos (t : ℝ) (ht : 2 ≤ t) : 0 < t := by linarith
  have hlog (t : ℝ) (ht : 2 ≤ t) : 0 < Real.log t := Real.log_pos (by linarith)
  have hf' (t : ℝ) (ht : 2 ≤ t) : HasDerivAt f (g t) t :=
    (Real.hasDerivAt_log (htpos t ht).ne').inv (hlog t ht).ne'
  have hf₀ : Tendsto f atTop (𝓝 0) := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hg_le (t : ℝ) (ht : 2 ≤ t) : g t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr (htpos t ht).le)) (sq_nonneg _)
  have hg : IntegrableOn g (Ioi 2) :=
    integrableOn_Ioi_deriv_of_nonpos' hf' (fun t ht => hg_le t ht.le) hf₀
  have hA : Measurable A := Monotone.measurable (fun t u htu =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htu))
      (fun n _ _ => hc n))
  have hE : Measurable E := hA.sub (Real.measurable_log.div_const _)
  have hgE : IntegrableOn (fun t => g t * E t) (Ioi 2) := by
    refine (hg.norm.const_mul B).mono' ((hg.aestronglyMeasurable).mul hE.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_eq_abs (E t), mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB t ht.le) (norm_nonneg _)
  have hboundary : Tendsto (fun t => f t * E t) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => f t * B) ?_ (by simpa using hf₀.mul_const B)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    rw [norm_mul, Real.norm_eq_abs (f t), Real.norm_eq_abs (E t),
      abs_of_nonneg (inv_nonneg.mpr (hlog t ht).le : 0 ≤ f t)]
    exact mul_le_mul_of_nonneg_left (hB t ht) (inv_nonneg.mpr (hlog t ht).le)
  have hseries : Tendsto (fun x => 1 / (q.totient : ℝ) + f x * E x -
      (∫ t in (2 : ℝ)..x, g t * E t) - H 2) atTop
      (𝓝 (1 / (q.totient : ℝ) + 0 - (∫ t in Ioi (2 : ℝ), g t * E t) - H 2)) :=
    (((tendsto_const_nhds.add hboundary).sub
      (intervalIntegral_tendsto_integral_Ioi 2 hgE tendsto_id)).sub_const _)
  refine ⟨_, hseries.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have htne (t : ℝ) (ht : t ∈ Icc 2 x) : t ≠ 0 := (htpos t ht.1).ne'
  have hlog_cont : ContinuousOn Real.log (Icc 2 x) :=
    Real.continuousOn_log.mono fun t ht => htne t ht
  have hg_cont : ContinuousOn g (Icc 2 x) :=
    ((continuous_id.continuousOn.inv₀ htne).neg.div (hlog_cont.pow 2)
      (fun t ht => pow_ne_zero _ (hlog t ht.1).ne'))
  have hderiv : EqOn (deriv f) g (Icc 2 x) := fun t ht => (hf' t ht.1).deriv
  have hab := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 x
    (fun t ht => (hf' t ht.1).differentiableAt)
    (hg_cont.integrableOn_Icc.congr_fun (fun t ht => (hderiv ht).symm) measurableSet_Icc)
  change (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * c n) = f x * A x -
    (∫ t in Ioc (2 : ℝ) x, deriv f t * A t) at hab
  have hint : (∫ t in Ioc (2 : ℝ) x, deriv f t * A t) = ∫ t in (2 : ℝ)..x, g t * A t := by
    rw [intervalIntegral.integral_of_le hx]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht =>
      congrArg (· * A t) (hderiv (Ioc_subset_Icc_self ht))
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * c n) = ∑ p ∈ classPrimes a x, (1 : ℝ) / p := by
    rw [classPrimes, Finset.sum_filter, Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime
    · have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
      by_cases ha' : (n : ZMod q) = a
      · simp only [f, c, hn, ha', and_self, ite_true, vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_ofPred_eq, vonMangoldt_apply_prime hn]
        field_simp [(hlog n hn₂).ne']
      · simp [c, hn, ha', vonMangoldt.residueClass]
    · simp [c, hn]
  have hmain_int : IntervalIntegrable (fun t => g t * M t) volume 2 x :=
    (hg_cont.mul (hlog_cont.div_const (q.totient : ℝ))).intervalIntegrable_of_Icc hx
  have herror_int : IntervalIntegrable (fun t => g t * E t) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr (hgE.mono_set Ioc_subset_Ioi_self)
  have hmain : (∫ t in (2 : ℝ)..x, g t * M t) = -H x - -H 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hmain_int
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht₀ := (htpos t ht.1).ne'
    have hl := (hlog t ht.1).ne'
    have hH : HasDerivAt H ((Real.log t)⁻¹ * t⁻¹ / (q.totient : ℝ)) t :=
      ((Real.hasDerivAt_log hl).comp t (Real.hasDerivAt_log ht₀)).div_const _
    have heq : g t * M t = -((Real.log t)⁻¹ * t⁻¹ / (q.totient : ℝ)) := by
      dsimp only [g, M]
      field_simp [hl]
    rw [heq]
    exact hH.neg
  have hsplit : (∫ t in (2 : ℝ)..x, g t * A t) =
      (∫ t in (2 : ℝ)..x, g t * M t) + ∫ t in (2 : ℝ)..x, g t * E t := by
    rw [← intervalIntegral.integral_add hmain_int herror_int]
    congr 1
    funext t
    dsimp [E]
    ring
  have hprod : f x * A x = 1 / (q.totient : ℝ) + f x * E x := by
    dsimp [f, E, M]
    field_simp [(hlog x hx).ne']
    ring
  rw [hsum, hint, hsplit, hmain, hprod] at hab
  change _ = (∑ p ∈ classPrimes a x, (1 : ℝ) / p) - H x
  linarith

/-- When `u` is small, the difference between `log (1 - u)` and `-u` is quadratic. -/
private lemma abs_log_one_sub_add_le {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  have hu₁ : u < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := u) (by simpa [abs_of_nonneg hu] using hu₁) 1
  have h' : |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - u) := by
    simpa [Finset.sum_range_one, abs_of_nonneg hu, add_comm] using h
  refine h'.trans ((div_le_iff₀ (sub_pos.mpr hu₁)).mpr ?_)
  nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1 - 2 * u by linarith)]

/-- Exponentiating the centered linear sum and the logarithmic remainder gives a positive
limit for the normalized class product. -/
private lemma exists_pos_tendsto_class_product {q : ℕ} (a : ZMod q) (u : ℕ → ℝ) (b : ℝ → ℝ)
    (hu : ∀ p : ℕ, p.Prime → 0 ≤ u p ∧ u p ≤ 1 / (p : ℝ)) {L : ℝ}
    (hL : Tendsto (fun x => b x - ∑ p ∈ classPrimes a x, u p) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun x =>
      Real.exp (b x) * ∏ p ∈ classPrimes a x, (1 - u p)) atTop (𝓝 C) := by
  let e (p : ℕ) : ℝ := Real.log (1 - u p) + u p
  have hu₂ (p : ℕ) (hp : p.Prime) : u p ≤ 1 / 2 :=
    (hu p hp).2.trans
      (div_le_div_of_nonneg_left zero_le_one (by norm_num) (by exact_mod_cast hp.two_le))
  have he : Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod q) = a then e p else 0) := by
    refine Summable.of_norm_bounded
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs]
    split_ifs with hp
    · calc |e p| ≤ 2 * u p ^ 2 := abs_log_one_sub_add_le (hu p hp.1).1 (hu₂ p hp.1)
        _ ≤ 2 * (1 / (p : ℝ)) ^ 2 := by
          gcongr <;> first | exact (hu p hp.1).1 | exact (hu p hp.1).2
        _ = 2 * (1 / (p : ℝ) ^ 2) := by rw [div_pow, one_pow]
    · rw [abs_zero]
      positivity
  refine ⟨_, Real.exp_pos _, ((hL.add (tendsto_sum_classPrimes a e he)).rexp).congr fun x => ?_⟩
  have hexp : Real.exp (∑ p ∈ classPrimes a x, Real.log (1 - u p)) =
      ∏ p ∈ classPrimes a x, (1 - u p) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp => Real.exp_log ?_
    exact sub_pos.mpr ((hu₂ p (Finset.mem_filter.mp hp).2.1).trans_lt (by norm_num))
  rw [← hexp, ← Real.exp_add]
  congr 1
  simp only [e, Finset.sum_add_distrib]
  ring

/-- The normalized first Mertens product converges to a positive constant. -/
private lemma exists_pos_tendsto_first_product {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun x : ℝ =>
      Real.log x ^ (1 / (q.totient : ℝ)) * ∏ p ∈ classPrimes a x, (1 - 1 / (p : ℝ)))
      atTop (𝓝 C) := by
  obtain ⟨L, hL⟩ := exists_tendsto_reciprocal_sub_log_log ha
  have hmain : Tendsto (fun x => Real.log (Real.log x) / (q.totient : ℝ) -
      ∑ p ∈ classPrimes a x, (1 : ℝ) / p) atTop (𝓝 (-L)) := by
    simpa only [neg_sub] using hL.neg
  obtain ⟨C, hCpos, hC⟩ := exists_pos_tendsto_class_product a (fun p => (1 : ℝ) / p)
    (fun x => Real.log (Real.log x) / q.totient) (fun p _ => ⟨by positivity, le_rfl⟩) hmain
  refine ⟨C, hCpos, hC.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  simp only [Real.rpow_def_of_pos (Real.log_pos (by linarith : 1 < x)), div_eq_mul_inv, one_mul]

/-- The second class product converges to a positive constant without normalization. -/
private lemma exists_pos_tendsto_second_product {q : ℕ} (a : ZMod q) :
    ∃ D : ℝ, 0 < D ∧ Tendsto (fun x : ℝ => ∏ p ∈ classPrimes a x, (1 - 1 / (p : ℝ) ^ 2))
      atTop (𝓝 D) := by
  let u (p : ℕ) : ℝ := 1 / (p : ℝ) ^ 2
  have hu : Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod q) = a then u p else 0) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    · split_ifs
      · change 0 ≤ (1 : ℝ) / (p : ℝ) ^ 2
        positivity
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · positivity
  have hmain : Tendsto (fun x => 0 - ∑ p ∈ classPrimes a x, u p) atTop (𝓝 _) :=
    (tendsto_sum_classPrimes a u hu).const_sub 0
  obtain ⟨D, hDpos, hD⟩ := exists_pos_tendsto_class_product a u (fun _ => 0) (fun p hp => by
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    refine ⟨by dsimp [u]; positivity, ?_⟩
    dsimp [u]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)) hmain
  exact ⟨D, hDpos, by simpa only [Real.exp_zero, one_mul, u] using hD⟩

/-- **Asymptotic for thinned Wallis-type prime products.** Let $m \ge 2$, let $q = 2^m$, and let
$S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's totient function and
$\chi_4$ the nontrivial Dirichlet character modulo $4$, put $\mu(S) = \sum_{a \in S} \chi_4(a)$,
where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$ modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Then there is a real number $K > 0$ such that
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 1 (`integers-2026-A90-thm-1`). -/
public theorem thinned_wallis_prime_product_asymptotic
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun x : ℝ =>
          (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
            (K * Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
        atTop (𝓝 1) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by decide)⟩
  choose! C hCpos hC using fun a (ha : a ∈ S) => exists_pos_tendsto_first_product (hS a ha)
  choose D hDpos hD using fun a : ZMod (2 ^ m) => exists_pos_tendsto_second_product a
  refine ⟨∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ (a.val : ZMod 4), ?_, ?_⟩
  · exact Finset.prod_pos fun a ha => zpow_pos (div_pos (sq_pos_of_pos (hCpos a ha)) (hDpos a)) _
  · exact (thinned_wallis_prime_product_constant m hm S hS C D hC (fun a _ => hD a)).1

end MetaMathlibExt
