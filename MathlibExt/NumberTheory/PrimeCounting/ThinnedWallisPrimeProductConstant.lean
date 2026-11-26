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
import Mathlib.NumberTheory.AbelSummation
import MathlibExt.NumberTheory.PrimeCounting.WallisPrimeFactor
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# The constant in the thinned Wallis-type prime product asymptotic

A one-sided bound for prime reciprocals, obtained by Abel summation from the bounded
error in the weighted Mertens estimate, ensures that the assumed normalized class limits
are positive. The Wallis factor identity then gives the constant by multiplication over
the selected residue classes.
-/

open Filter Topology

namespace MetaMathlibExt

open ArithmeticFunction MeasureTheory

/-- The weighted Mertens bound gives the requisite upper bound for the reciprocal sum after
partial summation with `1 / log t`. -/
private lemma exists_prime_reciprocal_sum_le {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ B : ℝ, ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
        (1 : ℝ) / p) ≤ Real.log (Real.log x) / q.totient + B := by
  obtain ⟨B, hB⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le a ha
  let c (n : ℕ) := vonMangoldt.residueClass a n / (n : ℝ)
  let A (t : ℝ) := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  let f (t : ℝ) := (Real.log t)⁻¹
  let F (t : ℝ) := B * f t - Real.log (Real.log t) / (q.totient : ℝ)
  have hc0 : c 0 = 0 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c, vonMangoldt.residueClass]
  have hA (t : ℝ) (ht : 1 ≤ t) : A t ≤ Real.log t / q.totient + B := by
    have h := (abs_le.mp (hB t ht)).2
    dsimp only [A]
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, zero_add]
    exact sub_le_iff_le_add'.mp h
  have hlog (t : ℝ) (ht : 2 ≤ t) : 0 < Real.log t := Real.log_pos (by linarith)
  have hderiv (t : ℝ) (ht : 2 ≤ t) : HasDerivAt f (-(t⁻¹) / Real.log t ^ 2) t :=
    (Real.hasDerivAt_log (by linarith)).inv (hlog t ht).ne'
  refine ⟨1 / (q.totient : ℝ) + F 2, fun x hx => ?_⟩
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 2 x) : DifferentiableAt ℝ f t :=
    (hderiv t ht.1).differentiableAt
  have hlogc : ContinuousOn Real.log (Set.Icc 2 x) :=
    Real.continuousOn_log.mono fun t ht => by
      have := ht.1
      simpa using (show t ≠ 0 by linarith)
  have hfc : ContinuousOn (deriv f) (Set.Icc 2 x) := by
    refine ((continuous_id.continuousOn.inv₀ (fun t ht => ?_)).neg.div (hlogc.pow 2)
      (fun t ht => pow_ne_zero _ (hlog t ht.1).ne')).congr (fun t ht => (hderiv t ht.1).deriv)
    have := ht.1
    exact (show t ≠ 0 by linarith)
  have hfi : IntegrableOn (deriv f) (Set.Icc 2 x) := hfc.integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 x hdiff hfi
  have hIntA : IntervalIntegrable (fun t => deriv f t * A t) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_mul_sum_Icc c (by norm_num) hfi)
  have hIntF : IntervalIntegrable (fun t => deriv f t * (Real.log t / q.totient + B))
      volume 2 x :=
    ((hfc.mul ((hlogc.div_const _).add continuousOn_const)).intervalIntegrable_of_Icc hx)
  have hFTC : (∫ t in (2 : ℝ)..x, deriv f t * (Real.log t / q.totient + B)) = F x - F 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hIntF
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by have := ht.1; linarith
    have hl := hlog t ht.1
    have h : HasDerivAt F
        (B * (-(t⁻¹) / Real.log t ^ 2) - (Real.log t)⁻¹ * t⁻¹ / q.totient) t :=
      ((hderiv t ht.1).const_mul B).sub
        (((Real.hasDerivAt_log hl.ne').comp t (Real.hasDerivAt_log ht0)).div_const (q.totient : ℝ))
    convert h using 1
    rw [(hderiv t ht.1).deriv]
    field_simp [ht0, hl.ne']
    ring
  have hInt : F x - F 2 ≤ ∫ t in (2 : ℝ)..x, deriv f t * A t := by
    rw [← hFTC]
    apply intervalIntegral.integral_mono_on hx hIntF hIntA
    intro t ht
    apply mul_le_mul_of_nonpos_left (hA t (by have := ht.1; linarith))
    rw [(hderiv t ht.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by have := ht.1; positivity))
      (sq_nonneg _)
  have hf_nonneg (n : ℕ) : 0 ≤ f n := inv_nonneg.mpr (Real.log_natCast_nonneg n)
  have hsum : ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), (1 : ℝ) / p ≤
      ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, f k * c k := by
    calc
      _ = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), f p * c p := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨hprime, hclass⟩ := (Finset.mem_filter.mp hp).2
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
        simp only [f, c, vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
          hclass, ite_true, vonMangoldt_apply_prime hprime]
        field_simp [(hlog p hp2).ne']
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simpa only [Finset.mem_Icc, zero_le, true_and, ← Nat.lt_succ_iff] using
            Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        · intro n _ _
          exact mul_nonneg (hf_nonneg n) (div_nonneg (vonMangoldt.residueClass_nonneg a n)
            (Nat.cast_nonneg _))
  rw [hab, ← intervalIntegral.integral_of_le hx] at hsum
  change _ ≤ f x * A x - _ at hsum
  have hmain := mul_le_mul_of_nonneg_left (hA x (by linarith)) (inv_nonneg.mpr (hlog x hx).le)
  have hnorm : f x * (Real.log x / (q.totient : ℝ) + B) - F x =
      1 / (q.totient : ℝ) + Real.log (Real.log x) / q.totient := by
    dsimp [F, f]
    field_simp [(hlog x hx).ne']
    ring
  linarith

/-- A lower bound for the logarithm of a factor close to `1`. -/
private lemma log_one_sub_lower {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    -u - 2 * u ^ 2 ≤ Real.log (1 - u) := by
  have hu1 : u < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := u) (by simpa [abs_of_nonneg hu] using hu1) 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, abs_of_nonneg hu] at h
  change |u + Real.log (1 - u)| ≤ u ^ 2 / (1 - u) at h
  have hle : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr hu1)]
    calc
      u ^ 2 = u ^ 2 * 1 := by rw [mul_one]
      _ ≤ u ^ 2 * (2 * (1 - u)) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = _ := by ring
  linarith [(abs_le.mp (h.trans hle)).1]

private lemma prime_factor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) ∧ 0 < 1 - 1 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  exact ⟨sub_pos.mpr ((div_lt_one hp0).2 (by linarith)),
    sub_pos.mpr ((div_lt_one (sq_pos_of_pos hp0)).2 (by nlinarith))⟩

/-- Any limit of the normalized first-power product over a reduced class is positive. -/
private lemma class_first_limit_pos {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {C : ℝ}
    (hC : Tendsto (fun x : ℝ => Real.log x ^ (1 / (q.totient : ℝ)) *
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), (1 - 1 / (p : ℝ))) atTop (𝓝 C)) :
    0 < C := by
  obtain ⟨B, hB⟩ := exists_prime_reciprocal_sum_le ha
  let U : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2
  refine (Real.exp_pos (-B - 2 * U)).trans_le (ge_of_tendsto hC ?_)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  let s := (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hw : 0 < Real.log x ^ (1 / (q.totient : ℝ)) := Real.rpow_pos_of_pos hlog _
  have hpos : 0 < ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
    Finset.prod_pos fun p hp => (prime_factor_pos (hprime p hp)).1
  have hsum : ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2 ≤ U :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).sum_le_tsum s (fun n _ => by positivity)
  have hlogs : ∑ p ∈ s, (-((1 : ℝ) / p) - 2 * (1 / (p : ℝ) ^ 2)) ≤
      ∑ p ∈ s, Real.log (1 - 1 / (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have h := log_one_sub_lower (u := 1 / (p : ℝ)) (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2)
    rwa [div_pow, one_pow] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hlogs
  change Real.exp (-B - 2 * U) ≤ _ * ∏ p ∈ s, (1 - 1 / (p : ℝ))
  rw [← Real.exp_log (mul_pos hw hpos), Real.exp_le_exp, Real.log_mul hw.ne' hpos.ne',
    Real.log_rpow hlog, Real.log_prod fun p hp => (prime_factor_pos (hprime p hp)).1.ne']
  have hrecip := hB x hx
  change ∑ p ∈ s, (1 : ℝ) / p ≤ _ at hrecip
  linarith [show 1 / (q.totient : ℝ) * Real.log (Real.log x) =
    Real.log (Real.log x) / (q.totient : ℝ) by ring]

/-- Any limit of the second-power product over a class is positive, by summability of `1 / p^2`. -/
private lemma class_second_limit_pos {q : ℕ} {a : ZMod q} {D : ℝ}
    (hD : Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
          (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), (1 - 1 / (p : ℝ) ^ 2)) atTop (𝓝 D)) :
    0 < D := by
  let U : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2
  refine (Real.exp_pos (-2 * U)).trans_le (ge_of_tendsto hD (Eventually.of_forall fun x => ?_))
  let s := (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpos : 0 < ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) :=
    Finset.prod_pos fun p hp => (prime_factor_pos (hprime p hp)).2
  have hsum : ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2 ≤ U :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).sum_le_tsum s (fun n _ => by positivity)
  have hlogs : ∑ p ∈ s, -2 * (1 / (p : ℝ) ^ 2) ≤
      ∑ p ∈ s, Real.log (1 - 1 / (p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    let u : ℝ := 1 / (p : ℝ) ^ 2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hu : 0 ≤ u := by positivity
    have hu' : u ≤ 1 / 2 := by
      dsimp [u]
      rw [div_le_div_iff₀ (show (0 : ℝ) < (p : ℝ) ^ 2 by nlinarith) (by norm_num)]
      nlinarith
    have := log_one_sub_lower hu hu'
    change -2 * u ≤ Real.log (1 - u)
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu')]
  rw [← Finset.mul_sum] at hlogs
  change Real.exp (-2 * U) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)
  rw [← Real.exp_log hpos, Real.exp_le_exp,
    Real.log_prod fun p hp => (prime_factor_pos (hprime p hp)).2.ne']
  linarith

/-- The character of a residue class modulo `2 ^ m` is read modulo `4`. -/
private lemma chi4_class_eq {m p : ℕ} (hm : 2 ≤ m) {a : ZMod (2 ^ m)}
    (h : (p : ZMod (2 ^ m)) = a) : ZMod.χ₄ (p : ZMod 4) = ZMod.χ₄ (a.val : ZMod 4) := by
  subst a
  have h4 : 4 ∣ 2 ^ m := pow_dvd_pow 2 hm
  rw [ZMod.val_natCast, (ZMod.natCast_eq_natCast_iff' _ _ 4).mpr (Nat.mod_mod_of_dvd p h4)]

/-- Each Wallis factor is a fixed integer power of the ratio of the two Mertens factors. -/
private lemma wallis_factor_eq_zpow {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) =
      (((1 - 1 / (p : ℝ)) ^ 2) / (1 - 1 / (p : ℝ) ^ 2)) ^ ZMod.χ₄ (p : ZMod 4) := by
  rw [wallis_prime_factor_eq p hp hodd]
  have h2 : p % 2 ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right h2]
  split_ifs
  · simp
  · simp only [Int.cast_neg, Int.cast_one, zpow_neg_one]
    have hM := prime_factor_pos hp
    have he : (1 + 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) = 1 - 1 / (p : ℝ) ^ 2 := by
      field_simp [hp0]
      ring
    rw [← he]
    have hplus : 1 + 1 / (p : ℝ) ≠ 0 := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    rw [neg_div, sub_neg_eq_add]
    field_simp [hM.1.ne', hplus]

/-- **The constant in the thinned Wallis-type prime product asymptotic.** Let $m \ge 2$, let
$q = 2^m$, and let $S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\varphi$ be Euler's
totient function and $\chi_4$ the nontrivial Dirichlet character modulo $4$, put
$\mu(S) = \sum_{a \in S} \chi_4(a)$, where $\chi_4(a)$ means $\chi_4$ of the reduction of $a$
modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Suppose that $C(a)$ and $D(a)$, for $a \in S$, are real
numbers with
$$C(a) = \lim_{x \to \infty} (\log x)^{1/\varphi(q)} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p),$$
$$D(a) = \lim_{x \to \infty} \prod_{p \le x,\ p \equiv a \ (q)} (1 - 1/p^2),$$
the products running over primes $p$. Put
$K = \prod_{a \in S} \left(C(a)^2 / D(a)\right)^{\chi_4(a)}$. Then
$P_S(x) / \left(K (\log x)^{-2\mu(S)/\varphi(q)}\right) \to 1$ as $x \to \infty$, and if
$\mu(S) = 0$ then $P_S(x) \to K$ as $x \to \infty$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Theorem 2 (`integers-2026-A90-thm-2`). -/
public theorem thinned_wallis_prime_product_constant
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a)
    (C D : ZMod (2 ^ m) → ℝ)
    (hC : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        Real.log x ^ (1 / (Nat.totient (2 ^ m) : ℝ)) *
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ)))
        atTop (𝓝 (C a)))
    (hD : ∀ a ∈ S, Tendsto (fun x : ℝ =>
        ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a), (1 - 1 / (p : ℝ) ^ 2))
        atTop (𝓝 (D a))) :
    Tendsto (fun x : ℝ =>
        (∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
          ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) /
          ((∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4)) *
            Real.log x ^
              (-2 * ((∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) /
                (Nat.totient (2 ^ m) : ℝ))))
      atTop (𝓝 1) ∧
    (∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0 →
      Tendsto (fun x : ℝ =>
          ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
              (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
            ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
        atTop (𝓝 (∏ a ∈ S, (C a ^ 2 / D a) ^ ZMod.χ₄ ((a.val : ℕ) : ZMod 4)))) := by
  let s (a : ZMod (2 ^ m)) (x : ℝ) := (Finset.range (⌊x⌋₊ + 1)).filter
    (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a)
  let B (a : ZMod (2 ^ m)) (x : ℝ) := ∏ p ∈ s a x, (1 - 1 / (p : ℝ))
  let E (a : ZMod (2 ^ m)) (x : ℝ) := ∏ p ∈ s a x, (1 - 1 / (p : ℝ) ^ 2)
  let χ (a : ZMod (2 ^ m)) : ℤ := ZMod.χ₄ (a.val : ZMod 4)
  let μ : ℤ := ∑ a ∈ S, χ a
  let φ : ℝ := Nat.totient (2 ^ m)
  let P (x : ℝ) := ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
      (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))
  let L (x : ℝ) := Real.log x ^ (1 / φ)
  let T (x : ℝ) := ∏ a ∈ S, ((L x * B a x) ^ 2 / E a x) ^ χ a
  let K : ℝ := ∏ a ∈ S, (C a ^ 2 / D a) ^ χ a
  change Tendsto (fun x => P x / (K * Real.log x ^ (-2 * (μ : ℝ) / φ))) atTop (𝓝 1) ∧
    (μ = 0 → Tendsto P atTop (𝓝 K))
  have hCpos (a : ZMod (2 ^ m)) (ha : a ∈ S) : 0 < C a :=
    class_first_limit_pos (hS a ha) (hC a ha)
  have hDpos (a : ZMod (2 ^ m)) (ha : a ∈ S) : 0 < D a := class_second_limit_pos (hD a ha)
  have hbase (a : ZMod (2 ^ m)) (ha : a ∈ S) : 0 < C a ^ 2 / D a :=
    div_pos (sq_pos_of_pos (hCpos a ha)) (hDpos a ha)
  have hK : 0 < K := Finset.prod_pos fun a ha => zpow_pos (hbase a ha) _
  have hT : Tendsto T atTop (𝓝 K) :=
    tendsto_finsetProd S fun a ha =>
      ((((hC a ha).pow 2).div (hD a ha) (hDpos a ha).ne').zpow₀ (χ a) (Or.inl (hbase a ha).ne'))
  -- Split the prime product into its fibers under reduction modulo `2 ^ m`.
  have hGroup (x : ℝ) : P x = ∏ a ∈ S, (B a x ^ 2 / E a x) ^ χ a := by
    dsimp only [P]
    rw [← Finset.prod_fiberwise_of_maps_to (t := S) (g := fun p : ℕ => (p : ZMod (2 ^ m)))
      (fun p hp => (Finset.mem_filter.mp hp).2.2)]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Finset.filter_filter]
    have hfilter : ((Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ =>
        (p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S) ∧ (p : ZMod (2 ^ m)) = a)) = s a x := by
      apply Finset.filter_congr
      intro p _
      constructor
      · rintro ⟨⟨hp, _⟩, h⟩
        exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩
        exact ⟨⟨hp, h ▸ ha⟩, h⟩
    rw [hfilter]
    dsimp only [B, E]
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨hprime, hclass⟩ := (Finset.mem_filter.mp hp).2
    have hunit : IsUnit (p : ZMod (2 ^ m)) := hclass ▸ hS a ha
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)] at hunit
    rw [wallis_factor_eq_zpow hprime hunit.odd_of_right, chi4_class_eq hm hclass]
  -- Collect the class normalizations into a single real power of `log x`.
  have hnorm (x : ℝ) (hx : 0 < Real.log x) : T x = P x * Real.log x ^ (2 * (μ : ℝ) / φ) := by
    have hpow : L x ^ 2 = Real.log x ^ (2 / φ) := by
      rw [show (2 : ℝ) / φ = (1 / φ) * (2 : ℕ) by push_cast; ring,
        Real.rpow_mul_natCast hx.le]
    have hCollect : (∏ a ∈ S, (L x ^ 2) ^ χ a) = Real.log x ^ (2 * (μ : ℝ) / φ) := by
      simp_rw [hpow, ← Real.rpow_mul_intCast hx.le]
      rw [← Real.rpow_sum_of_pos hx, ← Finset.mul_sum, ← Int.cast_sum]
      congr 1
      ring
    rw [hGroup, ← hCollect, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← mul_zpow]
    congr 1
    ring
  have hlarge : ∀ᶠ x : ℝ in atTop, 0 < Real.log x :=
    (eventually_gt_atTop (1 : ℝ)).mono fun _ hx => Real.log_pos hx
  constructor
  · have hratio := hT.div_const K
    rw [div_self hK.ne'] at hratio
    apply hratio.congr'
    filter_upwards [hlarge] with x hx
    rw [hnorm x hx, show -2 * (μ : ℝ) / φ = -(2 * (μ : ℝ) / φ) by ring,
      Real.rpow_neg hx.le, div_mul_eq_div_div, div_inv_eq_mul]
    ring
  · intro hμ
    apply hT.congr'
    filter_upwards [hlarge] with x hx
    simpa [hμ] using hnorm x hx

end MetaMathlibExt
