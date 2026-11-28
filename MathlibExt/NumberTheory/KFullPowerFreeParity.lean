/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.KFull
public import MathlibExt.NumberTheory.PowerFree
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Data.Set.Card
import MathlibExt.NumberTheory.ArithmeticFunction.PrimePowerValues

/-!
# Parity of `k`-full, `l`-free numbers

The indicator of odd `k`-full, `l`-free numbers is the Dirichlet convolution of the odd `k`th-power
indicator with a correction whose first possible nonconstant term at a prime has degree `k + 1`.
The odd count is the summatory function of this indicator. The weighted sum of the correction
converges absolutely and equals a positive Euler product.

For the even count, we group by the exact exponent of two as in Srisopha and Srichan (2024, §2,
equation (7)), generalizing Srichan's exact-exponent bijection (2020, §2, equation (7)).
The weight and factorization helpers and the odd-counting bijection and floor-limit proofs
are adapted from `MathlibExt.NumberTheory.KFullParity`.

## References

* Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of Numbers That Are
  Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, pp. 1–7, Theorem 1 and §2,
  equation (7). <https://math.colgate.edu/~integers/y106/y106.pdf>
* Teerapat Srichan, *The Odd/Even Dichotomy for the Set of Square-Full Numbers*, Applied Mathematics
  E-Notes 20 (2020), pp. 528–531, §2, equation (7).
  <https://tea.ntue.edu.tw/~amen/2020/AMEN-200219.pdf>
-/

namespace MetaMathlibExt

open Filter Topology

namespace KFullPowerFreeParity

private def counted (k l : ℕ) (P : ℕ → Prop) (x : ℝ) : Set ℕ :=
  {n | (n : ℝ) ≤ x ^ k ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧ P n}

private noncomputable def count (k l : ℕ) (P : ℕ → Prop) (x : ℝ) : ℝ :=
  (counted k l P x).ncard

private lemma counted_finite (k l : ℕ) (P : ℕ → Prop) {x : ℝ} (hx : 0 ≤ x) :
    (counted k l P x).Finite :=
  (Set.finite_Iic ⌊x ^ k⌋₊).subset fun _ hn => (Nat.le_floor_iff (pow_nonneg hx k)).2 hn.1

private noncomputable def weight (k n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / (k : ℝ)))

private lemma weight_pos {k n : ℕ} (hn : n ≠ 0) : 0 < weight k n := by
  unfold weight
  positivity

private lemma weight_nonneg (k n : ℕ) : 0 ≤ weight k n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private lemma weight_mul (k a b : ℕ) : weight k (a * b) = weight k a * weight k b := by
  simp only [weight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private lemma weight_pow (k a e : ℕ) : weight k (a ^ e) = (weight k a) ^ e := by
  rw [weight, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm,
    Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  rfl

private lemma weight_pow_k {k b : ℕ} (hk : 0 < k) :
    (weight k b) ^ k = (b : ℝ)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  rw [weight, ← Real.rpow_mul_natCast (Nat.cast_nonneg _), neg_mul,
    one_div_mul_cancel hk', Real.rpow_neg_one]

private lemma le_scale_iff {k b : ℕ} (hk : 0 < k) (hb : b ≠ 0) {x : ℝ} (hx : 0 ≤ x)
    {y : ℝ} (hy : 0 ≤ y) :
    y ^ k * (b : ℝ) ≤ x ^ k ↔ y ≤ x * weight k b := by
  have hb' : (0 : ℝ) < (b : ℝ) := by positivity
  rw [← le_div_iff₀ hb', ← pow_le_pow_iff_left₀ hy
    (mul_nonneg hx (weight_pos (k := k) hb).le) hk.ne', mul_pow, weight_pow_k hk, div_eq_mul_inv]

private lemma odd_ne_zero {n : ℕ} (hn : Odd n) : n ≠ 0 := by
  rintro rfl
  simp at hn

private lemma two_factorization {e m : ℕ} (hm : Odd m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm' : ¬ 2 ∣ m := fun h => Nat.not_even_iff_odd.mpr hm (even_iff_two_dvd.mpr h)
  rw [Nat.factorization_mul (by positivity) (odd_ne_zero hm), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm', add_zero]

private lemma full_two_pow_mul {k e m : ℕ} (hke : k ≤ e) (hm : Nat.IsKFull k m) :
    Nat.IsKFull k (2 ^ e * m) := by
  refine ⟨mul_ne_zero (by positivity) hm.1, fun p hp hd => ?_⟩
  rcases eq_or_ne p 2 with rfl | hne
  · exact (pow_dvd_pow 2 hke).trans (dvd_mul_right ..)
  · have hpm : p ∣ m := (hp.dvd_mul.mp hd).resolve_left fun h => hne
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp (hp.dvd_of_dvd_pow h))
    exact (hm.2 p hp hpm).trans (dvd_mul_left ..)

private lemma free_two_pow_mul {l e m : ℕ} (hel : e < l) (hm : m.IsPowerFree l) (ho : Odd m) :
    (2 ^ e * m).IsPowerFree l := by
  have hn : 0 < 2 ^ e * m := Nat.mul_pos (by positivity) hm.pos
  refine ⟨hm.two_le, hn, fun p hp hd => ?_⟩
  rcases eq_or_ne p 2 with rfl | hne
  · have h := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hd
    rw [two_factorization ho] at h
    omega
  · have hc := ((Nat.coprime_primes hp Nat.prime_two).mpr hne).pow l e
    exact hm.not_dvd hp (hc.dvd_of_dvd_mul_left hd)

private lemma full_ordCompl {k n : ℕ} (hn : Nat.IsKFull k n) :
    Nat.IsKFull k (ordCompl[2] n) := by
  apply (Nat.isKFull_iff_factorization (Nat.ordCompl_pos 2 hn.1).ne').mpr
  intro p hp hd
  have hne : p ≠ 2 := fun h => Nat.not_dvd_ordCompl Nat.prime_two hn.1 (h ▸ hd)
  rw [Nat.factorization_ordCompl, Finsupp.erase_ne hne]
  exact (Nat.isKFull_iff_factorization hn.1).mp hn p hp (hd.trans (Nat.ordCompl_dvd n 2))

private lemma even_count {k l : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) :
    count k l Even x = ∑ e ∈ Finset.Ico k l, count k l Odd (x * weight k (2 ^ e)) := by
  classical
  let S (e : ℕ) := counted k l Odd (x * weight k (2 ^ e))
  let f (p : Σ _ : ℕ, ℕ) := 2 ^ p.1 * p.2
  let s := (Finset.Ico k l).sigma (fun e =>
    (counted_finite k l Odd (mul_nonneg hx (weight_nonneg k (2 ^ e)))).toFinset)
  have hs (e m : ℕ) : (⟨e, m⟩ : Σ _ : ℕ, ℕ) ∈ s ↔ e ∈ Finset.Ico k l ∧ m ∈ S e := by
    simp [s, S]
  have hle (e m : ℕ) : (f ⟨e, m⟩ : ℝ) ≤ x ^ k ↔
      (m : ℝ) ≤ (x * weight k (2 ^ e)) ^ k := by
    have hpos : (0 : ℝ) < ((2 ^ e : ℕ) : ℝ) := by positivity
    simp only [f, Nat.cast_mul, mul_pow, weight_pow_k hk]
    rw [mul_comm (((2 ^ e : ℕ) : ℝ)), ← le_div_iff₀ hpos, div_eq_mul_inv]
  have h : Set.BijOn f (s : Set (Σ _ : ℕ, ℕ)) (counted k l Even x) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨e, m⟩ hmem
      obtain ⟨he, hm, hfull, hfree, ho⟩ := (hs _ _).mp hmem
      obtain ⟨hke, hel⟩ := Finset.mem_Ico.mp he
      refine ⟨(hle e m).2 hm, full_two_pow_mul hke hfull, free_two_pow_mul hel hfree ho, ?_⟩
      exact even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega : e ≠ 0)).trans (dvd_mul_right ..))
    · rintro ⟨e, a⟩ hea ⟨j, b⟩ hjb hab
      have ha := ((hs _ _).mp hea).2.2.2.2
      have hb := ((hs _ _).mp hjb).2.2.2.2
      have hval := congrArg (fun n : ℕ => n.factorization 2) hab
      change (2 ^ e * a).factorization 2 = (2 ^ j * b).factorization 2 at hval
      rw [two_factorization ha, two_factorization hb] at hval
      subst j
      have heq : a = b := Nat.eq_of_mul_eq_mul_left (by positivity) hab
      subst b
      rfl
    · rintro n ⟨hn, hfull, hfree, heven⟩
      let e := n.factorization 2
      let m := ordCompl[2] n
      have hke : k ≤ e :=
        (Nat.isKFull_iff_factorization hfull.1).mp hfull 2 Nat.prime_two (even_iff_two_dvd.mp heven)
      have hel : e < l := lt_of_not_ge fun h => hfree.not_dvd Nat.prime_two
        ((Nat.prime_two.pow_dvd_iff_le_factorization hfull.1).mpr h)
      have hfm : f ⟨e, m⟩ = n := Nat.ordProj_mul_ordCompl_eq_self n 2
      refine ⟨⟨e, m⟩, (hs _ _).mpr ⟨Finset.mem_Ico.mpr ⟨hke, hel⟩,
        (hle e m).1 (hfm ▸ hn), full_ordCompl hfull,
        hfree.of_dvd (Nat.ordCompl_dvd n 2), ?_⟩, hfm⟩
      exact Nat.not_even_iff_odd.mp fun hm =>
        Nat.not_dvd_ordCompl Nat.prime_two hfull.1 (even_iff_two_dvd.mp hm)
  rw [count, ← h.ncard_eq, Set.ncard_coe_finset, Finset.card_sigma, Nat.cast_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [count, Set.ncard_eq_toFinset_card _
    (counted_finite k l Odd (mul_nonneg hx (weight_nonneg k _)))]

private lemma tendsto_even_count {k l : ℕ} (hk : 0 < k) {c : ℝ}
    (ho : Tendsto (fun x => count k l Odd x / x) atTop (𝓝 c)) :
    Tendsto (fun x => count k l Even x / x) atTop
      (𝓝 (c * ∑ e ∈ Finset.Ico k l, weight k (2 ^ e))) := by
  let w (e : ℕ) := weight k (2 ^ e)
  have hw (e : ℕ) : 0 < w e := weight_pos (by positivity)
  have hlim (e : ℕ) : Tendsto (fun x => count k l Odd (x * w e) / x) atTop (𝓝 (c * w e)) := by
    have h := ho.comp (tendsto_id.atTop_mul_const (hw e))
    exact (h.mul_const (w e)).congr fun x => by
      simp only [Function.comp_apply, id_eq, div_mul_eq_div_div, div_mul_cancel₀ _ (hw e).ne']
  rw [Finset.mul_sum]
  refine (tendsto_finsetSum _ (fun e _ => hlim e)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [even_count hk hx, Finset.sum_div]

private lemma weight_sum {k l : ℕ} (hk : 0 < k) (hkl : k < l) :
    (∑ e ∈ Finset.Ico k l, weight k (2 ^ e))⁻¹ =
      (2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ))) / (1 - (2 : ℝ) ^ (1 - (l : ℝ) / k)) := by
  let q := weight k 2
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_lt_zero.mpr (one_div_pos.mpr hk'))
  have hqk : q ^ k = 2⁻¹ := weight_pow_k hk
  have hs : (∑ e ∈ Finset.Ico k l, weight k (2 ^ e)) * (1 - q) = q ^ k - q ^ l := by
    simp only [weight_pow, ← show q = weight k 2 from rfl]
    rw [Finset.sum_mul]
    calc
      _ = ∑ e ∈ Finset.Ico k l, (q ^ e - q ^ (e + 1)) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [pow_succ]
        ring
      _ = _ := by
        have h := Finset.sum_Ico_sub (fun e => q ^ e) hkl.le
        rw [Finset.sum_sub_distrib] at h ⊢
        linarith
  have hqexp (e : ℕ) : q ^ e = (2 : ℝ) ^ (-(e : ℝ) / k) := by
    dsimp only [q, weight]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (2 : ℕ))]
    congr 1
    ring
  have hnum : 2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ)) = 2 * (1 - q) := by
    rw [sub_eq_add_neg (1 : ℝ), Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    change 2 - 2 * q = _
    ring
  have hden : 1 - (2 : ℝ) ^ (1 - (l : ℝ) / k) = 2 * (q ^ k - q ^ l) := by
    rw [sub_eq_add_neg (1 : ℝ) ((l : ℝ) / k),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hqk, hqexp l, neg_div]
    ring
  rw [hnum, hden, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), ← hs,
    div_mul_cancel_right₀ (sub_ne_zero.mpr hq₁.ne')]

open ArithmeticFunction

private noncomputable def target (k l : ℕ) : ArithmeticFunction ℝ :=
  ofPrimePowerValues fun p e => if p ≠ 2 ∧ k ≤ e ∧ e < l then 1 else 0

private noncomputable def powers (k : ℕ) : ArithmeticFunction ℝ :=
  ofPrimePowerValues fun p e => if p ≠ 2 ∧ k ∣ e then 1 else 0

private noncomputable def step (k : ℕ) : ArithmeticFunction ℝ :=
  ofPrimePowerValues fun p e => if p ≠ 2 ∧ e = k then -1 else 0

private noncomputable def residual (k l : ℕ) : ArithmeticFunction ℝ := step k * target k l

private lemma residual_multiplicative (k l : ℕ) : (residual k l).IsMultiplicative :=
  (isMultiplicative_ofPrimePowerValues _).mul (isMultiplicative_ofPrimePowerValues _)

private lemma target_prime_pow (k l : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    target k l (p ^ e) = if e = 0 ∨ p ≠ 2 ∧ k ≤ e ∧ e < l then 1 else 0 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [(isMultiplicative_ofPrimePowerValues _).map_one, target]
  · rw [target, ofPrimePowerValues_prime_pow _ hp he]
    simp [he]

private lemma powers_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    powers k (p ^ e) = if e = 0 ∨ p ≠ 2 ∧ k ∣ e then 1 else 0 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [(isMultiplicative_ofPrimePowerValues _).map_one, powers]
  · rw [powers, ofPrimePowerValues_prime_pow _ hp he]
    simp [he]

private lemma step_prime_pow {k : ℕ} (hk : k ≠ 0) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    step k (p ^ e) = (if e = 0 then 1 else 0) - if p ≠ 2 ∧ e = k then 1 else 0 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [(isMultiplicative_ofPrimePowerValues _).map_one, step, Ne.symm hk]
  · rw [step, ofPrimePowerValues_prime_pow _ hp he, ite_eq_right he]
    split_ifs <;> simp

private lemma step_mul_prime_pow {k : ℕ} (hk : k ≠ 0) (f : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (step k * f) (p ^ e) = f (p ^ e) - if p ≠ 2 ∧ k ≤ e then f (p ^ (e - k)) else 0 := by
  classical
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => step k a * f b),
    Nat.divisors_prime_pow hp e, Finset.sum_map]
  calc
    _ = ∑ j ∈ Finset.range (e + 1),
        ((if j = 0 then 1 else 0) - if p ≠ 2 ∧ j = k then 1 else 0) * f (p ^ (e - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      change step k (p ^ j) * f (p ^ e / p ^ j) = _
      have hd : p ^ e / p ^ j = p ^ (e - j) := by
        calc
          _ = p ^ (e - j + j) / p ^ j := by rw [Nat.sub_add_cancel hje]
          _ = _ := by rw [pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
      rw [step_prime_pow hk hp, hd]
    _ = _ := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
      simp_rw [show ∀ j : ℕ, (if p ≠ 2 ∧ j = k then f (p ^ (e - j)) else 0) =
          (if p ≠ 2 then if j = k then f (p ^ (e - j)) else 0 else 0) by
        intro j; split_ifs <;> simp_all]
      by_cases hp₂ : p = 2 <;> simp [hp₂, Finset.sum_ite_eq']

private lemma step_mul_powers {k : ℕ} (hk : k ≠ 0) : step k * powers k = 1 := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (show (step k * powers k).IsMultiplicative from
      (isMultiplicative_ofPrimePowerValues _).mul (isMultiplicative_ofPrimePowerValues _))
    _ isMultiplicative_one).2
  intro p e hp
  rcases eq_or_ne e 0 with rfl | he
  · exact ((isMultiplicative_ofPrimePowerValues _).mul
      (isMultiplicative_ofPrimePowerValues _)).map_one
  · have hne : p ^ e ≠ 1 := fun h =>
      he (Nat.pow_right_injective hp.two_le (h.trans (pow_zero _).symm))
    rw [step_mul_prime_pow hk _ hp, powers_prime_pow _ hp, ArithmeticFunction.one_apply_ne hne]
    by_cases hp₂ : p = 2
    · simp [hp₂, he]
    by_cases hke : k ≤ e
    · have hd : k ∣ e - k ↔ k ∣ e := Nat.dvd_sub_iff_left hke (dvd_refl k)
      have hz : e - k = 0 → k ∣ e := fun h =>
        (show e = k by omega) ▸ dvd_refl k
      simp only [he, false_or, hp₂, ne_eq, not_false_eq_true, true_and, hke, ite_true,
        powers_prime_pow _ hp, hd]
      simp only [or_iff_right_of_imp hz, sub_self]
    · have hd : ¬k ∣ e := fun h => hke (Nat.le_of_dvd (Nat.pos_of_ne_zero he) h)
      simp [hke, hp₂, he, hd]

private lemma residual_mul_powers {k l : ℕ} (hk : k ≠ 0) :
    residual k l * powers k = target k l := by
  rw [residual, mul_comm (step k), mul_assoc, step_mul_powers hk, mul_one]

private lemma prod_ite_one (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∏ p ∈ s, (if P p then (1 : ℝ) else 0)) = if ∀ p ∈ s, P p then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun i hi => ite_eq_left (h i hi)
  · push Not at h
    obtain ⟨p, hp, hP⟩ := h
    exact Finset.prod_eq_zero hp (ite_eq_right hP)

open Classical in
private lemma target_apply {k l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    target k l n = if Nat.IsKFull k n ∧ n.IsPowerFree l ∧ Odd n then 1 else 0 := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.not_isKFull_zero]
  rw [target, ofPrimePowerValues_apply_of_ne_zero _ hn, Finsupp.prod,
    Nat.support_factorization, prod_ite_one]
  congr 1
  apply propext
  constructor
  · intro h
    refine ⟨(Nat.isKFull_iff_factorization hn).mpr (fun p hp hd =>
      (h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)).2.1), ⟨hl, Nat.pos_of_ne_zero hn, ?_⟩, ?_⟩
    · intro p hp hd
      have hdp : p ∣ n := (dvd_pow_self p (by omega : l ≠ 0)).trans hd
      exact (h p (Nat.mem_primeFactors.mpr ⟨hp, hdp, hn⟩)).2.2.not_ge
        ((hp.pow_dvd_iff_le_factorization hn).mp hd)
    · exact Nat.not_even_iff_odd.mp fun h₂ =>
        (h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp h₂, hn⟩)).1 rfl
  · rintro ⟨hf, hl', ho⟩ p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    refine ⟨fun h => Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr (h ▸ hpd)),
      (Nat.isKFull_iff_factorization hn).mp hf p hpp hpd, ?_⟩
    exact lt_of_not_ge fun h => hl'.not_dvd hpp ((hpp.pow_dvd_iff_le_factorization hn).mpr h)

open Classical in
private lemma powers_apply {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    powers k n = if ∃ a : ℕ, Odd a ∧ a ^ k = n then 1 else 0 := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · rw [ArithmeticFunction.map_zero, ite_eq_right]
    rintro ⟨a, ha, he⟩
    exact pow_ne_zero _ (odd_ne_zero ha) he
  rw [powers, ofPrimePowerValues_apply_of_ne_zero _ hn, Finsupp.prod,
    Nat.support_factorization, prod_ite_one]
  congr 1
  apply propext
  constructor
  · intro h
    let a := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / k)
    have hpow : a ^ k = n := by
      calc
        a ^ k = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          dsimp only [a]
          rw [← Finset.prod_pow]
          exact Finset.prod_congr rfl fun p hp => by rw [← pow_mul, Nat.div_mul_cancel (h p hp).2]
        _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm
    refine ⟨a, (Nat.odd_pow_iff hk).mp (hpow.symm ▸ ?_), hpow⟩
    exact Nat.not_even_iff_odd.mp fun h₂ =>
      (h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp h₂, hn⟩)).1 rfl
  · rintro ⟨a, ha, rfl⟩ p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpa := hpp.dvd_of_dvd_pow hpd
    refine ⟨fun h => Nat.not_even_iff_odd.mpr ha (even_iff_two_dvd.mpr (h ▸ hpa)), ?_⟩
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right ..

private lemma norm_residual_prime_pow {k l : ℕ} (hk : k ≠ 0) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖residual k l (p ^ e)‖ ≤ 1 := by
  rw [residual, step_mul_prime_pow hk _ hp, target_prime_pow _ _ hp, target_prime_pow _ _ hp]
  split_ifs <;> norm_num

private lemma residual_prime_pow_eq_zero {k l : ℕ} (hk : k ≠ 0) (hkl : k < l)
    {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (h : e ≤ k ∨ k + l ≤ e) :
    residual k l (p ^ e) = 0 := by
  rw [residual, step_mul_prime_pow hk _ hp, target_prime_pow _ _ hp]
  rcases eq_or_ne p 2 with rfl | hp₂
  · simp [he]
  rcases h with h | h
  · rcases lt_or_eq_of_le h with h | rfl
    · simp [he, h.not_ge]
    · simp [hkl, hp₂, hk, (isMultiplicative_ofPrimePowerValues _).map_one, target]
  · have hke : k ≤ e := by omega
    have hel : ¬e < l := by omega
    have hsub : ¬e - k < l := by omega
    have hn : e - k ≠ 0 := by omega
    simp [he, hp₂, hke, hel, hsub, hn, target_prime_pow _ _ hp]

private noncomputable def scaled (k l : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => residual k l n * weight k n, by simp⟩

private lemma scaled_multiplicative (k l : ℕ) : (scaled k l).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · change residual k l 1 * weight k 1 = 1
    simp [weight, (residual_multiplicative k l).map_one]
  · change residual k l (m * n) * weight k (m * n) =
      residual k l m * weight k m * (residual k l n * weight k n)
    rw [(residual_multiplicative k l).map_mul_of_coprime hmn, weight_mul]
    ring

private noncomputable def primeWeight (k l : ℕ) (pe : ℕ × ℕ) : ℝ :=
  if pe.1.Prime ∧ pe.2 ≠ 0 then ‖scaled k l (pe.1 ^ pe.2)‖ else 0

private lemma primeWeight_nonneg (k l : ℕ) (pe : ℕ × ℕ) : 0 ≤ primeWeight k l pe := by
  unfold primeWeight
  split_ifs <;> positivity

private lemma summable_primeWeight {k l : ℕ} (hk : 0 < k) (hkl : k < l) :
    Summable (primeWeight k l) := by
  let t (e : ℕ) : ℝ := if e < k + l then 1 else 0
  have ht : Summable t := summable_of_ne_finset_zero (s := Finset.range (k + l)) fun e he => by
    simp [t, Finset.mem_range.not.mp he]
  have hr : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hb : Summable (fun p : ℕ => (p : ℝ) ^ (-(1 + 1 / (k : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h := hb.mul_of_nonneg ht (fun _ => by positivity) (fun e => by
    unfold t; split_ifs <;> positivity)
  apply h.of_nonneg_of_le (primeWeight_nonneg k l)
  rintro ⟨p, e⟩
  change primeWeight k l (p, e) ≤ (p : ℝ) ^ (-(1 + 1 / (k : ℝ))) * t e
  unfold primeWeight
  split_ifs with hpe
  · obtain ⟨hp, he⟩ := hpe
    rcases lt_or_ge k e with hke | hek
    · rcases lt_or_ge e (k + l) with hel | hle
      · have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        change ‖residual k l (p ^ e) * weight k (p ^ e)‖ ≤ _
        rw [norm_mul, Real.norm_of_nonneg (weight_nonneg _ _), show t e = 1 by simp [t, hel],
          mul_one]
        refine (mul_le_of_le_one_left (weight_nonneg _ _)
          (norm_residual_prime_pow hk.ne' hp e)).trans ?_
        rw [weight, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
        apply Real.rpow_le_rpow_of_exponent_le hp₁
        have hrat : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
          exact mul_one_div_cancel (by positivity)
        have hke' : (k : ℝ) + 1 ≤ e := by exact_mod_cast hke
        nlinarith [mul_nonneg (sub_nonneg.mpr hke') hr.le]
      · change ‖residual k l (p ^ e) * weight k (p ^ e)‖ ≤ _
        rw [residual_prime_pow_eq_zero hk.ne' hkl hp he (Or.inr hle), zero_mul, norm_zero]
        exact mul_nonneg (by positivity) (by unfold t; split_ifs <;> positivity)
    · change ‖residual k l (p ^ e) * weight k (p ^ e)‖ ≤ _
      rw [residual_prime_pow_eq_zero hk.ne' hkl hp he (Or.inl hek), zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (by unfold t; split_ifs <;> positivity)
  · exact mul_nonneg (by positivity) (by unfold t; split_ifs <;> positivity)

-- A positive integer injects into finite sets of pairs of prime and exponent.
private def factorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  n.primeFactors.map ⟨fun p => (p, n.factorization p), fun _ _ h => congrArg Prod.fst h⟩

private lemma prod_factorPairs (n : ℕ) (hn : n ≠ 0) :
    (∏ pe ∈ factorPairs n, pe.1 ^ pe.2) = n := by
  rw [factorPairs, Finset.prod_map]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

private lemma scaled_prod_factorPairs (k l n : ℕ) (hn : n ≠ 0) :
    ‖scaled k l n‖ = ∏ pe ∈ factorPairs n, primeWeight k l pe := by
  rw [IsMultiplicative.multiplicative_factorization _ (scaled_multiplicative k l) hn,
    factorPairs, Finset.prod_map]
  change ‖∏ p ∈ n.primeFactors, scaled k l (p ^ n.factorization p)‖ = _
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have he : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  change ‖scaled k l (p ^ n.factorization p)‖ = primeWeight k l (p, n.factorization p)
  exact (ite_eq_left ⟨Nat.prime_of_mem_primeFactors hp, he⟩).symm

private lemma summable_scaled {k l : ℕ} (hk : 0 < k) (hkl : k < l) :
    Summable (‖scaled k l ·‖) := by
  have hi : Function.Injective (fun n : ℕ => factorPairs (n + 1)) := by
    intro a b h
    have he := congrArg (fun s : Finset (ℕ × ℕ) => ∏ pe ∈ s, pe.1 ^ pe.2) h
    rw [prod_factorPairs _ (by omega), prod_factorPairs _ (by omega)] at he
    omega
  apply (summable_nat_add_iff 1).mp
  exact ((summable_finsetProd_of_summable_nonneg (primeWeight_nonneg k l)
    (summable_primeWeight hk hkl)).comp_injective hi).congr fun n =>
      (scaled_prod_factorPairs k l (n + 1) (by omega)).symm

private lemma local_sum_pos {k l : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) :
    0 < ∑' e : ℕ, scaled k l (p ^ e) := by
  let q := weight k p
  have hq₀ : 0 < q := weight_pos hp.ne_zero
  have hq₁ : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
    (neg_lt_zero.mpr (one_div_pos.mpr (by exact_mod_cast hk)))
  let a (e : ℕ) := target k l (p ^ e) * q ^ e
  have ha₀ (e : ℕ) : 0 ≤ a e := by
    dsimp only [a]
    rw [target_prime_pow _ _ hp]
    split_ifs <;> positivity
  have ha : Summable a := (summable_geometric_of_lt_one hq₀.le hq₁).of_nonneg_of_le ha₀ fun e => by
    dsimp only [a]
    rw [target_prime_pow _ _ hp]
    split_ifs <;> simp [pow_nonneg hq₀.le]
  have hap : 0 < ∑' e : ℕ, a e := by
    apply ha.tsum_pos ha₀ 0
    simp [a, target, (isMultiplicative_ofPrimePowerValues _).map_one]
  let b (e : ℕ) := if k ≤ e then a (e - k) * q ^ k else 0
  have hb : Summable b := (summable_nat_add_iff k).mp ((ha.mul_right (q ^ k)).congr fun e => by
    simp [b])
  have hbs : (∑' e : ℕ, b e) = (∑' e : ℕ, a e) * q ^ k := by
    rw [← hb.sum_add_tsum_nat_add k]
    have hz : ∑ e ∈ Finset.range k, b e = 0 := Finset.sum_eq_zero fun j hj =>
      ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hj))
    simp [hz, b, ha.tsum_mul_right]
  have he (e : ℕ) : scaled k l (p ^ e) = a e - if p = 2 then 0 else b e := by
    change residual k l (p ^ e) * weight k (p ^ e) = _
    rw [residual, step_mul_prime_pow hk.ne' _ hp, weight_pow, sub_mul]
    change a e - (if p ≠ 2 ∧ k ≤ e then target k l (p ^ (e - k)) else 0) * q ^ e = _
    by_cases hp₂ : p = 2
    · simp [hp₂]
    by_cases hke : k ≤ e
    · rw [ite_eq_left ⟨hp₂, hke⟩, ite_eq_right hp₂]
      simp only [b, hke, ite_true, a, mul_assoc, ← pow_add, Nat.sub_add_cancel hke]
    · simp [hp₂, hke, b]
  simp only [he]
  by_cases hp₂ : p = 2
  · simpa [hp₂] using hap
  simp only [hp₂, ite_false]
  rw [ha.tsum_sub hb, hbs, ← mul_one_sub]
  exact mul_pos hap (sub_pos.mpr (pow_lt_one₀ hq₀.le hq₁ hk.ne'))

private lemma scaled_tsum_pos {k l : ℕ} (hk : 0 < k) (hkl : k < l) :
    0 < ∑' n : ℕ, scaled k l n := by
  let f (p : Nat.Primes) (e : ℕ) := scaled k l ((p : ℕ) ^ e)
  let L (p : Nat.Primes) := ∑' e : ℕ, f p e
  have hP : HasProd L (∑' n : ℕ, scaled k l n) :=
    (scaled_multiplicative k l).eulerProduct_hasProd (summable_scaled hk hkl)
  have hs : Summable (fun pe : Nat.Primes × ℕ => ‖f pe.1 (pe.2 + 1)‖) := by
    have hi : Function.Injective (fun pe : Nat.Primes × ℕ => ((pe.1 : ℕ), pe.2 + 1)) := by
      intro a b he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Nat.succ.inj (congrArg Prod.snd he))
    exact ((summable_primeWeight hk hkl).comp_injective hi).congr fun pe =>
      by simp [primeWeight, pe.1.property, f]
  have hBound (p : Nat.Primes) : ‖L p - 1‖ ≤ ∑' e : ℕ, ‖f p (e + 1)‖ := by
    have hi : Function.Injective (fun e : ℕ => (p, e)) := fun _ _ he => congrArg Prod.snd he
    have h₁ := (hs.comp_injective hi : Summable ((fun pe : Nat.Primes × ℕ =>
      ‖f pe.1 (pe.2 + 1)‖) ∘ (fun e : ℕ => (p, e))))
    change Summable (fun e : ℕ => ‖f p (e + 1)‖) at h₁
    have h₂ : Summable (f p) := (summable_nat_add_iff 1).mp h₁.of_norm
    have h₃ := h₂.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one, show f p 0 = 1 by
      simp [f, (scaled_multiplicative k l).map_one]] at h₃
    rw [← show (1 + ∑' e : ℕ, f p (e + 1)) = L p from h₃, add_sub_cancel_left]
    exact norm_tsum_le_tsum_norm h₁
  have hd : Summable (fun p : Nat.Primes => L p - 1) :=
    (hs.prod.of_nonneg_of_le (fun p => norm_nonneg (L p - 1)) hBound).of_norm
  have hlog : Summable (fun p => Real.log (L p)) :=
    (Real.summable_log_one_add_of_summable hd).congr fun p => by simp
  have hp : HasProd L (Real.exp (∑' p, Real.log (L p))) :=
    Real.hasProd_of_hasSum_log (fun p : Nat.Primes => local_sum_pos hk p.property) hlog.hasSum
  rw [← hP.tprod_eq, hp.tprod_eq]
  exact Real.exp_pos _

private noncomputable def halfFloor (y : ℝ) : ℝ := (⌊(y + 1) / 2⌋₊ : ℝ)

private lemma count_odd_base {y : ℝ} (hy : 0 ≤ y) :
    ({a : ℕ | (a : ℝ) ≤ y ∧ Odd a}.ncard : ℝ) = halfFloor y := by
  let f (j : ℕ) := 2 * j + 1
  have h : Set.BijOn f (Set.Iio ⌊(y + 1) / 2⌋₊) {a : ℕ | (a : ℝ) ≤ y ∧ Odd a} := by
    have hle (j : ℕ) : (f j : ℝ) ≤ y ↔ j < ⌊(y + 1) / 2⌋₊ := by
      rw [← Nat.succ_le_iff, Nat.le_floor_iff (by positivity)]
      push_cast [f]
      constructor <;> intro hj <;> linarith
    refine ⟨fun j hj => ⟨(hle j).2 hj, Nat.odd_iff.mpr (by dsimp [f]; omega)⟩, ?_, ?_⟩
    · intro a _ b _ hab
      dsimp [f] at hab
      omega
    · rintro a ⟨ha, ⟨j, rfl⟩⟩
      exact ⟨j, (hle j).1 (by simpa [f, two_mul, add_assoc] using ha), by simp [f, two_mul]⟩
  rw [halfFloor, ← h.ncard_eq, ← show (↑(Finset.range ⌊(y + 1) / 2⌋₊) : Set ℕ) =
    Set.Iio ⌊(y + 1) / 2⌋₊ by ext j; simp, Set.ncard_coe_finset, Finset.card_range]

private lemma halfFloor_le {y : ℝ} (hy : 0 ≤ y) : halfFloor y ≤ y := by
  unfold halfFloor
  rcases lt_or_ge y 1 with h | h
  · rw [Nat.floor_eq_zero.mpr (by linarith), Nat.cast_zero]
    exact hy
  · have h₁ := Nat.floor_le (show 0 ≤ (y + 1) / 2 by positivity)
    linarith

private lemma tendsto_halfFloor {w : ℝ} (hw : 0 < w) :
    Tendsto (fun x : ℝ => halfFloor (x * w) / x) atTop (𝓝 (w / 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun x : ℝ => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, inv_eq_one_div, div_sub' hx.ne', abs_div, abs_of_pos hx,
      div_le_div_iff_of_pos_right hx, abs_le]
    have h₁ := Nat.floor_le (show 0 ≤ (x * w + 1) / 2 by positivity)
    have h₂ := Nat.lt_floor_add_one ((x * w + 1) / 2)
    unfold halfFloor
    constructor <;> linarith
  · exact tendsto_inv_atTop_zero

private lemma sum_indicator (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ n ∈ s, if P n then (1 : ℝ) else 0) = ({n | n ∈ s ∧ P n}.ncard : ℝ) := by
  have hset : {n | n ∈ s ∧ P n} = (s.filter P : Set ℕ) := by ext n; simp
  rw [← Finset.sum_filter, hset, Set.ncard_coe_finset]
  simp

private lemma sum_powers {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d) :
    (∑ m ∈ Finset.Ioc 0 (⌊x ^ k⌋₊ / d), powers k m) = halfFloor (x * weight k d) := by
  classical
  simp_rw [powers_apply hk.ne']
  rw [sum_indicator]
  have hle (a : ℕ) : a ^ k ≤ ⌊x ^ k⌋₊ / d ↔ (a : ℝ) ≤ x * weight k d := by
    rw [Nat.le_div_iff_mul_le hd, Nat.le_floor_iff (pow_nonneg hx k), Nat.cast_mul, Nat.cast_pow,
      le_scale_iff hk hd.ne' hx (Nat.cast_nonneg a)]
  have h : Set.BijOn (fun a : ℕ => a ^ k) {a | (a : ℝ) ≤ x * weight k d ∧ Odd a}
      {n | n ∈ Finset.Ioc 0 (⌊x ^ k⌋₊ / d) ∧ ∃ a : ℕ, Odd a ∧ a ^ k = n} := by
    refine ⟨?_, (Nat.pow_left_injective hk.ne').injOn, ?_⟩
    · rintro a ⟨ha, ha'⟩
      exact ⟨Finset.mem_Ioc.mpr ⟨pow_pos (Nat.pos_of_ne_zero (odd_ne_zero ha')) _, (hle a).mpr ha⟩,
        a, ha', rfl⟩
    · rintro n ⟨hn, a, ha, rfl⟩
      exact ⟨a, ⟨(hle a).mp (Finset.mem_Ioc.mp hn).2, ha⟩, rfl⟩
  rw [← h.ncard_eq, count_odd_base (mul_nonneg hx (weight_nonneg k d))]

private lemma odd_count {k l : ℕ} (hk : 0 < k) (hl : 2 ≤ l) {x : ℝ} (hx : 0 ≤ x) :
    count k l Odd x = ∑' d, residual k l d * halfFloor (x * weight k d) := by
  classical
  have hc : count k l Odd x = ∑ n ∈ Finset.Ioc 0 ⌊x ^ k⌋₊, target k l n := by
    simp_rw [target_apply hl]
    rw [sum_indicator, count]
    congr 2
    ext n
    simp only [counted, Set.mem_ofPred_eq, Finset.mem_Ioc, Nat.le_floor_iff (pow_nonneg hx k)]
    constructor
    · exact fun ⟨hle, hf, hfree, ho⟩ => ⟨⟨hfree.pos, hle⟩, hf, hfree, ho⟩
    · exact fun ⟨⟨_, hle⟩, hf, hfree, ho⟩ => ⟨hle, hf, hfree, ho⟩
  rw [hc, ← residual_mul_powers hk.ne', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum,
    tsum_eq_sum (s := Finset.Ioc 0 ⌊x ^ k⌋₊)]
  · exact Finset.sum_congr rfl fun d hd => by rw [sum_powers hk hx (Finset.mem_Ioc.mp hd).1]
  · intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · simp
    have hnd : ¬d ≤ ⌊x ^ k⌋₊ := fun h => hd (Finset.mem_Ioc.mpr ⟨hd₀, h⟩)
    have hlt : x * weight k d < 1 := by
      contrapose! hnd
      rw [Nat.le_floor_iff (pow_nonneg hx k)]
      simpa using (le_scale_iff hk hd₀.ne' hx (by norm_num : (0 : ℝ) ≤ 1)).mpr hnd
    simp [halfFloor, Nat.floor_eq_zero.mpr (by linarith : (x * weight k d + 1) / 2 < 1)]

private lemma tendsto_odd_count {k l : ℕ} (hk : 0 < k) (hkl : k < l) (hl : 2 ≤ l) :
    Tendsto (fun x => count k l Odd x / x) atTop (𝓝 ((∑' d, scaled k l d) / 2)) := by
  let f (x : ℝ) (d : ℕ) := residual k l d * (halfFloor (x * weight k d) / x)
  have hlim (d : ℕ) : Tendsto (fun x => f x d) atTop (𝓝 (scaled k l d / 2)) := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [f, scaled]
    · simpa only [f, scaled, ArithmeticFunction.coe_mk, mul_div_assoc] using
        (tendsto_halfFloor (weight_pos (k := k) hd)).const_mul (residual k l d)
  have h := tendsto_tsum_of_dominated_convergence (summable_scaled hk hkl) hlim (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx d
    have hnn : 0 ≤ halfFloor (x * weight k d) := Nat.cast_nonneg _
    change ‖residual k l d * (halfFloor (x * weight k d) / x)‖ ≤ ‖residual k l d * weight k d‖
    simp only [norm_mul, Real.norm_of_nonneg (div_nonneg hnn hx.le),
      Real.norm_of_nonneg (weight_nonneg k d)]
    have hle := halfFloor_le (mul_nonneg hx.le (weight_nonneg k d))
    exact mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hx).mpr (hle.trans_eq (mul_comm x (weight k d)))) (norm_nonneg _))
  rw [tsum_div_const] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [odd_count hk hl hx.le, ← tsum_div_const]
  exact tsum_congr fun d => (mul_div_assoc ..).symm

end KFullPowerFreeParity

open KFullPowerFreeParity

/-- **Odd-to-even ratio of $k$-full, $l$-free numbers.** Let $2 \le k < l$. Call a natural number
$n$ a $[k, l]$-integer if it is $k$-full and $l$-free, that is, $n \ge 1$ and every prime $p$
dividing $n$ satisfies $p^k \mid n$ and $p^l \nmid n$. For a natural number $N$ let $O_{k,l}(N)$
and $E_{k,l}(N)$ be the numbers of odd and of even $[k, l]$-integers $n \le N$. Then
$O_{k,l}(N)/E_{k,l}(N) \to (2 - 2^{1 - 1/k})/(1 - 2^{1 - l/k})$ as $N \to \infty$.

The counts up to a real $x$ depend only on $\lfloor x \rfloor$, so this is the same as the limit
as $x \to \infty$ through the reals.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Theorem 1
(`integers-2024-A106-thm-1`). -/
public theorem tendsto_card_odd_kFull_lFree_div_card_even_kFull_lFree {k l : ℕ}
    (hk : 2 ≤ k) (hkl : k < l) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧
            Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧
            Even n}.ncard)
      atTop (𝓝 ((2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ))) / (1 - (2 : ℝ) ^ (1 - (l : ℝ) / k)))) := by
  have hk₀ : 0 < k := by omega
  let c : ℝ := (∑' d, scaled k l d) / 2
  let S : ℝ := ∑ e ∈ Finset.Ico k l, weight k (2 ^ e)
  have hc : 0 < c := half_pos (scaled_tsum_pos hk₀ hkl)
  have hS : 0 < S := Finset.sum_pos' (fun e _ => weight_nonneg k (2 ^ e))
    ⟨k, Finset.mem_Ico.mpr ⟨le_rfl, hkl⟩, weight_pos (by positivity)⟩
  have ho : Tendsto (fun x => count k l Odd x / x) atTop (𝓝 c) :=
    tendsto_odd_count hk₀ hkl (by omega)
  have h := ho.div (tendsto_even_count hk₀ ho) (mul_pos hc hS).ne'
  have hratio : c / (c * S) = S⁻¹ := by field_simp [hc.ne', hS.ne']
  rw [hratio, show S⁻¹ = _ from weight_sum hk₀ hkl] at h
  let root (N : ℕ) := (N : ℝ) ^ (1 / (k : ℝ))
  have hroot : Tendsto root atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  refine (h.comp hroot).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hpos : 0 < root N := by dsimp [root]; positivity
  have hpow : root N ^ k = (N : ℝ) := by
    have hk' : (k : ℝ) ≠ 0 := by positivity
    dsimp only [root]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), one_div_mul_cancel hk', Real.rpow_one]
  have hcount (P : ℕ → Prop) : count k l P (root N) =
      ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧ P n}.ncard : ℝ) := by
    simp only [count, counted, hpow, Nat.cast_le]
  simp only [Function.comp_apply, Pi.div_apply, div_div_div_cancel_right₀ hpos.ne', hcount]

end MetaMathlibExt
