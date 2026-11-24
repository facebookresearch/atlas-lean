/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Large valuations in short runs of consecutive integers

The number of starting points up to `x` whose run contains an exceptionally large
prime valuation is little-o of `x`.
-/

namespace MetaMathlibExt

open Filter Finset Real

namespace card_max_padicValNat_add_gt_isLittleO

private noncomputable def runLength (x : ℕ) : ℕ := ⌊exp (0.8 * √(log x))⌋₊

private noncomputable def digits (x p : ℕ) : ℕ := 1 + ⌊log x / log p⌋₊

private noncomputable def threshold (x p : ℕ) : ℝ := (digits x p : ℝ) / log (digits x p)

private noncomputable def exponent (x p : ℕ) : ℕ := ⌊threshold x p⌋₊ + 1

private theorem tendsto_sqrt_log :
    Tendsto (fun x : ℕ => √(log x)) atTop atTop :=
  tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem tendsto_runLength : Tendsto runLength atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_exp_atTop.comp
    (tendsto_sqrt_log.const_mul_atTop (by norm_num : (0 : ℝ) < 0.8)))

-- Eventually every relevant prime power is at least the cube of the run length.
private theorem eventually_large_powers :
    ∀ᶠ x : ℕ in atTop, 2 * runLength x ≤ x ∧
      ∀ p : ℕ, p.Prime → p < 2 * runLength x → runLength x ^ 3 ≤ p ^ exponent x p := by
  have hlim := (tendsto_exp_div_pow_atTop 2).comp
    (tendsto_sqrt_log.atTop_div_const (by norm_num : (0 : ℝ) < 3))
  filter_upwards [eventually_ge_atTop 1, tendsto_sqrt_log.eventually_ge_atTop 2,
    hlim.eventually_ge_atTop 27] with x hx ht hgrowth
  let t := √(log x)
  have ht' : 2 ≤ t := ht
  have htpos : 0 < t := by linarith
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hsq : t ^ 2 = log x := Real.sq_sqrt (log_nonneg hx')
  have hk : (runLength x : ℝ) ≤ exp t :=
    (Nat.floor_le (exp_pos _).le).trans (exp_le_exp.mpr (by linarith : 0.8 * t ≤ t))
  have hsmall : 2 * runLength x ≤ x := by
    have hxpos : 0 < (x : ℝ) := by positivity
    exact_mod_cast calc
      2 * (runLength x : ℝ) ≤ exp t * exp t :=
        mul_le_mul (by linarith [Real.add_one_le_exp t]) hk (by positivity) (exp_pos t).le
      _ = exp (t + t) := (exp_add _ _).symm
      _ ≤ exp (log x) := exp_le_exp.mpr (by nlinarith [mul_nonneg htpos.le (sub_nonneg.mpr ht')])
      _ = x := exp_log hxpos
  refine ⟨hsmall, fun p hp hpk => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlp : 0 < log p := log_pos (by linarith)
  have hhalf : 1 / 2 ≤ log (p : ℝ) := by
    refine le_trans ?_ (log_le_log (by norm_num : (0 : ℝ) < 2) hp2)
    convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlx := log_nonneg hx'
  have hratio : 1 ≤ log x / log p := by
    rw [le_div_iff₀ hlp, one_mul]
    exact log_le_log (by positivity) (by exact_mod_cast hpk.le.trans hsmall)
  have hd : 1 < (digits x p : ℝ) := by
    have hf : 1 ≤ ⌊log x / log p⌋₊ := Nat.le_floor (by simpa using hratio)
    exact_mod_cast (show 1 < digits x p by unfold digits; omega)
  have hlogd : 0 < log (digits x p) := log_pos hd
  -- digits ≤ 1 + 2 log x, and exp(t / 3) eventually dominates this quadratic in t.
  have hdub : (digits x p : ℝ) ≤ 1 + 2 * t ^ 2 := by
    simp only [digits, Nat.cast_add, Nat.cast_one]
    apply add_le_add_right
    refine (Nat.floor_le (div_nonneg hlx hlp.le)).trans ((div_le_iff₀ hlp).mpr ?_)
    nlinarith [mul_nonneg hlx (sub_nonneg.mpr hhalf)]
  change 27 ≤ exp (t / 3) / (t / 3) ^ 2 at hgrowth
  have hlogub : log (digits x p) ≤ t / 3 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hpoly := (le_div_iff₀ (by positivity)).mp hgrowth
    exact hdub.trans (by nlinarith [sq_nonneg (t - 1)])
  have hxD : log x ≤ (digits x p : ℝ) * log p := by
    apply (div_le_iff₀ hlp).mp
    simpa [digits, add_comm] using (Nat.lt_floor_add_one (log x / log p)).le
  have hDa : (digits x p : ℝ) ≤ (exponent x p : ℝ) * log (digits x p) := by
    apply (div_le_iff₀ hlogd).mp
    simpa [exponent, threshold] using (Nat.lt_floor_add_one (threshold x p)).le
  have hpower : 3 * t ≤ (exponent x p : ℝ) * log p := by
    apply le_of_mul_le_mul_right _ hlogd
    calc
      3 * t * log (digits x p) ≤ 3 * t * (t / 3) :=
        mul_le_mul_of_nonneg_left hlogub (by positivity)
      _ = log x := by linarith [hsq]
      _ ≤ (digits x p : ℝ) * log p := hxD
      _ ≤ _ := by simpa [mul_right_comm] using mul_le_mul_of_nonneg_right hDa hlp.le
  exact_mod_cast calc
    (runLength x : ℝ) ^ 3 ≤ (exp t) ^ 3 := pow_le_pow_left₀ (by positivity) hk _
    _ = exp (3 * t) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ exp ((exponent x p : ℝ) * log p) := exp_le_exp.mpr hpower
    _ = (p : ℝ) ^ exponent x p := by rw [Real.exp_nat_mul, exp_log (by positivity)]

private theorem card_shifted_multiples (x K q i : ℕ) (hi : i ≤ K) :
    ((Icc 1 x).filter fun m => q ∣ m + i).card ≤ (x + K) / q := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card_of_injOn (fun m => m + i) _ (add_left_injective i).injOn
  intro m hm
  obtain ⟨hm, hdvd⟩ := mem_filter.mp hm
  obtain ⟨hm₁, hmx⟩ := mem_Icc.mp hm
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by dsimp; omega, add_le_add hmx hi⟩, hdvd⟩

open scoped Classical in
private noncomputable def exceptional (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun m => ∃ p : ℕ, p.Prime ∧ p < 2 * runLength x ∧
    threshold x p < ((Icc 1 (runLength x)).sup fun i => padicValNat p (m + i) : ℕ)

private theorem card_exceptional_le (x : ℕ) (hK : 0 < runLength x)
    (hpowers : ∀ p : ℕ, p.Prime → p < 2 * runLength x → runLength x ^ 3 ≤ p ^ exponent x p) :
    (exceptional x).card * runLength x ≤ 2 * (x + runLength x) := by
  classical
  let K := runLength x
  let primes := (range (2 * K)).filter Nat.Prime
  let shifts := Icc 1 K
  let bad (p i : ℕ) := (Icc 1 x).filter fun m => p ^ exponent x p ∣ m + i
  have hcover : exceptional x ⊆ primes.biUnion (fun p => shifts.biUnion (bad p)) := by
    intro m hm
    obtain ⟨hm, p, hp, hpk, hv⟩ := mem_filter.mp hm
    obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup shifts (nonempty_Icc.mpr hK)
      (fun i => padicValNat p (m + i))
    change threshold x p < (shifts.sup (fun i => padicValNat p (m + i)) : ℕ) at hv
    rw [heq] at hv
    have hnonneg : 0 ≤ threshold x p :=
      div_nonneg (by positivity) (log_nonneg (by simp [digits]))
    have hval : exponent x p ≤ padicValNat p (m + i) :=
      Nat.succ_le_of_lt ((Nat.floor_lt hnonneg).mpr hv)
    refine mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_range.mpr hpk, hp⟩,
      mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨hm, ?_⟩⟩⟩
    rw [Nat.padicValNat_def] at hval
    exact (pow_dvd_pow p hval).trans (pow_multiplicity_dvd ..)
  have hcard := card_biUnion_le_card_mul primes (fun p => shifts.biUnion (bad p))
    (K * ((x + K) / K ^ 3)) (by
      intro p hp
      obtain ⟨hpk, hprime⟩ := mem_filter.mp hp
      have hq := hpowers p hprime (mem_range.mp hpk)
      simpa [shifts] using card_biUnion_le_card_mul shifts (bad p) ((x + K) / K ^ 3) (by
        intro i hi
        exact (card_shifted_multiples x K _ i (mem_Icc.mp hi).2).trans
          (Nat.div_le_div_left hq (pow_pos hK 3))))
  calc
    _ ≤ (primes.card * (K * ((x + K) / K ^ 3))) * K :=
      Nat.mul_le_mul_right K ((card_le_card hcover).trans hcard)
    _ ≤ (2 * K * (K * ((x + K) / K ^ 3))) * K := by
      gcongr
      exact (card_filter_le ..).trans_eq (card_range _)
    _ = 2 * (((x + K) / K ^ 3) * K ^ 3) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self ..)

end card_max_padicValNat_add_gt_isLittleO

open card_max_padicValNat_add_gt_isLittleO in
open scoped Classical in
/-- **Large valuations in short runs of consecutive integers are rare.** For a natural number
$x$ let $K = \lfloor \exp(0.8 \sqrt{\log x}) \rfloor$ and, for a prime $p$, let
$D_p = 1 + \lfloor \log x / \log p \rfloor$. Write $v_p(n)$ for the exponent of $p$ in a
positive integer $n$. Then the number of integers $m$ with $1 \le m \le x$ for which some prime
$p < 2K$ satisfies $\max \{ v_p(m + i) : 1 \le i \le K \} > D_p / \log D_p$ is $o(x)$ as
$x \to \infty$.

For large $x$ every prime $p < 2K$ is at most $x$, so $D_p \ge 2$ and $\log D_p > 0$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 5 (`integers-2026-A47-lem-5`). -/
public theorem card_max_padicValNat_add_gt_isLittleO :
    (fun x : ℕ => ((((Finset.Icc 1 x).filter fun m => ∃ p : ℕ, p.Prime ∧
        p < 2 * ⌊Real.exp (0.8 * Real.sqrt (Real.log x))⌋₊ ∧
          ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ) /
              Real.log ((1 + ⌊Real.log x / Real.log p⌋₊ : ℕ) : ℝ) <
            (((Finset.Icc 1 ⌊Real.exp (0.8 * Real.sqrt (Real.log x))⌋₊).sup
              fun i => padicValNat p (m + i) : ℕ) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x : ℕ => (x : ℝ) := by
  change (fun x : ℕ => ((exceptional x).card : ℝ)) =o[atTop] fun x : ℕ => (x : ℝ)
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hlim := tendsto_natCast_atTop_atTop (R := ℝ) |>.comp tendsto_runLength
  filter_upwards [eventually_large_powers, tendsto_runLength.eventually_ge_atTop 1,
    hlim.eventually_ge_atTop (4 / c)] with x ⟨hsmall, hpowers⟩ hk hcK
  have hbound : (exceptional x).card * runLength x ≤ 4 * x :=
    (card_exceptional_le x hk hpowers).trans (by omega)
  have hbound' : ((exceptional x).card : ℝ) * (runLength x : ℝ) ≤ 4 * (x : ℝ) := by
    exact_mod_cast hbound
  have hfour : 4 ≤ c * (runLength x : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hc).mp hcK
  simp only [Real.norm_natCast]
  apply le_of_mul_le_mul_right _ (by exact_mod_cast hk : (0 : ℝ) < runLength x)
  calc
    _ ≤ 4 * (x : ℝ) := hbound'
    _ ≤ _ := by simpa [mul_right_comm] using mul_le_mul_of_nonneg_right hfour (Nat.cast_nonneg x)

end MetaMathlibExt
