/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

private lemma coef_eq (j : ℕ) :
    ((bernoulli j : ℚ) : ℝ) = (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) := by
  by_cases hj : j = 1
  · subst hj
    have h : (bernoulli 1 : ℚ) = -1 / 2 := bernoulli_one
    simp [h]
  · simp [hj]

private lemma bernoulliFun_eq_sum (p : ℕ) (x : ℝ) :
    bernoulliFun p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j) := by
  have hunfold : bernoulliFun p x =
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli p)) := rfl
  rw [hunfold, Polynomial.bernoulli_def, Polynomial.map_sum]
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ Finset.range (p + 1),
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
        (Polynomial.monomial i (bernoulli (p - i) * ↑(p.choose i)))) =
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i := by
    intro i _
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    simp only [map_mul, map_natCast, eq_ratCast]
  rw [Finset.sum_congr rfl hterm]
  have hrefl : (∑ i ∈ Finset.range (p + 1),
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i) =
      ∑ j ∈ Finset.range (p + 1),
        ((bernoulli j : ℚ) : ℝ) * (Nat.choose p (p - j) : ℝ) * x ^ (p - j) := by
    rw [← Finset.sum_range_reflect (fun j => ((bernoulli j : ℚ) : ℝ) *
      (Nat.choose p (p - j) : ℝ) * x ^ (p - j)) (p + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : p + 1 - 1 - i = p - i := by omega
    have e2 : p - (p - i) = i := by omega
    rw [e1, e2]
  rw [hrefl]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjle : j ≤ p := by omega
  have hc : (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) =
      ((bernoulli j : ℚ) : ℝ) := (coef_eq j).symm
  rw [hc, Nat.choose_symm hjle]
  ring

/-- Bernoulli kernel on the unit interval starting at `c`: `B_m(x - c) / m!`. -/
private noncomputable def emKernel (c : ℤ) (m : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun m (x - (c : ℝ)) / (Nat.factorial m : ℝ)

private lemma emKernel_continuous (c : ℤ) (m : ℕ) : Continuous (emKernel c m) := by
  unfold emKernel
  exact ((continuous_bernoulliFun m).comp (continuous_id.sub continuous_const)).div_const _

private lemma hasDerivAt_emKernel_succ (c : ℤ) (q : ℕ) (x : ℝ) :
    HasDerivAt (emKernel c (q + 1)) (emKernel c q x) x := by
  have hsub : HasDerivAt (fun x : ℝ => x - (c : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (c : ℝ)
  have hB : HasDerivAt (fun x : ℝ => bernoulliFun (q + 1) (x - (c : ℝ)))
      (((q : ℝ) + 1) * bernoulliFun q (x - (c : ℝ))) x := by
    have h1 := (hasDerivAt_bernoulliFun (q + 1) (x - (c : ℝ))).comp x hsub
    simp only [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one] at h1
    exact h1
  have hdiv : HasDerivAt (emKernel c (q + 1))
      ((((q : ℝ) + 1) * bernoulliFun q (x - (c : ℝ))) / (Nat.factorial (q + 1) : ℝ)) x := by
    unfold emKernel
    exact hB.div_const _
  have hfact : (Nat.factorial (q + 1) : ℝ) = ((q : ℝ) + 1) * (Nat.factorial q : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hfq : (Nat.factorial q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
  have heq : ((((q : ℝ) + 1) * bernoulliFun q (x - (c : ℝ))) / (Nat.factorial (q + 1) : ℝ)) =
      emKernel c q x := by
    unfold emKernel
    rw [hfact]
    field_simp
  rwa [heq] at hdiv

/-- The within-derivative of an iterated within-derivative, restricted to a unit subinterval. -/
private lemma hasDerivWithinAt_iter (a b : ℤ) (f : ℝ → ℝ) (r q : ℕ) (c : ℤ) (x : ℝ)
    (hab : a < b) (hca : (a : ℝ) ≤ (c : ℝ)) (hcb : (c : ℝ) + 1 ≤ (b : ℝ))
    (hx : x ∈ Set.uIcc (c : ℝ) ((c : ℝ) + 1))
    (hqr : q + 1 ≤ r) (hdf : ContDiffOn ℝ ((r : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    HasDerivWithinAt (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      (iteratedDerivWithin (q + 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      (Set.uIcc ((c : ℝ)) ((c : ℝ) + 1)) x := by
  have habr : (a : ℝ) < (b : ℝ) := Int.cast_lt.mpr hab
  have huniq : UniqueDiffOn ℝ (Set.Icc ((a : ℝ)) ((b : ℝ))) := uniqueDiffOn_Icc habr
  have hcc : (c : ℝ) ≤ (c : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
  rw [Set.uIcc_of_le hcc] at hx
  have hxS : x ∈ Set.Icc ((a : ℝ)) ((b : ℝ)) := ⟨hca.trans hx.1, hx.2.trans hcb⟩
  have hlt : (q : WithTop ℕ∞) < (r : WithTop ℕ∞) := by
    exact_mod_cast Nat.lt_of_succ_le hqr
  have hdiffon : DifferentiableOn ℝ (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      (Set.Icc ((a : ℝ)) ((b : ℝ))) :=
    hdf.differentiableOn_iteratedDerivWithin hlt huniq
  have h1 : HasDerivWithinAt (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      (derivWithin (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
        (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      (Set.Icc ((a : ℝ)) ((b : ℝ))) x :=
    (hdiffon x hxS).hasDerivWithinAt
  rw [← iteratedDerivWithin_succ] at h1
  apply h1.mono
  rw [Set.uIcc_of_le hcc]
  intro y hy
  exact ⟨hca.trans hy.1, hy.2.trans hcb⟩

/-- Integrability of an iterated within-derivative on a unit subinterval. -/
private lemma intervalIntegrable_iter (a b : ℤ) (f : ℝ → ℝ) (r q : ℕ) (c : ℤ)
    (hab : a < b) (hca : (a : ℝ) ≤ (c : ℝ)) (hcb : (c : ℝ) + 1 ≤ (b : ℝ))
    (hqr : q ≤ r) (hdf : ContDiffOn ℝ ((r : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    IntervalIntegrable (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      MeasureTheory.volume (c : ℝ) ((c : ℝ) + 1) := by
  have habr : (a : ℝ) < (b : ℝ) := Int.cast_lt.mpr hab
  have huniq : UniqueDiffOn ℝ (Set.Icc ((a : ℝ)) ((b : ℝ))) := uniqueDiffOn_Icc habr
  have hle : (q : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hqr
  have hcont : ContinuousOn (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      (Set.Icc ((a : ℝ)) ((b : ℝ))) :=
    hdf.continuousOn_iteratedDerivWithin hle huniq
  have hcc : (c : ℝ) ≤ (c : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hcc]
  intro y hy
  exact (hcont y ⟨hca.trans hy.1, hy.2.trans hcb⟩).mono (Set.Icc_subset_Icc hca hcb)

/-- One integration-by-parts step on a unit interval. -/
private lemma ibp_step (a b : ℤ) (f : ℝ → ℝ) (r q : ℕ) (c : ℤ)
    (hab : a < b) (hca : (a : ℝ) ≤ (c : ℝ)) (hcb : (c : ℝ) + 1 ≤ (b : ℝ))
    (hqr : q + 1 ≤ r) (hdf : ContDiffOn ℝ ((r : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    (∫ x in (c : ℝ)..((c : ℝ) + 1),
      emKernel c (q + 1) x * iteratedDerivWithin (q + 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) =
    emKernel c (q + 1) ((c : ℝ) + 1) *
      iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
      emKernel c (q + 1) (c : ℝ) * iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ) -
    (∫ x in (c : ℝ)..((c : ℝ) + 1),
      emKernel c q x * iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) := by
  have hu : ∀ x ∈ Set.uIcc (c : ℝ) ((c : ℝ) + 1),
      HasDerivWithinAt (emKernel c (q + 1)) (emKernel c q x)
        (Set.uIcc ((c : ℝ)) ((c : ℝ) + 1)) x := by
    intro x _
    exact (hasDerivAt_emKernel_succ c q x).hasDerivWithinAt
  have hv : ∀ x ∈ Set.uIcc (c : ℝ) ((c : ℝ) + 1),
      HasDerivWithinAt (iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))))
        (iteratedDerivWithin (q + 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
        (Set.uIcc ((c : ℝ)) ((c : ℝ) + 1)) x := by
    intro x hx
    exact hasDerivWithinAt_iter a b f r q c x hab hca hcb hx hqr hdf
  have hint_u : IntervalIntegrable (emKernel c q) MeasureTheory.volume
      (c : ℝ) ((c : ℝ) + 1) :=
    (emKernel_continuous c q).intervalIntegrable _ _
  have hint_v : IntervalIntegrable (iteratedDerivWithin (q + 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))))
      MeasureTheory.volume (c : ℝ) ((c : ℝ) + 1) :=
    intervalIntegrable_iter a b f r (q + 1) c hab hca hcb hqr hdf
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hu hv
    hint_u hint_v

private lemma emKernel_left (c : ℤ) (m : ℕ) :
    emKernel c m (c : ℝ) = (bernoulli m : ℝ) / (Nat.factorial m : ℝ) := by
  unfold emKernel
  simp [bernoulliFun_eval_zero]

private lemma emKernel_right_of_ne_one (c : ℤ) (m : ℕ) (hm : m ≠ 1) :
    emKernel c m ((c : ℝ) + 1) = (bernoulli m : ℝ) / (Nat.factorial m : ℝ) := by
  unfold emKernel
  have harg : ((c : ℝ) + 1) - (c : ℝ) = 1 := by ring
  rw [harg, bernoulliFun_endpoints_eq_of_ne_one hm, bernoulliFun_eval_zero]

private lemma emKernel_one_left (c : ℤ) : emKernel c 1 (c : ℝ) = -1 / 2 := by
  have h0 : (c : ℝ) - (c : ℝ) = 0 := sub_self _
  unfold emKernel
  rw [h0, bernoulliFun_eval_zero, bernoulli_one, Nat.factorial_one, Nat.cast_one, div_one]
  norm_cast

private lemma emKernel_one_right (c : ℤ) : emKernel c 1 ((c : ℝ) + 1) = 1 / 2 := by
  have h1 : ((c : ℝ) + 1) - (c : ℝ) = 1 := by ring
  unfold emKernel
  rw [h1, bernoulliFun_eval_one, bernoulliFun_eval_zero, bernoulli_one,
    Nat.factorial_one, Nat.cast_one, div_one]
  norm_num

private lemma emKernel_zero_eq (c : ℤ) (x : ℝ) : emKernel c 0 x = 1 := by
  unfold emKernel
  rw [bernoulliFun_zero, Nat.factorial_zero, Nat.cast_one, div_one]

private lemma unitEM (a b : ℤ) (f : ℝ → ℝ) (q : ℕ) (c : ℤ)
    (hab : a < b) (hca : (a : ℝ) ≤ (c : ℝ)) (hcb : (c : ℝ) + 1 ≤ (b : ℝ))
    (hq : 1 ≤ q)
    (hdf : ContDiffOn ℝ ((q : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ) +
      iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1)) / 2
    = (∫ x in (c : ℝ)..((c : ℝ) + 1), f x)
      + (∑ m ∈ Finset.Icc 2 q, ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ))
          * (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ))))
      + ((-1 : ℝ) ^ (q + 1) * (∫ x in (c : ℝ)..((c : ℝ) + 1),
          emKernel c q x * iteratedDerivWithin q f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)) := by
  revert hdf
  induction q, hq using Nat.le_induction with
  | base =>
    intro hdf
    have hempty : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
    rw [hempty, Finset.sum_empty, add_zero]
    have hsign1 : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
    rw [hsign1, one_mul]
    have hIBP0 := ibp_step a b f 1 0 c hab hca hcb (by omega) hdf
    rw [emKernel_one_right, emKernel_one_left] at hIBP0
    have hK0 : (∫ x in (c : ℝ)..((c : ℝ) + 1), emKernel c 0 x *
        iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
        = (∫ x in (c : ℝ)..((c : ℝ) + 1), f x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro _
      rw [emKernel_zero_eq, iteratedDerivWithin_zero, one_mul]
    rw [hK0] at hIBP0
    have hring : (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ) +
        iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1)) / 2
        = 1 / 2 * iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
          (-1 / 2) * iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ) := by
      ring
    linear_combination hring - hIBP0
  | succ n hn IH =>
    intro hdf
    have hdfn : ContDiffOn ℝ ((n : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ))) :=
      hdf.of_le (by exact_mod_cast Nat.le_succ n)
    have IH' := IH hdfn
    have hIBP := ibp_step a b f (n + 1) n c hab hca hcb (le_refl _) hdf
    have hne : n + 1 ≠ 1 := by omega
    have hX : emKernel c (n + 1) ((c : ℝ) + 1)
        = (bernoulli (n + 1) : ℝ) / (Nat.factorial (n + 1) : ℝ) :=
      emKernel_right_of_ne_one c (n + 1) hne
    have hY : emKernel c (n + 1) (c : ℝ)
        = (bernoulli (n + 1) : ℝ) / (Nat.factorial (n + 1) : ℝ) :=
      emKernel_left c (n + 1)
    rw [hX, hY] at hIBP
    have hsum : (∑ m ∈ Finset.Icc 2 (n + 1), ((-1 : ℝ) ^ m *
        ((bernoulli m : ℝ) / (Nat.factorial m : ℝ))
          * (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ))))
        = (∑ m ∈ Finset.Icc 2 n, ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ))
          * (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ))))
          + ((-1 : ℝ) ^ (n + 1) * ((bernoulli (n + 1) : ℝ) / (Nat.factorial (n + 1) : ℝ))
          * (iteratedDerivWithin ((n + 1) - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((c : ℝ) + 1) -
            iteratedDerivWithin ((n + 1) - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) (c : ℝ))) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [hsum]
    have e1 : (n + 1) - 1 = n := Nat.add_sub_cancel n 1
    rw [e1]
    have hsign : (-1 : ℝ) ^ ((n + 1) + 1) = -(-1 : ℝ) ^ (n + 1) := by
      rw [pow_succ]; ring
    rw [hsign]
    linear_combination IH' + (-1 : ℝ) ^ (n + 1) * hIBP

/-- Collapse the `m`-sum over `Icc 2 p` to the even-index `k`-sum over `Icc 1 (p/2)`:
odd Bernoulli numbers beyond `B_1` vanish. -/
private lemma msum_eq_ksum (p : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 2 p, ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) * H (m - 1)))
    = ∑ k ∈ Finset.Icc 1 (p / 2),
      ((bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) * H (2 * k - 1)) := by
  induction p with
  | zero =>
    have e1 : Finset.Icc 2 0 = (∅ : Finset ℕ) := by decide
    have e2 : Finset.Icc 1 (0 / 2) = (∅ : Finset ℕ) := by decide
    rw [e1, e2, Finset.sum_empty, Finset.sum_empty]
  | succ p IH =>
    by_cases h2 : 2 ≤ p + 1
    · rw [Finset.sum_Icc_succ_top h2]
      by_cases hodd : Odd (p + 1)
      · obtain ⟨k, hk⟩ := hodd
        have hB0 : bernoulli (p + 1) = 0 := bernoulli_eq_zero_of_odd ⟨k, hk⟩ (by omega)
        have hB : ((bernoulli (p + 1) : ℚ) : ℝ) = 0 := by rw [hB0]; norm_cast
        have hterm : ((-1 : ℝ) ^ (p + 1) * ((bernoulli (p + 1) : ℝ) / (Nat.factorial (p + 1) : ℝ)) *
            H ((p + 1) - 1)) = 0 := by simp [hB]
        rw [hterm, add_zero]
        have hdiv : (p + 1) / 2 = p / 2 := by omega
        rw [hdiv]
        exact IH
      · obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hodd
        have hsign : (-1 : ℝ) ^ (p + 1) = 1 := Even.neg_one_pow ⟨t, ht⟩
        have hdiv : (p + 1) / 2 = p / 2 + 1 := by omega
        have e1 : 2 * (p / 2 + 1) = p + 1 := by omega
        have e2 : (p + 1) - 1 = p := by omega
        rw [hdiv, Finset.sum_Icc_succ_top (show 1 ≤ p / 2 + 1 by omega), IH, hsign, e1, e2]
        ring
    · have hp0 : p = 0 := by omega
      subst hp0
      have e1 : Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) := by decide
      have e2 : Finset.Icc 1 ((0 + 1) / 2) = (∅ : Finset ℕ) := by decide
      rw [e1, e2, Finset.sum_empty, Finset.sum_empty]

/-- Trapezoid decomposition of a sum over `range (N+1)`. -/
private lemma sum_range_trapezoid (h : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), h i =
      (∑ i ∈ Finset.range N, (h i + h (i + 1)) / 2) + (h 0 + h N) / 2 := by
  induction N with
  | zero => simp
  | succ N IH =>
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [IH]
    ring

/-- Reindex a sum over `Icc a (a+N)` (integers) as a sum over `range (N+1)`. -/
private lemma sum_Icc_int_reindex (a : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc a (a + (((N : ℕ)) : ℤ)), f n =
      ∑ i ∈ Finset.range (N + 1), f (a + (((i : ℕ)) : ℤ)) := by
  rw [eq_comm]
  apply Finset.sum_bij (fun i _ => a + (((i : ℕ)) : ℤ))
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    constructor <;> [skip; skip] <;> omega
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_range] at ha1 ha2
    have : ((((a1 : ℕ))) : ℤ) = ((((a2 : ℕ))) : ℤ) := Int.add_left_cancel heq
    exact Nat.cast_injective this
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n - a).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have hnn : 0 ≤ n - a := by omega
      have hto : (((((n - a).toNat : ℕ))) : ℤ) = n - a := Int.toNat_of_nonneg hnn
      omega
  · intro i hi
    rfl

/-- Pointwise agreement (a.e.) of the shifted kernel with the periodic kernel. -/
private lemma rem_ae (a b : ℤ) (f : ℝ → ℝ) (p : ℕ) (c : ℤ) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ∈ Set.uIoc (c : ℝ) ((c : ℝ) + 1) →
      emKernel c p x * iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x =
        (1 / (Nat.factorial p : ℝ)) *
          (bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) := by
  have hsingle : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ (c : ℝ) + 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬ x ≠ (c : ℝ) + 1} = {(c : ℝ) + 1} := by ext x; simp
    rw [hset]
    exact MeasureTheory.measure_singleton _
  have hcc : (c : ℝ) ≤ (c : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
  filter_upwards [hsingle] with x hx
  intro hmem
  rw [Set.uIoc_of_le hcc] at hmem
  have hlt : x < (c : ℝ) + 1 := lt_of_le_of_ne hmem.2 hx
  have hfr : Int.fract x = x - (c : ℝ) := by
    have e : Int.fract x = Int.fract (x - (c : ℝ)) := by
      conv_lhs => rw [show x = (c : ℝ) + (x - (c : ℝ)) from by ring, Int.fract_intCast_add]
    rw [e]
    exact Int.fract_eq_self.mpr ⟨by linarith [hmem.1], by linarith [hlt]⟩
  unfold emKernel
  rw [← hfr]
  ring

/-- Convert one unit-interval remainder integral to the periodic-kernel form. -/
private lemma piece_remainder (a b : ℤ) (f : ℝ → ℝ) (p : ℕ) (c : ℤ) :
    (∫ x in (c : ℝ)..((c : ℝ) + 1),
      emKernel c p x * iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
    = (1 / (Nat.factorial p : ℝ)) * (∫ x in (c : ℝ)..((c : ℝ) + 1),
      bernoulliFun p (Int.fract x) *
        iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) := by
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae (rem_ae a b f p c)

/-- Integrability of the periodic-kernel remainder integrand on a unit interval. -/
private lemma intervalIntegrable_remP (a b : ℤ) (f : ℝ → ℝ) (p r : ℕ) (c : ℤ)
    (hab : a < b) (hca : (a : ℝ) ≤ (c : ℝ)) (hcb : (c : ℝ) + 1 ≤ (b : ℝ))
    (hpr : p ≤ r)
    (hdf : ContDiffOn ℝ ((r : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    IntervalIntegrable (fun x => bernoulliFun p (Int.fract x) *
      iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      MeasureTheory.volume (c : ℝ) ((c : ℝ) + 1) := by
  have hfact : (Nat.factorial p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hKg : IntervalIntegrable (fun x => emKernel c p x *
      iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      MeasureTheory.volume (c : ℝ) ((c : ℝ) + 1) := by
    have hK : ContinuousOn (emKernel c p) (Set.uIcc (c : ℝ) ((c : ℝ) + 1)) :=
      (emKernel_continuous c p).continuousOn
    have hg : ContinuousOn (iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))))
        (Set.uIcc (c : ℝ) ((c : ℝ) + 1)) := by
      have habr : (a : ℝ) < (b : ℝ) := Int.cast_lt.mpr hab
      have huniq : UniqueDiffOn ℝ (Set.Icc ((a : ℝ)) ((b : ℝ))) := uniqueDiffOn_Icc habr
      have hle : (p : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hpr
      have hcont := hdf.continuousOn_iteratedDerivWithin hle huniq
      have hcc : (c : ℝ) ≤ (c : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
      rw [Set.uIcc_of_le hcc]
      intro y hy
      exact (hcont y ⟨hca.trans hy.1, hy.2.trans hcb⟩).mono (Set.Icc_subset_Icc hca hcb)
    exact (hK.mul hg).intervalIntegrable
  have hKg' := hKg.const_mul (Nat.factorial p : ℝ)
  have hpc : (Nat.factorial p : ℝ) * (1 / (Nat.factorial p : ℝ)) = 1 :=
    mul_one_div_cancel hfact
  have hfilter : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIoc (c : ℝ) ((c : ℝ) + 1) →
      (Nat.factorial p : ℝ) * (emKernel c p x *
        iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) =
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x := by
    have hrem := rem_ae a b f p c
    filter_upwards [hrem] with x hx
    intro hmem
    have e := hx hmem
    rw [e, ← mul_assoc, hpc, one_mul]
  have hae : (fun x => (Nat.factorial p : ℝ) * (emKernel c p x *
      iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (c : ℝ) ((c : ℝ) + 1))]
      (fun x => bernoulliFun p (Int.fract x) *
        iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr hfilter
  exact hKg'.congr_ae hae

/-- Cast bridge: `((a + i : ℤ) : ℝ) = a + i`. -/
private lemma castF1 (a : ℤ) (i : ℕ) :
    ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) = (a : ℝ) + ((((i : ℕ))) : ℝ) := by
  rw [Int.cast_add, Int.cast_natCast]

/-- Cast bridge: `((a + (i+1) : ℤ) : ℝ) = ((a + i : ℤ) : ℝ) + 1`. -/
private lemma castF2 (a : ℤ) (i : ℕ) :
    ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) =
      ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) + 1 := by
  have hint_eq : a + (((((i + 1 : ℕ))) : ℤ)) = (a + ((((i : ℕ))) : ℤ)) + 1 := by omega
  rw [hint_eq, Int.cast_add, Int.cast_one]

private lemma castF3 (a : ℤ) : ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ) = (a : ℝ) := by
  rw [Int.cast_add]
  simp

private lemma castF4 (a b : ℤ) (N : ℕ) (habN : a + ((((N : ℕ))) : ℤ) = b) :
    ((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ) = (b : ℝ) := by
  rw [habN]

private lemma em_assembly (a b : ℤ) (p : ℕ) (f : ℝ → ℝ)
    (hab : a < b) (hp : 1 ≤ p)
    (hdf : ContDiffOn ℝ ((p : WithTop ℕ∞)) f (Set.Icc ((a : ℝ)) ((b : ℝ)))) :
    ∑ n ∈ Finset.Icc a b, f ((((n : ℤ))) : ℝ) =
      (∫ x in ((a : ℝ))..((b : ℝ)), f x) + (f ((a : ℝ)) + f ((b : ℝ))) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)))) +
        ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
          (∫ x in ((a : ℝ))..((b : ℝ)), bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)) := by
  obtain ⟨N, habN⟩ : ∃ N : ℕ, a + ((((N : ℕ))) : ℤ) = b := ⟨(b - a).toNat, by
    have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ b - a by omega)
    rw [h]
    omega⟩
  have hNpos : 1 ≤ N := by omega
  have habR : (a : ℝ) < (b : ℝ) := Int.cast_lt.mpr hab
  have huniq : UniqueDiffOn ℝ (Set.Icc ((a : ℝ)) ((b : ℝ))) := uniqueDiffOn_Icc habR
  have hcontf : ContinuousOn f (Set.Icc ((a : ℝ)) ((b : ℝ))) := by
    have h0 : ((0 : ℕ) : WithTop ℕ∞) ≤ ((p : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.zero_le p
    have hc := hdf.continuousOn_iteratedDerivWithin (m := 0) h0 huniq
    rwa [iteratedDerivWithin_zero] at hc
  have hNb : ((((N : ℕ))) : ℝ) = (b : ℝ) - (a : ℝ) := by
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) habN
    rw [Int.cast_add, Int.cast_natCast] at h2
    linarith [h2]
  have hmem : ∀ i : ℕ, i ≤ N →
      ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) ∈ (Set.Icc ((a : ℝ)) ((b : ℝ))) := by
    intro i hi
    constructor
    · rw [castF1 a i]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · rw [castF1 a i]
      have hiR : ((((i : ℕ))) : ℝ) ≤ ((((N : ℕ))) : ℝ) := by exact_mod_cast hi
      rw [hNb] at hiR
      linarith [hiR]
  have hF5 : ∀ i : ℕ, i ≤ N → (a : ℝ) ≤ ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) :=
    fun i hi => (hmem i hi).1
  have hF6 : ∀ i : ℕ, i < N → ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) + 1 ≤ (b : ℝ) := by
    intro i hi
    have h2 : ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) + 1 =
        ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) := (castF2 a i).symm
    rw [h2]
    exact (hmem (i + 1) (by omega)).2
  have hreidx : ∑ n ∈ Finset.Icc a b, f ((((n : ℤ))) : ℝ)
      = ∑ i ∈ Finset.range (N + 1),
        iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) := by
    have hbb : b = a + ((((N : ℕ))) : ℤ) := habN.symm
    rw [hbb, sum_Icc_int_reindex]
    apply Finset.sum_congr rfl
    intro i _
    show f (((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) = _
    rw [iteratedDerivWithin_zero]
  have htrap_clean : (∑ i ∈ Finset.range (N + 1),
        iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))
      = (∑ i ∈ Finset.range N,
          (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
            iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + (((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ))) / 2)
        + (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ) +
          iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ)) / 2 :=
    sum_range_trapezoid _ N
  -- NOTE: the two endpoint terms above are intentionally grouped under one `/ 2`
  -- in this generated statement; the proof below re-associates them. (See `hLHS`.)
  have e0 : iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
      ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ) = f ((a : ℝ)) := by
    rw [castF3 a, iteratedDerivWithin_zero]
  have eN : iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
      ((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ) = f ((b : ℝ)) := by
    rw [castF4 a b N habN, iteratedDerivWithin_zero]
  have hLHS : ∑ n ∈ Finset.Icc a b, f ((((n : ℤ))) : ℝ)
      = (∑ i ∈ Finset.range N,
          (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
            iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + (((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ))) / 2)
        + (f ((a : ℝ)) + f ((b : ℝ))) / 2 := by
    rw [hreidx, htrap_clean, e0, eN]
  have hunit : ∀ i ∈ Finset.range N,
      (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
        ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
        iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
        ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1)) / 2
      = (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
        ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1), f x)
        + (∑ m ∈ Finset.Icc 2 p, ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
          (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))))
        + ((-1 : ℝ) ^ (p + 1) * (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
          emKernel (a + ((((i : ℕ))) : ℤ)) p x *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact unitEM a b f p (a + ((((i : ℕ))) : ℤ)) hab (hF5 i (le_of_lt hiN)) (hF6 i hiN) hp hdf
  have hSUM : (∑ i ∈ Finset.range N,
        (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
          iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1)) / 2)
      = ((∑ i ∈ Finset.range N,
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1), f x))
        + (∑ i ∈ Finset.range N, ∑ m ∈ Finset.Icc 2 p,
          ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
          (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)))))
        + (∑ i ∈ Finset.range N, ((-1 : ℝ) ^ (p + 1) *
          (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
          emKernel (a + ((((i : ℕ))) : ℤ)) p x *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))) := by
    have hsum_eq := Finset.sum_congr rfl (fun i hi => hunit i hi)
    rwa [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_eq
  have hbridge_trap : (∑ i ∈ Finset.range N,
        (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
          iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + (((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ))) / 2)
      = ∑ i ∈ Finset.range N,
        (iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ) +
          iteratedDerivWithin 0 f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1)) / 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [castF2 a i]
  have hmsum_bridge : (∑ i ∈ Finset.range N, ∑ m ∈ Finset.Icc 2 p,
        ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))))
      = ∑ i ∈ Finset.range N, ∑ m ∈ Finset.Icc 2 p,
        ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    rw [← castF2 a i]
  have hint_piece_f : ∀ k : ℕ, k < N →
      IntervalIntegrable f MeasureTheory.volume
        ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ) ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) := by
    intro k hk
    have h1 : ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ) ∈ (Set.Icc ((a : ℝ)) ((b : ℝ))) :=
      hmem k (by omega)
    have h2 : ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) ∈ (Set.Icc ((a : ℝ)) ((b : ℝ))) :=
      hmem (k + 1) (by omega)
    have hle : ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ) ≤
        ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) := by
      have hkk2 : a + ((((k : ℕ))) : ℤ) ≤ a + ((((k + 1 : ℕ))) : ℤ) := by omega
      exact_mod_cast hkk2
    have hsub : Set.uIcc ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)
        ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) ⊆ (Set.Icc ((a : ℝ)) ((b : ℝ))) := by
      rw [Set.uIcc_of_le hle]
      intro y hy
      exact ⟨h1.1.trans hy.1, hy.2.trans h2.2⟩
    exact (hcontf.mono hsub).intervalIntegrable
  have hINT : (∑ i ∈ Finset.range N,
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1), f x))
      = ∫ x in ((a : ℝ))..((b : ℝ)), f x := by
    have hconv_sum : (∑ i ∈ Finset.range N,
          (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1), f x))
        = ∑ k ∈ Finset.range N,
          (∫ x in ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ), f x) :=
      Finset.sum_congr rfl (fun k _ => by rw [castF2 a k])
    rw [hconv_sum]
    have hadj : (∑ k ∈ Finset.range N,
          (∫ x in ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ), f x))
        = ∫ x in ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ), f x :=
      intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hint_piece_f k hk)
    rw [hadj, castF3 a, castF4 a b N habN]
  have htel : ∀ m : ℕ, (∑ i ∈ Finset.range N,
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)))
      = iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) -
        iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)) := by
    intro m
    have hsub := Finset.sum_range_sub
      (fun i => iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
        ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) N
    have eN : iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
        ((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ) =
        iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) := by
      rw [castF4 a b N habN]
    have e0 : iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
        ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ) =
        iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)) := by
      rw [castF3 a]
    rw [eN, e0] at hsub
    exact hsub
  have hinner : ∀ m : ℕ, (∑ i ∈ Finset.range N,
        ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))))
      = ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)))) := by
    intro m
    rw [← Finset.mul_sum, htel m]
  have hMSUM : (∑ i ∈ Finset.range N, ∑ m ∈ Finset.Icc 2 p,
        ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
        (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
          iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
          ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))))
      = ∑ k ∈ Finset.Icc 1 (p / 2),
        ((bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
          (iteratedDerivWithin (2 * k - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) -
            iteratedDerivWithin (2 * k - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)))) := by
    have hswap : (∑ i ∈ Finset.range N, ∑ m ∈ Finset.Icc 2 p,
          ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
          (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))))
        = ∑ m ∈ Finset.Icc 2 p, ∑ i ∈ Finset.range N,
          ((-1 : ℝ) ^ m * ((bernoulli m : ℝ) / (Nat.factorial m : ℝ)) *
          (iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i + 1 : ℕ))) : ℤ)) : ℤ)) : ℝ) -
            iteratedDerivWithin (m - 1) f (Set.Icc ((a : ℝ)) ((b : ℝ)))
            ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ))) :=
      Finset.sum_comm
    rw [hswap]
    have hmid := Finset.sum_congr rfl (fun m (_ : m ∈ Finset.Icc 2 p) => hinner m)
    rw [hmid]
    exact msum_eq_ksum p (fun m => iteratedDerivWithin m f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((b : ℝ)) -
      iteratedDerivWithin m f (Set.Icc ((a : ℝ)) ((b : ℝ))) ((a : ℝ)))
  have hpiece : ∀ i ∈ Finset.range N,
      (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        emKernel (a + ((((i : ℕ))) : ℤ)) p x *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      = (1 / (Nat.factorial p : ℝ)) *
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact piece_remainder a b f p (a + ((((i : ℕ))) : ℤ))
  have hconvR : (∑ i ∈ Finset.range N,
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        emKernel (a + ((((i : ℕ))) : ℤ)) p x *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))
      = (1 / (Nat.factorial p : ℝ)) *
        (∑ i ∈ Finset.range N,
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hpiece i hi)
  have hintP : ∀ k : ℕ, k < N → IntervalIntegrable
      (fun x => bernoulliFun p (Int.fract x) *
        iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)
      MeasureTheory.volume ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)
      ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) := by
    intro k hk
    have e : ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ) =
        ((((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1) := castF2 a k
    rw [e]
    exact intervalIntegrable_remP a b f p p (a + ((((k : ℕ))) : ℤ)) hab
      (hF5 k (by omega)) (hF6 k hk) (le_refl p) hdf
  have hadjP : (∑ i ∈ Finset.range N,
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))
      = ∫ x in ((a : ℝ))..((b : ℝ)),
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x := by
    have hconv : (∑ i ∈ Finset.range N,
          (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
          bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))
        = ∑ k ∈ Finset.range N,
          (∫ x in ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ),
          bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x) :=
      Finset.sum_congr rfl (fun k _ => by rw [castF2 a k])
    rw [hconv]
    have hadj2 : (∑ k ∈ Finset.range N,
          (∫ x in ((((a + ((((k : ℕ))) : ℤ)) : ℤ)) : ℝ)..
            ((((a + (((((k + 1) : ℕ))) : ℤ)) : ℤ)) : ℝ),
          bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x))
        = ∫ x in ((((a + ((((0 : ℕ))) : ℤ)) : ℤ)) : ℝ)..((((a + ((((N : ℕ))) : ℤ)) : ℤ)) : ℝ),
          bernoulliFun p (Int.fract x) *
            iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x :=
      intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hintP k hk)
    rw [hadj2, castF3 a, castF4 a b N habN]
  have hREM : (∑ i ∈ Finset.range N,
        ((-1 : ℝ) ^ (p + 1) *
        (∫ x in ((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)..
          ((((((a + ((((i : ℕ))) : ℤ)) : ℤ)) : ℝ)) + 1),
        emKernel (a + ((((i : ℕ))) : ℤ)) p x *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)))
      = ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
        (∫ x in ((a : ℝ))..((b : ℝ)),
        bernoulliFun p (Int.fract x) *
          iteratedDerivWithin p f (Set.Icc ((a : ℝ)) ((b : ℝ))) x)) := by
    rw [← Finset.mul_sum, hconvR, hadjP]
    ring
  linear_combination hLHS + hbridge_trap + hSUM + hmsum_bridge + hINT + hMSUM + hREM

section
/-- **Euler–Maclaurin formula.** Let $a < b$ be integers, let $p \ge 1$ be a natural number, and
let $f : \mathbb{R} \to \mathbb{R}$ be $p$ times continuously differentiable on $[a, b]$, its
derivatives $f^{(k)}$ being taken relative to $[a, b]$ (one-sided at the endpoints). Let $B_j$
be the Bernoulli numbers with $B_1 = -\tfrac{1}{2}$. Then there are $1$-periodic functions
$P_m : \mathbb{R} \to \mathbb{R}$ for $m \ge 0$ such that $P_p$ agrees on $[0, 1)$ with the
Bernoulli polynomial $\sum_{j=0}^{p} \binom{p}{j} B_j x^{p-j}$, and
$\sum_{n=a}^{b} f(n) = I + E + R$, where $I = \int_a^b f(x)\,dx + \frac{f(a) + f(b)}{2}$,
$E = \sum_{k=1}^{\lfloor p/2 \rfloor} \frac{B_{2k}}{(2k)!} (f^{(2k-1)}(b) - f^{(2k-1)}(a))$
and $R = \frac{(-1)^{p+1}}{p!} \int_a^b P_p(x) f^{(p)}(x)\,dx$.

Proves `Wanted` entry `eulerMaclaurinFormula`.

Source: https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula.
-/
theorem eulerMaclaurinFormula :
    ∀ (a b : ℤ) (p : ℕ) (f : ℝ → ℝ),
      a < b →
      1 ≤ p →
      ContDiffOn ℝ (↑p) f (Set.Icc (↑a) (↑b)) →
      ∃ P : ℕ → ℝ → ℝ,
        (∀ (m : ℕ) (x : ℝ), P m (x + 1) = P m x) ∧
        (∀ x ∈ Set.Ico (0 : ℝ) 1, P p x =
          ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
            (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j)) ∧
        ∑ n ∈ Finset.Icc a b, f (↑n) =
          (∫ x in (↑a)..(↑b), f x) + (f (↑a) + f (↑b)) / 2 +
            (∑ k ∈ Finset.Icc 1 (p / 2),
              (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
                (iteratedDerivWithin (2 * k - 1) f (Set.Icc (↑a) (↑b)) (↑b) -
                  iteratedDerivWithin (2 * k - 1) f (Set.Icc (↑a) (↑b)) (↑a))) +
            ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
              (∫ x in (↑a)..(↑b), P p x * iteratedDerivWithin p f (Set.Icc (↑a) (↑b)) x)) := by
  intro a b p f hab hp hdf
  refine ⟨fun m x => bernoulliFun m (Int.fract x), ?_, ?_, ?_⟩
  · intro m x
    change bernoulliFun m (Int.fract (x + 1)) = bernoulliFun m (Int.fract x)
    rw [Int.fract_add_one]
  · intro x hx
    change bernoulliFun p (Int.fract x) =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j)
    rw [Int.fract_eq_self.mpr ⟨hx.1, hx.2⟩]
    exact bernoulliFun_eq_sum p x
  · exact em_assembly a b p f hab hp hdf

end
end MetaMathlibExt
