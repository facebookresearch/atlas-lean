/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 15

X·cot x integral of order n reduces via a binomial recurrence.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry15Xcot

open scoped Nat Real BigOperators Interval Polynomial
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9CotPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in Real.pi / 4..x, u ^ n * (Real.cos u / Real.sin u)

-- Helper: the cotangent-weighted power is integrable between any two points
-- of the open interval (0, π), where `Real.sin` does not vanish.
private lemma xcot_pow_integrable (k : ℕ) (a b : ℝ) (ha0 : 0 < a) (ha : a < Real.pi)
    (hb0 : 0 < b) (hb : b < Real.pi) :
    IntervalIntegrable (fun u : ℝ => u ^ k * (Real.cos u / Real.sin u))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hcont : ContinuousOn (fun u : ℝ => u ^ k * (Real.cos u / Real.sin u))
      (Set.Ioo 0 Real.pi) := by
    apply ContinuousOn.mul (ContinuousOn.pow continuous_id.continuousOn k)
    apply ContinuousOn.div Real.continuous_cos.continuousOn
      Real.continuous_sin.continuousOn
    intro u hu
    simp only [Set.mem_Ioo] at hu
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2)
  apply hcont.mono
  intro u hu
  rw [Set.mem_uIcc] at hu
  simp only [Set.mem_Ioo]
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor <;> linarith
  · constructor <;> linarith

-- Helper: binomial expansion of `(π - t) ^ n` with the exact coefficient shape
-- used in the entry.
private lemma xcot_binom (n : ℕ) (t : ℝ) : (Real.pi - t) ^ n =
    ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
      t ^ k := by
  have h := add_pow (-t) Real.pi n
  rw [show (-t + Real.pi) = (Real.pi - t) from by ring] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  ring

-- Helper: a binomial-weighted sum of power integrals is the integral of the
-- binomial-weighted power.
private lemma xcot_sum_int (n : ℕ) (t : ℝ) (pw : ℕ → ℝ → ℝ) (T : ℝ → ℝ)
    (hbin : ∀ u : ℝ, T u * (Real.cos u / Real.sin u) =
      ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
        (pw k u * (Real.cos u / Real.sin u)))
    (hint : ∀ k ∈ range (n + 1), IntervalIntegrable
      (fun u : ℝ => pw k u * (Real.cos u / Real.sin u))
      MeasureTheory.volume (Real.pi / 4) t) :
    (∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
      (∫ u in Real.pi / 4..t, pw k u * (Real.cos u / Real.sin u))) =
      ∫ u in Real.pi / 4..t, T u * (Real.cos u / Real.sin u) := by
  have h2 : ∀ k ∈ range (n + 1), IntervalIntegrable
      (fun u : ℝ => ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
        (pw k u * (Real.cos u / Real.sin u)))
      MeasureTheory.volume (Real.pi / 4) t := by
    intro k hk
    exact (hint k hk).const_mul _
  have hpush : ∀ k ∈ range (n + 1),
      ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
        (∫ u in Real.pi / 4..t, pw k u * (Real.cos u / Real.sin u)) =
      ∫ u in Real.pi / 4..t, ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
        (pw k u * (Real.cos u / Real.sin u)) := by
    intro k _
    rw [intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl hpush]
  rw [← intervalIntegral.integral_finsetSum h2]
  congr 1
  ext u
  rw [hbin u]

-- Helper: integrability of `(π - u) ^ n * cot u` between points of `(0, π)`.
private lemma xcot_A_int (n : ℕ) (a b : ℝ) (ha0 : 0 < a) (ha : a < Real.pi)
    (hb0 : 0 < b) (hb : b < Real.pi) :
    IntervalIntegrable
      (fun u : ℝ => (Real.pi - u) ^ n * (Real.cos u / Real.sin u))
      MeasureTheory.volume a b := by
  have hfun : (fun u : ℝ => (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) =
      (∑ k ∈ range (n + 1), fun u : ℝ =>
        ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          (u ^ k * (Real.cos u / Real.sin u))) := by
    funext u
    rw [Finset.sum_apply]
    rw [xcot_binom n u, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun]
  exact IntervalIntegrable.sum (range (n + 1)) (fun k _ => by
    apply IntervalIntegrable.const_mul
    exact xcot_pow_integrable k a b ha0 ha hb0 hb)

-- Helper: integrability of `(π - 2 * u) ^ n * cot u` between points of `(0, π)`.
private lemma xcot_B_int (n : ℕ) (a b : ℝ) (ha0 : 0 < a) (ha : a < Real.pi)
    (hb0 : 0 < b) (hb : b < Real.pi) :
    IntervalIntegrable
      (fun u : ℝ => (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u))
      MeasureTheory.volume a b := by
  have hfun : (fun u : ℝ => (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u)) =
      (∑ k ∈ range (n + 1), fun u : ℝ =>
        ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          ((2 * u) ^ k * (Real.cos u / Real.sin u))) := by
    funext u
    rw [Finset.sum_apply]
    rw [xcot_binom n (2 * u), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun]
  exact IntervalIntegrable.sum (range (n + 1)) (fun k _ => by
    apply IntervalIntegrable.const_mul
    have heq : (fun u : ℝ => (2 * u) ^ k * (Real.cos u / Real.sin u)) =
        (fun u : ℝ => (2 : ℝ) ^ k * (u ^ k * (Real.cos u / Real.sin u))) := by
      funext u
      rw [mul_pow]
      ring
    rw [heq]
    apply IntervalIntegrable.const_mul
    exact xcot_pow_integrable k a b ha0 ha hb0 hb)

-- Helper: integrability of `(π - w) ^ n * cot (w / 2)` on `[2 * x, π / 2]`.
private lemma xcot_G_int (n : ℕ) (x : ℝ) (hx0 : 0 < x) (hx2 : x < Real.pi / 2) :
    IntervalIntegrable
      (fun w : ℝ => (Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2)))
      MeasureTheory.volume (2 * x) (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcon1 : ContinuousOn (fun w : ℝ => (Real.pi - w) ^ n) [[2 * x, Real.pi / 2]] := by
    fun_prop
  have hcon2 : ContinuousOn (fun w : ℝ => Real.cos (w / 2) / Real.sin (w / 2))
      [[2 * x, Real.pi / 2]] := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousOn
    · exact (Real.continuous_sin.comp (continuous_id.div_const 2)).continuousOn
    · intro w hw
      rw [Set.mem_uIcc] at hw
      have hw0 : (0 : ℝ) < w := by
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hwpi : w < Real.pi := by
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hh0 : (0 : ℝ) < w / 2 := by linarith
      have hhpi : w / 2 < Real.pi := by linarith
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hh0 hhpi)
  exact hcon1.mul hcon2

-- Helper: `cot ((π - w) / 2) = tan (w / 2)`, unconditionally.
private lemma xcot_cot_half (w : ℝ) :
    Real.cos ((Real.pi - w) / 2) / Real.sin ((Real.pi - w) / 2) =
      Real.sin (w / 2) / Real.cos (w / 2) := by
  have e : (Real.pi - w) / 2 = Real.pi / 2 - w / 2 := by ring
  rw [e, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

-- Helper: the half-angle identity `tan (w/2) = cot (w/2) - 2 * cot w`.
private lemma xcot_tan_half (w : ℝ) (hs1 : Real.sin (w / 2) ≠ 0)
    (hc1 : Real.cos (w / 2) ≠ 0) (hs : Real.sin w ≠ 0) :
    Real.sin (w / 2) / Real.cos (w / 2) =
      Real.cos (w / 2) / Real.sin (w / 2) - 2 * (Real.cos w / Real.sin w) := by
  have h2w : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) := by
    have h := Real.sin_two_mul (w / 2)
    rw [show 2 * (w / 2) = w from by ring] at h
    linarith [h]
  have hcos : Real.cos w = 2 * Real.cos (w / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (w / 2)
    rw [show 2 * (w / 2) = w from by ring] at h
    linarith [h]
  have hsq : Real.sin (w / 2) ^ 2 + Real.cos (w / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  field_simp
  linear_combination (Real.sin (w / 2) ^ 2 - Real.cos (w / 2) ^ 2) * h2w +
    (2 * Real.sin (w / 2) * Real.cos (w / 2)) * hcos +
    (2 * Real.sin (w / 2) * Real.cos (w / 2)) * hsq

-- Helper: the affine substitution `w = π - 2 * u`.
private lemma xcot_sub1 (x : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * (∫ u in Real.pi / 4..(Real.pi / 2 - x),
      u ^ n * (Real.cos u / Real.sin u)) =
    (1 / 2) * (∫ w in (2 * x)..(Real.pi / 2),
      (Real.pi - w) ^ n *
        (Real.cos ((Real.pi - w) / 2) / Real.sin ((Real.pi - w) / 2))) := by
  set f : ℝ → ℝ := fun w : ℝ => (Real.pi - w) ^ n *
    (Real.cos ((Real.pi - w) / 2) / Real.sin ((Real.pi - w) / 2)) with hf
  have hpt : ∀ u : ℝ, f (-2 * u + Real.pi) =
      (2 : ℝ) ^ n * (u ^ n * (Real.cos u / Real.sin u)) := by
    intro u
    have e1 : Real.pi - (-2 * u + Real.pi) = 2 * u := by ring
    have e1b : (2 * u) / 2 = u := by ring
    simp only [hf]
    rw [e1, e1b]
    ring
  have step1 : (2 : ℝ) ^ n * (∫ u in Real.pi / 4..(Real.pi / 2 - x),
      u ^ n * (Real.cos u / Real.sin u)) =
      ∫ u in Real.pi / 4..(Real.pi / 2 - x), f (-2 * u + Real.pi) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext u
    rw [hpt u]
  have hsub := intervalIntegral.integral_comp_mul_add f
    (show (-2 : ℝ) ≠ 0 by norm_num) (Real.pi) (a := Real.pi / 4)
    (b := Real.pi / 2 - x)
  rw [step1, hsub]
  have lim1 : -2 * (Real.pi / 4) + Real.pi = Real.pi / 2 := by ring
  have lim2 : -2 * (Real.pi / 2 - x) + Real.pi = 2 * x := by ring
  rw [lim1, lim2, smul_eq_mul, intervalIntegral.integral_symm]
  have hinv : (-2 : ℝ)⁻¹ = -(1 / 2) := by norm_num
  rw [hinv]
  ring

-- Helper: the scaling substitution `v = w / 2`.
private lemma xcot_sub2 (x : ℝ) (n : ℕ) :
    (∫ w in (2 * x)..(Real.pi / 2),
      ((1 : ℝ) / 2) * ((Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2)))) =
    (∫ v in x..(Real.pi / 4),
      (Real.pi - 2 * v) ^ n * (Real.cos v / Real.sin v)) := by
  set g : ℝ → ℝ := fun w : ℝ => ((1 : ℝ) / 2) *
    ((Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2))) with hg
  have hpt : ∀ v : ℝ, 2 * g (2 * v) =
      (Real.pi - 2 * v) ^ n * (Real.cos v / Real.sin v) := by
    intro v
    have e : 2 * v / 2 = v := by ring
    simp only [hg]
    rw [e]
    ring
  have hsub := intervalIntegral.integral_comp_mul_left g
    (show (2 : ℝ) ≠ 0 by norm_num) (a := x) (b := Real.pi / 4)
  have lim : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [lim] at hsub
  have h2 : (2 : ℝ) • (∫ v in x..(Real.pi / 4), g (2 * v)) =
      ∫ v in x..(Real.pi / 4), (Real.pi - 2 * v) ^ n * (Real.cos v / Real.sin v) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    ext v
    rw [hpt v]
  have h3 : (2 : ℝ) • (∫ v in x..(Real.pi / 4), g (2 * v)) =
      ∫ w in (2 * x)..(Real.pi / 2), g w := by
    rw [hsub, smul_eq_mul, smul_eq_mul]
    ring
  rw [← h2, h3]

-- Helper: pushing `(2 ^ k)` inside the primitive integral.
private lemma xcot_pow_push (k : ℕ) (x : ℝ) :
    (2 : ℝ) ^ k * (∫ u in Real.pi / 4..x, u ^ k * (Real.cos u / Real.sin u)) =
    (∫ u in Real.pi / 4..x, (2 * u) ^ k * (Real.cos u / Real.sin u)) := by
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext u
  rw [mul_pow]
  ring

/-- **Entry 15 of Chapter 9: integrals of $u^n \cot u$ at $\pi/2 - x$.** For an integer $k \ge 0$
and real $y$ write $F_k(y) = \int_{\pi/4}^{y} u^k \cot u \, du$. Let $n \ge 0$ be an integer. Then
for every integer $k$ with $0 \le k \le n$ and every real $y$ with $0 < y < \pi$, the function
$u \mapsto u^k \cot u$ is integrable on the interval between $\pi/4$ and $y$; and for every real
$x$ with $0 < x < \pi/2$,
$$2^n F_n(\pi/2 - x) = \sum_{k=0}^{n} (-1)^k \binom{n}{k} \pi^{n-k}
\bigl(F_k(2x) - 2^k F_k(x)\bigr) - \sum_{k=0}^{n} (-1)^k \binom{n}{k} \pi^{n-k} F_k(\pi/2).$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
Proves `Wanted` entry `ramanujan_part1_ch9_entry15_xcot`.
-/
theorem ramanujan_part1_ch9_entry15_xcot (n : ℕ) :
    (∀ k : ℕ, k ≤ n → ∀ y : ℝ, 0 < y → y < Real.pi →
      IntervalIntegrable
        (fun u : ℝ => u ^ k * (Real.cos u / Real.sin u))
        volume (Real.pi / 4) y) ∧
      ∀ x : ℝ, 0 < x → x < Real.pi / 2 →
        (2 : ℝ) ^ n * chapter9CotPrimitive n (Real.pi / 2 - x) =
          (∑ k ∈ range (n + 1),
            (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k) *
              (chapter9CotPrimitive k (2 * x) -
                (2 : ℝ) ^ k * chapter9CotPrimitive k x)) -
          ∑ k ∈ range (n + 1),
            (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k) *
              chapter9CotPrimitive k (Real.pi / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h14 : (0 : ℝ) < Real.pi / 4 := by positivity
  have h14b : Real.pi / 4 < Real.pi := by linarith
  constructor
  · intro k _ y hy0 hy
    exact xcot_pow_integrable k _ _ h14 h14b hy0 hy
  · intro x hx0 hx2
    have hx0' : (0 : ℝ) < 2 * x := by linarith
    have hx2' : 2 * x < Real.pi := by linarith
    have hpx : (0 : ℝ) < Real.pi / 2 - x := by linarith
    have hpx2 : Real.pi / 2 - x < Real.pi := by linarith
    have hh : (0 : ℝ) < Real.pi / 2 := by positivity
    have hh2 : Real.pi / 2 < Real.pi := by linarith
    have hxpi : x < Real.pi := by linarith
    have hInt : ∀ k : ℕ, k ≤ n → ∀ y : ℝ, 0 < y → y < Real.pi →
        IntervalIntegrable (fun u : ℝ => u ^ k * (Real.cos u / Real.sin u))
          MeasureTheory.volume (Real.pi / 4) y := by
      intro k _ y hy0 hy
      exact xcot_pow_integrable k _ _ h14 h14b hy0 hy
    have hbinA : ∀ u : ℝ, (Real.pi - u) ^ n * (Real.cos u / Real.sin u) =
        ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          (u ^ k * (Real.cos u / Real.sin u)) := by
      intro u
      rw [xcot_binom n u, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hbinB : ∀ u : ℝ, (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u) =
        ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          ((2 * u) ^ k * (Real.cos u / Real.sin u)) := by
      intro u
      rw [xcot_binom n (2 * u), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hmem : ∀ k ∈ range (n + 1), k ≤ n := by
      intro k hk
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have S1 : (∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
            (∫ u in Real.pi / 4..(2 * x), u ^ k * (Real.cos u / Real.sin u))) =
        ∫ u in Real.pi / 4..(2 * x),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u) :=
      xcot_sum_int n (2 * x) (fun k u => u ^ k) (fun u => (Real.pi - u) ^ n) hbinA
        (fun k hk => hInt k (hmem k hk) (2 * x) hx0' hx2')
    have S2 : (∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
            (∫ u in Real.pi / 4..(Real.pi / 2), u ^ k * (Real.cos u / Real.sin u))) =
        ∫ u in Real.pi / 4..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u) :=
      xcot_sum_int n (Real.pi / 2) (fun k u => u ^ k) (fun u => (Real.pi - u) ^ n)
        hbinA (fun k hk => hInt k (hmem k hk) (Real.pi / 2) hh hh2)
    have S3 : (∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
            ((2 : ℝ) ^ k * (∫ u in Real.pi / 4..x, u ^ k * (Real.cos u / Real.sin u)))) =
        ∫ u in Real.pi / 4..x,
          (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u) := by
      have hbase := xcot_sum_int n x (fun k u => (2 * u) ^ k)
        (fun u => (Real.pi - 2 * u) ^ n) hbinB (fun k hk => by
          have heq : (fun u : ℝ => (2 * u) ^ k * (Real.cos u / Real.sin u)) =
              (fun u : ℝ => (2 : ℝ) ^ k * (u ^ k * (Real.cos u / Real.sin u))) := by
            funext u
            rw [mul_pow]
            ring
          rw [heq]
          exact ((hInt k (hmem k hk) x hx0 hxpi).const_mul _))
      rw [← hbase]
      apply Finset.sum_congr rfl
      intro k _
      rw [xcot_pow_push k x]
    simp only [chapter9CotPrimitive]
    have hsplit : ∀ k ∈ range (n + 1),
        ((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          ((∫ u in Real.pi / 4..(2 * x), u ^ k * (Real.cos u / Real.sin u)) -
            (2 : ℝ) ^ k * (∫ u in Real.pi / 4..x, u ^ k * (Real.cos u / Real.sin u))) =
        (((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          (∫ u in Real.pi / 4..(2 * x), u ^ k * (Real.cos u / Real.sin u))) -
        (((-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k)) *
          ((2 : ℝ) ^ k * (∫ u in Real.pi / 4..x, u ^ k * (Real.cos u / Real.sin u)))) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl hsplit, sum_sub_distrib, S1, S3, S2]
    have hA1 := xcot_A_int n (Real.pi / 4) (Real.pi / 2) h14 h14b hh hh2
    have hA2 := xcot_A_int n (Real.pi / 2) (2 * x) hh hh2 hx0' hx2'
    have hadj : (∫ u in Real.pi / 4..(2 * x),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) =
        (∫ u in Real.pi / 4..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) +
        (∫ u in Real.pi / 2..(2 * x),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) :=
      (intervalIntegral.integral_add_adjacent_intervals hA1 hA2).symm
    have hsymmA : (∫ u in Real.pi / 2..(2 * x),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) =
        -(∫ u in (2 * x)..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) :=
      intervalIntegral.integral_symm _ _
    have hRHS : (∫ u in Real.pi / 4..(2 * x),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) -
        (∫ u in Real.pi / 4..x,
          (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u)) -
        (∫ u in Real.pi / 4..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) =
        -(∫ u in (2 * x)..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) -
        (∫ u in Real.pi / 4..x,
          (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u)) := by
      rw [hadj, hsymmA]
      ring
    have hG2 : IntervalIntegrable
        (fun w => ((1 : ℝ) / 2) *
          ((Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2))))
        MeasureTheory.volume (2 * x) (Real.pi / 2) :=
      (xcot_G_int n x hx0 hx2).const_mul _
    have hA3 := xcot_A_int n (2 * x) (Real.pi / 2) hx0' hx2' hh hh2
    have heq : Set.EqOn
        (fun w => ((1 : ℝ) / 2) *
          ((Real.pi - w) ^ n *
            (Real.cos ((Real.pi - w) / 2) / Real.sin ((Real.pi - w) / 2))))
        (fun w => ((1 : ℝ) / 2) *
          ((Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2))) -
          (Real.pi - w) ^ n * (Real.cos w / Real.sin w))
        [[2 * x, Real.pi / 2]] := by
      intro w hw
      show ((1 : ℝ) / 2) *
          ((Real.pi - w) ^ n *
            (Real.cos ((Real.pi - w) / 2) / Real.sin ((Real.pi - w) / 2))) =
        ((1 : ℝ) / 2) *
          ((Real.pi - w) ^ n * (Real.cos (w / 2) / Real.sin (w / 2))) -
          (Real.pi - w) ^ n * (Real.cos w / Real.sin w)
      rw [Set.mem_uIcc] at hw
      have hw0 : (0 : ℝ) < w := by
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hwpi : w < Real.pi := by
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hh0 : (0 : ℝ) < w / 2 := by linarith
      have hhpi : w / 2 < Real.pi := by linarith
      have hs1 : Real.sin (w / 2) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hh0 hhpi)
      have hc1 : Real.cos (w / 2) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith, by linarith⟩)
      have hs : Real.sin w ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hw0 hwpi)
      rw [xcot_cot_half w, xcot_tan_half w hs1 hc1 hs]
      ring
    have hLHS : (2 : ℝ) ^ n * (∫ u in Real.pi / 4..(Real.pi / 2 - x),
          u ^ n * (Real.cos u / Real.sin u)) =
        -(∫ u in (2 * x)..(Real.pi / 2),
          (Real.pi - u) ^ n * (Real.cos u / Real.sin u)) -
        (∫ u in Real.pi / 4..x,
          (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u)) := by
      rw [xcot_sub1 x n, ← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_congr heq,
        intervalIntegral.integral_sub hG2 hA3, xcot_sub2 x n,
        show (∫ v in x..(Real.pi / 4),
          (Real.pi - 2 * v) ^ n * (Real.cos v / Real.sin v)) =
          -(∫ u in Real.pi / 4..x,
            (Real.pi - 2 * u) ^ n * (Real.cos u / Real.sin u))
          from intervalIntegral.integral_symm _ _]
      ring
    rw [hLHS, hRHS]

end

end Entry15Xcot

end MathlibExt.Analysis.Ramanujan.Part1Ch9
