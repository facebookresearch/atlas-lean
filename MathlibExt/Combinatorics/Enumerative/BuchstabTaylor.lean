/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Taylor coefficients of the Buchstab function

The integrated Buchstab equation gives a recursion for the coefficients of the Taylor
expansions centered at the midpoints of successive unit intervals.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace MetaMathlibExt
namespace BuchstabTaylor

private theorem continuousOn_buchstab {ω : ℝ → ℝ}
    (h₁ : ∀ x ∈ Icc (1 : ℝ) 2, ω x = 1 / x)
    (h₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (n : ℕ) : ContinuousOn ω (Icc 1 (n + 2 : ℝ)) := by
  have hbase : ContinuousOn ω (Icc (1 : ℝ) 2) :=
    (continuousOn_const.div continuousOn_id (fun x hx ↦ by
      change x ≠ 0
      linarith [hx.1])).congr h₁
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have hn : (1 : ℝ) ≤ n + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hprim := intervalIntegral.continuousOn_primitive_interval'
      (μ := volume) (ih.intervalIntegrable_of_Icc hn) left_mem_uIcc
    rw [uIcc_of_le hn] at hprim
    push_cast
    have hcomp : ContinuousOn (fun x ↦ ∫ t in (1 : ℝ)..(x - 1), ω t)
        (Icc 2 (↑n + 1 + 2)) :=
      hprim.comp (by fun_prop) fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hnext : ContinuousOn ω (Icc (2 : ℝ) (↑n + 1 + 2)) := by
      refine (((continuousOn_const (c := (1 : ℝ))).add hcomp).div continuousOn_id ?_).congr ?_
      · intro x hx
        change x ≠ 0
        linarith [hx.1]
      · intro x hx
        change ω x = (1 + ∫ t in (1 : ℝ)..(x - 1), ω t) / x
        exact (eq_div_iff (by linarith [hx.1] : x ≠ 0)).2 ((mul_comm _ _).trans (h₂ x hx.1))
    exact (hbase.union_of_isClosed hnext isClosed_Icc isClosed_Icc).mono
      Icc_subset_Icc_union_Icc

private theorem term_bound (a : ℕ → ℝ) (i : ℕ) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    ‖a i * z ^ i‖ ≤ ‖a i‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (abs_le.mpr hz))

/- Uniform convergence extends the given half-open expansion to the right endpoint. -/
public theorem hasSum_endpoint {a : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hs : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ a i * z ^ i) (f z))
    (ha : Summable fun i ↦ ‖a i‖) : HasSum a (f 1) := by
  have heq : EqOn (fun z ↦ ∑' i, a i * z ^ i) f (Ico (-1 : ℝ) 1) :=
    fun z hz ↦ (hs z hz).tsum_eq
  have hcont := continuousOn_tsum (f := fun i z ↦ a i * z ^ i)
    (fun i ↦ by fun_prop) ha (term_bound a)
  have hclosed := heq.of_subset_closure hcont hf Ico_subset_Icc_self
    (by rw [closure_Ico (by norm_num : (-1 : ℝ) ≠ 1)])
  have h := hclosed (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
  simp only [one_pow, mul_one] at h
  rw [← h]
  exact (Summable.of_norm ha).hasSum

public theorem hasSum_integral {a : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ a i * z ^ i) (f z))
    (ha : Summable fun i ↦ ‖a i‖) {z : ℝ} (hz : z ∈ Ico (-1 : ℝ) 1) :
    HasSum (fun i ↦ a i * ((z ^ (i + 1) - (-1 : ℝ) ^ (i + 1)) / (i + 1)))
      (∫ t in (-1 : ℝ)..z, f t) := by
  have hmem {t : ℝ} (ht : t ∈ uIoc (-1 : ℝ) z) : t ∈ Ico (-1 : ℝ) 1 := by
    rw [uIoc_of_le hz.1] at ht
    exact ⟨ht.1.le, ht.2.trans_lt hz.2⟩
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i t ↦ a i * t ^ i) (fun i _ ↦ ‖a i‖)
    (fun i ↦ (by fun_prop : Continuous (fun t : ℝ ↦ a i * t ^ i)).aestronglyMeasurable)
    (fun i ↦ ae_of_all _ fun _ ht ↦ term_bound a i (Ico_subset_Icc_self (hmem ht)))
    (ae_of_all _ fun _ _ ↦ ha) intervalIntegrable_const
    (ae_of_all _ fun t ht ↦ hs t (hmem ht))
  simpa only [intervalIntegral.integral_const_mul, integral_pow] using h

public theorem coefficients_eq {a b : ℕ → ℝ} {f : ℝ → ℝ}
    (ha : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ a i * z ^ i) (f z))
    (hb : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ b i * z ^ i) (f z)) : a = b := by
  have series (d : ℕ → ℝ) (hd : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ d i * z ^ i) (f z)) :
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ d) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with z hz
    simpa [mul_comm] using hd z ⟨hz.1.le, hz.2⟩
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    ((series a ha).eq_formalMultilinearSeries (series b hb))

/-- Subtract the integrated Buchstab equation at the left endpoint and change variables. -/
private theorem integrated_equation {ω : ℝ → ℝ}
    (h₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    {n : ℝ} (hn : 1 ≤ n) (hcont : ContinuousOn ω (Icc 1 (n + 2)))
    {z : ℝ} (hz : z ∈ Ico (-1 : ℝ) 1) :
    (2 * n + 3 + z) * ω (n + 1 + (1 + z) / 2) =
      2 * (n + 1) * ω (n + 1) + ∫ t in (-1 : ℝ)..z, ω (n + (1 + t) / 2) := by
  have hx : n ≤ n + (1 + z) / 2 := by linarith [hz.1]
  have hend : n + (1 + z) / 2 ≤ n + 2 := by linarith [hz.2]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) ((hcont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc hn)
    ((hcont.mono (Icc_subset_Icc hn hend)).intervalIntegrable_of_Icc hx)
  have hleft := h₂ (n + 1) (by linarith)
  have hright := h₂ (n + 1 + (1 + z) / 2) (by linarith)
  rw [add_sub_cancel_right] at hleft
  rw [show n + 1 + (1 + z) / 2 - 1 = n + (1 + z) / 2 by ring] at hright
  have hchange : (∫ t in (-1 : ℝ)..z, ω (n + (1 + t) / 2)) =
      2 * ∫ t in n..(n + (1 + z) / 2), ω t := by
    simp_rw [show ∀ t : ℝ, n + (1 + t) / 2 = (1 / 2) * t + (n + 1 / 2) by intro t; ring]
    rw [intervalIntegral.integral_comp_mul_add ω (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    norm_num
  rw [hchange]
  linarith only [hright, hleft, hadd]

/-- Compare the constant term and the tail after integrating the preceding row. -/
private theorem coefficient_step {a b : ℕ → ℝ} {f g : ℝ → ℝ} {D K : ℝ}
    (ha : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ a i * z ^ i) (f z))
    (hb : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ b i * z ^ i) (g z))
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (heq : ∀ z ∈ Ico (-1 : ℝ) 1, (D + z) * g z = K * f 1 + ∫ t in (-1 : ℝ)..z, f t) :
    D * b 0 = ∑' i, a i * (K + (-1 : ℝ) ^ i / (i + 1)) ∧
      ∀ i : ℕ, D * b (i + 1) = a i / (i + 1) - b i := by
  -- At the left endpoint every power has norm one.
  have hnorm : Summable fun i ↦ ‖a i‖ := by
    simpa [norm_mul, norm_pow] using
      (ha (-1) (by constructor <;> norm_num)).summable.norm
  let A := K * f 1 + ∫ t in (-1 : ℝ)..0, f t
  have hz₀ : (0 : ℝ) ∈ Ico (-1 : ℝ) 1 := by constructor <;> norm_num
  have hI := hasSum_integral ha hnorm hz₀
  have hA : HasSum (fun i : ℕ ↦ a i * (K + (-1 : ℝ) ^ i / (i + 1))) A := by
    apply (((hasSum_endpoint hf ha hnorm).mul_left K).add hI).congr_fun
    intro i
    simp [pow_succ]
    ring
  -- Remove the constant term and the product z * g z before shifting the index.
  have hcoeff : (fun i ↦ D * b i) =
      Stream'.cons A (fun i ↦ a i / (i + 1) - b i) := by
    apply coefficients_eq (f := fun z ↦ D * g z)
    · intro z hz
      simpa only [mul_assoc] using (hb z hz).mul_left D
    · intro z hz
      apply (hasSum_nat_add_iff' 1).mp
      simp only [Finset.sum_range_one, Stream'.cons, pow_zero, mul_one]
      have hdiff := ((hasSum_integral ha hnorm hz).sub hI).sub ((hb z hz).mul_right z)
      have hvalue : ((∫ t in (-1 : ℝ)..z, f t) - (∫ t in (-1 : ℝ)..0, f t)) - g z * z =
          D * g z - A := by
        dsimp [A]
        linarith only [heq z hz]
      rw [← hvalue]
      apply hdiff.congr_fun
      intro i
      simp [pow_succ]
      ring
  exact ⟨(congrFun hcoeff 0).trans hA.tsum_eq.symm, fun i ↦ congrFun hcoeff (i + 1)⟩

end BuchstabTaylor

open BuchstabTaylor

/-- **Recursion for the Taylor coefficients of the Buchstab function.** Let $\omega$ be a real
function with $\omega(x) = 1/x$ for $1 \le x \le 2$ and
$x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for $x \ge 2$, and let $c_{n,i}$ ($n, i \ge 0$)
be real numbers such that for every integer $n \ge 1$ and every real $z$ with $-1 \le z < 1$ the
series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to $\omega(n + (1+z)/2)$. Then
$c_{1,i} = \frac{2}{3} \left(-\frac{1}{3}\right)^i$ for every $i \ge 0$, and for every $n \ge 1$

$$c_{n+1,0} = \frac{1}{2n+3} \sum_{i \ge 0} c_{n,i} \left(2(n+1) + \frac{(-1)^i}{i+1}\right)$$

and, for every $i \ge 1$,

$$c_{n+1,i} = \frac{1}{2n+3} \left(\frac{c_{n,i-1}}{i} - c_{n+1,i-1}\right).$$

The printed statement of Theorem 3 has $c_{n,i}/n$ in place of $c_{n,i-1}/i$; the recursion above
is the identity $(2n+3) c_{n+1,i} + c_{n+1,i-1} = c_{n,i-1}/i$ derived in the paper's proof.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 3
(`integers-2024-A7-thm-3`). -/
public theorem buchstab_taylor_coeff_recursion (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (ω (n + (1 + z) / 2))) :
    (∀ i, c 1 i = 2 / 3 * (-1 / 3 : ℝ) ^ i) ∧
      (∀ n : ℕ, 1 ≤ n → c (n + 1) 0 =
        (∑' i, c n i * (2 * ((n : ℝ) + 1) + (-1 : ℝ) ^ i / ((i : ℝ) + 1))) /
          (2 * (n : ℝ) + 3)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
        c (n + 1) i = (c n (i - 1) / i - c (n + 1) (i - 1)) / (2 * (n : ℝ) + 3)) := by
  constructor
  · apply congrFun
    apply coefficients_eq (hc 1 le_rfl)
    intro z hz
    rw [Nat.cast_one, hω₁ _ ⟨by linarith [hz.1], by linarith [hz.2]⟩]
    have hr : |(-1 / 3 : ℝ) * z| < 1 := abs_lt.mpr
      ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have hgeom := (hasSum_geometric_of_abs_lt_one hr).mul_left (2 / 3)
    rw [show 1 + (1 + z) / 2 = 3 / 2 * (1 - (-1 / 3) * z) by ring, one_div, mul_inv_rev]
    convert hgeom using 1
    · ext i
      ring
    · ring
  have hstep (n : ℕ) (hn : 1 ≤ n) :
      (2 * n + 3 : ℝ) * c (n + 1) 0 =
        ∑' i, c n i * (2 * ((n : ℝ) + 1) + (-1 : ℝ) ^ i / (i + 1)) ∧
      ∀ j : ℕ, (2 * n + 3 : ℝ) * c (n + 1) (j + 1) = c n j / (j + 1) - c (n + 1) j := by
    let f (k : ℕ) (z : ℝ) := ω (k + (1 + z) / 2)
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hcont := continuousOn_buchstab hω₁ hω₂ n
    have hf : ContinuousOn (f n) (Icc (-1 : ℝ) 1) :=
      hcont.comp (by fun_prop) fun z hz ↦
        ⟨by linarith [hz.1], by linarith [hz.2]⟩
    apply coefficient_step (f := f n) (g := f (n + 1)) (D := 2 * n + 3) (K := 2 * (n + 1))
      (hc n hn) (hc (n + 1) (by omega)) hf
    intro z hz
    simpa [f] using integrated_equation hω₂ hn' hcont hz
  constructor
  · intro n hn
    apply (eq_div_iff (by positivity)).mpr
    simpa only [mul_comm (c (n + 1) 0)] using (hstep n hn).1
  · intro n hn i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    apply (eq_div_iff (by positivity)).mpr
    simpa [mul_comm (c (n + 1) (j + 1))] using (hstep n hn).2 j

end MetaMathlibExt
