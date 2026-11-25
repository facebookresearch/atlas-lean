/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MathlibExt.Combinatorics.Enumerative.BuchstabTaylor
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Stream.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Taylor coefficients of the generalized Buchstab function

The integrated delay equation determines the first two rows of Taylor coefficients
and gives a recursion for the expansions about the later half-integers.
-/

open Set MeasureTheory

namespace MetaMathlibExt
namespace GeneralizedBuchstabTaylor

private theorem continuousOn_integrand {Ω : ℝ → ℝ} {n : ℝ}
    (hcont : ContinuousOn Ω (Icc 1 n)) :
    ContinuousOn (fun u ↦ Ω (u - 1) / (u - 1)) (Icc 2 (n + 1)) := by
  refine (hcont.comp (by fun_prop) (fun u hu ↦ ⟨?_, ?_⟩)).div (by fun_prop) ?_
  · linarith [hu.1]
  · linarith [hu.2]
  · intro u hu
    linarith [hu.1]

private theorem continuousOn_generalized {K : ℝ} {Ω : ℝ → ℝ}
    (h₁ : ∀ x ∈ Ico (1 : ℝ) 2, Ω x = 1)
    (h₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
    (n : ℕ) : ContinuousOn Ω (Icc 1 (n + 2 : ℝ)) := by
  have hbase : ContinuousOn Ω (Icc (1 : ℝ) 2) := by
    apply (continuousOn_const (c := (1 : ℝ))).congr
    intro x hx
    rcases hx.2.lt_or_eq with hlt | rfl
    · exact h₁ x ⟨hx.1, hlt⟩
    · simpa using h₂ 2 le_rfl
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have hintegrand := continuousOn_integrand ih
    rw [show (n : ℝ) + 2 + 1 = n + 3 by ring] at hintegrand
    have hn : (2 : ℝ) ≤ n + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hprim := intervalIntegral.continuousOn_primitive_interval'
      (μ := volume) (hintegrand.intervalIntegrable_of_Icc hn) left_mem_uIcc
    rw [uIcc_of_le hn] at hprim
    have hnext : ContinuousOn Ω (Icc (2 : ℝ) (n + 3)) :=
      (continuousOn_const.add (continuousOn_const.mul hprim)).congr (fun x hx ↦ h₂ x hx.1)
    have hunion := (hbase.union_of_isClosed hnext isClosed_Icc isClosed_Icc).mono
      Icc_subset_Icc_union_Icc
    simpa only [Nat.cast_succ, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hunion

private theorem integrated_step {K : ℝ} {Ω : ℝ → ℝ}
    (h₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
    {n : ℝ} (hn : 2 ≤ n) (hcont : ContinuousOn Ω (Icc 1 n))
    {z : ℝ} (hz : z ∈ Ico (-1 : ℝ) 1) :
    Ω (n + (1 + z) / 2) = Ω n +
      K * ∫ t in (-1 : ℝ)..z, Ω (n - 1 + (1 + t) / 2) / (2 * n - 1 + t) := by
  have hnx : n ≤ n + (1 + z) / 2 := by linarith [hz.1]
  have hcont' := continuousOn_integrand hcont
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hcont'.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc hn)
    ((hcont'.mono (Icc_subset_Icc hn (by linarith [hz.2]))).intervalIntegrable_of_Icc hnx)
  let F : ℝ → ℝ := fun u ↦ Ω (u - 1) / (u - 1)
  have hchange :
      (∫ t in (-1 : ℝ)..z, Ω (n - 1 + (1 + t) / 2) / (2 * n - 1 + t)) =
        ∫ u in n..(n + (1 + z) / 2), F u := by
    have hfun (t : ℝ) :
        Ω (n - 1 + (1 + t) / 2) / (2 * n - 1 + t) = (1 / 2) * F ((1 / 2) * t + (n + 1 / 2)) := by
      dsimp [F]
      rw [show 1 / 2 * t + (n + 1 / 2) - 1 = n - 1 + (1 + t) / 2 by ring,
        show 2 * n - 1 + t = 2 * (n - 1 + (1 + t) / 2) by ring, div_mul_eq_div_div]
      ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add F (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [show (1 / 2 : ℝ) * (-1) + (n + 1 / 2) = n by ring,
      show 1 / 2 * z + (n + 1 / 2) = n + (1 + z) / 2 by ring]
    norm_num
    ring
  rw [hchange, h₂ _ (hn.trans hnx), h₂ n hn, ← hadd]
  dsimp [F]
  ring

private theorem hasSum_geometric_convolution {a : ℕ → ℝ} {D : ℝ} (hD : 1 < D)
    {z L : ℝ} (hz : z ∈ Ico (-1 : ℝ) 1) (ha : HasSum (fun i ↦ a i * z ^ i) L) :
    HasSum (fun i ↦ (∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i - j) / D ^ (i - j) * a j) * z ^ i)
      (D * (L / (D + z))) := by
  have hD₀ : 0 < D := by linarith
  have hzD : |(-1 / D : ℝ) * z| < 1 := by
    rw [abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hD₀, one_div_mul_eq_div, div_lt_one hD₀]
    exact (abs_le.mpr ⟨hz.1, hz.2.le⟩).trans_lt hD
  have hg := hasSum_geometric_of_abs_lt_one hzD
  have hprod := hasSum_sum_range_mul_of_summable_norm ha.summable.norm hg.summable.norm
  rw [ha.tsum_eq, hg.tsum_eq] at hprod
  convert hprod using 1
  · ext i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hji : j ≤ i := by simpa using Finset.mem_range.mp hj
    have hzpow : z ^ i = z ^ j * z ^ (i - j) := by
      rw [← pow_add, Nat.add_sub_of_le hji]
    rw [hzpow, mul_pow, div_pow]
    ring
  · have hdenom : 1 - -1 / D * z = (D + z) / D := by field_simp; ring
    rw [hdenom, inv_div]
    ring

/-- Compare the coefficients after integrating the product with the geometric series. -/
private theorem coefficient_step {a b : ℕ → ℝ} {f g : ℝ → ℝ} {D K : ℝ}
    (hD : 1 < D)
    (ha : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ a i * z ^ i) (f z))
    (hb : ∀ z ∈ Ico (-1 : ℝ) 1, HasSum (fun i ↦ b i * z ^ i) (g z))
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (heq : ∀ z ∈ Ico (-1 : ℝ) 1,
      g z = f 1 + K * ∫ t in (-1 : ℝ)..z, f t / (D + t)) :
    let α (i : ℕ) := ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i - j) / D ^ (i - j) * a j
    b 0 = (∑' i, a i) - K / D * (∑' i : ℕ, (-1 : ℝ) ^ (i + 1) * α i / ((i : ℝ) + 1)) ∧
      ∀ i : ℕ, b (i + 1) = K * α i / (D * ((i : ℝ) + 1)) := by
  intro α
  let q (t : ℝ) := D * (f t / (D + t))
  have hq (z : ℝ) (hz : z ∈ Ico (-1 : ℝ) 1) :
      HasSum (fun i ↦ α i * z ^ i) (q z) :=
    hasSum_geometric_convolution hD hz (ha z hz)
  have hleft : (-1 : ℝ) ∈ Ico (-1 : ℝ) 1 := by constructor <;> norm_num
  have hnorm : Summable fun i ↦ ‖α i‖ := by
    simpa [norm_mul, norm_pow] using (hq (-1) hleft).summable.norm
  have hnorm_a : Summable fun i ↦ ‖a i‖ := by
    simpa [norm_mul, norm_pow] using (ha (-1) hleft).summable.norm
  have hEq (z : ℝ) (hz : z ∈ Ico (-1 : ℝ) 1) :
      g z = f 1 + K / D * ∫ t in (-1 : ℝ)..z, q t := by
    rw [heq z hz]
    dsimp [q]
    rw [intervalIntegral.integral_const_mul]
    field_simp
  have hz₀ : (0 : ℝ) ∈ Ico (-1 : ℝ) 1 := by constructor <;> norm_num
  have hI₀ := BuchstabTaylor.hasSum_integral hq hnorm hz₀
  have hcoeff : b = Stream'.cons (g 0) (fun i ↦ K * α i / (D * ((i : ℝ) + 1))) := by
    apply BuchstabTaylor.coefficients_eq hb
    intro z hz
    apply (hasSum_nat_add_iff' 1).mp
    simp only [Finset.sum_range_one, Stream'.cons, pow_zero, mul_one]
    have hdiff := ((BuchstabTaylor.hasSum_integral hq hnorm hz).sub hI₀).mul_left (K / D)
    have hvalue : K / D * ((∫ t in (-1 : ℝ)..z, q t) - (∫ t in (-1 : ℝ)..0, q t)) =
        g z - g 0 := by
      rw [hEq z hz, hEq 0 hz₀]
      ring
    rw [← hvalue]
    apply hdiff.congr_fun
    intro i
    simp [pow_succ, div_mul_eq_div_div]
    ring
  have hI₀' := hI₀.neg.congr_fun (g := fun i : ℕ ↦ (-1 : ℝ) ^ (i + 1) * α i / ((i : ℝ) + 1))
    (fun i ↦ by simp [pow_succ]; ring)
  refine ⟨?_, fun i ↦ congrFun hcoeff (i + 1)⟩
  rw [congrFun hcoeff 0, hEq 0 hz₀, (BuchstabTaylor.hasSum_endpoint hf ha hnorm_a).tsum_eq,
    hI₀'.tsum_eq]
  change _ + _ * _ = _ - _ * _
  ring

private theorem hasSum_binomial (k : ℕ) :
    HasSum (fun j : ℕ ↦ (-1 : ℝ) ^ (j + (k + 1) - 1) * ((j + (k + 1)).choose (k + 1) : ℝ) /
      (((j : ℝ) + ((k + 1 : ℕ) : ℝ)) * 2 ^ (j + (k + 1))))
      ((-1 : ℝ) ^ k / (3 ^ (k + 1) * ((k : ℝ) + 1))) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k
    (by norm_num : ‖(-1 / 2 : ℝ)‖ < 1)).mul_left
      ((-1 : ℝ) ^ k / (2 ^ (k + 1) * ((k : ℝ) + 1)))
  convert h using 1
  · ext j
    rw [show j + (k + 1) - 1 = j + k by omega, pow_add (-1 : ℝ),
      pow_add (2 : ℝ) j (k + 1), div_pow, Nat.cast_add, Nat.cast_one]
    have hchoose : ((j + k + 1).choose (k + 1) : ℝ) * (k + 1) =
        (j + k + 1 : ℝ) * ((j + k).choose k : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq (j + k) k).symm
    field_simp
    linear_combination hchoose
  · rw [show (1 - -1 / 2 : ℝ) = 3 / 2 by norm_num, div_pow]
    field_simp

end GeneralizedBuchstabTaylor

open GeneralizedBuchstabTaylor

set_option linter.unusedVariables false in
/-- **Recursion for the Taylor coefficients of the generalized Buchstab function.** Let $K > 0$,
let $\Omega$ be a real function with $\Omega(x) = 1$ for $1 \le x < 2$ and
$\Omega(x) = 1 + K \int_2^x \frac{\Omega(u-1)}{u-1}\,du$ for $x \ge 2$, and let $c_{n,i}$
($n, i \ge 0$) be real numbers such that for every integer $n \ge 1$ and every real $z$ with
$-1 \le z < 1$ the series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to
$\Omega(n + (1+z)/2)$. Then $c_{1,0} = 1$, $c_{1,i} = 0$ for every $i \ge 1$,

$$c_{2,0} = 1 + K \sum_{i \ge 0} \frac{(-1)^i}{(i+1)\,2^{i+1}},$$

$$c_{2,i} = K \sum_{j \ge 0} \frac{(-1)^{j+i-1} \binom{j+i}{i}}{(j+i)\,2^{j+i}} \quad (i \ge 1),$$

and for every $n \ge 3$, writing
$\alpha_{n,m} = \sum_{j=0}^{m} \frac{(-1)^{m-j}}{(2n-1)^{m-j}}\, c_{n-1,j}$ for $m \ge 0$,

$$c_{n,0} = \sum_{i \ge 0} c_{n-1,i} -
\frac{K}{2n-1} \sum_{i \ge 0} \frac{(-1)^{i+1} \alpha_{n,i}}{i+1}$$

and $c_{n,i} = \dfrac{K\, \alpha_{n,i-1}}{(2n-1)\, i}$ for every $i \ge 1$.

Here $c_{2,0} = 1 + K \log(3/2)$. The printed statement of Theorem 4 has
$c_{2,0} = 1 + K \sum_{i \ge 1} 1/(i\, 2^i)$, which omits the sign $(-1)^{i-1}$.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 4
(`integers-2024-A7-thm-4`). -/
public theorem generalized_buchstab_taylor_coeff_recursion (K : ℝ) (hK : 0 < K)
    (Ω : ℝ → ℝ) (hΩ₁ : ∀ x ∈ Set.Ico (1 : ℝ) 2, Ω x = 1)
    (hΩ₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (Ω (n + (1 + z) / 2))) :
    c 1 0 = 1 ∧ (∀ i : ℕ, 1 ≤ i → c 1 i = 0) ∧
      c 2 0 = 1 + K * ∑' i : ℕ, (-1 : ℝ) ^ i / (((i : ℝ) + 1) * 2 ^ (i + 1)) ∧
      (∀ i : ℕ, 1 ≤ i → c 2 i =
        K * ∑' j : ℕ, (-1 : ℝ) ^ (j + i - 1) * ((j + i).choose i : ℝ) /
          (((j : ℝ) + i) * 2 ^ (j + i))) ∧
      (∀ n : ℕ, 3 ≤ n → c n 0 = ∑' i, c (n - 1) i -
        K / (2 * (n : ℝ) - 1) * ∑' i : ℕ, (-1 : ℝ) ^ (i + 1) *
          (∑ j ∈ Finset.range (i + 1),
            (-1 : ℝ) ^ (i - j) / (2 * (n : ℝ) - 1) ^ (i - j) * c (n - 1) j) / ((i : ℝ) + 1)) ∧
      (∀ n : ℕ, 3 ≤ n → ∀ i : ℕ, 1 ≤ i → c n i =
        K * (∑ j ∈ Finset.range i,
            (-1 : ℝ) ^ (i - 1 - j) / (2 * (n : ℝ) - 1) ^ (i - 1 - j) * c (n - 1) j) /
          ((2 * (n : ℝ) - 1) * i)) := by
  have hfirst : c 1 = Stream'.cons 1 (fun _ ↦ 0) := by
    apply BuchstabTaylor.coefficients_eq (hc 1 le_rfl)
    intro z hz
    rw [Nat.cast_one, hΩ₁ _ ⟨by linarith [hz.1], by linarith [hz.2]⟩]
    apply (hasSum_nat_add_iff' 1).mp
    simp [Stream'.cons, hasSum_zero]
  have hstep (n : ℕ) (hn : 2 ≤ n) :
      let D := 2 * (n : ℝ) - 1
      let α (i : ℕ) :=
        ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i - j) / D ^ (i - j) * c (n - 1) j
      c n 0 = (∑' i, c (n - 1) i) -
        K / D * (∑' i : ℕ, (-1 : ℝ) ^ (i + 1) * α i / ((i : ℝ) + 1)) ∧
        ∀ i : ℕ, c n (i + 1) = K * α i / (D * ((i : ℝ) + 1)) := by
    let f (k : ℕ) (z : ℝ) := Ω (k + (1 + z) / 2)
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcont : ContinuousOn Ω (Icc 1 (n : ℝ)) := by
      have h := continuousOn_generalized hΩ₁ hΩ₂ (n - 2)
      have hend : (↑(n - 2) : ℝ) + 2 = n := by exact_mod_cast Nat.sub_add_cancel hn
      rwa [hend] at h
    have hf : ContinuousOn (f (n - 1)) (Icc (-1 : ℝ) 1) := by
      refine hcont.comp (by fun_prop) fun z hz ↦ ?_
      simp only [hcast]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    apply coefficient_step (D := 2 * (n : ℝ) - 1) (by linarith)
      (hc (n - 1) (by omega)) (hc n (by omega)) hf
    intro z hz
    have h := integrated_step hΩ₂ hn' hcont hz
    simpa [f, hcast] using h
  have hα₂ (i : ℕ) : (∑ j ∈ Finset.range (i + 1),
      (-1 : ℝ) ^ (i - j) / (2 * (↑(2 : ℕ) : ℝ) - 1) ^ (i - j) * c (2 - 1) j) =
      (-1 : ℝ) ^ i / 3 ^ i := by
    rw [Finset.sum_eq_single 0]
    · norm_num [hfirst, Stream'.cons]
    · intro j _ hj
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      norm_num [hfirst, Stream'.cons]
    · simp
  refine ⟨congrFun hfirst 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact congrFun hfirst (j + 1)
  · have hzero : (∑' i, c 2 i * (0 : ℝ) ^ i) = Ω (2 + (1 + 0) / 2) :=
      (hc 2 (by omega) 0 (by constructor <;> norm_num)).tsum_eq
    have hvalue : Ω (2 + (1 + 0) / 2) = 1 + K * Real.log (3 / 2) := by
      norm_num
      rw [hΩ₂ _ (by norm_num)]
      congr 2
      calc
        (∫ u in (2 : ℝ)..5 / 2, Ω (u - 1) / (u - 1)) =
            ∫ u in (2 : ℝ)..5 / 2, (u - 1)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at hu
          change Ω (u - 1) / (u - 1) = (u - 1)⁻¹
          rw [hΩ₁ _ ⟨by linarith [hu.1], by linarith [hu.2]⟩, one_div]
        _ = Real.log (3 / 2) := by
          simp only [sub_eq_add_neg]
          rw [intervalIntegral.integral_comp_add_right (f := fun x : ℝ ↦ x⁻¹)]
          norm_num
    have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (by norm_num : |(-1 / 2 : ℝ)| < 1)).neg
    have hseries : HasSum (fun i : ℕ ↦ (-1 : ℝ) ^ i / (((i : ℝ) + 1) * 2 ^ (i + 1)))
        (Real.log (3 / 2)) := by
      convert hlog using 1
      · ext i
        rw [div_pow, pow_succ (-1 : ℝ)]
        field_simp
      · norm_num
    rw [hseries.tsum_eq, ← hvalue, ← hzero, tsum_eq_single 0]
    · simp
    · intro i hi
      simp [zero_pow hi]
  · intro i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [(hstep 2 (by omega)).2 k]
    dsimp only
    rw [hα₂, (hasSum_binomial k).tsum_eq]
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub, Nat.cast_succ]
    rw [pow_succ, div_mul_eq_div_div, div_mul_eq_div_div, div_mul_eq_div_div]
    ring
  · exact fun n hn ↦ (hstep n (by omega)).1
  · intro n hn i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simpa using (hstep n (by omega)).2 k

end MetaMathlibExt
