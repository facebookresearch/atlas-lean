/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosinePowerAreaRecurrence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosineAlternatingIntegralLimit

/-!
# Double-factorial sums for limiting cosine-power areas

The double-factorial normalization turns the two-step area recurrence into a sum,
with initial values at exponents one and two.

## References

* Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer
  Sequences **28** (2025), Article 25.2.3, pp. 1–31, Theorems 3 and 4, and Lemma 11 and §6
  for the first exponent. <https://cs.uwaterloo.ca/journals/JIS/VOL28/Dresden/dresden4.pdf>
* Henry W. Gould and Jocelyn Quaintance, *Double Fun with Double Factorials*, Mathematics
  Magazine **85** (2012), pp. 177–192, for double-factorial background cited in §4.
-/

open Real Filter Topology Set intervalIntegral

namespace MetaMathlibExt

private lemma signed_sin_nonneg {x : ℝ} {i : ℕ}
    (h₁ : i * π ≤ x) (h₂ : x ≤ (i + 1 : ℝ) * π) : 0 ≤ (-1 : ℝ) ^ i * sin x := by
  rw [show x = (x - i * π) + i * π by ring, sin_add_nat_mul_pi, ← mul_assoc, ← pow_add]
  simp only [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr h₁) (by linarith)

-- The two sine factors have equal signs on the first interval and opposite signs on the second.
private lemma integral_abs_cos_sub_cells {k : ℝ} {i : ℕ} (hi : 2 * (i + 1 : ℝ) ≤ k - 1)
    (hk : 1 < k) :
    let a (j : ℕ) := (j : ℝ) * 2 * π / (k - 1)
    let b (j : ℕ) := (j : ℝ) * 2 * π / (k + 1)
    (∫ x in a i..a (i + 1), |cos x - cos (k * x)|) =
      (∫ x in a i..b (i + 1), cos x - cos (k * x)) -
        ∫ x in b (i + 1)..a (i + 1), cos x - cos (k * x) := by
  dsimp only
  let a (j : ℕ) := (j : ℝ) * 2 * π / (k - 1)
  let b (j : ℕ) := (j : ℝ) * 2 * π / (k + 1)
  change (∫ x in a i..a (i + 1), |cos x - cos (k * x)|) = _
  have hd : 0 < k - 1 := sub_pos.mpr hk
  have he : 0 < k + 1 := by linarith
  have hab (j : ℕ) : b j ≤ a j := by
    apply div_le_div_of_nonneg_left (by positivity) hd
    linarith
  have hba (j : ℕ) (hj : 2 * (j : ℝ) ≤ k - 1) : a j ≤ b (j + 1) := by
    dsimp [a, b]
    rw [div_le_div_iff₀ hd he, Nat.cast_add, Nat.cast_one]
    have h : (j : ℝ) * (k + 1) ≤ (j + 1 : ℝ) * (k - 1) := by nlinarith only [hj]
    convert mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * π) using 1 <;> ring
  have hcut := hba i (by linarith : 2 * (i : ℝ) ≤ k - 1)
  have hc : Continuous (fun x : ℝ => |cos x - cos (k * x)|) := by fun_prop
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable (a i) (b (i + 1)))
    (hc.intervalIntegrable (b (i + 1)) (a (i + 1))), sub_eq_add_neg, ← integral_neg]
  have hu (x : ℝ) (hx : x ∈ Icc (a i) (a (i + 1))) :
      0 ≤ (-1 : ℝ) ^ i * sin ((k - 1) * x / 2) := by
    have h₁ := (div_le_iff₀ hd).mp hx.1
    have h₂ := (le_div_iff₀ hd).mp hx.2
    apply signed_sin_nonneg
    · linarith only [h₁]
    · simp only [Nat.cast_add, Nat.cast_one] at h₂
      linarith only [h₂]
  have hv (x : ℝ) (j : ℕ) (hx : x ∈ Icc (b j) (b (j + 1))) :
      0 ≤ (-1 : ℝ) ^ j * sin ((k + 1) * x / 2) := by
    have h₁ := (div_le_iff₀ he).mp hx.1
    have h₂ := (le_div_iff₀ he).mp hx.2
    apply signed_sin_nonneg
    · linarith only [h₁]
    · simp only [Nat.cast_add, Nat.cast_one] at h₂
      linarith only [h₂]
  have hcos (x : ℝ) : cos x - cos (k * x) =
      2 * (sin ((k - 1) * x / 2) * sin ((k + 1) * x / 2)) := by
    rw [cos_sub_cos, show (x + k * x) / 2 = (k + 1) * x / 2 by ring,
      show (x - k * x) / 2 = -((k - 1) * x / 2) by ring, sin_neg]
    ring
  have hsign (x : ℝ) (hx : x ∈ Icc (a i) (a (i + 1))) : cos x - cos (k * x) =
      2 * (((-1 : ℝ) ^ i * sin ((k - 1) * x / 2)) *
        ((-1 : ℝ) ^ i * sin ((k + 1) * x / 2))) := by
    rw [hcos]
    have hsq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [mul_mul_mul_comm, hsq, one_mul]
  congr 1
  · apply integral_congr
    rw [uIcc_of_le hcut]
    intro x hx
    have hx' : x ∈ Icc (a i) (a (i + 1)) := ⟨hx.1, hx.2.trans (hab _)⟩
    change |cos x - cos (k * x)| = cos x - cos (k * x)
    apply abs_of_nonneg
    rw [hsign x hx']
    exact mul_nonneg (by norm_num) (mul_nonneg (hu x hx') (hv x i ⟨(hab _).trans hx.1, hx.2⟩))
  · apply integral_congr
    rw [uIcc_of_le (hab _)]
    intro x hx
    have hx' : x ∈ Icc (a i) (a (i + 1)) := ⟨hcut.trans hx.1, hx.2⟩
    change |cos x - cos (k * x)| = -(cos x - cos (k * x))
    rw [abs_of_nonpos]
    have h := hv x (i + 1) ⟨hx.1, hx.2.trans (hba (i + 1) (by simpa using hi))⟩
    rw [pow_succ, mul_neg_one, neg_mul, neg_nonneg] at h
    rw [hsign x hx']
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (mul_nonpos_of_nonneg_of_nonpos (hu x hx') h)

private lemma norm_integral_cos_sub_le (k a b : ℝ) :
    ‖(∫ x in a..b, cos x - cos (k * x))‖ ≤ 2 * |b - a| := by
  apply norm_integral_le_of_norm_le_const
  intro x _
  simp only [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by linarith [abs_cos_le_one x, abs_cos_le_one (k * x)])

private lemma norm_integral_abs_cos_sub_le (k a b : ℝ) :
    ‖(∫ x in a..b, |cos x - cos (k * x)|)‖ ≤ 2 * |b - a| := by
  apply norm_integral_le_of_norm_le_const
  intro x _
  simp only [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by linarith [abs_cos_le_one x, abs_cos_le_one (k * x)])

private noncomputable def signedCell (m i : ℕ) : ℝ :=
    (∫ x in ((i : ℝ) * 2 * π / ((2 * m : ℝ) - 1))..
        (((i + 1 : ℕ) : ℝ) * 2 * π / ((2 * m : ℝ) + 1)),
      cos x - cos ((2 * m : ℝ) * x)) -
    ∫ x in (((i + 1 : ℕ) : ℝ) * 2 * π / ((2 * m : ℝ) + 1))..
        (((i + 1 : ℕ) : ℝ) * 2 * π / ((2 * m : ℝ) - 1)),
      cos x - cos ((2 * m : ℝ) * x)

private lemma cosPowArea_one_sub_sum_le {m : ℕ} (hm : 0 < m) :
    ‖cosPowArea 1 (2 * m) - ∑ i ∈ Finset.range m, signedCell m i‖ ≤ 6 * π / (2 * m - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let k : ℝ := 2 * ((t + 1 : ℕ) : ℝ)
  let a (j : ℕ) := (j : ℝ) * 2 * π / (k - 1)
  let b (j : ℕ) := (j : ℝ) * 2 * π / (k + 1)
  let g (x : ℝ) := |cos x - cos (k * x)|
  have hk : 1 < k := by
    simp only [k, Nat.cast_add, Nat.cast_one]
    linarith only [Nat.cast_nonneg (α := ℝ) t]
  have hd : 0 < k - 1 := by linarith
  have he : 0 < k + 1 := by linarith
  have ha : a t ≤ π := by
    dsimp [a]
    rw [div_le_iff₀ hd]
    simp only [k, Nat.cast_add, Nat.cast_one]
    linarith only [pi_pos]
  have hb : a t ≤ b (t + 1) := by
    dsimp [a, b]
    rw [div_le_div_iff₀ hd he, Nat.cast_add, Nat.cast_one]
    have h : (t : ℝ) * (k + 1) ≤ (t + 1 : ℝ) * (k - 1) := by
      simp only [k, Nat.cast_add, Nat.cast_one]
      nlinarith
    convert mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * π) using 1 <;> ring
  have hab : ∀ j, b j ≤ a j := fun j =>
    div_le_div_of_nonneg_left (by positivity) hd (by linarith)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have hsum : ∑ i ∈ Finset.range t, signedCell (t + 1) i = ∫ x in (0 : ℝ)..a t, g x := by
    rw [← show a 0 = 0 by simp [a], ← sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (a := a) (n := t) (fun i _ => hc.intervalIntegrable (a i) (a (i + 1)))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hit : i + 1 ≤ t := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hit' : (i : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hit
    have hsmall : 2 * (i + 1 : ℝ) ≤ k - 1 := by
      simp only [k, Nat.cast_add, Nat.cast_one]
      linarith
    exact (integral_abs_cos_sub_cells hsmall hk).symm
  have hπ : π - a t = π / (k - 1) := by
    dsimp [a]
    field_simp
    simp only [k, Nat.cast_add, Nat.cast_one]
    ring
  have hlast : a (t + 1) - a t = 2 * π / (k - 1) := by
    simp only [a, Nat.cast_add, Nat.cast_one, ← sub_div]
    congr 1
    ring
  have htail : ‖(∫ x in a t..π, g x)‖ ≤ 2 * (π / (k - 1)) := by
    have h := norm_integral_abs_cos_sub_le k (a t) π
    rwa [abs_of_nonneg (sub_nonneg.mpr ha), hπ] at h
  have hcell : ‖signedCell (t + 1) t‖ ≤ 2 * (2 * π / (k - 1)) := by
    dsimp only [signedCell]
    calc
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 * |b (t + 1) - a t| + 2 * |a (t + 1) - b (t + 1)| :=
        add_le_add (norm_integral_cos_sub_le _ _ _) (norm_integral_cos_sub_le _ _ _)
      _ = _ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (sub_nonneg.mpr (hab _)), ← mul_add]
        rw [show b (t + 1) - a t + (a (t + 1) - b (t + 1)) = a (t + 1) - a t by ring, hlast]
  rw [Finset.sum_range_succ, hsum]
  have harea : cosPowArea 1 (2 * (t + 1)) = ∫ x in (0 : ℝ)..π, g x := by
    simp only [cosPowArea, g, k, pow_one, Nat.cast_mul, Nat.cast_ofNat]
  rw [harea, ← integral_add_adjacent_intervals (hc.intervalIntegrable 0 (a t))
    (hc.intervalIntegrable (a t) π), add_sub_add_left_eq_sub]
  change _ ≤ 6 * π / (k - 1)
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add htail hcell
    _ = _ := by ring

private lemma tendsto_cosPowArea_one : Tendsto (cosPowArea 1) atTop (𝓝 (8 / π)) := by
  have hsum : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, signedCell m i) atTop (𝓝 (8 / π)) := by
    have h := tendsto_sum_integral_cos_sub_cos_even_odd (q := 1) (by decide)
    convert h using 1
    · funext m
      apply Finset.sum_bij (fun i _ => i + 1)
      · intro i hi
        simp only [Finset.mem_range] at hi
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i _ j _ h
        exact Nat.add_right_cancel h
      · intro j hj
        obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
        exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i _
        simp only [Nat.cast_add, Nat.cast_one, one_mul, add_sub_cancel_right, signedCell]
    · simp
  have herr : Tendsto (fun m : ℕ => cosPowArea 1 (2 * m) -
      ∑ i ∈ Finset.range m, signedCell m i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun m : ℕ => 6 * π / (2 * m - 1)) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
      exact cosPowArea_one_sub_sum_le hm
    · have h : Tendsto (fun m : ℕ => 2 * (m : ℝ) - 1) atTop atTop := by
        refine tendsto_atTop.2 fun x => ?_
        filter_upwards [tendsto_atTop.1 (tendsto_natCast_atTop_atTop (R := ℝ)) (x + 1)] with m hm
        linarith only [hm, Nat.cast_nonneg (α := ℝ) m]
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp h).const_mul (6 * π)
  have hl : Tendsto (fun m : ℕ => cosPowArea 1 (2 * m)) atTop (𝓝 (8 / π)) := by
    simpa only [sub_add_cancel, zero_add] using herr.add hsum
  obtain ⟨_, L, _, hL, _⟩ := cosPowArea_limit_recursion (n := 3) (by decide)
  change Tendsto (cosPowArea 1) atTop (𝓝 L) at hL
  have hcofinal : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 2 * m; omega) tendsto_id
  rwa [tendsto_nhds_unique (hL.comp hcofinal) hl] at hL

private lemma cosPowArea_two_eq_half (k : ℕ) : cosPowArea 2 k = cosPowArea 1 k / 2 := by
  let f (x : ℝ) := |cos x - cos ((k : ℝ) * x)|
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hreflect (x : ℝ) : f (2 * π - x) = f x := by
    dsimp [f]
    rw [show (k : ℝ) * (2 * π - x) = -(k * x) + k * (2 * π) by ring,
      cos_add_nat_mul_two_pi, cos_neg, cos_two_pi_sub]
  have hfold : (∫ x in (0 : ℝ)..(2 * π), f x) = 2 * ∫ x in (0 : ℝ)..π, f x := by
    have h := integral_comp_sub_left (a := (0 : ℝ)) (b := π) f (2 * π)
    simp only [hreflect, sub_zero, show 2 * π - π = π by ring] at h
    rw [← integral_add_adjacent_intervals (hf.intervalIntegrable 0 π)
      (hf.intervalIntegrable π (2 * π)), ← h, two_mul]
  unfold cosPowArea
  simp only [pow_one]
  change (∫ x in (0 : ℝ)..π, |cos x ^ 2 - cos (k * x) ^ 2|) = _
  calc
    _ = ∫ x in (0 : ℝ)..π, (2 : ℝ)⁻¹ * f (2 * x) := by
      apply integral_congr
      intro x _
      dsimp [f]
      rw [show cos x ^ 2 - cos (k * x) ^ 2 = (2 : ℝ)⁻¹ *
          (cos (2 * x) - cos (k * (2 * x))) by
        rw [show (k : ℝ) * (2 * x) = 2 * (k * x) by ring, cos_two_mul, cos_two_mul]; ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0),
        mul_zero, smul_eq_mul, hfold]
      change _ = (∫ x in (0 : ℝ)..π, f x) / 2
      ring

private lemma tendsto_cosPowArea_two : Tendsto (cosPowArea 2) atTop (𝓝 (4 / π)) := by
  have h := tendsto_cosPowArea_one.div_const 2
  rw [show (8 / π) / 2 = 4 / π by ring] at h
  exact h.congr fun k => (cosPowArea_two_eq_half k).symm

private noncomputable def factorialRatio (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2

private noncomputable def factorialTerm (n : ℕ) : ℝ :=
  ((n - 2).doubleFactorial : ℝ) / ((n - 1).doubleFactorial * n)

private lemma factorialRatio_add_two (n : ℕ) :
    factorialRatio (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * factorialRatio n := by
  have h : (n.doubleFactorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos n).ne'
  simp only [factorialRatio, Nat.doubleFactorial_add_two, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

private lemma factorialRatio_mul_term (n : ℕ) :
    factorialRatio (n + 2) * factorialTerm (n + 2) = 1 / ((n : ℝ) + 2) ^ 2 := by
  have h : (n.doubleFactorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos n).ne'
  have h' : ((n + 1).doubleFactorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (n + 1)).ne'
  simp only [factorialRatio, factorialTerm, Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega,
    Nat.factorial_eq_mul_doubleFactorial (n + 1), Nat.doubleFactorial_add_two,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp

private lemma tendsto_cosPowArea_factorial_sum (b : ℕ) (c : ℝ)
    (hb : 1 ≤ b) (hc : (if Odd b then (8 : ℝ) else 16) = c)
    (hbase : Tendsto (cosPowArea b) atTop (𝓝 (c / π * factorialRatio b * factorialTerm b)))
    (m : ℕ) : Tendsto (cosPowArea (2 * m + b)) atTop
      (𝓝 (c / π * factorialRatio (2 * m + b) *
        ∑ j ∈ Finset.range (m + 1), factorialTerm (2 * j + b))) := by
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
    have hindex : 2 * (m + 1) + b = (2 * m + b) + 2 := by omega
    have hparity : Odd (2 * (m + 1) + b) ↔ Odd b := by simp [Nat.odd_iff, Nat.add_mod]
    obtain ⟨L, L', hL, hL', hrec⟩ :=
      cosPowArea_limit_recursion (n := 2 * (m + 1) + b) (by omega)
    rw [hindex, Nat.add_sub_cancel] at hL'
    rw [tendsto_nhds_unique hL' ih, if_congr hparity rfl rfl, hc, hindex,
      Nat.cast_add, Nat.cast_ofNat] at hrec
    rw [hindex, hrec] at hL
    rw [Finset.sum_range_succ, hindex, mul_add, mul_assoc _ _ (factorialTerm _),
      factorialRatio_mul_term, factorialRatio_add_two]
    convert hL using 2
    field_simp [pi_ne_zero]
    ring

/-- **Limiting area between cosine powers via double factorials.** For natural numbers $n$ and
$k$, let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. As $k \to \infty$ through the natural
numbers: if $n$ is odd, then
$$A_n(k) \to \frac{8 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!! (2j+1)},$$
and if $n \ge 2$ is even, then
$$A_n(k) \to \frac{16 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!! (2j+2)}.$$
Here $(-1)!! = 1$ and $0!! = 1$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem tendsto_cosPowArea_doubleFactorial (n : ℕ) :
    (Odd n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (8 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
          ((2 * j - 1).doubleFactorial : ℝ) /
            ((2 * j).doubleFactorial * (2 * j + 1))))) ∧
    (Even n → 0 < n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
          ((2 * j).doubleFactorial : ℝ) /
            ((2 * j + 1).doubleFactorial * (2 * j + 2))))) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hbase : Tendsto (cosPowArea 1) atTop
        (𝓝 (8 / π * factorialRatio 1 * factorialTerm 1)) := by
      simpa [factorialRatio, factorialTerm] using tendsto_cosPowArea_one
    rw [show (2 * m + 1 - 1) / 2 = m by omega]
    simpa only [factorialRatio, factorialTerm,
      show ∀ j : ℕ, 2 * j + 1 - 2 = 2 * j - 1 by omega,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      tendsto_cosPowArea_factorial_sum 1 8 (by decide) (by norm_num [Nat.odd_iff]) hbase m
  · intro hn hp
    have hmod := Nat.even_iff.mp hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨(n - 2) / 2, by omega⟩
    have hbase : Tendsto (cosPowArea 2) atTop
        (𝓝 (16 / π * factorialRatio 2 * factorialTerm 2)) := by
      convert tendsto_cosPowArea_two using 2
      norm_num [factorialRatio, factorialTerm, Nat.factorial_succ, Nat.doubleFactorial_add_two]
      ring
    rw [show (2 * m + 2 - 2) / 2 = m by omega]
    simpa only [factorialRatio, factorialTerm,
      show ∀ j : ℕ, 2 * j + 2 - 1 = 2 * j + 1 by omega,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_cosPowArea_factorial_sum 2 16 (by decide) (by norm_num [Nat.odd_iff]) hbase m

end MetaMathlibExt
