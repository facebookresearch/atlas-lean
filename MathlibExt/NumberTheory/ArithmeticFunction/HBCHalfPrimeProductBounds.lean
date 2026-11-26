/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product bounds for prime tuples at $1/2$ by size of the first prime

We prove Stone's bounds for the product $P = p_1 \cdots p_k$ of primes $p_1 < \dots < p_k$ with
$\prod_{i=1}^{k} (1 - 1/p_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/p_i)$ and $p_1 \ge 5$
(`MetaMathlibExt.hbcAdmissible_half_prime_prod_le_of_five_le`).

The tail $p_2 < \dots < p_k$ is HBC-admissible for $a/(a + d)$ with $a = p_1$ and $d = p_1 - 2$.
For such a tuple, a variant of the general bound for HBC-admissible tuples (Theorem 1 of the same
source) is proved here by strong induction on the length: comparing the prefix products of the
tuple with those of the calibrating numbers $1 + \alpha^{2^{i-1}}$, $\alpha = (a + d)/d$, gives an
index $\kappa$ with $a p_2 \cdots p_{\kappa + 1} + d \le d \alpha^{2^\kappa}$ and a bound for
$a p_2 \cdots p_k$ in terms of $d \alpha^{2^\kappa}$. The comparison uses the prefix-product
domination inequality for $\prod (1 - 1/x_i)$, which follows from the concavity of
$t \mapsto \log(1 - e^{-t})$ by Abel summation. Since consecutive odd primes differ by at least
$2$, the prefix products of the tail are large, which forces $\kappa$ to be large; comparing
$d \alpha^{2^\kappa}$ with the constants of the statement then gives the four bounds.
-/

namespace MetaMathlibExt

open Finset

namespace hbcAdmissible_half_prime_prod_le_of_five_le

/-! ### Prefix-product domination -/

/-- The tangent-line bound for the concave function `u ↦ log (1 - e⁻ᵘ)`, written in `t = eᵘ`. -/
private theorem log_one_sub_inv_le {y z : ℝ} (hy : 1 < y) (hz : 1 < z) :
    Real.log (1 - 1 / z) ≤ Real.log (1 - 1 / y) + (Real.log z - Real.log y) / (y - 1) := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hy1 : 0 < 1 - 1 / y := by rw [sub_pos, div_lt_one hy0]; exact hy
  have hz1 : 0 < 1 - 1 / z := by rw [sub_pos, div_lt_one hz0]; exact hz
  have h1 : Real.log (1 - 1 / z) - Real.log (1 - 1 / y) ≤ (1 - 1 / z) / (1 - 1 / y) - 1 := by
    rw [← Real.log_div hz1.ne' hy1.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hz1 hy1)
  have h2 : 1 - (z / y)⁻¹ ≤ Real.log (z / y) := Real.one_sub_inv_le_log_of_pos (div_pos hz0 hy0)
  rw [Real.log_div hz0.ne' hy0.ne'] at h2
  have hy1' : 0 < y - 1 := by linarith
  have h3 : (1 - 1 / z) / (1 - 1 / y) - 1 = (1 - (z / y)⁻¹) / (y - 1) := by
    field_simp
    ring
  have h4 : (1 - (z / y)⁻¹) / (y - 1) ≤ (Real.log z - Real.log y) / (y - 1) :=
    div_le_div_of_nonneg_right h2 hy1'.le
  linarith

/-- Abel summation with nonincreasing weights and nonnegative partial sums. -/
private theorem abel_bound (w δ : ℕ → ℝ) (p : ℕ)
    (hw : ∀ i, i + 1 < p + 1 → w (i + 1) ≤ w i)
    (hΔ : ∀ l ≤ p + 1, 0 ≤ ∑ i ∈ range l, δ i) :
    w p * ∑ i ∈ range (p + 1), δ i ≤ ∑ i ∈ range (p + 1), w i * δ i := by
  induction p with
  | zero => simp
  | succ p ih =>
    have ih' := ih (fun i hi => hw i (by omega)) (fun l hl => hΔ l (by omega))
    rw [sum_range_succ, sum_range_succ (fun i => w i * δ i), mul_add]
    have hwp : w (p + 1) ≤ w p := hw p (by omega)
    have hnn : 0 ≤ ∑ i ∈ range (p + 1), δ i := hΔ (p + 1) (by omega)
    linarith [mul_le_mul_of_nonneg_right hwp hnn]

/-- Prefix-product domination: if the prefix products of `z` are at most those of the
nondecreasing sequence `y`, then `∏ (1 - 1/z i) ≤ ∏ (1 - 1/y i)`, strictly when the full products
differ. -/
private theorem prod_one_sub_inv_le (p : ℕ) (y z : ℕ → ℝ)
    (hy : ∀ i < p, 1 < y i) (hz : ∀ i < p, 1 < z i)
    (hmono : ∀ i, i + 1 < p → y i ≤ y (i + 1))
    (hpre : ∀ l ≤ p, ∏ i ∈ range l, z i ≤ ∏ i ∈ range l, y i) :
    ∏ i ∈ range p, (1 - 1 / z i) ≤ ∏ i ∈ range p, (1 - 1 / y i) ∧
      (∏ i ∈ range p, z i < ∏ i ∈ range p, y i →
        ∏ i ∈ range p, (1 - 1 / z i) < ∏ i ∈ range p, (1 - 1 / y i)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hy0 : ∀ i < q + 1, 0 < y i := fun i hi => by linarith [hy i hi]
  have hz0 : ∀ i < q + 1, 0 < z i := fun i hi => by linarith [hz i hi]
  have hyf : ∀ i < q + 1, 0 < 1 - 1 / y i := fun i hi => by
    rw [sub_pos, div_lt_one (hy0 i hi)]; exact hy i hi
  have hzf : ∀ i < q + 1, 0 < 1 - 1 / z i := fun i hi => by
    rw [sub_pos, div_lt_one (hz0 i hi)]; exact hz i hi
  have hprody : ∀ l ≤ q + 1, 0 < ∏ i ∈ range l, y i := fun l hl =>
    prod_pos fun i hi => hy0 i (by rw [mem_range] at hi; omega)
  have hprodz : ∀ l ≤ q + 1, 0 < ∏ i ∈ range l, z i := fun l hl =>
    prod_pos fun i hi => hz0 i (by rw [mem_range] at hi; omega)
  set δ : ℕ → ℝ := fun i => Real.log (y i) - Real.log (z i) with hδ
  set w : ℕ → ℝ := fun i => 1 / (y i - 1) with hw
  have hΔ : ∀ l ≤ q + 1, ∑ i ∈ range l, δ i =
      Real.log (∏ i ∈ range l, y i) - Real.log (∏ i ∈ range l, z i) := by
    intro l hl
    rw [Real.log_prod (fun i hi => (hy0 i (by rw [mem_range] at hi; omega)).ne'),
      Real.log_prod (fun i hi => (hz0 i (by rw [mem_range] at hi; omega)).ne'),
      ← sum_sub_distrib]
  have hΔnn : ∀ l ≤ q + 1, 0 ≤ ∑ i ∈ range l, δ i := by
    intro l hl
    rw [hΔ l hl, sub_nonneg]
    exact Real.log_le_log (hprodz l hl) (hpre l hl)
  have hwmono : ∀ i, i + 1 < q + 1 → w (i + 1) ≤ w i := by
    intro i hi
    simp only [hw]
    exact one_div_le_one_div_of_le (by linarith [hy i (by omega)]) (by linarith [hmono i hi])
  have habel := abel_bound w δ q hwmono hΔnn
  have hsum : ∑ i ∈ range (q + 1), w i * δ i ≤
      ∑ i ∈ range (q + 1), (Real.log (1 - 1 / y i) - Real.log (1 - 1 / z i)) := by
    apply sum_le_sum
    intro i hi
    rw [mem_range] at hi
    have h := log_one_sub_inv_le (hy i hi) (hz i hi)
    have hy1 : 0 < y i - 1 := by linarith [hy i hi]
    have he : w i * δ i = -((Real.log (z i) - Real.log (y i)) / (y i - 1)) := by
      simp only [hw, hδ]
      field_simp
      ring
    rw [he]
    linarith
  have hlogy : Real.log (∏ i ∈ range (q + 1), (1 - 1 / y i)) =
      ∑ i ∈ range (q + 1), Real.log (1 - 1 / y i) :=
    Real.log_prod (fun i hi => (hyf i (by rw [mem_range] at hi; omega)).ne')
  have hlogz : Real.log (∏ i ∈ range (q + 1), (1 - 1 / z i)) =
      ∑ i ∈ range (q + 1), Real.log (1 - 1 / z i) :=
    Real.log_prod (fun i hi => (hzf i (by rw [mem_range] at hi; omega)).ne')
  have hwq : 0 < w q := by
    have := hy q (by omega)
    simp only [hw]
    exact one_div_pos.mpr (by linarith)
  have hpy : 0 < ∏ i ∈ range (q + 1), (1 - 1 / y i) :=
    prod_pos fun i hi => hyf i (by rw [mem_range] at hi; omega)
  have hpz : 0 < ∏ i ∈ range (q + 1), (1 - 1 / z i) :=
    prod_pos fun i hi => hzf i (by rw [mem_range] at hi; omega)
  rw [sum_sub_distrib] at hsum
  refine ⟨?_, fun hlt => ?_⟩
  · rw [← Real.log_le_log_iff hpz hpy, hlogy, hlogz]
    have := mul_nonneg hwq.le (hΔnn (q + 1) le_rfl)
    linarith
  · rw [← Real.log_lt_log_iff hpz hpy, hlogy, hlogz]
    have hpos : 0 < ∑ i ∈ range (q + 1), δ i := by
      rw [hΔ _ le_rfl, sub_pos]
      exact Real.log_lt_log (hprodz _ le_rfl) hlt
    have := mul_pos hwq hpos
    linarith

/-! ### Calibrating sequences -/

/-- The calibrating sequence of length `L` for `1 - 1/β`, indexed from `0`:
`1 + β ^ 2 ^ i` for `i + 1 < L`, and `β ^ 2 ^ (L - 1)` for the last index. -/
private noncomputable def cal (β : ℝ) (L i : ℕ) : ℝ :=
  if i + 1 < L then 1 + β ^ 2 ^ i else β ^ 2 ^ i

private theorem cal_prefix (β : ℝ) (L j : ℕ) (hj : j < L) :
    (β - 1) * ∏ i ∈ range j, cal β L i = β ^ 2 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, ← mul_assoc, ih (by omega), cal, ite_eq_left (by omega), pow_succ,
      pow_mul]
    ring

private theorem cal_full (β : ℝ) (L : ℕ) (hL : 1 ≤ L) :
    (β - 1) * ∏ i ∈ range L, cal β L i = β ^ 2 ^ L - β ^ 2 ^ (L - 1) := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [prod_range_succ, ← mul_assoc, cal_prefix β (L + 1) L (by omega), cal,
    ite_eq_right (by omega), Nat.add_sub_cancel, pow_succ, pow_mul]
  ring

private theorem cal_one_sub (β : ℝ) (hβ : 1 < β) (L : ℕ) (hL : 1 ≤ L) :
    ∏ i ∈ range L, (1 - 1 / cal β L i) = 1 - 1 / β := by
  have hβ0 : 0 < β := by linarith
  have hpre : ∀ j < L, (∏ i ∈ range j, (1 - 1 / cal β L i)) * ((β ^ 2 ^ j - 1) * β) =
      (β - 1) * β ^ 2 ^ j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [prod_range_succ, cal, ite_eq_left (by omega)]
      have ih' := ih (by omega)
      have hx : 0 < β ^ 2 ^ j := pow_pos hβ0 _
      have hx1 : 0 < 1 + β ^ 2 ^ j := by linarith
      rw [pow_succ, pow_mul]
      have key : (1 - 1 / (1 + β ^ 2 ^ j)) * (((β ^ 2 ^ j) ^ 2 - 1) * β) =
          β ^ 2 ^ j * ((β ^ 2 ^ j - 1) * β) := by
        field_simp
        ring
      rw [mul_assoc, key, mul_left_comm, ih']
      ring
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h := hpre L (by omega)
  rw [prod_range_succ, cal, ite_eq_right (by omega)]
  have hx : 0 < β ^ 2 ^ L := pow_pos hβ0 _
  have hx1 : β ^ 2 ^ L - 1 ≠ 0 := by
    have : 1 < β ^ 2 ^ L := one_lt_pow₀ hβ (by positivity)
    linarith
  have hQ : ∏ i ∈ range L, (1 - 1 / cal β (L + 1) i) =
      (β - 1) * β ^ 2 ^ L / ((β ^ 2 ^ L - 1) * β) := by
    rw [eq_div_iff (mul_ne_zero hx1 hβ0.ne'), h]
  rw [hQ]
  field_simp

private theorem cal_shift (α : ℝ) (L κ i : ℕ) (hκ : κ ≤ L) :
    cal α L (κ + i) = cal (α ^ 2 ^ κ) (L - κ) i := by
  unfold cal
  rw [pow_add, pow_mul]
  by_cases h : i + 1 < L - κ
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-! ### A recursion for HBC-admissible tuples -/

private theorem prod_range_split {M : Type*} [CommMonoid M] (f : ℕ → M) {κ m : ℕ}
    (h : κ ≤ m) :
    ∏ i ∈ range m, f i = (∏ i ∈ range κ, f i) * ∏ i ∈ range (m - κ), f (κ + i) := by
  rw [← prod_range_add, Nat.add_sub_cancel' h]

private theorem add_le_of_strictMono (u : ℕ → ℕ) (m : ℕ)
    (hmono : ∀ i, i + 1 < m → u i < u (i + 1)) : ∀ i < m, u 0 + i ≤ u i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hmono i hi
    have h2 := ih (by omega)
    omega

/-- Monotonicity of `t ↦ t ^ 2 ^ L - t ^ 2 ^ (L - 1)` on `[1, ∞)`. -/
private theorem pow_sub_pow_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (L : ℕ) (hL : 1 ≤ L) :
    s ^ 2 ^ L - s ^ 2 ^ (L - 1) ≤ t ^ 2 ^ L - t ^ 2 ^ (L - 1) := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, pow_mul, pow_mul]
  have hS : 1 ≤ s ^ 2 ^ L := one_le_pow₀ hs
  have hST : s ^ 2 ^ L ≤ t ^ 2 ^ L := pow_le_pow_left₀ (by linarith) hst _
  nlinarith

private theorem mul_sq_sub_le {D U V : ℝ} (hD : 1 ≤ D) (hU : 1 ≤ U) (hVU : D * U ≤ V) :
    D * (U ^ 2 - U) ≤ V ^ 2 - V := by
  have hDU : 1 ≤ D * U := one_le_mul_of_one_le_of_one_le hD hU
  nlinarith [mul_nonneg (sub_nonneg.mpr hVU) (by linarith : (0 : ℝ) ≤ V + D * U - 1),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ D) (sq_nonneg U)) (sub_nonneg.mpr hD)]

/-- For an HBC-admissible tuple `u 0 < ⋯ < u (m - 1)` for `a/(a + d)` and `α = (a + d)/d`, some
`κ` with `1 ≤ κ ≤ m` has `a ∏_{i<κ} u i + d ≤ d α ^ 2 ^ κ`, and then `a ∏ u i` is at most
`F_{m-κ}(d α ^ 2 ^ κ)` if `κ < m` and at most `d F_m(α)` if `κ = m`, where
`F_L(t) = t ^ 2 ^ L - t ^ 2 ^ (L - 1)`. The index `κ` is the largest one whose prefix product is
at most that of the calibrating numbers; the tail after it is again HBC-admissible, with a
defect at most `d`, and the induction hypothesis bounds it. -/
private theorem hbc_recursion (m : ℕ) : ∀ (a d : ℕ) (u : ℕ → ℕ), 0 < a → 0 < d → 1 ≤ m →
    (∀ i, i + 1 < m → u i < u (i + 1)) → 0 < u 0 →
    ∏ i ∈ range m, (1 - 1 / (u i : ℝ)) ≤ (a : ℝ) / (a + d) →
    (a : ℝ) / (a + d) < ∏ i ∈ range (m - 1), (1 - 1 / (u i : ℝ)) →
    ∃ κ, 1 ≤ κ ∧ κ ≤ m ∧
      (a : ℝ) * ∏ i ∈ range κ, (u i : ℝ) + d ≤ d * (((a : ℝ) + d) / d) ^ 2 ^ κ ∧
      (κ < m → (a : ℝ) * ∏ i ∈ range m, (u i : ℝ) ≤
        (d * (((a : ℝ) + d) / d) ^ 2 ^ κ) ^ 2 ^ (m - κ) -
          (d * (((a : ℝ) + d) / d) ^ 2 ^ κ) ^ 2 ^ (m - κ - 1)) ∧
      (κ = m → (a : ℝ) * ∏ i ∈ range m, (u i : ℝ) ≤
        d * ((((a : ℝ) + d) / d) ^ 2 ^ m - (((a : ℝ) + d) / d) ^ 2 ^ (m - 1))) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro a d u ha hd hm hmono hu0 hle hlt
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  set α : ℝ := ((a : ℝ) + d) / d with hα_def
  have hα1 : 1 < α := by rw [hα_def, lt_div_iff₀ hdR]; linarith
  have hα0 : 0 < α := by linarith
  have hαd : (d : ℝ) * (α - 1) = a := by rw [hα_def]; field_simp; ring
  have hr : (a : ℝ) / (a + d) = 1 - 1 / α := by rw [hα_def]; field_simp; ring
  have hgrow := add_le_of_strictMono u m hmono
  have hupos : ∀ i < m, (0 : ℝ) < u i := fun i hi => by
    have := hgrow i hi
    exact_mod_cast (show 0 < u i by omega)
  have hcal1 : ∀ i, 1 < cal α m i := fun i => by
    unfold cal
    split_ifs
    · have : 0 < α ^ 2 ^ i := pow_pos hα0 _
      linarith
    · exact one_lt_pow₀ hα1 (by positivity)
  have hcal0 : ∀ i, 0 < cal α m i := fun i => by linarith [hcal1 i]
  have hNpre : ∀ j < m, (a : ℝ) * ∏ i ∈ range j, cal α m i = d * (α ^ 2 ^ j - 1) := by
    intro j hj
    rw [← cal_prefix α m j hj, ← hαd]
    ring
  have hNfull : (a : ℝ) * ∏ i ∈ range m, cal α m i = d * (α ^ 2 ^ m - α ^ 2 ^ (m - 1)) := by
    rw [← cal_full α m hm, ← hαd]
    ring
  have hcalr : ∏ i ∈ range m, (1 - 1 / cal α m i) = (a : ℝ) / (a + d) := by
    rw [cal_one_sub α hα1 m hm, hr]
  classical
  set S := (Icc 1 m).filter (fun j => ∏ i ∈ range j, (u i : ℝ) ≤ ∏ i ∈ range j, cal α m i)
    with hS_def
  -- Some prefix product is at most the calibrating one.
  have hSne : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hS
    have hgt : ∀ j ∈ Icc 1 m, ∏ i ∈ range j, cal α m i < ∏ i ∈ range j, (u i : ℝ) := by
      intro j hj
      by_contra hcon
      have hjS : j ∈ S := by rw [hS_def, mem_filter]; exact ⟨hj, not_lt.mp hcon⟩
      rw [hS] at hjS
      exact notMem_empty j hjS
    have hu1 : (1 : ℝ) < u 0 := by
      have h := hgt 1 (by rw [mem_Icc]; omega)
      rw [prod_range_one, prod_range_one] at h
      linarith [hcal1 0]
    have hy : ∀ i < m, (1 : ℝ) < u i := fun i hi => by
      have := hgrow i hi
      have : (u 0 : ℝ) ≤ u i := by exact_mod_cast (show u 0 ≤ u i by omega)
      linarith
    have hL2 := prod_one_sub_inv_le m (fun i => (u i : ℝ)) (cal α m) hy (fun i _ => hcal1 i)
      (fun i hi => by exact_mod_cast (hmono i hi).le)
      (fun l hl => by
        rcases Nat.eq_zero_or_pos l with rfl | hl0
        · simp
        · exact (hgt l (by rw [mem_Icc]; omega)).le)
    have := hL2.2 (hgt m (by rw [mem_Icc]; omega))
    rw [hcalr] at this
    linarith
  set κ := S.max' hSne with hκ_def
  have hκS : κ ∈ S := max'_mem S hSne
  rw [hS_def, mem_filter, mem_Icc] at hκS
  obtain ⟨⟨hκ1, hκm⟩, hκle⟩ := hκS
  have hκmax : ∀ j, κ < j → j ≤ m →
      ∏ i ∈ range j, cal α m i < ∏ i ∈ range j, (u i : ℝ) := by
    intro j hκj hjm
    by_contra hcon
    have hjS : j ∈ S := by
      rw [hS_def, mem_filter, mem_Icc]
      exact ⟨⟨by omega, hjm⟩, not_lt.mp hcon⟩
    have := le_max' S j hjS
    rw [← hκ_def] at this
    omega
  clear_value κ
  clear hκ_def hSne hS_def S
  have hfirst : (a : ℝ) * ∏ i ∈ range κ, (u i : ℝ) + d ≤ d * α ^ 2 ^ κ := by
    have h := mul_le_mul_of_nonneg_left hκle haR.le
    rcases lt_or_eq_of_le hκm with hlt' | heq
    · rw [hNpre κ hlt'] at h
      linarith
    · rw [heq] at h ⊢
      rw [hNfull] at h
      have : (d : ℝ) * 1 ≤ d * α ^ 2 ^ (m - 1) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hα1.le) hdR.le
      linarith
  refine ⟨κ, hκ1, hκm, hfirst, ?_, ?_⟩
  swap
  · intro heq
    rw [heq] at hκle
    have h := mul_le_mul_of_nonneg_left hκle haR.le
    rwa [hNfull] at h
  intro hκm'
  -- Every term of the tuple is at least `2`.
  have hu2 : 2 ≤ u 0 := by
    by_contra hcon
    have h1 : u 0 = 1 := by omega
    have hz : ∏ i ∈ range (m - 1), (1 - 1 / (u i : ℝ)) = 0 :=
      prod_eq_zero (i := 0) (by rw [mem_range]; omega) (by rw [h1]; norm_num)
    rw [hz] at hlt
    have : (0 : ℝ) < a / (a + d) := by positivity
    linarith
  have hy : ∀ i < m, (2 : ℝ) ≤ u i := fun i hi => by
    have := hgrow i hi
    exact_mod_cast (show 2 ≤ u i by omega)
  have hfac : ∀ i < m, 0 < 1 - 1 / (u i : ℝ) := fun i hi => by
    have := hy i hi
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hfac1 : ∀ i < m, 1 - 1 / (u i : ℝ) ≤ 1 := fun i hi => by
    have := hy i hi
    have : 0 ≤ 1 / (u i : ℝ) := by positivity
    linarith
  have hQm := prod_range_split (fun i => 1 - 1 / (u i : ℝ)) hκm
  have hQm1 := prod_range_split (fun i => 1 - 1 / (u i : ℝ)) (show κ ≤ m - 1 by omega)
  have hPm := prod_range_split (fun i => (u i : ℝ)) hκm
  rw [Nat.sub_right_comm] at hQm1
  -- The tail of the tuple dominates the tail of the calibrating sequence.
  have htail : ∀ l ≤ m - κ,
      ∏ i ∈ range l, cal α m (κ + i) ≤ ∏ i ∈ range l, (u (κ + i) : ℝ) := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · simp
    have h3 := hκmax (κ + l) (by omega) (by omega)
    rw [prod_range_add, prod_range_add] at h3
    have hPu : 0 ≤ ∏ i ∈ range l, (u (κ + i) : ℝ) := prod_nonneg fun i _ => by positivity
    have hNκ : 0 < ∏ i ∈ range κ, cal α m i := prod_pos fun i _ => hcal0 i
    have h4 : (∏ i ∈ range κ, cal α m i) * ∏ i ∈ range l, cal α m (κ + i) <
        (∏ i ∈ range κ, cal α m i) * ∏ i ∈ range l, (u (κ + i) : ℝ) :=
      lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_right hκle hPu)
    exact (lt_of_mul_lt_mul_left h4 hNκ.le).le
  have hL2 := (prod_one_sub_inv_le (m - κ) (fun i => (u (κ + i) : ℝ))
    (fun i => cal α m (κ + i))
    (fun i hi => by have := hy (κ + i) (by omega); linarith) (fun i _ => hcal1 _)
    (fun i hi => by exact_mod_cast (hmono (κ + i) (by omega)).le) htail).1
  have hRc : ∏ i ∈ range (m - κ), (1 - 1 / cal α m (κ + i)) = 1 - 1 / α ^ 2 ^ κ := by
    simp_rw [cal_shift α m κ _ hκm]
    exact cal_one_sub _ (one_lt_pow₀ hα1 (by positivity)) _ (by omega)
  rw [hRc] at hL2
  set β := α ^ 2 ^ κ with hβ_def
  have hβ1 : 1 < β := one_lt_pow₀ hα1 (by positivity)
  set Pκ := ∏ i ∈ range κ, (u i : ℝ) with hPκ_def
  set Qκ := ∏ i ∈ range κ, (1 - 1 / (u i : ℝ)) with hQκ_def
  set Ru := ∏ i ∈ range (m - κ), (1 - 1 / (u (κ + i) : ℝ)) with hRu_def
  set Ru' := ∏ i ∈ range (m - κ - 1), (1 - 1 / (u (κ + i) : ℝ)) with hRu'_def
  have hPκpos : 0 < Pκ := prod_pos fun i hi => hupos i (by rw [mem_range] at hi; omega)
  have hQκpos : 0 < Qκ := prod_pos fun i hi => hfac i (by rw [mem_range] at hi; omega)
  have hQRu : Qκ * Ru ≤ a / (a + d) := by rw [← hQm]; exact hle
  have hQRu' : a / (a + d) < Qκ * Ru' := by rw [← hQm1]; exact hlt
  have hQβ : Qκ * (β - 1) ≤ (a : ℝ) / (a + d) * β := by
    have h2 : Qκ * (1 - 1 / β) ≤ Qκ * Ru := mul_le_mul_of_nonneg_left hL2 hQκpos.le
    have h3 : Qκ * (β - 1) = Qκ * (1 - 1 / β) * β := by field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_right (h2.trans hQRu) (by linarith)
  have hQκgt : (a : ℝ) / (a + d) < Qκ := by
    have hRu'1 : Ru' ≤ 1 := prod_le_one₀ (fun i hi => (hfac _ (by rw [mem_range] at hi; omega)).le)
      (fun i hi => hfac1 _ (by rw [mem_range] at hi; omega))
    nlinarith
  -- The tail is HBC-admissible for `a' / (a' + d')`.
  set a' : ℕ := a * ∏ i ∈ range κ, u i with ha'_def
  set A : ℕ := ∏ i ∈ range κ, (u i - 1) with hA_def
  have ha'R : (a' : ℝ) = a * Pκ := by rw [ha'_def]; push_cast; rfl
  have hAR : (A : ℝ) = Pκ * Qκ := by
    rw [hA_def, Nat.cast_prod, hPκ_def, hQκ_def, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    rw [mem_range] at hi
    have h1 : 1 ≤ u i := by have := hgrow i (by omega); omega
    have hui : (0 : ℝ) < u i := hupos i (by omega)
    rw [Nat.cast_sub h1, Nat.cast_one]
    field_simp
  have hadR : (0 : ℝ) < a + d := by positivity
  have hlt_nat : a' < (a + d) * A := by
    have : (a' : ℝ) < ((a + d : ℕ) : ℝ) * A := by
      rw [ha'R, hAR]
      push_cast
      have := (div_lt_iff₀ hadR).mp hQκgt
      nlinarith
    exact_mod_cast this
  set d' : ℕ := (a + d) * A - a' with hd'_def
  have hd'pos : 0 < d' := by omega
  have hd'R : (d' : ℝ) = (a + d) * (Pκ * Qκ) - a * Pκ := by
    rw [hd'_def, Nat.cast_sub hlt_nat.le]
    push_cast
    rw [hAR, ha'R]
  clear_value d' A a'
  have hd'le : (d' : ℝ) ≤ d := by
    have hQβ2 : ((a : ℝ) + d) * Qκ * (β - 1) ≤ a * β := by
      have h := mul_le_mul_of_nonneg_left hQβ hadR.le
      have e : ((a : ℝ) + d) * (a / (a + d) * β) = a * β := by field_simp
      rw [e, ← mul_assoc] at h
      exact h
    have h1 : (d' : ℝ) * (β - 1) ≤ a * Pκ := by
      have h := mul_le_mul_of_nonneg_left hQβ2 hPκpos.le
      have e : (d' : ℝ) * (β - 1) =
          Pκ * (((a : ℝ) + d) * Qκ * (β - 1)) - a * Pκ * (β - 1) := by
        rw [hd'R]
        ring
      have e2 : Pκ * (a * β) - a * Pκ * (β - 1) = a * Pκ := by ring
      rw [e]
      linarith
    have h2 : (a : ℝ) * Pκ ≤ d * (β - 1) := by
      have e : (d : ℝ) * (β - 1) = d * β - d := by ring
      rw [e]
      linarith [hfirst]
    have hβ1' : 0 < β - 1 := by linarith
    exact le_of_mul_le_mul_right (h1.trans h2) hβ1'
  have hsum : ((a' : ℝ) + d') = (a + d) * (Pκ * Qκ) := by rw [hd'R, ha'R]; ring
  have ha'pos : 0 < a' := by
    have : (0 : ℝ) < a' := by rw [ha'R]; positivity
    exact_mod_cast this
  have hle' : ∏ i ∈ range (m - κ), (1 - 1 / (u (κ + i) : ℝ)) ≤ (a' : ℝ) / (a' + d') := by
    rw [hsum, ha'R, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hQRu (by positivity : (0 : ℝ) ≤ (a + d) * Pκ)
    rw [div_mul_eq_mul_div, mul_div_assoc] at this
    have e : ((a : ℝ) + d) * Pκ / (a + d) = Pκ := by field_simp
    rw [e] at this
    have e3 : Ru * ((a + d) * (Pκ * Qκ)) = Qκ * Ru * ((a + d) * Pκ) := by ring
    rw [e3]
    exact this
  have hlt' : (a' : ℝ) / (a' + d') < ∏ i ∈ range (m - κ - 1), (1 - 1 / (u (κ + i) : ℝ)) := by
    rw [hsum, ha'R, div_lt_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_right hQRu' (by positivity : (0 : ℝ) < (a + d) * Pκ)
    rw [div_mul_eq_mul_div, mul_div_assoc] at this
    have e : ((a : ℝ) + d) * Pκ / (a + d) = Pκ := by field_simp
    rw [e] at this
    have e3 : Ru' * ((a + d) * (Pκ * Qκ)) = Qκ * Ru' * ((a + d) * Pκ) := by ring
    rw [e3]
    exact this
  obtain ⟨κ', hκ'1, hκ'm, -, hIHlt, hIHeq⟩ := IH (m - κ) (by omega) a' d' (fun i => u (κ + i))
    ha'pos hd'pos (by omega) (fun i hi => hmono (κ + i) (by omega))
    (by rw [Nat.add_zero]; have := hgrow κ (by omega); omega) hle' hlt'
  have hXm : (a' : ℝ) * ∏ i ∈ range (m - κ), (u (κ + i) : ℝ) =
      a * ∏ i ∈ range m, (u i : ℝ) := by
    rw [ha'R, hPm]
    ring
  set α' := ((a' : ℝ) + d') / d' with hα'_def
  have hd'0 : (0 : ℝ) < d' := by exact_mod_cast hd'pos
  have hd'1 : (1 : ℝ) ≤ d' := by exact_mod_cast hd'pos
  have hα'1 : 1 ≤ α' := by
    rw [hα'_def, le_div_iff₀ hd'0]
    have : (0 : ℝ) ≤ a' := by positivity
    linarith
  have hΓ : (d' : ℝ) * α' ≤ d * β := by
    rw [hα'_def, mul_div_cancel₀ _ hd'0.ne', ha'R]
    linarith [hfirst, hd'le]
  rcases lt_or_eq_of_le hκ'm with hκ'lt | hκ'eq
  · have h := hIHlt hκ'lt
    rw [hXm] at h
    refine h.trans ?_
    have hs1 : 1 ≤ (d' : ℝ) * α' ^ 2 ^ κ' := one_le_mul_of_one_le_of_one_le hd'1 (one_le_pow₀ hα'1)
    have hst : (d' : ℝ) * α' ^ 2 ^ κ' ≤ (d * β) ^ 2 ^ κ' := by
      calc (d' : ℝ) * α' ^ 2 ^ κ' ≤ (d' : ℝ) ^ 2 ^ κ' * α' ^ 2 ^ κ' := by
            gcongr
            exact le_self_pow₀ hd'1 (by positivity)
        _ = ((d' : ℝ) * α') ^ 2 ^ κ' := (mul_pow _ _ _).symm
        _ ≤ (d * β) ^ 2 ^ κ' := pow_le_pow_left₀ (by positivity) hΓ _
    have := pow_sub_pow_le hs1 hst (m - κ - κ') (by omega)
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at this
    have e1 : κ' + (m - κ - κ') = m - κ := by omega
    have e2 : κ' + (m - κ - κ' - 1) = m - κ - 1 := by omega
    rw [e1, e2] at this
    exact this
  · have h := hIHeq hκ'eq
    rw [hXm] at h
    refine h.trans ?_
    obtain ⟨L, hL⟩ : ∃ L, m - κ = L + 1 := ⟨m - κ - 1, by omega⟩
    rw [hL, Nat.add_sub_cancel, pow_succ, pow_mul, pow_mul]
    have hU1 : 1 ≤ α' ^ 2 ^ L := one_le_pow₀ hα'1
    have hVU : (d' : ℝ) * α' ^ 2 ^ L ≤ (d * β) ^ 2 ^ L := by
      calc (d' : ℝ) * α' ^ 2 ^ L ≤ (d' : ℝ) ^ 2 ^ L * α' ^ 2 ^ L := by
            gcongr
            exact le_self_pow₀ hd'1 (by positivity)
        _ = ((d' : ℝ) * α') ^ 2 ^ L := (mul_pow _ _ _).symm
        _ ≤ (d * β) ^ 2 ^ L := pow_le_pow_left₀ (by positivity) hΓ _
    exact mul_sq_sub_le hd'1 hU1 hVU


/-! ### From the recursion to explicit bounds -/

private theorem mul_sq_sub_le' {D U V : ℝ} (hD : 1 ≤ D) (hU : 1 ≤ U)
    (h : D * U ^ 2 ≤ V ^ 2) : D * (U ^ 2 - U) ≤ V ^ 2 - V := by
  rcases le_total V (D * U) with hle | hle
  · nlinarith
  · exact mul_sq_sub_le hD hU hle

/-- A bound `d α ^ 2 ^ j₀ ≤ c ^ 2 ^ j₀` persists for every larger index. -/
private theorem lift_pow {j₀ κ : ℕ} {d α c : ℝ} (hj₀ : j₀ ≤ κ) (hd : 1 ≤ d) (hα : 0 ≤ α)
    (hc : d * α ^ 2 ^ j₀ ≤ c ^ 2 ^ j₀) : d * α ^ 2 ^ κ ≤ c ^ 2 ^ κ := by
  obtain ⟨s, rfl⟩ : ∃ s, κ = j₀ + s := ⟨κ - j₀, by omega⟩
  rw [pow_add, pow_mul, pow_mul]
  calc d * (α ^ 2 ^ j₀) ^ 2 ^ s ≤ d ^ 2 ^ s * (α ^ 2 ^ j₀) ^ 2 ^ s := by
        gcongr
        exact le_self_pow₀ hd (by positivity)
    _ = (d * α ^ 2 ^ j₀) ^ 2 ^ s := (mul_pow _ _ _).symm
    _ ≤ (c ^ 2 ^ j₀) ^ 2 ^ s := pow_le_pow_left₀ (by positivity) hc _

/-- The output of `hbc_recursion` and `d α ^ 2 ^ κ ≤ c ^ 2 ^ κ` give
`X ≤ c ^ 2 ^ m - c ^ 2 ^ (m - 1)`. -/
private theorem range_bound {m κ : ℕ} {X d α c : ℝ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m)
    (hd : 1 ≤ d) (hα : 1 ≤ α)
    (hlt : κ < m → X ≤ (d * α ^ 2 ^ κ) ^ 2 ^ (m - κ) - (d * α ^ 2 ^ κ) ^ 2 ^ (m - κ - 1))
    (heq : κ = m → X ≤ d * (α ^ 2 ^ m - α ^ 2 ^ (m - 1)))
    (hc : d * α ^ 2 ^ κ ≤ c ^ 2 ^ κ) : X ≤ c ^ 2 ^ m - c ^ 2 ^ (m - 1) := by
  have hs1 : 1 ≤ d * α ^ 2 ^ κ := one_le_mul_of_one_le_of_one_le hd (one_le_pow₀ hα)
  rcases lt_or_eq_of_le hκm with hlt' | heq'
  · refine (hlt hlt').trans ?_
    have := pow_sub_pow_le hs1 hc (m - κ) (by omega)
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at this
    have e1 : κ + (m - κ) = m := by omega
    have e2 : κ + (m - κ - 1) = m - 1 := by omega
    rwa [e1, e2] at this
  · refine (heq heq').trans ?_
    rw [heq'] at hc
    obtain ⟨L, hL⟩ : ∃ L, m = L + 1 := ⟨m - 1, by omega⟩
    rw [hL] at hc ⊢
    rw [Nat.add_sub_cancel]
    rw [pow_succ, pow_mul, pow_mul] at hc ⊢
    exact mul_sq_sub_le' hd (one_le_pow₀ hα) hc

/-- The index from `hbc_recursion` is at least `j₀` when every smaller index is excluded by a
lower bound `L` for the prefix products. -/
private theorem le_index {κ m j₀ : ℕ} {a d α A : ℝ} {P L : ℕ → ℝ} (hκ1 : 1 ≤ κ)
    (hκm : κ ≤ m) (ha : 0 ≤ a) (hd : 0 ≤ d) (hα : 0 ≤ α) (hαA : α ≤ A)
    (hL : ∀ j ≤ m, L j ≤ P j) (hfirst : a * P κ + d ≤ d * α ^ 2 ^ κ)
    (hcheck : ∀ j, 1 ≤ j → j < j₀ → d * A ^ 2 ^ j < a * L j + d) : j₀ ≤ κ := by
  by_contra h
  have h1 := hcheck κ hκ1 (not_le.mp h)
  have h2 : d * α ^ 2 ^ κ ≤ d * A ^ 2 ^ κ :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα hαA _) hd
  have h3 : a * L κ ≤ a * P κ := mul_le_mul_of_nonneg_left (hL κ hκm) ha
  linarith

private theorem prod_Icc_one_eq (f : ℕ → ℝ) (n : ℕ) :
    ∏ i ∈ Icc 1 (n + 1), f i = f 1 * ∏ i ∈ range n, f (i + 2) := by
  rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel, prod_range_succ',
    mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 1
  omega

private theorem sqrt_pow_two_pow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Real.sqrt c ^ 2 ^ (n + 1) = c ^ 2 ^ n := by
  rw [pow_succ', pow_mul, Real.sq_sqrt hc]

private theorem c₁_pow : (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 = 8 ^ 8 / 3 ^ 7 := by
  rw [div_pow, ← Real.rpow_natCast ((3 : ℝ) ^ ((7 : ℝ) / 8)), ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem c₂_pow : (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)) ^ 16 = 12 ^ 16 / 5 ^ 15 := by
  rw [div_pow, ← Real.rpow_natCast ((5 : ℝ) ^ ((15 : ℝ) / 16)), ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem c₃_pow : (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)) ^ 32 = 512 ^ 32 / 255 ^ 31 := by
  rw [div_pow, ← Real.rpow_natCast ((255 : ℝ) ^ ((31 : ℝ) / 32)), ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem c₄_pow : ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ 4 =
    2 ^ 5 * ((2 ^ 16 + 1) / 2 ^ 16) ^ 4 := by
  rw [mul_div_assoc, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 4)),
    ← Real.rpow_mul (by norm_num)]
  norm_num

private theorem c₂_le_c₁ : 12 / (5 : ℝ) ^ ((15 : ℝ) / 16) ≤ 8 / (3 : ℝ) ^ ((7 : ℝ) / 8) := by
  have h : (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 16 = (8 ^ 8 / 3 ^ 7) ^ 2 := by
    rw [← c₁_pow, ← pow_mul]
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (16 : ℕ) ≠ 0),
    c₂_pow, h]
  norm_num

private theorem c₃_le_c₁ : 512 / (255 : ℝ) ^ ((31 : ℝ) / 32) ≤ 8 / (3 : ℝ) ^ ((7 : ℝ) / 8) := by
  have h : (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 32 = (8 ^ 8 / 3 ^ 7) ^ 4 := by
    rw [← c₁_pow, ← pow_mul]
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (32 : ℕ) ≠ 0),
    c₃_pow, h]
  norm_num

private theorem c₄_le_c₁ :
    (2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16 ≤ 8 / (3 : ℝ) ^ ((7 : ℝ) / 8) := by
  have h : ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ 8 =
      (2 ^ 5 * ((2 ^ 16 + 1) / 2 ^ 16) ^ 4) ^ 2 := by
    rw [← c₄_pow, ← pow_mul]
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (8 : ℕ) ≠ 0),
    h, c₁_pow]
  norm_num

end hbcAdmissible_half_prime_prod_le_of_five_le

open hbcAdmissible_half_prime_prod_le_of_five_le in
/-- **Product bounds for prime tuples at $1/2$ by size of the first prime.** Let
$p_1 < p_2 < \dots < p_k$ be primes with
$\prod_{i=1}^{k} (1 - 1/p_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/p_i)$ and $p_1 \ge 5$, and let
$F_k(x) = x^{2^k} - x^{2^{k-1}}$ and $P = \prod_{i=1}^{k} p_i$. Then $P \le F_k(\sqrt{8/3^{7/8}})$.
Moreover, if $6 \le p_1 < 18$, then $P \le F_k(\sqrt{12/5^{15/16}})$; if $18 \le p_1 < 258$, then
$P \le F_k(\sqrt{512/255^{31/32}})$; and if $p_1 \ge 258$, then
$P \le F_k\bigl(\sqrt{2^{5/4} (2^{16} + 1)/2^{16}}\bigr)$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 7. -/
public theorem hbcAdmissible_half_prime_prod_le_of_five_le (k : ℕ) (y : ℕ → ℕ)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hprime : ∀ i ∈ Finset.Icc 1 k, (y i).Prime)
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (h5 : 5 ≤ y 1) :
    let F : ℝ → ℝ := fun x => x ^ 2 ^ k - x ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (8 / (3 : ℝ) ^ ((7 : ℝ) / 8))) ∧
      (6 ≤ y 1 → y 1 < 18 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)))) ∧
      (18 ≤ y 1 → y 1 < 258 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)))) ∧
      (258 ≤ y 1 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          F (Real.sqrt ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16))) := by
  intro F
  have hy5 : (5 : ℝ) ≤ y 1 := by exact_mod_cast h5
  -- The tuple has at least two terms.
  have hk2 : 2 ≤ k := by
    by_contra hk
    interval_cases k
    · norm_num at hle
    · rw [Icc_self, prod_singleton] at hle
      have : 1 / (y 1 : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hy5
      linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  rw [Nat.add_sub_cancel] at hlt
  have hyprime : ∀ j, 1 ≤ j → j ≤ m + 1 → (y j).Prime := fun j h1 h2 =>
    hprime j (mem_Icc.mpr ⟨h1, h2⟩)
  obtain ⟨p, hp⟩ : ∃ p, y 1 = p := ⟨_, rfl⟩
  have hpprime : p.Prime := hp ▸ hyprime 1 le_rfl (by omega)
  rw [hp] at h5 hy5
  rw [hp]
  -- The primes after the first grow by at least two at each step.
  have hygrow : ∀ j, 1 ≤ j → j ≤ m + 1 → p + 2 * (j - 1) ≤ y j := by
    intro j h1 h2
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [hp]
      · have h := ih hj (by omega)
        have hlt' := hmono j hj (by omega)
        have hoddj : Odd (y j) := (hyprime j hj (by omega)).odd_of_ne_two (by omega)
        have hoddj1 : Odd (y (j + 1)) :=
          (hyprime (j + 1) (by omega) h2).odd_of_ne_two (by omega)
        obtain ⟨r, hr⟩ := hoddj
        obtain ⟨s, hs⟩ := hoddj1
        omega
  have hu_ge : ∀ i < m, p + 2 * (i + 1) ≤ y (i + 2) := fun i hi => by
    have := hygrow (i + 2) (by omega) (by omega)
    omega
  have hp0 : (0 : ℝ) < p := by linarith
  have hdR : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hfacp : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  -- The tail `p₂, …, p_k` is HBC-admissible for `p₁ / (2 (p₁ - 1))`.
  have hle' : ∏ i ∈ range m, (1 - 1 / (y (i + 2) : ℝ)) ≤ (p : ℝ) / (p + ((p - 2 : ℕ) : ℝ)) := by
    rw [prod_Icc_one_eq (fun i => 1 - 1 / (y i : ℝ)) m, hp, hfacp, div_mul_eq_mul_div,
      div_le_iff₀ hp0] at hle
    rw [hdR, le_div_iff₀ (by linarith)]
    nlinarith
  have hlt' : (p : ℝ) / (p + ((p - 2 : ℕ) : ℝ)) <
      ∏ i ∈ range (m - 1), (1 - 1 / (y (i + 2) : ℝ)) := by
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hn, prod_Icc_one_eq (fun i => 1 - 1 / (y i : ℝ)) n, hp, hfacp, div_mul_eq_mul_div,
      lt_div_iff₀ hp0] at hlt
    rw [hdR, div_lt_iff₀ (by linarith), hn, Nat.add_sub_cancel]
    nlinarith
  obtain ⟨κ, hκ1, hκm, hfirst, hκlt, hκeq⟩ := hbc_recursion m p (p - 2) (fun i => y (i + 2))
    (by omega) (by omega) hm1
    (fun i hi => by
      rw [show i + 1 + 2 = i + 2 + 1 by omega]
      exact hmono (i + 2) (by omega) (by omega))
    (by change 0 < y 2; have := hygrow 2 (by omega) (by omega); omega) hle' hlt'
  rw [hdR] at hfirst hκlt hκeq
  set α : ℝ := ((p : ℝ) + ((p : ℝ) - 2)) / ((p : ℝ) - 2) with hα_def
  have hd1 : (1 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  have hα1 : 1 ≤ α := by
    rw [hα_def, le_div_iff₀ (by linarith)]
    linarith
  have hα0 : 0 ≤ α := by linarith
  -- Reduce each claim to a bound on `(p₁ - 2) α ^ 2 ^ κ`.
  have hbound : ∀ c : ℝ, 0 ≤ c → ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ c ^ 2 ^ κ →
      ∏ i ∈ Icc 1 (m + 1), (y i : ℝ) ≤ F (Real.sqrt c) := by
    intro c hc hcκ
    have hX : ∏ i ∈ Icc 1 (m + 1), (y i : ℝ) = (p : ℝ) * ∏ i ∈ range m, (y (i + 2) : ℝ) := by
      rw [prod_Icc_one_eq (fun i => (y i : ℝ)) m, hp]
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hF : F (Real.sqrt c) = c ^ 2 ^ m - c ^ 2 ^ (m - 1) := by
      simp only [F]
      rw [Nat.add_sub_cancel, hn, Nat.add_sub_cancel, sqrt_pow_two_pow hc, sqrt_pow_two_pow hc]
    rw [hX, hF]
    exact range_bound hκ1 hκm hd1 hα1 hκlt hκeq hcκ
  have hPlow : ∀ q : ℝ, 0 ≤ q → q ≤ p → ∀ j ≤ m,
      ∏ i ∈ range j, (q + 2 * ((i : ℝ) + 1)) ≤ ∏ i ∈ range j, (y (i + 2) : ℝ) := by
    intro q hq hqp j hj
    apply prod_le_prod₀
    · intro i _
      positivity
    · intro i hi
      rw [mem_range] at hi
      have h' : ((p + 2 * (i + 1) : ℕ) : ℝ) ≤ (y (i + 2) : ℝ) := by
        exact_mod_cast hu_ge i (by omega)
      push_cast at h'
      linarith
  -- First prime `5`.
  have hA : p = 5 → ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 2 ^ κ := by
    intro hp5
    have hpr : (p : ℝ) = 5 := by exact_mod_cast hp5
    have hαv : α = 8 / 3 := by
      rw [hα_def, hpr]
      norm_num
    have hκ3 : 3 ≤ κ := le_index (A := 8 / 3)
      (L := fun j => ∏ i ∈ range j, ((5 : ℝ) + 2 * ((i : ℝ) + 1))) hκ1 hκm hp0.le (by linarith)
      hα0 hαv.le (fun j hj => hPlow 5 (by norm_num) (by linarith) j hj) hfirst (by
        intro j hj1 hj3
        rw [hpr]
        interval_cases j <;> norm_num [prod_range_succ])
    apply lift_pow hκ3 hd1 hα0
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, c₁_pow, hαv, hpr]
    norm_num
  -- First prime between `6` and `18`.
  have hB : 6 ≤ p → p < 18 →
      ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)) ^ 2 ^ κ := by
    intro h6 h18
    have hp7 : 7 ≤ p := by
      by_contra h
      have h6' : p = 6 := by omega
      rw [h6'] at hpprime
      norm_num at hpprime
    have hp7R : (7 : ℝ) ≤ p := by exact_mod_cast hp7
    have hαA : α ≤ 12 / 5 := by
      rw [hα_def, div_le_iff₀ (by linarith)]
      linarith
    have hκ4 : 4 ≤ κ := le_index (A := 12 / 5)
      (L := fun j => ∏ i ∈ range j, ((7 : ℝ) + 2 * ((i : ℝ) + 1))) hκ1 hκm hp0.le (by linarith)
      hα0 hαA (fun j hj => hPlow 7 (by norm_num) hp7R j hj) hfirst (by
        intro j hj1 hj4
        interval_cases j <;> norm_num [prod_range_succ] <;> linarith)
    apply lift_pow hκ4 hd1 hα0
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, c₂_pow]
    have key : ∀ q : ℕ, q.Prime → 6 ≤ q → q < 18 →
        ((q : ℝ) - 2) * (((q : ℝ) + ((q : ℝ) - 2)) / ((q : ℝ) - 2)) ^ 16 ≤ 12 ^ 16 / 5 ^ 15 := by
      intro q hq hq6 hq18
      revert hq
      interval_cases q <;> norm_num
    exact key p hpprime h6 h18
  -- First prime between `18` and `258`.
  have hC : 18 ≤ p → p < 258 →
      ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)) ^ 2 ^ κ := by
    intro h18 h258
    have hp18R : (18 : ℝ) ≤ p := by exact_mod_cast h18
    have hp257R : (p : ℝ) ≤ 257 := by exact_mod_cast (show p ≤ 257 by omega)
    rcases Nat.lt_or_ge p 89 with h89 | h89
    · have hαA : α ≤ 17 / 8 := by
        rw [hα_def, div_le_iff₀ (by linarith)]
        linarith
      have hκ5 : 5 ≤ κ := le_index (A := 17 / 8)
        (L := fun j => ∏ i ∈ range j, ((18 : ℝ) + 2 * ((i : ℝ) + 1))) hκ1 hκm hp0.le
        (by linarith) hα0 hαA (fun j hj => hPlow 18 (by norm_num) hp18R j hj) hfirst (by
          intro j hj1 hj5
          interval_cases j <;> norm_num [prod_range_succ] <;> linarith)
      apply lift_pow hκ5 hd1 hα0
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num, c₃_pow]
      rcases Nat.lt_or_ge p 42 with h42 | h42
      · have hp41 : (p : ℝ) ≤ 41 := by exact_mod_cast (show p ≤ 41 by omega)
        calc ((p : ℝ) - 2) * α ^ 32 ≤ 39 * (17 / 8) ^ 32 :=
              mul_le_mul (by linarith) (pow_le_pow_left₀ hα0 hαA 32) (pow_nonneg hα0 _)
                (by norm_num)
          _ ≤ 512 ^ 32 / 255 ^ 31 := by norm_num
      · have hp42R : (42 : ℝ) ≤ p := by exact_mod_cast h42
        have hp88 : (p : ℝ) ≤ 88 := by exact_mod_cast (show p ≤ 88 by omega)
        have hαA' : α ≤ 41 / 20 := by
          rw [hα_def, div_le_iff₀ (by linarith)]
          linarith
        calc ((p : ℝ) - 2) * α ^ 32 ≤ 86 * (41 / 20) ^ 32 :=
              mul_le_mul (by linarith) (pow_le_pow_left₀ hα0 hαA' 32) (pow_nonneg hα0 _)
                (by norm_num)
          _ ≤ 512 ^ 32 / 255 ^ 31 := by norm_num
    · have hp89R : (89 : ℝ) ≤ p := by exact_mod_cast h89
      have hαA : α ≤ 176 / 87 := by
        rw [hα_def, div_le_iff₀ (by linarith)]
        linarith
      have hκ6 : 6 ≤ κ := le_index (A := 176 / 87)
        (L := fun j => ∏ i ∈ range j, ((89 : ℝ) + 2 * ((i : ℝ) + 1))) hκ1 hκm hp0.le
        (by linarith) hα0 hαA (fun j hj => hPlow 89 (by norm_num) hp89R j hj) hfirst (by
          intro j hj1 hj6
          interval_cases j <;> norm_num [prod_range_succ] <;> linarith)
      apply lift_pow hκ6 hd1 hα0
      rw [show (2 : ℕ) ^ 6 = 32 * 2 by norm_num,
        pow_mul (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)) 32 2, c₃_pow]
      calc ((p : ℝ) - 2) * α ^ (32 * 2) ≤ 255 * (176 / 87) ^ (32 * 2) :=
            mul_le_mul (by linarith) (pow_le_pow_left₀ hα0 hαA _) (pow_nonneg hα0 _)
              (by norm_num)
        _ ≤ (512 ^ 32 / 255 ^ 31) ^ 2 := by norm_num
  -- First prime at least `258`.
  have hD : 258 ≤ p → ((p : ℝ) - 2) * α ^ 2 ^ κ ≤
      ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ 2 ^ κ := by
    intro h258
    have hp258R : (258 : ℝ) ≤ p := by exact_mod_cast h258
    have hαA : α ≤ 257 / 128 := by
      rw [hα_def, div_le_iff₀ (by linarith)]
      linarith
    have hPκ : (p : ℝ) ^ κ ≤ ∏ i ∈ range κ, (y (i + 2) : ℝ) := by
      have e : (p : ℝ) ^ κ = ∏ i ∈ range κ, (p : ℝ) := by rw [prod_const, card_range]
      rw [e]
      apply prod_le_prod₀
      · intro i _
        positivity
      · intro i hi
        rw [mem_range] at hi
        exact_mod_cast (show p ≤ y (i + 2) by have := hu_ge i (by omega); omega)
    have hpow : (p : ℝ) ^ κ < α ^ 2 ^ κ := by
      have h1 : (p : ℝ) * (p : ℝ) ^ κ ≤ (p : ℝ) * ∏ i ∈ range κ, (y (i + 2) : ℝ) :=
        mul_le_mul_of_nonneg_left hPκ hp0.le
      have h2 : ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ (p : ℝ) * α ^ 2 ^ κ :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hα0 _)
      have h3 : (p : ℝ) * (p : ℝ) ^ κ < (p : ℝ) * α ^ 2 ^ κ := by linarith
      exact lt_of_mul_lt_mul_left h3 hp0.le
    have hκ5 : 5 ≤ κ := by
      by_contra h
      have hα' : α ^ 2 ^ κ ≤ (257 / 128) ^ 2 ^ κ := pow_le_pow_left₀ hα0 hαA _
      have hp' : (258 : ℝ) ^ κ ≤ (p : ℝ) ^ κ := pow_le_pow_left₀ (by norm_num) hp258R _
      have hcon : (258 : ℝ) ^ κ < (257 / 128) ^ 2 ^ κ := hp'.trans_lt (hpow.trans_le hα')
      clear hfirst hκlt hκeq hbound hA hB hC hPκ hpow hα' hp'
      interval_cases κ <;> norm_num at hcon
    have hc₄4 : ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ 4 ≥ 32 := by
      rw [c₄_pow]
      norm_num
    have hdκ : ((p : ℝ) - 2) ^ κ ≤ α ^ 2 ^ κ :=
      (pow_le_pow_left₀ (by linarith) (by linarith : (p : ℝ) - 2 ≤ p) κ).trans hpow.le
    have hακ : α ^ (κ + 1) ≤ ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ κ := by
      rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0),
        ← pow_mul, ← pow_mul, mul_comm κ 4, pow_mul _ 4 κ]
      obtain ⟨s, rfl⟩ : ∃ s, κ = 5 + s := ⟨κ - 5, by omega⟩
      calc α ^ ((5 + s + 1) * 4) ≤ (257 / 128) ^ ((5 + s + 1) * 4) :=
            pow_le_pow_left₀ hα0 hαA _
        _ = (257 / 128) ^ 24 * ((257 / 128) ^ 4) ^ s := by
            rw [← pow_mul, ← pow_add]
            ring_nf
        _ ≤ 32 ^ 5 * 32 ^ s :=
            mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) s)
              (by positivity) (by positivity)
        _ = 32 ^ (5 + s) := by rw [pow_add]
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hc₄4 _
    have hD0 : 0 ≤ ((p : ℝ) - 2) * α ^ 2 ^ κ := mul_nonneg (by linarith) (pow_nonneg hα0 _)
    have hfin : (((p : ℝ) - 2) * α ^ 2 ^ κ) ^ κ ≤
        (((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ 2 ^ κ) ^ κ := by
      calc (((p : ℝ) - 2) * α ^ 2 ^ κ) ^ κ = ((p : ℝ) - 2) ^ κ * (α ^ 2 ^ κ) ^ κ := mul_pow _ _ _
        _ ≤ α ^ 2 ^ κ * (α ^ 2 ^ κ) ^ κ :=
            mul_le_mul_of_nonneg_right hdκ (pow_nonneg (pow_nonneg hα0 _) _)
        _ = (α ^ (κ + 1)) ^ 2 ^ κ := by rw [← pow_succ', ← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16) ^ κ) ^ 2 ^ κ :=
            pow_le_pow_left₀ (pow_nonneg hα0 _) hακ _
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ hD0 (by positivity) (by omega : κ ≠ 0)).mp hfin
  -- Assemble the four bounds.
  have hc : ∀ {c c' : ℝ}, 0 ≤ c → c ≤ c' → ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ c ^ 2 ^ κ →
      ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ c' ^ 2 ^ κ := fun hc0 hcc' h =>
    h.trans (pow_le_pow_left₀ hc0 hcc' _)
  have h₁ : ((p : ℝ) - 2) * α ^ 2 ^ κ ≤ (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 2 ^ κ := by
    rcases Nat.lt_or_ge p 6 with h6 | h6
    · exact hA (by omega)
    rcases Nat.lt_or_ge p 18 with h18 | h18
    · exact hc (by positivity) c₂_le_c₁ (hB h6 h18)
    rcases Nat.lt_or_ge p 258 with h258 | h258
    · exact hc (by positivity) c₃_le_c₁ (hC h18 h258)
    · exact hc (by positivity) c₄_le_c₁ (hD h258)
  exact ⟨hbound _ (by positivity) h₁, fun h6 h18 => hbound _ (by positivity) (hB h6 h18),
    fun h18 h258 => hbound _ (by positivity) (hC h18 h258),
    fun h258 => hbound _ (by positivity) (hD h258)⟩

end MetaMathlibExt
