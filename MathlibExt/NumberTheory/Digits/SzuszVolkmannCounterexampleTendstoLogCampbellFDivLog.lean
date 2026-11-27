/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample

/-! # Growth exponent of Campbell's interpolation

This module proves that for Campbell's interpolation `f`, `log f x / log x` tends to `2`
as `x → ∞` over the reals (`tendsto_log_campbellF_div_log`); that is, `η(f) = 2`, where
`η(h) = lim_{x → ∞} log h x / log x`. The proof traps `f` on each decade past `100`
between consecutive values of Campbell's sequence `h₂`, bounds `h₂` at powers of ten
between fixed multiples of their squares, and squeezes `log f x - 2 log x` in a constant.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 6
(`jis-2026-26.3.4-lem-6`).
-/

namespace MetaMathlibExt

@[expose] public section

namespace tendsto_log_campbellF_div_log

-- Upper bound: `h₂ (10 ^ j)` is at most `(10 ^ j) ^ 2`. Every term of the defining sum
-- is at most `10 ^ j`, and rounding the partial sum down can only decrease it.
private theorem campbellH2_pow_le (j : ℕ) :
    ((campbellH2 (10 ^ j) : ℕ) : ℝ) ≤ (10 : ℝ) ^ j * 10 ^ j := by
  have hlog : Nat.log 10 (10 ^ j) = j := Nat.log_pow (by decide) j
  have hterm : ∀ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i ≤ 10 ^ j := by
    intro i hi
    obtain ⟨-, hhi⟩ := Finset.mem_Icc.mp hi
    by_cases h10 : i < 10
    · simp [campbellH1, h10]
    · have hlogi : Nat.log 10 i ≤ j := by
        have hle : Nat.log 10 i ≤ Nat.log 10 (10 ^ j) := Nat.log_mono_right hhi
        have hlogj : Nat.log 10 (10 ^ j) = j := Nat.log_pow (by decide) j
        rwa [hlogj] at hle
      have hif : campbellH1 i = 10 ^ Nat.log 10 i := by simp [campbellH1, h10]
      rw [hif]
      exact Nat.pow_le_pow_right (by decide) hlogi
  have hsum : ∑ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i ≤ 10 ^ j * 10 ^ j := by
    calc ∑ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i
        ≤ ∑ i ∈ Finset.Icc 1 (10 ^ j), 10 ^ j := Finset.sum_le_sum hterm
      _ = (Finset.Icc 1 (10 ^ j)).card * 10 ^ j := Finset.sum_const_nat (fun i _ => rfl)
      _ = 10 ^ j * 10 ^ j := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h2eq : campbellH2 (10 ^ j)
      = 10 ^ j * ((∑ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i) / 10 ^ j) := by
    simp [campbellH2, hlog]
  have hround : 10 ^ j * ((∑ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i) / 10 ^ j)
      ≤ ∑ i ∈ Finset.Icc 1 (10 ^ j), campbellH1 i :=
    Nat.mul_div_le _ _
  have hnat : campbellH2 (10 ^ j) ≤ 10 ^ j * 10 ^ j := by
    rw [h2eq]
    exact hround.trans hsum
  exact_mod_cast hnat

-- Lower bound: `h₂ (10 ^ (m + 1))` is at least `8 * (10 ^ m) ^ 2`. The last decimal
-- block contributes `9 * 10 ^ m * 10 ^ m` to the defining sum, while the rounding-down
-- loses less than `10 ^ (m + 1) ≤ 10 ^ m * 10 ^ m`.
private theorem le_campbellH2_pow (m : ℕ) (hm : 1 ≤ m) :
    (8 : ℝ) * 10 ^ m * 10 ^ m ≤ ((campbellH2 (10 ^ (m + 1)) : ℕ) : ℝ) := by
  have hlog : Nat.log 10 (10 ^ (m + 1)) = m + 1 := Nat.log_pow (by decide) (m + 1)
  have hposm : 1 ≤ 10 ^ m := one_le_pow₀ (by norm_num)
  have hterm : ∀ i ∈ Finset.Icc (10 ^ m) (10 ^ (m + 1) - 1), campbellH1 i = 10 ^ m := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    have h10 : ¬ i < 10 := by
      have h10m : 10 ≤ 10 ^ m :=
        calc (10 : ℕ) = 10 ^ 1 := by norm_num
          _ ≤ 10 ^ m := Nat.pow_le_pow_right (by decide) hm
      omega
    have hlogi : Nat.log 10 i = m := Nat.log_eq_of_pow_le_of_lt_pow hlo (by omega)
    simp [campbellH1, h10, hlogi]
  have hcard : (Finset.Icc (10 ^ m) (10 ^ (m + 1) - 1)).card = 9 * 10 ^ m := by
    rw [Nat.card_Icc]
    have h10 : 10 ^ (m + 1) = 10 ^ m * 10 := pow_succ 10 m
    omega
  have hblock :
      ∑ i ∈ Finset.Icc (10 ^ m) (10 ^ (m + 1) - 1), campbellH1 i = 9 * 10 ^ m * 10 ^ m := by
    rw [Finset.sum_const_nat hterm, hcard]
  have hsub : Finset.Icc (10 ^ m) (10 ^ (m + 1) - 1) ⊆ Finset.Icc 1 (10 ^ (m + 1)) :=
    Finset.Icc_subset_Icc hposm (by omega)
  have hle : 9 * 10 ^ m * 10 ^ m ≤ ∑ i ∈ Finset.Icc 1 (10 ^ (m + 1)), campbellH1 i := by
    rw [← hblock]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
  have h2eq : campbellH2 (10 ^ (m + 1))
      = 10 ^ (m + 1) * ((∑ i ∈ Finset.Icc 1 (10 ^ (m + 1)), campbellH1 i) / 10 ^ (m + 1)) := by
    simp [campbellH2, hlog]
  have hmod : (∑ i ∈ Finset.Icc 1 (10 ^ (m + 1)), campbellH1 i) % 10 ^ (m + 1)
      < 10 ^ (m + 1) :=
    Nat.mod_lt _ (by positivity)
  have hround : ∑ i ∈ Finset.Icc 1 (10 ^ (m + 1)), campbellH1 i
      ≤ campbellH2 (10 ^ (m + 1)) + 10 ^ (m + 1) := by
    have hdm :=
      Nat.div_add_mod (∑ i ∈ Finset.Icc 1 (10 ^ (m + 1)), campbellH1 i) (10 ^ (m + 1))
    omega
  have h10m : (10 : ℝ) ≤ 10 ^ m :=
    calc (10 : ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hB : (10 : ℝ) ^ (m + 1) ≤ (10 : ℝ) ^ m * 10 ^ m := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left h10m (by positivity)
  have hcast : (9 : ℝ) * 10 ^ m * 10 ^ m
      ≤ ((campbellH2 (10 ^ (m + 1)) : ℕ) : ℝ) + 10 ^ (m + 1) := by
    exact_mod_cast hle.trans hround
  linarith

-- On each decade past `100`, monotonicity traps `f` between the values of `h₂` at the
-- decade endpoints, hence between the bounds of the two lemmas above.
private theorem campbellF_bounds (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx1 : (10 : ℝ) ^ (m + 1) ≤ x) (hx2 : x < (10 : ℝ) ^ (m + 2)) :
    (8 : ℝ) * 10 ^ m * 10 ^ m ≤ campbellF x
      ∧ campbellF x ≤ (10 : ℝ) ^ (m + 2) * 10 ^ (m + 2) := by
  have e1 : ((10 ^ (m + 1) : ℕ) : ℝ) = (10 : ℝ) ^ (m + 1) := by norm_cast
  have e2 : ((10 ^ (m + 2) : ℕ) : ℝ) = (10 : ℝ) ^ (m + 2) := by norm_cast
  have h10a : 10 ≤ 10 ^ (m + 1) :=
    calc (10 : ℕ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h10b : 10 ≤ 10 ^ (m + 2) :=
    calc (10 : ℕ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (m + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hx0 : (0 : ℝ) ≤ x := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (m + 1) := by positivity
    linarith
  have hlo : campbellF ((10 ^ (m + 1) : ℕ) : ℝ) ≤ campbellF x :=
    campbellF_monotoneOn (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Set.mem_Ici.2 hx0)
      (by rw [e1]; exact hx1)
  have hhi : campbellF x ≤ campbellF ((10 ^ (m + 2) : ℕ) : ℝ) :=
    campbellF_monotoneOn (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (Nat.cast_nonneg _))
      (by rw [e2]; exact hx2.le)
  rw [floor_campbellF_eq_campbellH2.2 _ h10a] at hlo
  rw [floor_campbellF_eq_campbellH2.2 _ h10b] at hhi
  exact ⟨(le_campbellH2_pow m hm).trans hlo, hhi.trans (campbellH2_pow_le (m + 2))⟩

-- `|log f x - 2 log x|` is at most `4 log 10` on each decade past `100`: both
-- logarithms lie between consecutive multiples of `log 10` determined by the decade.
private theorem abs_log_campbellF_sub (m : ℕ) (hm : 1 ≤ m) (x : ℝ)
    (hx1 : (10 : ℝ) ^ (m + 1) ≤ x) (hx2 : x < (10 : ℝ) ^ (m + 2)) :
    |Real.log (campbellF x) - 2 * Real.log x| ≤ 4 * Real.log 10 := by
  have hL : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have ecast1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_cast
  have ecast2 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by norm_cast
  obtain ⟨hflower, hfupper⟩ := campbellF_bounds m hm x hx1 hx2
  have hApos : (0 : ℝ) < 8 * 10 ^ m * 10 ^ m := by positivity
  have hfpos : (0 : ℝ) < campbellF x := lt_of_lt_of_le hApos hflower
  have hxpos : (0 : ℝ) < x := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (m + 1) := by positivity
    linarith
  have hlogA : Real.log (8 * 10 ^ m * 10 ^ m)
      = Real.log 8 + (m : ℝ) * Real.log 10 + (m : ℝ) * Real.log 10 := by
    have ne1 : (8 : ℝ) * 10 ^ m ≠ 0 := by positivity
    have ne2 : (10 : ℝ) ^ m ≠ 0 := by positivity
    have ne8 : (8 : ℝ) ≠ 0 := by norm_num
    rw [Real.log_mul ne1 ne2, Real.log_mul ne8 ne2, Real.log_pow]
  have hloglo : Real.log 8 + (m : ℝ) * Real.log 10 + (m : ℝ) * Real.log 10
      ≤ Real.log (campbellF x) := by
    rw [← hlogA]
    exact Real.log_le_log hApos hflower
  have hlogB : Real.log ((10 : ℝ) ^ (m + 2) * 10 ^ (m + 2))
      = ((m : ℝ) + 2) * Real.log 10 + ((m : ℝ) + 2) * Real.log 10 := by
    have neB : (10 : ℝ) ^ (m + 2) ≠ 0 := by positivity
    rw [Real.log_mul neB neB, Real.log_pow, ecast2]
  have hloghi : Real.log (campbellF x)
      ≤ ((m : ℝ) + 2) * Real.log 10 + ((m : ℝ) + 2) * Real.log 10 := by
    rw [← hlogB]
    exact Real.log_le_log hfpos hfupper
  have hlogxlo : ((m : ℝ) + 1) * Real.log 10 ≤ Real.log x := by
    have e : Real.log ((10 : ℝ) ^ (m + 1)) = ((m : ℝ) + 1) * Real.log 10 := by
      rw [Real.log_pow, ecast1]
    have hPpos : (0 : ℝ) < (10 : ℝ) ^ (m + 1) := by positivity
    rw [← e]
    exact Real.log_le_log hPpos hx1
  have hlogxhi : Real.log x < ((m : ℝ) + 2) * Real.log 10 := by
    have e : Real.log ((10 : ℝ) ^ (m + 2)) = ((m : ℝ) + 2) * Real.log 10 := by
      rw [Real.log_pow, ecast2]
    rw [← e]
    exact Real.log_lt_log hxpos hx2
  rw [abs_le]
  constructor <;> linarith

end tendsto_log_campbellF_div_log

/-- **Growth exponent of Campbell's interpolation.** For Campbell's interpolation $f$,
$\log f(x) / \log x \to 2$ as $x \to \infty$ over the reals; that is, $\eta(f) = 2$, where
$\eta(h) = \lim_{x \to \infty} \log h(x) / \log x$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 6
(`jis-2026-26.3.4-lem-6`). -/
public theorem tendsto_log_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (campbellF x) / Real.log x) Filter.atTop (nhds 2) := by
  have key : ∀ᶠ x : ℝ in Filter.atTop,
      |Real.log (campbellF x) / Real.log x - 2| ≤ 4 * Real.log 10 / Real.log x := by
    rw [Filter.eventually_atTop]
    refine ⟨100, fun x hx => ?_⟩
    have hx100 : (100 : ℝ) ≤ x := hx
    have h1x : (1 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos h1x
    have hlogxne : Real.log x ≠ 0 := ne_of_gt hlogx
    have hfloor : (100 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx100)
    have hk2 : 2 ≤ Nat.log 10 ⌊x⌋₊ := by
      have hmono : Nat.log 10 100 ≤ Nat.log 10 ⌊x⌋₊ := Nat.log_mono_right hfloor
      have h100 : Nat.log 10 100 = 2 := by decide
      omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.log 10 ⌊x⌋₊ ≠ 0 by omega)
    rw [Nat.succ_eq_add_one] at hm
    have hm1 : 1 ≤ m := by omega
    have h1pow : (10 : ℕ) ^ Nat.log 10 ⌊x⌋₊ ≤ ⌊x⌋₊ :=
      Nat.pow_log_le_self 10 (show ⌊x⌋₊ ≠ 0 by omega)
    have h2pow : ⌊x⌋₊ < (10 : ℕ) ^ (Nat.log 10 ⌊x⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by decide) ⌊x⌋₊
    have hx1 : (10 : ℝ) ^ (m + 1) ≤ x := by
      have hcast : ((10 ^ Nat.log 10 ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_le.mpr h1pow
      have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have h := hcast.trans hfl
      rw [hm] at h
      exact_mod_cast h
    have hx2 : x < (10 : ℝ) ^ (m + 2) := by
      have hle : ⌊x⌋₊ + 1 ≤ (10 : ℕ) ^ (Nat.log 10 ⌊x⌋₊ + 1) := h2pow
      have hlt : (⌊x⌋₊ : ℝ) + 1 ≤ ((10 ^ (Nat.log 10 ⌊x⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hle
      have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h := hfl.trans_le hlt
      rw [hm] at h
      have e : m + 1 + 1 = m + 2 := by omega
      rw [e] at h
      exact_mod_cast h
    have habs := tendsto_log_campbellF_div_log.abs_log_campbellF_sub m hm1 x hx1 hx2
    have hdecomp : Real.log (campbellF x) / Real.log x - 2
        = (Real.log (campbellF x) - 2 * Real.log x) / Real.log x := by
      rw [sub_div, mul_div_cancel_right₀ _ hlogxne]
    rw [hdecomp, abs_div, abs_of_pos hlogx, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right habs (le_of_lt (inv_pos.mpr hlogx))
  have hC0 : Filter.Tendsto (fun x : ℝ => 4 * Real.log 10 / Real.log x) Filter.atTop (nhds 0) := by
    have h :=
      Filter.Tendsto.const_mul (4 * Real.log 10) Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa [div_eq_mul_inv, Pi.inv_apply] using h
  have h2c : Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) := tendsto_const_nhds
  have hg : Filter.Tendsto (fun x : ℝ => 2 - 4 * Real.log 10 / Real.log x) Filter.atTop
      (nhds 2) := by
    simpa using h2c.sub hC0
  have hh : Filter.Tendsto (fun x : ℝ => 2 + 4 * Real.log 10 / Real.log x) Filter.atTop
      (nhds 2) := by
    simpa using h2c.add hC0
  have hle1 : ∀ᶠ x : ℝ in Filter.atTop,
      2 - 4 * Real.log 10 / Real.log x ≤ Real.log (campbellF x) / Real.log x := by
    refine key.mono fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    linarith
  have hle2 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (campbellF x) / Real.log x ≤ 2 + 4 * Real.log 10 / Real.log x := by
    refine key.mono fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh hle1 hle2

end

end MetaMathlibExt
