/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import MathlibExt.Analysis.SpecificLimits.DirichletTest
import MathlibExt.NumberTheory.ArithmeticFunction.DirichletHyperbola

/-!
# Partial sums of Dirichlet characters and of `1 * χ`

Let `χ` be a nontrivial Dirichlet character modulo `q`. We prove the trivial bound
`|∑_{m ≤ n < m'} χ n| ≤ q` for character sums over intervals, the resulting Abel summation
bound, and the quantitative convergence of `∑ χ n / n` to `L(1, χ)`:

`|L(1, χ) - ∑_{n ≤ M} χ n / n| ≤ q / (M + 1)`.

Combined with Dirichlet's hyperbola method this gives the mean value of the divisor sum
`(1 * χ)(n) = ∑_{d ∣ n} χ d` (Mathlib's `DirichletCharacter.zetaMul`):

`∑_{n ≤ x} (1 * χ)(n) = x L(1, χ) + O(q √x)`,

with an absolute implied constant, and its weighted variant

`∑_{n ≤ x} (1 * χ)(n) / √n = 2 L(1, χ) √x + O(q)`.

## Main statements

* `ZMod.norm_sum_Ico_le_of_sum_eq_zero`: `‖∑_{m ≤ n < m'} Φ n‖ ≤ ∑_a ‖Φ a‖` for every
  `Φ : ZMod q → E` with total sum `0`.
* `DirichletCharacter.norm_sum_Ico_le`: `‖∑_{m ≤ n < m'} χ n‖ ≤ q` for `χ ≠ 1`.
* `DirichletCharacter.norm_sum_Ioc_mul_le_of_antitoneOn`: Abel's inequality for `χ`.
* `DirichletCharacter.norm_LFunction_one_sub_sum_Ioc_le`: the tail of `∑ χ n / n`.
* `DirichletCharacter.tendsto_sum_Ioc_div_atTop_nhds_LFunction_one`: `∑ χ n / n = L(1, χ)`.
* `DirichletCharacter.norm_sum_zetaMul_sub_le`: `∑_{n ≤ x} (1 * χ)(n) = x L(1, χ) + O(q √x)`,
  uniformly in `q`.
* `DirichletCharacter.sum_zetaMul_sub_isBigO_sqrt`: the same as an `IsBigO` statement.
* `DirichletCharacter.norm_sum_zetaMul_div_sqrt_sub_le` and
  `DirichletCharacter.sum_zetaMul_div_sqrt_sub_isBigO_one`:
  `∑_{n ≤ x} (1 * χ)(n) / √n = 2 L(1, χ) √x + O(q)`.
-/

@[expose] public section

open Finset Filter Asymptotics ArithmeticFunction

open scoped Topology ArithmeticFunction.zeta

namespace ZMod

variable {E : Type*} {q : ℕ} [NeZero q]

/-- A function on `ZMod q` summed over `q` consecutive integers gives its total sum. -/
theorem sum_Ico_add_eq_sum [AddCommMonoid E] (Φ : ZMod q → E) (m : ℕ) :
    ∑ n ∈ Ico m (m + q), Φ n = ∑ a, Φ a := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hshift : ∑ k ∈ range q, Φ ((m + k : ℕ) : ZMod q) = ∑ a : ZMod q, Φ ((m : ZMod q) + a) := by
    refine sum_nbij' (fun k ↦ (k : ZMod q)) (fun a ↦ a.val) (fun _ _ ↦ mem_univ _)
      (fun a _ ↦ mem_range.2 (ZMod.val_lt a)) (fun k hk ↦ ZMod.val_cast_of_lt (mem_range.1 hk))
      (fun a _ ↦ by simp) (fun k _ ↦ by push_cast; ring_nf)
  rw [hshift]
  exact Fintype.sum_equiv (Equiv.addLeft (m : ZMod q)) _ _ (fun _ ↦ rfl)

/-- **Sums of a mean-zero periodic function over intervals.** If `Φ : ZMod q → E` has total
sum `0`, then every sum of `Φ` over an interval of integers has norm at most `∑_a ‖Φ a‖`. -/
theorem norm_sum_Ico_le_of_sum_eq_zero [SeminormedAddCommGroup E] {Φ : ZMod q → E}
    (hΦ : ∑ a, Φ a = 0) (m n : ℕ) : ‖∑ k ∈ Ico m n, Φ k‖ ≤ ∑ a, ‖Φ a‖ := by
  rcases le_or_gt n m with hnm | hmn
  · simp only [Ico_eq_empty_of_le hnm, sum_empty, norm_zero]
    exact sum_nonneg fun _ _ ↦ norm_nonneg _
  have hblocks : ∀ k j : ℕ, ∑ n ∈ Ico j (j + q * k), Φ n = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro j
      rw [show j + q * (k + 1) = (j + q * k) + q by ring,
        ← sum_Ico_consecutive _ (Nat.le_add_right j (q * k)) (Nat.le_add_right _ q), ih j,
        sum_Ico_add_eq_sum, hΦ, add_zero]
  have hq : 0 < q := Nat.pos_of_neZero q
  set j := m + q * ((n - m) / q)
  have h1 : m ≤ j := Nat.le_add_right _ _
  have h2 : j ≤ n := by
    have := Nat.mul_div_le (n - m) q
    omega
  have h3 : n < j + q := by
    have := Nat.div_add_mod (n - m) q
    have := Nat.mod_lt (n - m) hq
    omega
  rw [← sum_Ico_consecutive _ h1 h2, hblocks, zero_add]
  -- The remaining block is shorter than `q`, so it meets each residue at most once.
  have hinj : Set.InjOn (fun k : ℕ ↦ (k : ZMod q)) (Ico j n : Set ℕ) := by
    intro k hk l hl hkl
    simp only [coe_Ico, Set.mem_Ico] at hk hl
    have h := (ZMod.natCast_eq_natCast_iff' k l q).mp hkl
    have h1 : k - l = 0 :=
      Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h))
        (by omega)
    have h2 : l - k = 0 :=
      Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm))
        (by omega)
    omega
  calc ‖∑ k ∈ Ico j n, Φ k‖ ≤ ∑ k ∈ Ico j n, ‖Φ k‖ := norm_sum_le _ _
    _ = ∑ a ∈ (Ico j n).image (fun k : ℕ ↦ (k : ZMod q)), ‖Φ a‖ :=
        (sum_image (f := fun a ↦ ‖Φ a‖) hinj).symm
    _ ≤ ∑ a, ‖Φ a‖ := sum_le_univ_sum_of_nonneg fun _ ↦ norm_nonneg _

end ZMod

namespace DirichletCharacter

section NormedField

variable {F : Type*} [NormedField F] {q : ℕ} [NeZero q] {χ : DirichletCharacter F q}

/-- A nontrivial Dirichlet character modulo `q` sums to zero over any `q` consecutive
integers. -/
theorem sum_Ico_add_modulus_eq_zero (hχ : χ ≠ 1) (m : ℕ) :
    ∑ n ∈ Ico m (m + q), χ n = 0 :=
  (ZMod.sum_Ico_add_eq_sum _ m).trans (MulChar.sum_eq_zero_of_ne_one hχ)

/-- **The trivial bound for character sums.** For a nontrivial Dirichlet character `χ` modulo
`q`, every sum of `χ` over an interval has norm at most `q`. -/
theorem norm_sum_Ico_le (hχ : χ ≠ 1) (m n : ℕ) : ‖∑ k ∈ Ico m n, χ k‖ ≤ q := by
  rcases le_or_gt n m with hnm | hmn
  · simp [Ico_eq_empty_of_le hnm]
  have hblocks : ∀ k j : ℕ, ∑ n ∈ Ico j (j + q * k), χ n = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro j
      rw [show j + q * (k + 1) = (j + q * k) + q by ring,
        ← sum_Ico_consecutive _ (Nat.le_add_right j (q * k)) (Nat.le_add_right _ q), ih j,
        sum_Ico_add_modulus_eq_zero hχ, add_zero]
  have hq : 0 < q := Nat.pos_of_neZero q
  have h1 : m ≤ m + q * ((n - m) / q) := Nat.le_add_right _ _
  have h2 : m + q * ((n - m) / q) ≤ n := by
    have := Nat.mul_div_le (n - m) q
    omega
  rw [← sum_Ico_consecutive _ h1 h2, hblocks, zero_add]
  calc ‖∑ k ∈ Ico (m + q * ((n - m) / q)) n, χ k‖
      ≤ ∑ _k ∈ Ico (m + q * ((n - m) / q)) n, (1 : ℝ) :=
        norm_sum_le_of_le _ fun k _ ↦ χ.norm_le_one _
    _ = ((n - (m + q * ((n - m) / q)) : ℕ) : ℝ) := by simp
    _ ≤ q := by
        have := Nat.mod_lt (n - m) hq
        have := Nat.div_add_mod (n - m) q
        exact_mod_cast (by omega)

/-- **The trivial bound for character sums**, for sums over `m < n ≤ m'`. -/
theorem norm_sum_Ioc_le (hχ : χ ≠ 1) (m n : ℕ) : ‖∑ k ∈ Ioc m n, χ k‖ ≤ q := by
  have : Ioc m n = Ico (m + 1) (n + 1) := by ext; simp only [mem_Ioc, mem_Ico]; omega
  rw [this]
  exact norm_sum_Ico_le hχ _ _

end NormedField

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Abel's inequality for character sums.** If `w` is nonincreasing and nonnegative on
`[m + 1, ∞)` and `χ` is a nontrivial Dirichlet character modulo `q`, then
`‖∑_{m < k ≤ n} χ k w k‖ ≤ q w (m + 1)`. -/
theorem norm_sum_Ioc_mul_le_of_antitoneOn (hχ : χ ≠ 1) {w : ℕ → ℝ} {m : ℕ}
    (hw : AntitoneOn w (Set.Ici (m + 1))) (hw0 : ∀ k, m + 1 ≤ k → 0 ≤ w k) (n : ℕ) :
    ‖∑ k ∈ Ioc m n, χ k * w k‖ ≤ q * w (m + 1) := by
  have hI : Ioc m n = Ico (m + 1) (n + 1) := by ext; simp only [mem_Ioc, mem_Ico]; omega
  have h := norm_sum_Ico_smul_le_of_antitoneOn (z := fun k ↦ χ k) hw hw0
    (norm_sum_Ico_le hχ (m + 1)) (n + 1)
  simpa [hI, Complex.real_smul, mul_comm] using h

/-- **The tail of `∑ χ n / n`.** For a nontrivial Dirichlet character `χ` modulo `q` and every
`M`, `‖L(1, χ) - ∑_{n ≤ M} χ n / n‖ ≤ q / (M + 1)`. -/
theorem norm_LFunction_one_sub_sum_Ioc_le (hχ : χ ≠ 1) (M : ℕ) :
    ‖LFunction χ 1 - ∑ n ∈ Ioc 0 M, χ n / n‖ ≤ q / (M + 1) := by
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  -- For real `σ > 1` the same bound holds with the weights `n ^ (-σ)`.
  have hσ : ∀ σ : ℝ, 1 < σ →
      ‖LFunction χ σ - ∑ n ∈ Ioc 0 M, ((n : ℝ) ^ (-σ) : ℝ) • χ n‖ ≤ q / (M + 1) := by
    intro σ hσ1
    have hre : 1 < (σ : ℂ).re := by simpa using hσ1
    rw [LFunction_eq_LSeries χ hre]
    have hterm : ∀ n : ℕ, LSeries.term (fun n ↦ χ n) σ n = ((n : ℝ) ^ (-σ) : ℝ) • χ n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [LSeries.term_of_ne_zero hn, Real.rpow_neg hn0.le, Complex.real_smul,
          Complex.ofReal_inv, Complex.ofReal_cpow hn0.le]
        push_cast
        ring
    have htend : Tendsto (fun N ↦ ∑ n ∈ range N, ((n : ℝ) ^ (-σ) : ℝ) • χ n) atTop
        (𝓝 (LSeries (fun n ↦ χ n) σ)) := by
      have hs : HasSum (LSeries.term (fun n ↦ χ n) σ) (LSeries (fun n ↦ χ n) σ) :=
        (LSeriesSummable_of_one_lt_re χ hre).hasSum
      rw [funext hterm] at hs
      exact hs.tendsto_sum_nat
    have hw : AntitoneOn (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) (Set.Ici (M + 1)) := by
      intro a ha b _ hab
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast le_trans (by omega) (Set.mem_Ici.1 ha)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by exact_mod_cast hab) (by linarith)
    have h := norm_sub_sum_range_smul_le_of_tendsto hw
      (fun k _ ↦ Real.rpow_nonneg (Nat.cast_nonneg k) _) (norm_sum_Ico_le hχ (M + 1)) htend
    have hrange : ∑ n ∈ range (M + 1), ((n : ℝ) ^ (-σ) : ℝ) • χ n
        = ∑ n ∈ Ioc 0 M, ((n : ℝ) ^ (-σ) : ℝ) • χ n := by
      have hI : Ico 1 (M + 1) = Ioc 0 M := by ext; simp only [mem_Ioc, mem_Ico]; omega
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), hI]
      simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
    rw [hrange] at h
    refine h.trans ?_
    have hlast : ((M + 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 / (M + 1) := by
      rw [one_div, ← Real.rpow_neg_one]
      push_cast
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc (q : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (-σ) ≤ q * (1 / (M + 1)) :=
          mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg q)
      _ = q / (M + 1) := by ring
  -- Let `σ → 1⁺`, using the continuity of the entire function `L(s, χ)`.
  have hcont : Continuous fun σ : ℝ ↦
      LFunction χ σ - ∑ n ∈ Ioc 0 M, ((n : ℝ) ^ (-σ) : ℝ) • χ n := by
    refine ((differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal).sub
      (continuous_finsetSum _ fun n hn ↦ ?_)
    have hn : (n : ℝ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1
      positivity
    exact ((Real.continuous_const_rpow hn).comp continuous_neg).smul continuous_const
  have hlim := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  have hval := le_of_tendsto hlim.norm
    (by filter_upwards [self_mem_nhdsWithin] with σ hσ1 using hσ σ hσ1)
  have heq : ∑ n ∈ Ioc 0 M, ((n : ℝ) ^ (-(1 : ℝ)) : ℝ) • χ n = ∑ n ∈ Ioc 0 M, χ n / n :=
    sum_congr rfl fun n _ ↦ by
      rw [Real.rpow_neg_one, Complex.real_smul, div_eq_mul_inv, mul_comm]
      push_cast
      rfl
  rwa [heq, Complex.ofReal_one] at hval

/-- **`L(1, χ)` as a conditionally convergent series.** For a nontrivial Dirichlet character
`χ`, the partial sums `∑_{n ≤ N} χ n / n` converge to `L(1, χ)`. -/
theorem tendsto_sum_Ioc_div_atTop_nhds_LFunction_one (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, χ n / (n : ℂ)) atTop (𝓝 (LFunction χ 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat
    (q : ℝ) |>.comp (tendsto_add_atTop_nat 1))
  rw [norm_sub_rev]
  simpa using norm_LFunction_one_sub_sum_Ioc_le hχ N

omit [NeZero q] in
/-- The divisor sum `(1 * χ)(n) = ∑_{d ∣ n} χ d`. -/
theorem zetaMul_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ.zetaMul n = ∑ d ∈ n.divisors, χ d := by
  rw [zetaMul, coe_zeta_mul_apply]
  refine sum_congr rfl fun d hd ↦ ?_
  simp [toArithmeticFunction, Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]

/-- **The mean value of `1 * χ`, uniformly in the modulus.** For a nontrivial Dirichlet
character `χ` modulo `q` and every `x ≥ 0`,

`‖∑_{n ≤ x} (1 * χ)(n) - x L(1, χ)‖ ≤ 4 q √x`. -/
theorem norm_sum_zetaMul_sub_le (hχ : χ ≠ 1) {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n - x * LFunction χ 1‖ ≤ 4 * q * √x := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_neZero q
  have hL : ‖LFunction χ 1‖ ≤ q := by simpa using norm_LFunction_one_sub_sum_Ioc_le hχ 0
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- For `x < 1` the sum is empty and `x ≤ √x`.
    rw [Nat.floor_eq_zero.2 hx1, Ioc_self, sum_empty, zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hx]
    have hxs : x ≤ √x := by
      rw [Real.le_sqrt hx hx]
      nlinarith
    calc x * ‖LFunction χ 1‖ ≤ √x * q := mul_le_mul hxs hL (norm_nonneg _) (Real.sqrt_nonneg x)
      _ ≤ 4 * q * √x := by nlinarith [Real.sqrt_nonneg x]
  set s := √x with hsdef
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hx1
  have hs0 : 0 < s := by linarith
  have hxs : x / s = s := Real.div_sqrt
  set M := ⌊s⌋₊ with hMdef
  have hMs : (M : ℝ) ≤ s := Nat.floor_le hs0.le
  have hsM : s < M + 1 := Nat.lt_floor_add_one s
  have hG : ∀ t : ℕ, ‖∑ d ∈ Ioc 0 t, χ d‖ ≤ q := norm_sum_Ioc_le hχ 0
  -- Dirichlet's hyperbola method for `χ * 1` with `y = √x`.
  have hyp := sum_Ioc_mul_eq_hyperbola (toArithmeticFunction (χ ·)) (ζ : ArithmeticFunction ℂ)
    x hs0
  rw [← mul_comm, ← zetaMul, hxs, ← hMdef] at hyp
  have hχd : ∀ t : ℕ, ∑ d ∈ Ioc 0 t, toArithmeticFunction (χ ·) d = ∑ d ∈ Ioc 0 t, χ d :=
    fun t ↦ sum_congr rfl fun d hd ↦ by
      simp [toArithmeticFunction, (mem_Ioc.1 hd).1.ne']
  have hζ : ∀ t : ℕ, ∑ e ∈ Ioc 0 t, (ζ : ArithmeticFunction ℂ) e = t := fun t ↦ by
    simp_rw [natCoe_apply]
    exact_mod_cast sum_Ioc_zeta t
  have hζe : ∀ e ∈ Ioc 0 M, (ζ : ArithmeticFunction ℂ) e = 1 := fun e he ↦ by
    simp [natCoe_apply, (mem_Ioc.1 he).1.ne']
  simp only [hχd, hζ] at hyp
  have hyp' : ∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n
      = ∑ d ∈ Ioc 0 M, χ d * (⌊x / d⌋₊ : ℂ) + ∑ e ∈ Ioc 0 M, ∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d
        - (∑ d ∈ Ioc 0 M, χ d) * M := by
    rw [hyp]
    congr 2
    · exact sum_congr rfl fun d hd ↦ by simp [toArithmeticFunction, (mem_Ioc.1 hd).1.ne']
    · exact sum_congr rfl fun e he ↦ by rw [hζe e he, mul_one]
  have key : ∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n - x * LFunction χ 1
      = (∑ d ∈ Ioc 0 M, χ d * (⌊x / d⌋₊ : ℂ) - x * ∑ d ∈ Ioc 0 M, χ d / d)
        - x * (LFunction χ 1 - ∑ d ∈ Ioc 0 M, χ d / d)
        + ∑ e ∈ Ioc 0 M, ∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d
        - (∑ d ∈ Ioc 0 M, χ d) * M := by
    rw [hyp']; ring
  have b1 : ‖∑ d ∈ Ioc 0 M, χ d * (⌊x / d⌋₊ : ℂ) - x * ∑ d ∈ Ioc 0 M, χ d / d‖ ≤ s := by
    refine (norm_sum_mul_natFloor_div_sub_mul_sum_div_le (fun d ↦ χ d) hx _).trans ?_
    calc ∑ d ∈ Ioc 0 M, ‖χ d‖ ≤ ∑ _d ∈ Ioc 0 M, (1 : ℝ) :=
          sum_le_sum fun d _ ↦ χ.norm_le_one _
      _ = M := by simp
      _ ≤ s := hMs
  have b2 : ‖(x : ℂ) * (LFunction χ 1 - ∑ d ∈ Ioc 0 M, χ d / d)‖ ≤ q * s := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]
    calc x * ‖LFunction χ 1 - ∑ d ∈ Ioc 0 M, χ d / d‖ ≤ x * (q / (M + 1)) :=
          mul_le_mul_of_nonneg_left (norm_LFunction_one_sub_sum_Ioc_le hχ M) hx
      _ ≤ x * (q / s) := by
          gcongr
      _ = q * (x / s) := by ring
      _ = q * s := by rw [hxs]
  have b3 : ‖∑ e ∈ Ioc 0 M, ∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d‖ ≤ q * s := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ e ∈ Ioc 0 M, ‖∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d‖ ≤ ∑ _e ∈ Ioc 0 M, (q : ℝ) :=
          sum_le_sum fun e _ ↦ hG _
      _ = M * q := by simp
      _ ≤ q * s := by nlinarith
  have b4 : ‖(∑ d ∈ Ioc 0 M, χ d) * (M : ℂ)‖ ≤ q * s := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul (hG M) hMs (Nat.cast_nonneg _) (by linarith)
  have tri : ∀ a b c d : ℂ, ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := fun a b c d ↦ by
    linarith [norm_sub_le (a - b + c) d, norm_add_le (a - b) c, norm_sub_le a b]
  rw [key]
  refine (tri _ _ _ _).trans ?_
  nlinarith

/-- **The mean value of `1 * χ`.** For a nontrivial Dirichlet character `χ`,
`∑_{n ≤ x} (1 * χ)(n) = x L(1, χ) + O(√x)`. -/
theorem sum_zetaMul_sub_isBigO_sqrt (hχ : χ ≠ 1) :
    (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n - x * LFunction χ 1) =O[atTop] (fun x ↦ √x) := by
  refine IsBigO.of_bound (4 * q) ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  exact norm_sum_zetaMul_sub_le hχ hx

/-- **The mean value of `(1 * χ)(n) / √n`.** For a nontrivial Dirichlet character `χ` modulo `q`
and every real `x`,

`‖∑_{n ≤ x} (1 * χ)(n) / √n - 2 L(1, χ) √x‖ ≤ 6 q + 2`. -/
theorem norm_sum_zetaMul_div_sqrt_sub_le (hχ : χ ≠ 1) (x : ℝ) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n / (√(n : ℝ) : ℂ) - 2 * LFunction χ 1 * (√x : ℂ)‖
      ≤ 6 * q + 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hL : ‖LFunction χ 1‖ ≤ q := by simpa using norm_LFunction_one_sub_sum_Ioc_le hχ 0
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- For `x < 1` the sum is empty and `√x ≤ 1`.
    rw [Nat.floor_eq_zero.2 hx1, Ioc_self, sum_empty, zero_sub, norm_neg, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
    have h1 : √x ≤ 1 := Real.sqrt_le_one.2 hx1.le
    norm_num
    nlinarith [Real.sqrt_nonneg x, norm_nonneg (LFunction χ 1)]
  have hx0 : 0 < x := by linarith
  -- Elementary square-root increments.
  have hsq : ∀ n : ℕ, √((n : ℝ) + 1) ^ 2 = √(n : ℝ) ^ 2 + 1 := fun n ↦ by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hstep : ∀ n : ℕ, 1 / √((n : ℝ) + 1) ≤ 2 * (√((n : ℝ) + 1) - √(n : ℝ)) := by
    intro n
    have hb : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have h := hsq n
    rw [div_le_iff₀ hb]
    nlinarith [sq_nonneg (√((n : ℝ) + 1) - √(n : ℝ))]
  have hstep2 : ∀ n : ℕ, 1 ≤ n → 2 * (√((n : ℝ) + 1) - √(n : ℝ)) ≤ 1 / √(n : ℝ) := by
    intro n hn
    have ha : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have h := hsq n
    rw [le_div_iff₀ ha]
    nlinarith [sq_nonneg (√((n : ℝ) + 1) - √(n : ℝ))]
  -- `φ K = ∑_{n ≤ K} 1 / √n - 2 √K` is antitone, vanishes at `0`, and is at least `-2`.
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, ∀ K, φ K = ∑ n ∈ Ioc 0 K, 1 / √(n : ℝ) - 2 * √(K : ℝ) :=
    ⟨_, fun _ ↦ rfl⟩
  have hφanti : Antitone φ := by
    refine antitone_nat_of_succ_le fun K ↦ ?_
    rw [hφ, hφ, sum_Ioc_succ_top (Nat.zero_le K)]
    have := hstep K
    push_cast
    linarith
  have hφle : ∀ K, φ K ≤ 0 := fun K ↦ by
    simpa [hφ] using hφanti (Nat.zero_le K)
  have hHge : ∀ K : ℕ, 2 * √((K : ℝ) + 1) - 2 ≤ ∑ n ∈ Ioc 0 K, 1 / √(n : ℝ) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le K)]
      have := hstep2 (K + 1) (by omega)
      push_cast at this ⊢
      linarith
  have hφge : ∀ K, -2 ≤ φ K := by
    intro K
    have h2 : √(K : ℝ) ≤ √((K : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    rw [hφ]
    linarith [hHge K]
  -- The weight `1 / √n`.
  have hw0 : ∀ n : ℕ, 0 ≤ 1 / √(n : ℝ) := fun n ↦ by positivity
  have hwa : ∀ m : ℕ, AntitoneOn (fun n : ℕ ↦ 1 / √(n : ℝ)) (Set.Ici (m + 1)) := by
    intro m a ha b _ hab
    have ha' : (0 : ℝ) < √(a : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast lt_of_lt_of_le (by omega) (Set.mem_Ici.1 ha))
    exact one_div_le_one_div_of_le ha' (Real.sqrt_le_sqrt (by exact_mod_cast hab))
  -- The hyperbola method for `(χ / √·) * (1 / √·)` with `y = √x`.
  set A := toArithmeticFunction fun d : ℕ ↦ χ d * ((1 / √(d : ℝ) : ℝ) : ℂ) with hAdef
  set B := toArithmeticFunction fun e : ℕ ↦ ((1 / √(e : ℝ) : ℝ) : ℂ) with hBdef
  have hAv : ∀ d : ℕ, A d = χ d * ((1 / √(d : ℝ) : ℝ) : ℂ) := fun d ↦ by
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · simp [hAdef, toArithmeticFunction, hd]
  have hBv : ∀ e : ℕ, B e = ((1 / √(e : ℝ) : ℝ) : ℂ) := fun e ↦ by
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · simp [hBdef, toArithmeticFunction, he]
  have hAB : ∀ n : ℕ, (A * B) n = χ.zetaMul n / (√(n : ℝ) : ℂ) := by
    intro n
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e ↦ A d * B e), zetaMul_apply, sum_div]
    refine sum_congr rfl fun d hd ↦ ?_
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := (Nat.mem_divisors.1 hd).2
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hq0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hd0
    have hsqrt : √(d : ℝ) * √((n / d : ℕ) : ℝ) = √(n : ℝ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, Nat.mul_div_cancel' hdn]
    have h1 : (√(d : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by exact_mod_cast hd0)).ne'
    have h2 : (√((n / d : ℕ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by exact_mod_cast hq0)).ne'
    rw [hAv, hBv, ← hsqrt]
    push_cast
    field_simp
  set s := √x with hsdef
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hx1
  have hs0 : 0 < s := by linarith
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hxs : x / s = s := Real.div_sqrt
  set M := ⌊s⌋₊ with hMdef
  have hMs : (M : ℝ) ≤ s := Nat.floor_le hs0.le
  have hsM : s < M + 1 := Nat.lt_floor_add_one s
  have hyp := sum_Ioc_mul_eq_hyperbola A B x hs0
  rw [hxs, ← hMdef] at hyp
  simp only [hAv, hBv] at hyp
  rw [sum_congr rfl fun n _ ↦ (hAB n).symm, hyp]
  -- (1) The second hyperbola sum minus the correction term.
  have hBpart : ‖∑ e ∈ Ioc 0 M, (∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
        * ((1 / √(e : ℝ) : ℝ) : ℂ)
      - (∑ d ∈ Ioc 0 M, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
        * ∑ e ∈ Ioc 0 M, ((1 / √(e : ℝ) : ℝ) : ℂ)‖ ≤ 2 * q := by
    have hrw : ∑ e ∈ Ioc 0 M, (∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
          * ((1 / √(e : ℝ) : ℝ) : ℂ)
        - (∑ d ∈ Ioc 0 M, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
          * ∑ e ∈ Ioc 0 M, ((1 / √(e : ℝ) : ℝ) : ℂ)
        = ∑ e ∈ Ioc 0 M, (∑ d ∈ Ioc M ⌊x / e⌋₊, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
          * ((1 / √(e : ℝ) : ℝ) : ℂ) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun e he ↦ ?_
      have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (mem_Ioc.1 he).1
      have heM : (e : ℝ) ≤ M := by exact_mod_cast (mem_Ioc.1 he).2
      have hle : M ≤ ⌊x / e⌋₊ := by
        refine Nat.floor_le_floor ?_
        rw [le_div_iff₀ (by linarith), ← hss]
        exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
      rw [← sum_Ioc_consecutive _ (Nat.zero_le M) hle]
      ring
    rw [hrw]
    have hterm : ∀ e ∈ Ioc 0 M, ‖(∑ d ∈ Ioc M ⌊x / e⌋₊, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
        * ((1 / √(e : ℝ) : ℝ) : ℂ)‖ ≤ q * (1 / √((M : ℝ) + 1)) * (1 / √(e : ℝ)) := by
      intro e _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 e)]
      refine mul_le_mul_of_nonneg_right ?_ (hw0 e)
      have := norm_sum_Ioc_mul_le_of_antitoneOn hχ (hwa M) (fun k _ ↦ hw0 k) ⌊x / e⌋₊
      rwa [Nat.cast_succ] at this
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← mul_sum]
    have hsum : ∑ e ∈ Ioc 0 M, 1 / √(e : ℝ) ≤ 2 * √((M : ℝ) + 1) := by
      have h1 := hφle M
      have h2 : √(M : ℝ) ≤ √((M : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      rw [hφ] at h1
      linarith
    have hpos : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    calc q * (1 / √((M : ℝ) + 1)) * ∑ e ∈ Ioc 0 M, 1 / √(e : ℝ)
        ≤ q * (1 / √((M : ℝ) + 1)) * (2 * √((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * q := by field_simp
  -- (2) Split each term of the first hyperbola sum.
  have hid : ∀ r a t p N : ℝ, 0 < r → a * r = t →
      1 / r * (p + 2 * N) = 2 * t / (r * r) + p * (1 / r) + 2 * (N - a) * (1 / r) := by
    intro r a t p N hr hat
    subst hat
    field_simp
    ring
  have hAterm : ∀ d ∈ Ioc 0 M, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ)
        * ∑ e ∈ Ioc 0 ⌊x / d⌋₊, ((1 / √(e : ℝ) : ℝ) : ℂ)
      = 2 * (s : ℂ) * (χ d / d)
        + χ d * ((φ ⌊x / d⌋₊ * (1 / √(d : ℝ)) : ℝ) : ℂ)
        + χ d * ((2 * (√(⌊x / d⌋₊ : ℝ) - √(x / d)) * (1 / √(d : ℝ)) : ℝ) : ℂ) := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.1 hd).1
    have hr : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by linarith)
    have har : √(x / d) * √(d : ℝ) = s := by
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
    have hHr : ∑ e ∈ Ioc 0 ⌊x / d⌋₊, ((1 / √(e : ℝ) : ℝ) : ℂ)
        = ((φ ⌊x / d⌋₊ + 2 * √(⌊x / d⌋₊ : ℝ) : ℝ) : ℂ) := by
      rw [hφ, ← Complex.ofReal_sum]
      congr 1
      ring
    calc χ d * ((1 / √(d : ℝ) : ℝ) : ℂ) * ∑ e ∈ Ioc 0 ⌊x / d⌋₊, ((1 / √(e : ℝ) : ℝ) : ℂ)
        = χ d * ((1 / √(d : ℝ) * (φ ⌊x / d⌋₊ + 2 * √(⌊x / d⌋₊ : ℝ)) : ℝ) : ℂ) := by
          rw [hHr]; push_cast; ring
      _ = χ d * ((2 * s / (√(d : ℝ) * √(d : ℝ)) + φ ⌊x / d⌋₊ * (1 / √(d : ℝ))
          + 2 * (√(⌊x / d⌋₊ : ℝ) - √(x / d)) * (1 / √(d : ℝ)) : ℝ) : ℂ) := by
          rw [hid _ _ _ _ _ hr har]
      _ = _ := by
          rw [Real.mul_self_sqrt (by linarith)]
          push_cast
          ring
  rw [sum_congr rfl hAterm, sum_add_distrib, sum_add_distrib, ← mul_sum]
  -- (2a) The main term against `L(1, χ)`.
  have hT1 : ‖2 * (s : ℂ) * ∑ d ∈ Ioc 0 M, χ d / d - 2 * LFunction χ 1 * (s : ℂ)‖ ≤ 2 * q := by
    rw [show 2 * (s : ℂ) * ∑ d ∈ Ioc 0 M, χ d / d - 2 * LFunction χ 1 * (s : ℂ)
        = -(((2 * s : ℝ) : ℂ) * (LFunction χ 1 - ∑ d ∈ Ioc 0 M, χ d / d)) by push_cast; ring,
      norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hM0 : (0 : ℝ) < M + 1 := by positivity
    calc 2 * s * ‖LFunction χ 1 - ∑ d ∈ Ioc 0 M, χ d / d‖ ≤ 2 * s * (q / (M + 1)) :=
          mul_le_mul_of_nonneg_left (norm_LFunction_one_sub_sum_Ioc_le hχ M) (by positivity)
      _ = 2 * q * (s / (M + 1)) := by ring
      _ ≤ 2 * q * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hM0]
          exact hsM.le
      _ = 2 * q := mul_one _
  -- (2b) The `φ`-weighted sum, by Abel summation.
  have hT2 : ‖∑ d ∈ Ioc 0 M, χ d * ((φ ⌊x / d⌋₊ * (1 / √(d : ℝ)) : ℝ) : ℂ)‖ ≤ 2 * q := by
    have hw0' : ∀ n : ℕ, 0 ≤ -φ ⌊x / n⌋₊ * (1 / √(n : ℝ)) := fun n ↦
      mul_nonneg (by linarith [hφle ⌊x / n⌋₊]) (hw0 n)
    have hwa' : AntitoneOn (fun n : ℕ ↦ -φ ⌊x / n⌋₊ * (1 / √(n : ℝ))) (Set.Ici (0 + 1)) := by
      intro m hm n hn hmn
      have hm' : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le (by omega) (Set.mem_Ici.1 hm)
      have hfl : ⌊x / n⌋₊ ≤ ⌊x / m⌋₊ :=
        Nat.floor_le_floor (div_le_div_of_nonneg_left hx0.le hm' (by exact_mod_cast hmn))
      have h1 := hφanti hfl
      exact mul_le_mul (by linarith) (hwa 0 hm hn hmn) (hw0 n) (by linarith [hφle ⌊x / m⌋₊])
    have h := norm_sum_Ioc_mul_le_of_antitoneOn hχ hwa' (fun k _ ↦ hw0' k) M
    rw [show ∑ d ∈ Ioc 0 M, χ d * ((φ ⌊x / d⌋₊ * (1 / √(d : ℝ)) : ℝ) : ℂ)
        = -∑ d ∈ Ioc 0 M, χ d * ((-φ ⌊x / d⌋₊ * (1 / √(d : ℝ)) : ℝ) : ℂ) by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun d _ ↦ ?_
        push_cast; ring, norm_neg]
    refine h.trans ?_
    norm_num
    nlinarith [hφge ⌊x⌋₊]
  -- (2c) The rounding error from `⌊x / d⌋₊`.
  have herr : ∀ a b r t : ℝ, 0 < a → 0 < r → b ≤ a → a ^ 2 - b ^ 2 ≤ 1 → 0 ≤ b →
      a * r = t → |2 * (b - a) * (1 / r)| ≤ 2 / t := by
    intro a b r t ha hr hba hab hb hat
    subst hat
    rw [abs_of_nonpos (by
      have : 0 ≤ 1 / r := by positivity
      nlinarith), le_div_iff₀ (by positivity)]
    have : -(2 * (b - a) * (1 / r)) * (a * r) = 2 * (a - b) * a := by field_simp; ring
    rw [this]
    nlinarith
  have hT3 : ‖∑ d ∈ Ioc 0 M, χ d * ((2 * (√(⌊x / d⌋₊ : ℝ) - √(x / d))
      * (1 / √(d : ℝ)) : ℝ) : ℂ)‖ ≤ 2 := by
    have hterm : ∀ d ∈ Ioc 0 M, ‖χ d * ((2 * (√(⌊x / d⌋₊ : ℝ) - √(x / d))
        * (1 / √(d : ℝ)) : ℝ) : ℂ)‖ ≤ 2 / s := by
      intro d hd
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.1 hd).1
      have hdM : (d : ℝ) ≤ M := by exact_mod_cast (mem_Ioc.1 hd).2
      have hxd : 1 ≤ x / d := by
        rw [le_div_iff₀ (by linarith), one_mul, ← hss]
        nlinarith
      have hr : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by linarith)
      have har : √(x / d) * √(d : ℝ) = s := by
        rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
      have hfl1 : ((⌊x / d⌋₊ : ℕ) : ℝ) ≤ x / d := Nat.floor_le (by linarith)
      have hfl2 : x / d < ((⌊x / d⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ x / d by linarith)
      have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((⌊x / d⌋₊ : ℕ) : ℝ) by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hE := herr (√(x / d)) (√(⌊x / d⌋₊ : ℝ)) (√(d : ℝ)) s
        (Real.sqrt_pos.2 (by linarith)) hr (Real.sqrt_le_sqrt hfl1) (by linarith)
        (Real.sqrt_nonneg _) har
      calc _ ≤ 1 * (2 / s) := mul_le_mul (χ.norm_le_one _) hE (abs_nonneg _) zero_le_one
        _ = 2 / s := one_mul _
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero, ← mul_div_assoc, div_le_iff₀ hs0]
    linarith
  calc _ = ‖(2 * (s : ℂ) * ∑ d ∈ Ioc 0 M, χ d / d - 2 * LFunction χ 1 * (s : ℂ))
        + ∑ d ∈ Ioc 0 M, χ d * ((φ ⌊x / d⌋₊ * (1 / √(d : ℝ)) : ℝ) : ℂ)
        + ∑ d ∈ Ioc 0 M, χ d * ((2 * (√(⌊x / d⌋₊ : ℝ) - √(x / d)) * (1 / √(d : ℝ)) : ℝ) : ℂ)
        + (∑ e ∈ Ioc 0 M, (∑ d ∈ Ioc 0 ⌊x / e⌋₊, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
            * ((1 / √(e : ℝ) : ℝ) : ℂ)
          - (∑ d ∈ Ioc 0 M, χ d * ((1 / √(d : ℝ) : ℝ) : ℂ))
            * ∑ e ∈ Ioc 0 M, ((1 / √(e : ℝ) : ℝ) : ℂ))‖ := by congr 1; ring
    _ ≤ 2 * q + 2 * q + 2 + 2 * q := by
        refine (norm_add_le _ _).trans (add_le_add ?_ hBpart)
        refine (norm_add_le _ _).trans (add_le_add ?_ hT3)
        exact (norm_add_le _ _).trans (add_le_add hT1 hT2)
    _ = 6 * q + 2 := by ring

/-- **The mean value of `(1 * χ)(n) / √n`.** For a nontrivial Dirichlet character `χ`,
`∑_{n ≤ x} (1 * χ)(n) / √n = 2 L(1, χ) √x + O(1)`. -/
theorem sum_zetaMul_div_sqrt_sub_isBigO_one (hχ : χ ≠ 1) :
    (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, χ.zetaMul n / (√(n : ℝ) : ℂ) - 2 * LFunction χ 1 * (√x : ℂ))
      =O[atTop] (fun _ ↦ (1 : ℝ)) :=
  IsBigO.of_bound (6 * q + 2) (Eventually.of_forall fun x ↦ by
    simpa using norm_sum_zetaMul_div_sqrt_sub_le hχ x)

end DirichletCharacter
