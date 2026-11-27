/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JensenHyperbolicity
import Mathlib.Tactic.IntervalCases

/-!
# The log-ratio expansion of Griffin, Ono, Rolen and Zagier

`HasLogRatioExpansion α d` is the hypothesis of
`MetaMathlibExt.eventually_jensen_hyperbolic_of_log_ratio_expansion` with its functions left
existential:
`log (α (n + k) / α n) = A n k − δ n ² k² + ∑_{j=3}^{d} g j n kʲ + o(δ n ^ d)` for `k ≤ d`, where
`δ > 0`, `δ → 0` and `g j = o(δʲ)`.

* `hasLogRatioExpansion_of_Icc_one`: an expansion whose sum runs over `1 ≤ j ≤ d` can be put in
  this form, absorbing `g 1` into `A` and `g 2` into `δ`.
* `hasLogRatioExpansion_of_le_one`: in degree `d ≤ 1` every sequence has the expansion.
* `HasLogRatioExpansion.shift`: the expansion survives `n ↦ n + N`.
* `HasLogRatioExpansion.eventually_card_roots`: the expansion, eventual positivity and a lower
  bound on `log (α (n + 1) / α n)` give eventual hyperbolicity of the Jensen polynomials, in the
  wording `roots.card = natDegree`. The criterion asks for `A > 0`; multiplying `α n` by `e^{c n}`
  adds `c` to `A` and only rescales the variable of each Jensen polynomial.
-/

open Filter Asymptotics Polynomial Finset
open scoped Topology

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

/-- The log-ratio expansion of Griffin, Ono, Rolen and Zagier in degree `d`: the hypothesis of
`MetaMathlibExt.eventually_jensen_hyperbolic_of_log_ratio_expansion`, with `A`, `δ` and `g`
existential. -/
def HasLogRatioExpansion (α : ℕ → ℝ) (d : ℕ) : Prop :=
  ∃ (A δ : ℕ → ℝ) (g : ℕ → ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧ (∀ n, 0 < δ n) ∧
    (∀ j ∈ Icc 3 d, g j =o[atTop] fun n => δ n ^ j) ∧
    ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
      (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
        fun n => δ n ^ d

end

lemma isBigO_pow_of_sq_le {a b : ℕ → ℝ} (h : ∀ᶠ n in atTop, a n ^ 2 ≤ 2 * b n ^ 2) (i : ℕ) :
    (fun n => a n ^ i) =O[atTop] (fun n => b n ^ i) := by
  refine IsBigO.of_bound (2 ^ i) ?_
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
  have e1 : (|a n| ^ i) ^ 2 = (a n ^ 2) ^ i := by rw [← pow_mul, mul_comm, pow_mul, sq_abs]
  have e1b : (|b n| ^ i) ^ 2 = (b n ^ 2) ^ i := by rw [← pow_mul, mul_comm, pow_mul, sq_abs]
  have h1 : (|a n| ^ i) ^ 2 ≤ (2 ^ i * |b n| ^ i) ^ 2 := by
    rw [mul_pow, e1, e1b]
    have h2 : (a n ^ 2) ^ i ≤ (2 * b n ^ 2) ^ i := pow_le_pow_left₀ (sq_nonneg _) hn i
    have h3 : (2 : ℝ) ^ i ≤ (2 ^ i) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    rw [mul_pow] at h2
    have : 0 ≤ (b n ^ 2) ^ i := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1

lemma sum_Icc_one_split (g : ℕ → ℕ → ℝ) (d n : ℕ) (x : ℝ) :
    ∑ i ∈ Icc 1 d, g i n * x ^ i = (if 1 ≤ d then g 1 n else 0) * x +
      (if 2 ≤ d then g 2 n else 0) * x ^ 2 + ∑ i ∈ Icc 3 d, g i n * x ^ i := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d <;> simp
  · rw [← insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ d), sum_insert (by simp),
      ← insert_Icc_add_one_left_eq_Icc (by omega : 1 + 1 ≤ d), sum_insert (by simp)]
    simp only [show 1 ≤ d by omega, hd, ↓reduceIte, pow_one, Nat.reduceAdd, add_assoc]

/-- If `log (α (n + k) / α n) = A n k − δ n ² k² + ∑_{j=1}^{d} g j n kʲ + o(δ n ^ d)` for `k ≤ d`,
with `g j = o(δʲ)` (`1 ≤ j ≤ d`), `δ > 0` and `δ → 0`, then `α` has the log-ratio expansion in
degree `d`. -/
public theorem hasLogRatioExpansion_of_Icc_one {α : ℕ → ℝ} {d : ℕ} {A δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ n, 0 < δ n) {g : ℕ → ℕ → ℝ}
    (hg : ∀ i ∈ Icc 1 d, (fun n => g i n) =o[atTop] (fun n => δ n ^ i))
    (hexp : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) -
      (A n * j - δ n ^ 2 * j ^ 2 + ∑ i ∈ Icc 1 d, g i n * (j : ℝ) ^ i)) =o[atTop]
        (fun n => δ n ^ d)) :
    HasLogRatioExpansion α d := by
  set g1 : ℕ → ℝ := fun n => if 1 ≤ d then g 1 n else 0 with hg1
  set g2 : ℕ → ℝ := fun n => if 2 ≤ d then g 2 n else 0 with hg2
  have hg2o : g2 =o[atTop] (fun n => δ n ^ 2) := by
    by_cases h : 2 ≤ d
    · simp only [hg2, h, ↓reduceIte]; exact hg 2 (mem_Icc.2 ⟨by omega, h⟩)
    · simp only [hg2, h, ↓reduceIte]; exact isLittleO_zero _ _
  set D : ℕ → ℝ := fun n => δ n ^ 2 - g2 n with hD
  set δ' : ℕ → ℝ := fun n => if 0 < D n then Real.sqrt (D n) else δ n with hδ'
  -- eventually `δ²/2 ≤ D ≤ 3δ²/2` and `δ'² = D`
  have hev : ∀ᶠ n in atTop, |g2 n| ≤ δ n ^ 2 / 2 := by
    have := hg2o.def (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [this] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (δ n))] at hn
    linarith
  have hsq : ∀ᶠ n in atTop, δ' n ^ 2 = D n ∧ δ n ^ 2 / 2 ≤ D n ∧ D n ≤ 2 * δ n ^ 2 := by
    filter_upwards [hev] with n hn
    have hd2 : 0 < δ n ^ 2 := pow_pos (hδpos n) 2
    have h1 : δ n ^ 2 / 2 ≤ D n := by
      simp only [hD]; linarith [neg_abs_le (g2 n), le_abs_self (g2 n)]
    have h2 : D n ≤ 2 * δ n ^ 2 := by simp only [hD]; linarith [neg_abs_le (g2 n)]
    have hpos : 0 < D n := by linarith
    refine ⟨?_, h1, h2⟩
    simp only [hδ', hpos, ↓reduceIte]
    exact Real.sq_sqrt hpos.le
  have hO1 : ∀ i, (fun n => δ n ^ i) =O[atTop] (fun n => δ' n ^ i) := fun i =>
    isBigO_pow_of_sq_le (hsq.mono fun n ⟨h1, h2, _⟩ => by rw [h1]; linarith) i
  have hO2 : ∀ i, (fun n => δ' n ^ i) =O[atTop] (fun n => δ n ^ i) := fun i =>
    isBigO_pow_of_sq_le (hsq.mono fun n ⟨h1, _, h3⟩ => by rw [h1]; linarith) i
  refine ⟨fun n => A n + g1 n, δ', g, ?_, ?_, ?_, ?_⟩
  · have := (hO2 1).trans_tendsto (by simpa using hδ)
    simpa using this
  · intro n
    simp only [hδ']
    split_ifs with h
    · exact Real.sqrt_pos.2 h
    · exact hδpos n
  · intro i hi
    exact (hg i (mem_Icc.2 ⟨by rw [mem_Icc] at hi; omega, (mem_Icc.1 hi).2⟩)).trans_isBigO (hO1 i)
  · intro j hj
    refine ((hexp j hj).trans_isBigO (hO1 d)).congr' (hsq.mono fun n ⟨h1, _, _⟩ => ?_)
      (Eventually.of_forall fun _ => rfl)
    beta_reduce
    rw [sum_Icc_one_split g d n (j : ℝ), h1]
    simp only [hD, hg1, hg2]
    ring

/-- In degree `d ≤ 1` every sequence has the log-ratio expansion: take `δ n = 1/(n+1)` and let
`A` absorb the one shift. -/
public theorem hasLogRatioExpansion_of_le_one (α : ℕ → ℝ) {d : ℕ} (hd : d ≤ 1) :
    HasLogRatioExpansion α d := by
  refine ⟨fun n => Real.log (α (n + 1) / α n) + (1 / ((n : ℝ) + 1)) ^ 2,
    fun n => 1 / ((n : ℝ) + 1), fun _ _ => 0, tendsto_one_div_add_atTop_nhds_zero_nat,
    fun n => by positivity, fun j hj => by rw [mem_Icc] at hj; omega, fun k hk => ?_⟩
  have hI : Icc 3 d = ∅ := by ext i; simp only [mem_Icc, Finset.notMem_empty, iff_false]; omega
  refine (isLittleO_zero _ _).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · simp [hI]
  · simp only [hI, sum_empty, add_zero, Nat.cast_one, mul_one, one_pow]
    ring

/-- The log-ratio expansion survives the shift `n ↦ n + N`. -/
public theorem HasLogRatioExpansion.shift {α : ℕ → ℝ} {d : ℕ} (h : HasLogRatioExpansion α d)
    (N : ℕ) : HasLogRatioExpansion (fun n => α (n + N)) d := by
  obtain ⟨A, δ, g, hδ, hδ0, hg, hexp⟩ := h
  have hN : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  refine ⟨fun n => A (n + N), fun n => δ (n + N), fun j n => g j (n + N), hδ.comp hN,
    fun n => hδ0 _, fun j hj => (hg j hj).comp_tendsto hN, fun k hk => ?_⟩
  refine ((hexp k hk).comp_tendsto hN).congr' (Eventually.of_forall fun n => ?_)
    EventuallyEq.rfl
  simp only [Function.comp_apply, add_right_comm]

/- Multiplying `α n` by `e^{c n}` adds `c` to `A` in the log-ratio expansion. -/
private lemma HasLogRatioExpansion.twist_of_pos {α A δ : ℕ → ℝ} {g : ℕ → ℕ → ℝ} {d : ℕ}
    (hα : ∀ n, 0 < α n) (c : ℝ)
    (hexp : ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
      (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
        fun n => δ n ^ d) :
    ∀ k ≤ d, (fun n => Real.log (α (n + k) * Real.exp (c * (n + k : ℕ)) /
        (α n * Real.exp (c * n))) -
      ((A n + c) * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
        fun n => δ n ^ d := by
  intro k hk
  refine (hexp k hk).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
  have h1 := hα n
  have h2 := hα (n + k)
  have key : α (n + k) * Real.exp (c * (n + k : ℕ)) / (α n * Real.exp (c * n)) =
      α (n + k) / α n * Real.exp (c * k) := by
    rw [show c * ((n + k : ℕ) : ℝ) = c * n + c * k by push_cast; ring, Real.exp_add]
    field_simp
  dsimp only
  rw [key, Real.log_mul (div_pos h2 h1).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/- Rescaling the variable and the polynomial by nonzero constants preserves both the number of
roots and the degree. -/
private lemma card_roots_comp_C_mul_X {p : ℝ[X]} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C b * p.comp (C a * X)).roots.card = p.roots.card ∧
      (C b * p.comp (C a * X)).natDegree = p.natDegree := by
  have hlin : C a * X = C a * X + C 0 := by simp
  constructor
  · rw [roots_C_mul _ hb, hlin, roots_comp_C_mul_X_add_C _ _ _ (Ne.isUnit ha), Multiset.card_map]
  · rw [natDegree_C_mul hb, natDegree_comp, natDegree_C_mul_X a ha, mul_one]

/-- **Eventual hyperbolicity from the log-ratio expansion.** If `α` is eventually positive, has the
log-ratio expansion in degree `d ≥ 1`, and `log (α (n + 1) / α n)` is eventually bounded below,
then for all large `n` the Jensen polynomial of degree `d` and shift `n` of `α` has as many real
roots, with multiplicity, as its degree. -/
public theorem HasLogRatioExpansion.eventually_card_roots {α : ℕ → ℝ} {d : ℕ} (hd : 1 ≤ d)
    (h : HasLogRatioExpansion α d) (hα : ∀ᶠ n in atTop, 0 < α n)
    (hlow : ∃ c, ∀ᶠ n in atTop, -c ≤ Real.log (α (n + 1) / α n)) :
    ∀ᶠ n in atTop,
      (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).roots.card =
        (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).natDegree := by
  obtain ⟨c, hc⟩ := hlow
  obtain ⟨A, δ, g, hδ, hδ0, hg, hexp⟩ := h
  -- `A` is eventually bounded below, by the case `k = 1` of the expansion
  have hA : ∀ᶠ n in atTop, -(c + 1) < A n := by
    have hδd : Tendsto (fun n => δ n ^ d) atTop (𝓝 0) := by
      simpa [zero_pow (by omega : d ≠ 0)] using hδ.pow d
    have h1 := ((hexp 1 hd).trans_tendsto hδd)
    have hgs : Tendsto (fun n => ∑ j ∈ Icc 3 d, g j n * ((1 : ℕ) : ℝ) ^ j) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Icc 3 d) fun j hj =>
        ((hg j hj).trans_tendsto (by
          simpa [zero_pow (by simp only [mem_Icc] at hj; omega : j ≠ 0)] using hδ.pow j)).mul_const
          (((1 : ℕ) : ℝ) ^ j)
      simpa using this
    have hh : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 / 2 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hc, h1.eventually hh, hgs.eventually hh] with n hn hn' hs
    simp only [Nat.cast_one, mul_one, one_pow] at hn' hs
    have := sq_nonneg (δ n)
    linarith [abs_lt.1 hn', abs_lt.1 hs]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hα.and hA)
  set c' : ℝ := c + 2 with hc'
  set β : ℕ → ℝ := fun n => α (n + N) * Real.exp (c' * n) with hβ
  have hpos : ∀ n, 0 < α (n + N) := fun n => (hN _ (by omega)).1
  have hβpos : ∀ n, 0 < β n := fun n => mul_pos (hpos n) (Real.exp_pos _)
  -- the criterion applies to `β`
  have hshift := (show HasLogRatioExpansion α d from ⟨A, δ, g, hδ, hδ0, hg, hexp⟩).shift N
  have hN' : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  have hβexp := HasLogRatioExpansion.twist_of_pos hpos c' (A := fun n => A (n + N))
    (δ := fun n => δ (n + N)) (g := fun j n => g j (n + N)) (d := d) fun k hk =>
      ((hexp k hk).comp_tendsto hN').congr' (Eventually.of_forall fun n => by
        simp only [Function.comp_apply, add_right_comm]) EventuallyEq.rfl
  have hcrit := eventually_jensen_hyperbolic_of_log_ratio_expansion (α := β)
    (A := fun n => A (n + N) + c') (δ := fun n => δ (n + N)) hβpos
    (fun n => by have := (hN (n + N) (by omega)).2; simp only [hc']; linarith)
    (fun n => hδ0 _) (hδ.comp hN') hd (fun j n => g j (n + N))
    (fun j hj => (hg j hj).comp_tendsto hN') (fun k hk => by
      refine (hβexp k hk).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
      simp only [hβ, add_right_comm])
  -- relate the Jensen polynomials of `β` and `α`
  obtain ⟨M, hM⟩ := eventually_atTop.1 hcrit
  refine eventually_atTop.2 ⟨M + N, fun m hm => ?_⟩
  have hm' := hM (m - N) (by omega)
  have heq : (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * β (m - N + j)) * X ^ j) =
      C (Real.exp (c' * (m - N : ℕ))) *
        (∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (m + j)) * X ^ j).comp
          (C (Real.exp c') * X) := by
    simp only [Polynomial.sum_comp, mul_comp, C_comp, X_pow_comp, mul_sum, hβ]
    refine sum_congr rfl fun j _ => ?_
    rw [show m - N + j + N = m + j by omega, mul_pow, ← C_pow, ← Real.exp_nat_mul]
    simp only [← C_mul, ← mul_assoc]
    congr 2
    rw [show c' * ((m - N + j : ℕ) : ℝ) = c' * ((m - N : ℕ) : ℝ) + j * c' by push_cast; ring,
      Real.exp_add]
    ring
  rw [heq] at hm'
  obtain ⟨h1, h2⟩ := card_roots_comp_C_mul_X
    (p := ∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * α (m + j)) * X ^ j)
    (Real.exp_pos c').ne' (Real.exp_pos (c' * (m - N : ℕ))).ne'
  rw [h1, h2] at hm'
  exact hm'

end MetaMathlibExt.ColoredPartitionsJensen
