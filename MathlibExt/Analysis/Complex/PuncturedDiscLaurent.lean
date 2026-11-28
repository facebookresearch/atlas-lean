/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Laurent series on the punctured unit disc

A coefficient sequence `b : ℤ → ℂ` is a *Laurent series on the punctured unit disc*
(`WLight.IsPuncturedDiscLaurent b`) if `b n = 0` for `n < -m` for some `m : ℕ` and
`∑ₙ ‖bₙ‖ rⁿ` converges for every `0 < r < 1`. Its sum is
`WLight.laurentSum b w = ∑' n : ℤ, b n * w ^ n`, which converges absolutely for `0 < ‖w‖ < 1`.

This file proves:

* the product of two such sums is the sum of the convolution of the coefficient sequences
  (`WLight.laurentConv`), which is again such a sequence (`WLight.laurentSum_mul`,
  `WLight.IsPuncturedDiscLaurent.laurentConv`); the convolution of sequences vanishing below
  commutes with ring homomorphisms (`WLight.map_laurentConv`);
* the coefficients are unique: if the sum vanishes on the punctured disc, all coefficients
  vanish (`WLight.IsPuncturedDiscLaurent.eq_zero_of_laurentSum_eq_zero`,
  `WLight.IsPuncturedDiscLaurent.ext_of_laurentSum_eq`);
* closure under sums, negation and monomials.

Uniqueness is reduced to the uniqueness of power series coefficients
(`HasFPowerSeriesAt.eq_zero`) after multiplication by `w ^ m`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9, where the `q`-expansions of the roots `jN(γk τ)` are
multiplied: "the coefficients of the q-expansions of jN(τ) and the jN(γk τ) are algebraic
integers, as is any polynomial combination of them".
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

namespace WLight

/-- A coefficient sequence `b : ℤ → ℂ` is a Laurent series on the punctured unit disc if it
vanishes below some `-m` (`m : ℕ`) and `∑ₙ ‖bₙ‖ rⁿ` is summable for every `0 < r < 1`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, pp. 8–9 (`q`-expansions in `ℚ(ζN)((q^{1/N}))`). -/
def IsPuncturedDiscLaurent (b : ℤ → ℂ) : Prop :=
  (∃ m : ℕ, ∀ n : ℤ, n < -(m : ℤ) → b n = 0) ∧
    ∀ r : ℝ, 0 < r → r < 1 → Summable fun n : ℤ => ‖b n‖ * r ^ n

/-- The sum `∑' n : ℤ, b n * w ^ n` of a Laurent series with coefficients `b` at `w`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, pp. 8–9. -/
noncomputable def laurentSum (b : ℤ → ℂ) (w : ℂ) : ℂ :=
  ∑' n : ℤ, b n * w ^ n

/-- The convolution `(b ⋆ b')ₙ = ∑ₖ bₖ b'ₙ₋ₖ` of two `ℤ`-indexed sequences in a semiring, as a
`finsum` (so it is the honest finite sum when the sequences vanish below, and `0` when the
sum has infinite support).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9 ("any polynomial combination of them"). -/
noncomputable def laurentConv {R : Type*} [Semiring R] (b b' : ℤ → R) (n : ℤ) : R :=
  ∑ᶠ k : ℤ, b k * b' (n - k)

private theorem conv_term_eq_zero {R : Type*} [Semiring R] {b b' : ℤ → R} {m m' : ℕ}
    (hb : ∀ n : ℤ, n < -(m : ℤ) → b n = 0) (hb' : ∀ n : ℤ, n < -(m' : ℤ) → b' n = 0)
    (n k : ℤ) (hk : k ∉ Finset.Icc (-(m : ℤ)) (n + m')) : b k * b' (n - k) = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hb k hk, zero_mul]
  · rw [hb' (n - k) (by omega), mul_zero]

private theorem conv_eq_sum {R : Type*} [Semiring R] {b b' : ℤ → R} {m m' : ℕ}
    (hb : ∀ n : ℤ, n < -(m : ℤ) → b n = 0) (hb' : ∀ n : ℤ, n < -(m' : ℤ) → b' n = 0)
    (n : ℤ) :
    laurentConv b b' n = ∑ k ∈ Finset.Icc (-(m : ℤ)) (n + m'), b k * b' (n - k) := by
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  by_contra h
  exact hk (conv_term_eq_zero hb hb' n k h)

/-- The convolution of two sequences vanishing below `-m` and `-m'` vanishes below
`-(m + m')`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem laurentConv_eq_zero_of_lt {R : Type*} [Semiring R] {b b' : ℤ → R} {m m' : ℕ}
    (hb : ∀ n : ℤ, n < -(m : ℤ) → b n = 0) (hb' : ∀ n : ℤ, n < -(m' : ℤ) → b' n = 0)
    {n : ℤ} (hn : n < -((m + m' : ℕ) : ℤ)) : laurentConv b b' n = 0 := by
  rw [conv_eq_sum hb hb', Finset.Icc_eq_empty (by push_cast at hn; omega), Finset.sum_empty]

/-- A ring homomorphism maps the convolution of two sequences vanishing below some index to
the convolution of their images.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9 (the Galois action on the coefficients of a product of
`q`-expansions). -/
theorem map_laurentConv {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) {b b' : ℤ → R}
    {m m' : ℕ} (hb : ∀ n : ℤ, n < -(m : ℤ) → b n = 0)
    (hb' : ∀ n : ℤ, n < -(m' : ℤ) → b' n = 0) (n : ℤ) :
    f (laurentConv b b' n) = laurentConv (fun k => f (b k)) (fun k => f (b' k)) n := by
  have hfb : ∀ n : ℤ, n < -(m : ℤ) → f (b n) = 0 := fun n hn => by rw [hb n hn, map_zero]
  have hfb' : ∀ n : ℤ, n < -(m' : ℤ) → f (b' n) = 0 := fun n hn => by rw [hb' n hn, map_zero]
  rw [conv_eq_sum hb hb', conv_eq_sum hfb hfb', map_sum]
  simp only [map_mul]

/-- For a Laurent series on the punctured disc and `0 < ‖w‖ < 1`, the series
`∑ ‖bₙ wⁿ‖` converges.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, pp. 8–9. -/
theorem IsPuncturedDiscLaurent.summable_norm {b : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b)
    {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) : Summable fun n : ℤ => ‖b n * w ^ n‖ := by
  simpa only [norm_mul, norm_zpow] using hb.2 ‖w‖ (norm_pos_iff.mpr hw0) hw1

/-- The equivalence `(n, k) ↦ (k, n - k)` of `ℤ × ℤ`. -/
private def convEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- **Product of Laurent series.** For Laurent series `b`, `b'` on the punctured unit disc and
`0 < ‖w‖ < 1`, `(∑ bₙ wⁿ)(∑ b'ₙ wⁿ) = ∑ (b ⋆ b')ₙ wⁿ`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9 ("any polynomial combination of them"). -/
theorem laurentSum_mul {b b' : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b)
    (hb' : IsPuncturedDiscLaurent b') {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    laurentSum b w * laurentSum b' w = laurentSum (laurentConv b b') w := by
  obtain ⟨m, hm⟩ := hb.1
  obtain ⟨m', hm'⟩ := hb'.1
  have hs := hb.summable_norm hw0 hw1
  have hs' := hb'.summable_norm hw0 hw1
  have hF := summable_mul_of_summable_norm hs hs'
  have hFe := (convEquiv.summable_iff).mpr hF
  unfold laurentSum
  rw [tsum_mul_tsum_of_summable_norm hs hs', ← convEquiv.tsum_eq]
  have hprod := hFe.tsum_prod
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  refine tsum_congr fun n => ?_
  have e : ∀ k : ℤ, (fun p : ℤ × ℤ => b p.1 * w ^ p.1 * (b' p.2 * w ^ p.2)) (convEquiv (n, k)) =
      b k * b' (n - k) * w ^ n := by
    intro k
    change b k * w ^ k * (b' (n - k) * w ^ (n - k)) = _
    rw [show w ^ n = w ^ k * w ^ (n - k) by rw [← zpow_add₀ hw0]; congr 1; ring]
    ring
  simp only [e]
  rw [tsum_mul_right, laurentConv, tsum_eq_finsum]
  refine (Finset.Icc (-(m : ℤ)) (n + m')).finite_toSet.subset fun k hk => ?_
  by_contra h
  exact hk (conv_term_eq_zero hm hm' n k h)

/-- **The convolution of Laurent series on the punctured disc is one.** If `b` and `b'` are
Laurent series on the punctured unit disc, so is `b ⋆ b'` (it vanishes below `-(m + m')`, and
`∑ ‖(b ⋆ b')ₙ‖ rⁿ ≤ (∑ ‖bₙ‖ rⁿ)(∑ ‖b'ₙ‖ rⁿ)`).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem IsPuncturedDiscLaurent.laurentConv {b b' : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b)
    (hb' : IsPuncturedDiscLaurent b') : IsPuncturedDiscLaurent (laurentConv b b') := by
  obtain ⟨⟨m, hm⟩, hbs⟩ := hb
  obtain ⟨⟨m', hm'⟩, hbs'⟩ := hb'
  refine ⟨⟨m + m', fun n hn => laurentConv_eq_zero_of_lt hm hm' hn⟩, fun r hr0 hr1 => ?_⟩
  have hG := Summable.mul_of_nonneg (hbs r hr0 hr1) (hbs' r hr0 hr1)
    (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr0 n).le)
    (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr0 n).le)
  have hGe := (convEquiv.summable_iff).mpr hG
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr0 n).le)
    (fun n => ?_) hGe.prod
  have e : ∀ k : ℤ, (fun p : ℤ × ℤ => ‖b p.1‖ * r ^ p.1 * (‖b' p.2‖ * r ^ p.2))
      (convEquiv (n, k)) = ‖b k‖ * ‖b' (n - k)‖ * r ^ n := by
    intro k
    change ‖b k‖ * r ^ k * (‖b' (n - k)‖ * r ^ (n - k)) = _
    rw [show r ^ n = r ^ k * r ^ (n - k) by rw [← zpow_add₀ hr0.ne']; congr 1; ring]
    ring
  simp only [Function.comp_def, e]
  rw [conv_eq_sum hm hm']
  calc ‖∑ k ∈ Finset.Icc (-(m : ℤ)) (n + m'), b k * b' (n - k)‖ * r ^ n
      ≤ (∑ k ∈ Finset.Icc (-(m : ℤ)) (n + m'), ‖b k‖ * ‖b' (n - k)‖) * r ^ n := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    _ = ∑ k ∈ Finset.Icc (-(m : ℤ)) (n + m'), ‖b k‖ * ‖b' (n - k)‖ * r ^ n := by
        rw [Finset.sum_mul]
    _ ≤ ∑' k : ℤ, ‖b k‖ * ‖b' (n - k)‖ * r ^ n := by
        refine Summable.sum_le_tsum _ (fun k _ => ?_) ?_
        · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (zpow_pos hr0 n).le
        · have := hGe.prod_factor n
          simpa only [Function.comp_def, e] using this

/-- The sum of two Laurent series on the punctured disc is one.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem IsPuncturedDiscLaurent.add {b b' : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b)
    (hb' : IsPuncturedDiscLaurent b') : IsPuncturedDiscLaurent (b + b') := by
  obtain ⟨⟨m, hm⟩, hbs⟩ := hb
  obtain ⟨⟨m', hm'⟩, hbs'⟩ := hb'
  refine ⟨⟨m + m', fun n hn => ?_⟩, fun r hr0 hr1 => ?_⟩
  · rw [Pi.add_apply, hm n (by omega), hm' n (by omega), add_zero]
  · refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr0 n).le)
      (fun n => ?_) ((hbs r hr0 hr1).add (hbs' r hr0 hr1))
    rw [← add_mul, Pi.add_apply]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (zpow_pos hr0 n).le

/-- The negative of a Laurent series on the punctured disc is one.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem IsPuncturedDiscLaurent.neg {b : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b) :
    IsPuncturedDiscLaurent (-b) := by
  obtain ⟨⟨m, hm⟩, hbs⟩ := hb
  refine ⟨⟨m, fun n hn => by rw [Pi.neg_apply, hm n hn, neg_zero]⟩, fun r hr0 hr1 => ?_⟩
  simpa only [Pi.neg_apply, norm_neg] using hbs r hr0 hr1

/-- A monomial `c wⁿ⁰` (the sequence equal to `c` at `n₀` and `0` elsewhere) is a Laurent series
on the punctured disc, with sum `c w ^ n₀`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, pp. 8–9 (the terms `1/q^N` and `744`). -/
theorem isPuncturedDiscLaurent_single (n₀ : ℤ) (c : ℂ) :
    IsPuncturedDiscLaurent (fun n => if n = n₀ then c else 0) ∧
      ∀ w : ℂ, laurentSum (fun n => if n = n₀ then c else 0) w = c * w ^ n₀ := by
  refine ⟨⟨⟨n₀.natAbs, fun n hn => ?_⟩, fun r _ _ => ?_⟩, fun w => ?_⟩
  · rw [ite_eq_right_iff]
    intro h
    omega
  · refine summable_of_ne_finset_zero (s := {n₀}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn
    simp only [hn, ↓reduceIte, norm_zero, zero_mul]
  · unfold laurentSum
    rw [← tsum_ite_eq n₀ (fun _ => c * w ^ n₀)]
    refine tsum_congr fun n => ?_
    by_cases h : n = n₀
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, zero_mul]

/-- The sum of Laurent series is additive: `∑ (bₙ + b'ₙ) wⁿ = ∑ bₙ wⁿ + ∑ b'ₙ wⁿ` for
`0 < ‖w‖ < 1`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem laurentSum_add {b b' : ℤ → ℂ} (hb : IsPuncturedDiscLaurent b)
    (hb' : IsPuncturedDiscLaurent b') {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    laurentSum (b + b') w = laurentSum b w + laurentSum b' w := by
  unfold laurentSum
  simp only [Pi.add_apply, add_mul]
  exact (hb.summable_norm hw0 hw1).of_norm.tsum_add (hb'.summable_norm hw0 hw1).of_norm

/-- `∑ (-bₙ) wⁿ = -∑ bₙ wⁿ`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem laurentSum_neg (b : ℤ → ℂ) (w : ℂ) : laurentSum (-b) w = -laurentSum b w := by
  unfold laurentSum
  simp only [Pi.neg_apply, neg_mul]
  exact tsum_neg

/-- **Uniqueness of Laurent coefficients.** If a Laurent series on the punctured unit disc has
sum `0` at every `w` with `0 < ‖w‖ < 1`, all its coefficients vanish.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9 (the coefficients of a `q`-expansion are well
defined). The proof multiplies by `w ^ m` and uses the uniqueness of power series
coefficients. -/
theorem IsPuncturedDiscLaurent.eq_zero_of_laurentSum_eq_zero {b : ℤ → ℂ}
    (hb : IsPuncturedDiscLaurent b)
    (h : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → laurentSum b w = 0) : b = 0 := by
  obtain ⟨⟨m, hm⟩, hbs⟩ := hb
  set a : ℕ → ℂ := fun k => b ((k : ℤ) - m) with ha
  set p := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - m := fun k l hkl => by
    simp only at hkl
    omega
  have hrange : ∀ n : ℤ, (∀ k : ℕ, (k : ℤ) - m ≠ n) → b n = 0 := fun n hn => by
    refine hm n ?_
    by_contra hc
    exact hn (n + m).toNat (by omega)
  -- the radius of `p` is at least `1/2`
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have hs := (hbs (1 / 2) (by norm_num) (by norm_num)).comp_injective hinj
    have hs2 := hs.mul_left (((1 : ℝ) / 2) ^ m)
    refine hs2.congr fun k => ?_
    simp only [Function.comp_apply, hp, FormalMultilinearSeries.ofScalars_norm, ha,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [mul_left_comm, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 2
    ring
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hball := p.hasFPowerSeriesOnBall hpos
  -- the sum of `p` vanishes on a punctured neighbourhood of `0`
  have hzero : ∀ y : ℂ, y ≠ 0 → ‖y‖ < 1 / 2 → p.sum y = 0 := by
    intro y hy0 hy1
    have hy1' : ‖y‖ < 1 := by linarith
    have hsum : p.sum y = ∑' k : ℕ, a k * y ^ k := by
      rw [FormalMultilinearSeries.sum]
      simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    have hlaur := h y hy0 hy1'
    unfold laurentSum at hlaur
    rw [← (hinj.tsum_eq (f := fun n : ℤ => b n * y ^ n) fun n hn => ?_)] at hlaur
    · rw [hsum]
      have e : ∀ k : ℕ, a k * y ^ k = y ^ (m : ℤ) * (b ((k : ℤ) - m) * y ^ ((k : ℤ) - m)) := by
        intro k
        rw [ha, mul_left_comm, ← zpow_add₀ hy0, ← zpow_natCast]
        congr 2
        ring
      simp only [e]
      rw [tsum_mul_left, hlaur, mul_zero]
    · by_contra hc
      exact hn (by
        change b n * y ^ n = 0
        rw [hrange n fun k hk => hc ⟨k, hk⟩, zero_mul])
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz hz0
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hzero z hz0 hz
  have hev0 := (hball.analyticAt.frequently_zero_iff_eventually_zero).mp hev.frequently
  have hp0 : p = 0 := (hball.hasFPowerSeriesAt.congr hev0).eq_zero
  funext n
  by_cases hn : n < -(m : ℤ)
  · exact hm n hn
  · have hk := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q (n + m).toNat) hp0
    simp only [FormalMultilinearSeries.zero_apply] at hk
    have hk' := (FormalMultilinearSeries.ofScalars_eq_zero ℂ (c := a) _).mp hk
    rw [ha] at hk'
    simp only at hk'
    rw [show ((n + m).toNat : ℤ) - m = n by omega] at hk'
    exact hk'

/-- **Uniqueness of Laurent coefficients**, two-sequence form: two Laurent series on the
punctured unit disc with the same sum at every `w` with `0 < ‖w‖ < 1` have the same
coefficients.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.17, p. 9. -/
theorem IsPuncturedDiscLaurent.ext_of_laurentSum_eq {b b' : ℤ → ℂ}
    (hb : IsPuncturedDiscLaurent b) (hb' : IsPuncturedDiscLaurent b')
    (h : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → laurentSum b w = laurentSum b' w) : b = b' := by
  have hd := hb.add hb'.neg
  have h0 := hd.eq_zero_of_laurentSum_eq_zero fun w hw0 hw1 => by
    rw [laurentSum_add hb hb'.neg hw0 hw1, laurentSum_neg, h w hw0 hw1, add_neg_cancel]
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact h0

end WLight
