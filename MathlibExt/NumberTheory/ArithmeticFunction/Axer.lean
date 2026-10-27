/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSummatory
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.AtTopBot.Floor
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import MathlibExt.Analysis.BoundedVariation
import MathlibExt.NumberTheory.Harmonic.Floor

/-!
# Axer's theorem

Let `0 ≤ β < 1` and let `G` be a function of bounded variation on every interval `[1, T]` with
`G(x) = O(x ^ β)`. **Axer's theorem** states that if the Mertens function satisfies
`M(x) = o(x)`, then `∑_{n ≤ x} μ(n) G(x / n) = o(x)`.

As an application we prove a Tauberian theorem: if `f` has bounded variation on every `[1, T]`
and `∑_{n ≤ x} f(x / n) = x log x + C x + O(x ^ β)` with `0 ≤ β < 1`, then `M(x) = o(x)` implies
`f(x) = x + o(x)`.

Sums over `n ≤ x` for real `x` are written `∑ n ∈ Finset.Icc 1 ⌊x⌋₊, _`.

## Main statements

* `Real.sum_Icc_rpow_neg_le`: `∑_{n ≤ K} n ^ (-β) ≤ K ^ (1 - β) / (1 - β)` for `0 ≤ β < 1`.
* `boundedVariationOn_sum_comp_div_floor`: if `g` has bounded variation on every `[1, T]`, so
  does `y ↦ ∑_{n ≤ y} g(y / n)`.
* `isBigO_sum_comp_div_sub_id_sub_const`: normalising `∑_{n ≤ x} f(x / n) = x log x + C x + O(g)`
  to `∑_{n ≤ x} (f(x / n) - x / n - (C - γ)) = O(g)`.
* `ArithmeticFunction.isLittleO_sum_moebius_mul_comp_div`: Axer's theorem.
* `ArithmeticFunction.isLittleO_sub_id_of_isBigO_sum_comp_div_sub`: the Tauberian application.
-/

@[expose] public section

open Finset Filter Asymptotics

namespace Real

/-- **A partial `p`-series bound.** For `0 ≤ β < 1` and every integer `K ≥ 1`,
`∑_{n = 1}^{K} n ^ (-β) ≤ K ^ (1 - β) / (1 - β)`. -/
theorem sum_Icc_rpow_neg_le {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) {K : ℕ} (hK : 1 ≤ K) :
    ∑ n ∈ Icc 1 K, (n : ℝ) ^ (-β) ≤ (K : ℝ) ^ (1 - β) / (1 - β) := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-β)) (Set.Icc ((1 : ℕ) : ℝ) ((K : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := by
      have := hx.1; push_cast at this; linarith
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
    simp only [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    gcongr
  have hint := AntitoneOn.sum_le_integral_Ico hK hanti
  have hval : (∫ x in ((1 : ℕ) : ℝ)..((K : ℕ) : ℝ), x ^ (-β))
      = ((K : ℝ) ^ (1 - β) - 1) / (1 - β) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -β))]
    norm_num
    ring_nf
  have hre : ∑ n ∈ Icc 1 K, (n : ℝ) ^ (-β) = 1 + ∑ i ∈ Ico 1 K, ((i + 1 : ℕ) : ℝ) ^ (-β) := by
    rw [show Icc 1 K = Ico 1 (K + 1) by ext x; simp, sum_eq_sum_Ico_succ_bot (by omega),
      sum_Ico_add' (fun n : ℕ => ((n : ℝ)) ^ (-β)) 1 K 1]
    norm_num
  have hone : (1 : ℝ) ≤ 1 / (1 - β) := by
    rw [le_div_iff₀ h1β]; linarith
  rw [hval, sub_div] at hint
  rw [hre]
  linarith

end Real

/-- A finite Abel bound: if the partial sums `A m = ∑_{n ≤ m} a n` satisfy `|A m| ≤ D` for
`K ≤ m ≤ N`, and the weights `w` are nonnegative and nonincreasing on `(K, N]`, then
`|∑_{K < n ≤ N} a n w n| ≤ 2 D w (K + 1)`. A reindexing of
`Finset.abs_sum_mul_le_mul_of_abs_sum_range_le`. -/
private theorem abs_sum_Ioc_mul_le_of_antitoneOn {a w : ℕ → ℝ} {K N : ℕ} {D : ℝ} (hKN : K < N)
    (hpartial : ∀ m ∈ Icc K N, |∑ n ∈ Icc 1 m, a n| ≤ D)
    (hw₀ : ∀ m ∈ Ioc K N, 0 ≤ w m) (hw : AntitoneOn w (Set.Icc (K + 1) N)) :
    |∑ n ∈ Ioc K N, a n * w n| ≤ 2 * D * w (K + 1) := by
  set L := N - K with hL
  set g : ℕ → ℝ := fun i => if i < L then w (K + 1 + i) else 0 with hg
  have hsum : ∑ n ∈ Ioc K N, a n * w n = ∑ i ∈ range L, a (K + 1 + i) * g i := by
    rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
      show N + 1 - (K + 1) = L by omega]
    exact sum_congr rfl fun i hi => by simp [hg, mem_range.1 hi]
  have hpart : ∀ k, ∑ i ∈ range k, a (K + 1 + i)
      = ∑ n ∈ Icc 1 (K + k), a n - ∑ n ∈ Icc 1 K, a n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih, ← add_assoc, sum_Icc_succ_top (by omega)]
      ring_nf
  have hmain := abs_sum_mul_le_mul_of_abs_sum_range_le (f := fun i => a (K + 1 + i)) (g := g)
    (M := 2 * D) (n := L) ?_ ?_ ?_
  · rw [hsum]
    simpa [hg, show 0 < L by omega] using hmain
  · intro k hk
    rw [hpart, sub_eq_add_neg, two_mul]
    refine (abs_add_le _ _).trans (add_le_add (hpartial _ (mem_Icc.2 ⟨by omega, by omega⟩)) ?_)
    rw [abs_neg]
    exact hpartial _ (mem_Icc.2 ⟨le_rfl, hKN.le⟩)
  · intro i
    simp only [hg, Pi.zero_apply]
    split_ifs with h
    · exact hw₀ _ (mem_Ioc.2 ⟨by omega, by omega⟩)
    · exact le_rfl
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [hg, hi, hj, ↓reduceIte]
    exact hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)

/-- **Bounded variation of a floor-indexed dilation sum.** If `g` has bounded variation on every
interval `[1, T]`, then so does `y ↦ ∑_{n ≤ y} g (y / n)`. -/
theorem boundedVariationOn_sum_comp_div_floor {g : ℝ → ℝ}
    (hg : ∀ T : ℝ, BoundedVariationOn g (Set.Icc 1 T)) (T : ℝ) :
    BoundedVariationOn (fun y : ℝ => ∑ n ∈ Icc 1 ⌊y⌋₊, g (y / n)) (Set.Icc 1 T) := by
  rcases lt_or_ge T 1 with hT | hT
  · exact BoundedVariationOn.of_subsingleton
      (by rw [Set.Icc_eq_empty (not_le.mpr hT)]; exact Set.subsingleton_empty)
  -- On `[1, T]`, the `n`-th summand is `g` composed with the monotone self-map
  -- `y ↦ max y n / n` of `[1, T]`, corrected by a single jump at `y = n`.
  have hcomp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ T →
      BoundedVariationOn (fun y : ℝ => g (max y n / n)) (Set.Icc 1 T) := by
    intro n hn1 hnT
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hmono : MonotoneOn (fun y : ℝ => max y n / n) (Set.Icc 1 T) := fun p _ q _ hpq =>
      div_le_div_of_nonneg_right (max_le_max hpq le_rfl) hn0.le
    have hmaps : Set.MapsTo (fun y : ℝ => max y n / n) (Set.Icc 1 T) (Set.Icc 1 T) := by
      rintro y ⟨-, hy2⟩
      refine ⟨(one_le_div hn0).2 (le_max_right _ _), (div_le_iff₀ hn0).2 ?_⟩
      have h1 : max y n ≤ T := max_le hy2 hnT
      have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    exact ((eVariationOn.comp_le_of_monotoneOn g _ hmono hmaps).trans_lt (hg T).lt_top).ne
  set F : ℕ → ℝ → ℝ := fun n y => g (max y n / n) + (if (n : ℝ) ≤ y then 0 else -g 1) with hF
  have hBV : BoundedVariationOn (fun y => ∑ n ∈ Icc 1 ⌊T⌋₊, F n y) (Set.Icc 1 T) := by
    refine BoundedVariationOn.finsetSum fun n hn => ?_
    obtain ⟨hn1, hnT⟩ := mem_Icc.1 hn
    have hnT' : (n : ℝ) ≤ T := (Nat.le_floor_iff (by linarith)).1 hnT
    exact (hcomp n hn1 hnT').add (boundedVariationOn_ite_le _ _ _ _)
  refine ne_of_eq_of_ne (eVariationOn.eq_of_eqOn ?_) hBV
  rintro y ⟨hy1, hy2⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hFval : ∀ n ∈ Icc 1 ⌊T⌋₊, F n y = if (n : ℝ) ≤ y then g (y / n) else 0 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
    by_cases h : (n : ℝ) ≤ y
    · simp [hF, h]
    · simp [hF, h, max_eq_right (not_le.mp h).le, div_self (by linarith : (n : ℝ) ≠ 0)]
  have hfilter : (Icc 1 ⌊T⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ y) = Icc 1 ⌊y⌋₊ := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, Nat.le_floor h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans (Nat.floor_mono hy2)⟩, (Nat.le_floor_iff hy0).1 h2⟩
  simp only
  rw [sum_congr rfl hFval, ← sum_filter, hfilter]

/-- **Harmonic normalisation of a dilation sum.** Let `g` be eventually bounded below away from
zero in the sense `1 = O(g)`, and suppose `∑_{n ≤ x} f(x / n) = x log x + C x + O(g)`. Then,
with `γ` Euler's constant, `∑_{n ≤ x} (f(x / n) - x / n - (C - γ)) = O(g)`. -/
theorem isBigO_sum_comp_div_sub_id_sub_const {f g : ℝ → ℝ} {C : ℝ}
    (hg : (fun _ : ℝ => (1 : ℝ)) =O[atTop] g)
    (hF : (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, f (x / n) - (x * Real.log x + C * x)) =O[atTop] g) :
    (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, (f (x / n) - x / n - (C - Real.eulerMascheroniConstant)))
      =O[atTop] g := by
  set γ := Real.eulerMascheroniConstant
  -- `x (H_⌊x⌋ - log x - γ) = O(1)`.
  have hH : (fun x : ℝ => x * ((harmonic ⌊x⌋₊ : ℝ) - Real.log x - γ))
      =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    refine ((isBigO_refl (fun x : ℝ => x) atTop).mul
      Real.isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant).trans ?_
    refine (isBigO_refl _ _).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ne_atTop 0] with x hx using mul_inv_cancel₀ hx
  -- `(C - γ) (x - ⌊x⌋) = O(1)`.
  have hfl : (fun x : ℝ => (C - γ) * (x - ⌊x⌋₊)) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    refine IsBigO.of_bound |C - γ| ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [norm_one, mul_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le hx, Nat.lt_floor_add_one x]
  refine ((hF.sub (hH.trans hg)).add (hfl.trans hg)).congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  have hsum : ∑ n ∈ Icc 1 ⌊x⌋₊, x / (n : ℝ) = x * (harmonic ⌊x⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  simp only [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, hsum]
  ring

namespace ArithmeticFunction

open scoped Moebius

/-- **Axer's theorem.** Let `0 ≤ β < 1` and let `G` have bounded variation on every interval
`[1, T]` with `G(x) = O(x ^ β)`. If the Mertens function satisfies `M(x) = o(x)`, then
`∑_{n ≤ x} μ(n) G(x / n) = o(x)`. -/
theorem isLittleO_sum_moebius_mul_comp_div {G : ℝ → ℝ} {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (hG : G =O[atTop] fun x : ℝ => x ^ β)
    (hG_bv : ∀ T : ℝ, BoundedVariationOn G (Set.Icc 1 T))
    (hM : (fun x : ℝ => (mertens x : ℝ)) =o[atTop] fun x : ℝ => x) :
    (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * G (x / n)) =o[atTop] fun x : ℝ => x := by
  simp only [mertens, Int.cast_sum] at hM
  have h1β : (0 : ℝ) < 1 - β := by linarith
  have hIcc : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => rfl
  have hmu : ∀ n : ℕ, |(μ n : ℝ)| ≤ 1 := fun n => by
    exact_mod_cast abs_moebius_le_one (n := n)
  -- A global growth bound for `G` above a threshold `T ≥ 1`.
  obtain ⟨C₀, hC₀⟩ := hG.bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC₀
  obtain ⟨C, hC1, hGbd⟩ :
      ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, max T₀ 1 ≤ t → |G t| ≤ C * t ^ β := by
    refine ⟨max C₀ 1, le_max_right _ _, fun t ht => ?_⟩
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos (le_trans (le_max_right T₀ 1) ht)
    have h1 := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htpos.le β)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg htpos.le β))
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  rw [isLittleO_iff]
  intro c hc
  -- Choice of the splitting parameter `ε`.
  have hθ : (0 : ℝ) < c * (1 - β) / (2 * C) := by positivity
  obtain ⟨ε, hε0, hεhalf, hεT, hεrpow⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ T ≤ 1 / ε ∧ C / (1 - β) * ε ^ (1 - β) ≤ c / 2 := by
    set θ : ℝ := c * (1 - β) / (2 * C) with hθdef
    set u : ℝ := θ ^ (1 / (1 - β)) with hudef
    have hu : 0 < u := Real.rpow_pos_of_pos hθ _
    have hueq : u ^ (1 - β) = θ := by
      rw [hudef, ← Real.rpow_mul hθ.le, one_div, inv_mul_cancel₀ (ne_of_gt h1β), Real.rpow_one]
    have hpos : (0 : ℝ) < min (min u (1 / 2)) (1 / T) :=
      lt_min (lt_min hu (by norm_num)) (by positivity)
    refine ⟨min (min u (1 / 2)) (1 / T), hpos, le_trans (min_le_left _ _) (min_le_right _ _),
      ?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      have h3 := mul_le_mul_of_nonneg_right (min_le_right (min u (1 / 2)) (1 / T)) hTpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hTpos)] at h3
      linarith
    · have hle : min (min u (1 / 2)) (1 / T) ≤ u := le_trans (min_le_left _ _) (min_le_left _ _)
      have hmono : (min (min u (1 / 2)) (1 / T)) ^ (1 - β) ≤ θ := by
        rw [← hueq]; exact Real.rpow_le_rpow hpos.le hle h1β.le
      have hfin : C / (1 - β) * θ = c / 2 := by
        rw [hθdef]; field_simp
      calc C / (1 - β) * (min (min u (1 / 2)) (1 / T)) ^ (1 - β)
          ≤ C / (1 - β) * θ := mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = c / 2 := hfin
  have hεinv1 : (1 : ℝ) ≤ 1 / ε := le_trans hT1 hεT
  have hmem1 : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (1 / ε) := ⟨le_refl 1, hεinv1⟩
  have hmemE : (1 / ε) ∈ Set.Icc (1 : ℝ) (1 / ε) := ⟨hεinv1, le_refl _⟩
  -- Decompose `G` into a difference of monotone functions on `[1, 1/ε]`.
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    (hG_bv (1 / ε)).locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hBp : 0 ≤ p (1 / ε) - p 1 := sub_nonneg.mpr (hp hmem1 hmemE hεinv1)
  have hBq : 0 ≤ q (1 / ε) - q 1 := sub_nonneg.mpr (hq hmem1 hmemE hεinv1)
  obtain ⟨S, hSdef⟩ :
      ∃ S : ℝ, S = (p (1 / ε) - p 1) + (q (1 / ε) - q 1) + |G 1| + 1 := ⟨_, rfl⟩
  have hS1 : (1 : ℝ) ≤ S := by rw [hSdef]; linarith [abs_nonneg (G 1)]
  have hS0 : (0 : ℝ) < S := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = c / (4 * S) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηS : η * S = c / 4 := by rw [hηdef]; field_simp
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (isLittleO_iff.mp hM hη)
  filter_upwards [eventually_ge_atTop (max (max 2 (1 / ε)) ((X₀ + 1) / ε))] with x hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxinv : 1 / ε ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX : (X₀ + 1) / ε ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊x⌋₊ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊ε * x⌋₊ := ⟨_, rfl⟩
  have hNle : (N : ℝ) ≤ x := by rw [hN]; exact Nat.floor_le hx0.le
  have hNgt : x - 1 < (N : ℝ) := by
    have := Nat.lt_floor_add_one x
    rw [hN]; linarith
  have hεx0 : (0 : ℝ) < ε * x := mul_pos hε0 hx0
  have hKle : (K : ℝ) ≤ ε * x := by rw [hK]; exact Nat.floor_le hεx0.le
  have hεx1 : (1 : ℝ) ≤ ε * x := by
    have := (div_le_iff₀ hε0).mp hxinv
    linarith
  have hKgt : ε * x - 1 < (K : ℝ) := by
    have := Nat.lt_floor_add_one (ε * x)
    rw [hK]; linarith
  have hK1 : 1 ≤ K := by
    rw [hK]
    exact Nat.le_floor (by exact_mod_cast hεx1)
  have hKx : (K : ℝ) ≤ x := by nlinarith
  have hKN : K < N := by
    have h1 : (K : ℝ) ≤ x / 2 := by nlinarith
    have h2 : (K : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast h2
  have hKX₀ : X₀ ≤ (K : ℝ) := by
    have h := (div_le_iff₀ hε0).mp hxX
    linarith
  -- The dilated arguments stay inside `[1, 1/ε]`.
  have hrange : ∀ n : ℕ, K < n → n ≤ N → (x / (n : ℝ)) ∈ Set.Icc (1 : ℝ) (1 / ε) := by
    intro n hn1 hn2
    have hn1' : (K : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) K]
    have hn2' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    constructor
    · rw [le_div_iff₀ hnpos]; linarith
    · rw [div_le_iff₀ hnpos]
      have hid : (1 / ε) * (ε * x) = x := by field_simp
      have := mul_le_mul_of_nonneg_left (by linarith : ε * x ≤ (n : ℝ))
        (by positivity : (0 : ℝ) ≤ 1 / ε)
      linarith [hid ▸ this]
  -- Uniform bound on the Mertens function on the relevant range.
  have hAbound : ∀ m : ℕ, X₀ ≤ (m : ℝ) → (m : ℝ) ≤ x →
      |∑ n ∈ Icc 1 m, (μ n : ℝ)| ≤ η * x := by
    intro m hm1 hm2
    have h := hX₀ (m : ℝ) hm1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.floor_natCast,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)] at h
    exact h.trans (mul_le_mul_of_nonneg_left hm2 hη.le)
  -- The Abel bound, applied to an arbitrary monotone piece.
  have habel : ∀ r : ℝ → ℝ, MonotoneOn r (Set.Icc (1 : ℝ) (1 / ε)) →
      |∑ n ∈ Ioc K N, (μ n : ℝ) * (r (x / (n : ℝ)) - r 1)|
        ≤ 2 * (η * x) * (r (1 / ε) - r 1) := by
    intro r hr
    have hmain := abs_sum_Ioc_mul_le_of_antitoneOn (a := fun n : ℕ => (μ n : ℝ))
      (w := fun n : ℕ => r (x / (n : ℝ)) - r 1) (D := η * x) hKN ?_ ?_ ?_
    · refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact sub_le_sub_right
        (hr (hrange (K + 1) (by omega) (by omega)) hmemE (hrange (K + 1) (by omega) (by omega)).2) _
    · intro m hm
      rw [mem_Icc] at hm
      have hmK : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
      have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm.2
      exact hAbound m (le_trans hKX₀ hmK) (le_trans hmN hNle)
    · intro m hm
      rw [mem_Ioc] at hm
      exact sub_nonneg.mpr (hr hmem1 (hrange m hm.1 hm.2) (hrange m hm.1 hm.2).1)
    · intro m hm m' hm' hmm'
      simp only [Set.mem_Icc] at hm hm'
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
      have hdiv : x / (m' : ℝ) ≤ x / (m : ℝ) :=
        div_le_div_of_nonneg_left hx0.le hmpos (by exact_mod_cast hmm')
      exact sub_le_sub_right
        (hr (hrange m' (by omega) hm'.2) (hrange m (by omega) hm.2) hdiv) _
  -- The tail sum of `μ`.
  have hmusum : |∑ n ∈ Ioc K N, (μ n : ℝ)| ≤ 2 * (η * x) := by
    have hs : ∑ n ∈ Ioc K N, (μ n : ℝ)
        = ∑ n ∈ Icc 1 N, (μ n : ℝ) - ∑ n ∈ Icc 1 K, (μ n : ℝ) := by
      rw [hIcc K, hIcc N, eq_sub_iff_add_eq, add_comm]
      exact sum_Ioc_consecutive _ (Nat.zero_le K) hKN.le
    have h1 := hAbound K hKX₀ hKx
    have h2 := hAbound N (le_trans hKX₀ (by exact_mod_cast hKN.le)) hNle
    rw [hs]
    exact (abs_sub _ _).trans (by linarith)
  -- The small-index part.
  have hpart1 : |∑ n ∈ Icc 1 K, (μ n : ℝ) * G (x / (n : ℝ))| ≤ c / 2 * x := by
    have hCx : (0 : ℝ) ≤ C * x ^ β := mul_nonneg hC0.le (Real.rpow_nonneg hx0.le β)
    have hterm : ∀ n ∈ Icc 1 K,
        |(μ n : ℝ) * G (x / (n : ℝ))| ≤ (C * x ^ β) * (n : ℝ) ^ (-β) := by
      intro n hn
      rw [mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnle : (n : ℝ) ≤ ε * x := le_trans (by exact_mod_cast hn.2) hKle
      have harg : T ≤ x / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]
        have h1 : T * (n : ℝ) ≤ (1 / ε) * (ε * x) :=
          mul_le_mul hεT hnle (by linarith) (by positivity)
        have h2 : (1 / ε) * (ε * x) = x := by field_simp
        linarith
      have hrw : (x / (n : ℝ)) ^ β = x ^ β * (n : ℝ) ^ (-β) := by
        rw [Real.div_rpow hx0.le hnpos.le, Real.rpow_neg hnpos.le]
        ring
      rw [abs_mul]
      calc |(μ n : ℝ)| * |G (x / (n : ℝ))| ≤ 1 * (C * (x / (n : ℝ)) ^ β) :=
            mul_le_mul (hmu n) (hGbd _ harg) (abs_nonneg _) zero_le_one
        _ = (C * x ^ β) * (n : ℝ) ^ (-β) := by rw [hrw]; ring
    have hmono : ((K : ℝ)) ^ (1 - β) ≤ (ε * x) ^ (1 - β) :=
      Real.rpow_le_rpow (Nat.cast_nonneg K) hKle h1β.le
    calc |∑ n ∈ Icc 1 K, (μ n : ℝ) * G (x / (n : ℝ))|
        ≤ ∑ n ∈ Icc 1 K, |(μ n : ℝ) * G (x / (n : ℝ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 K, (C * x ^ β) * (n : ℝ) ^ (-β) := sum_le_sum hterm
      _ = (C * x ^ β) * ∑ n ∈ Icc 1 K, (n : ℝ) ^ (-β) := by rw [mul_sum]
      _ ≤ (C * x ^ β) * ((K : ℝ) ^ (1 - β) / (1 - β)) :=
          mul_le_mul_of_nonneg_left (Real.sum_Icc_rpow_neg_le hβ₀ hβ₁ hK1) hCx
      _ ≤ (C * x ^ β) * ((ε * x) ^ (1 - β) / (1 - β)) := by
          gcongr
      _ = (C / (1 - β) * ε ^ (1 - β)) * (x ^ β * x ^ (1 - β)) := by
          rw [Real.mul_rpow hε0.le hx0.le]; ring
      _ = (C / (1 - β) * ε ^ (1 - β)) * x := by
          rw [← Real.rpow_add hx0]; norm_num
      _ ≤ c / 2 * x := mul_le_mul_of_nonneg_right hεrpow hx0.le
  -- The large-index part.
  have hpart2 : |∑ n ∈ Ioc K N, (μ n : ℝ) * G (x / (n : ℝ))| ≤ c / 2 * x := by
    have hdec : ∑ n ∈ Ioc K N, (μ n : ℝ) * G (x / (n : ℝ))
        = (∑ n ∈ Ioc K N, (μ n : ℝ) * (p (x / (n : ℝ)) - p 1))
          - (∑ n ∈ Ioc K N, (μ n : ℝ) * (q (x / (n : ℝ)) - q 1))
          + G 1 * ∑ n ∈ Ioc K N, (μ n : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      have hG1 : G 1 = p 1 - q 1 := by rw [hpq]; simp
      have hGn : G (x / (n : ℝ)) = p (x / (n : ℝ)) - q (x / (n : ℝ)) := by rw [hpq]; simp
      rw [hG1, hGn]; ring
    have h1 := habel p hp
    have h2 := habel q hq
    have h3 : |G 1 * ∑ n ∈ Ioc K N, (μ n : ℝ)| ≤ |G 1| * (2 * (η * x)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hmusum (abs_nonneg _)
    have hηx : (0 : ℝ) ≤ η * x := by positivity
    rw [hdec]
    have hS : 2 * (η * x) * (p (1 / ε) - p 1) + 2 * (η * x) * (q (1 / ε) - q 1)
        + |G 1| * (2 * (η * x)) = c / 2 * x - 2 * (η * x) := by
      have h4 : c / 2 * x = 2 * x * (η * S) := by rw [hηS]; ring
      rw [h4, hSdef]; ring
    linarith [abs_add_le ((∑ n ∈ Ioc K N, (μ n : ℝ) * (p (x / (n : ℝ)) - p 1))
        - (∑ n ∈ Ioc K N, (μ n : ℝ) * (q (x / (n : ℝ)) - q 1)))
        (G 1 * ∑ n ∈ Ioc K N, (μ n : ℝ)),
      abs_sub (∑ n ∈ Ioc K N, (μ n : ℝ) * (p (x / (n : ℝ)) - p 1))
        (∑ n ∈ Ioc K N, (μ n : ℝ) * (q (x / (n : ℝ)) - q 1))]
  -- Put the two halves together.
  have hsplit : ∑ n ∈ Icc 1 N, (μ n : ℝ) * G (x / (n : ℝ))
      = (∑ n ∈ Icc 1 K, (μ n : ℝ) * G (x / (n : ℝ)))
        + ∑ n ∈ Ioc K N, (μ n : ℝ) * G (x / (n : ℝ)) := by
    rw [hIcc K, hIcc N]
    exact (sum_Ioc_consecutive _ (Nat.zero_le K) hKN.le).symm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, ← hN, hsplit]
  linarith [abs_add_le (∑ n ∈ Icc 1 K, (μ n : ℝ) * G (x / (n : ℝ)))
    (∑ n ∈ Ioc K N, (μ n : ℝ) * G (x / (n : ℝ)))]

/-- **A Tauberian theorem from `M(x) = o(x)`.** Let `f` have bounded variation on every interval
`[1, T]`, and suppose that `∑_{n ≤ x} f(x / n) = x log x + C x + O(x ^ β)` with `0 ≤ β < 1`.
If the Mertens function satisfies `M(x) = o(x)`, then `f(x) = x + o(x)`. -/
theorem isLittleO_sub_id_of_isBigO_sum_comp_div_sub {f : ℝ → ℝ} {C β : ℝ} (hβ₀ : 0 ≤ β)
    (hβ₁ : β < 1) (hbv : ∀ T : ℝ, BoundedVariationOn f (Set.Icc 1 T))
    (hF : (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, f (x / n) - (x * Real.log x + C * x))
      =O[atTop] fun x : ℝ => x ^ β)
    (hM : (fun x : ℝ => (mertens x : ℝ)) =o[atTop] fun x : ℝ => x) :
    (fun x : ℝ => f x - x) =o[atTop] fun x : ℝ => x := by
  set γ := Real.eulerMascheroniConstant
  -- The normalised function `f₀ y = f y - y - (C - γ)` inherits bounded variation from `f`.
  have hbv0 : ∀ T : ℝ, BoundedVariationOn (fun y : ℝ => f y - y - (C - γ)) (Set.Icc 1 T) := by
    intro T
    have h := ((hbv T).sub (BoundedVariationOn.id_Icc 1 T)).sub
      (boundedVariationOn_const (C - γ) (Set.Icc (1 : ℝ) T))
    exact h
  have hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] fun x : ℝ => x ^ β := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) β)]
    exact Real.one_le_rpow hx hβ₀
  have hGO : (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, (f (x / n) - x / n - (C - γ)))
      =O[atTop] fun x : ℝ => x ^ β :=
    isBigO_sum_comp_div_sub_id_sub_const hone hF
  have hGbv : ∀ T : ℝ, BoundedVariationOn
      (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, (f (x / n) - x / n - (C - γ))) (Set.Icc 1 T) :=
    boundedVariationOn_sum_comp_div_floor (g := fun y : ℝ => f y - y - (C - γ)) hbv0
  have hAxer := isLittleO_sum_moebius_mul_comp_div hβ₀ hβ₁ hGO hGbv hM
  -- Möbius inversion recovers `f₀` from its dilation sum.
  have hinv := (sum_floor_div_eq_iff_sum_moebius_smul_floor_div_eq
      (fun y : ℝ => f y - y - (C - γ))
      (fun y : ℝ => ∑ n ∈ Icc 1 ⌊y⌋₊, (f (y / n) - y / n - (C - γ)))).mp (fun x _ => rfl)
  have hf₀ : (fun x : ℝ => f x - x - (C - γ)) =o[atTop] fun x : ℝ => x := by
    refine hAxer.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [hinv x hx, zsmul_eq_mul]
  simpa using hf₀.add (isLittleO_const_id_atTop (C - γ))

end ArithmeticFunction
