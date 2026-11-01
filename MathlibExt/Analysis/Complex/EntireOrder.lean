/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Bound

/-!
# The order of growth of an entire function

A function `f : ℂ → E` has *order of growth at most `ρ`* if for every `ε > 0` it is
`O(exp (‖z‖ ^ (ρ + ε)))` as `z → ∞`. It has *order `ρ`* if moreover `ρ ≥ 0` and it has order
at most no smaller nonnegative exponent. For a nonzero entire function this is the classical order
`limsup_{r → ∞} log log M(r) / log r`, where `M(r)` is the maximum of `‖f‖` on the circle of
radius `r`; in particular constants and polynomials have order `0`. Negative exponents are
excluded because a bounded function has order at most every real number.

This is not Mathlib's `analyticOrderAt` or `meromorphicOrderAt`, which measure the order of
vanishing at a point.

The two growth statements about zeros proved here are the inputs of Hadamard's factorization
theorem: for `f` entire of order at most `ρ ≥ 0`, the number of zeros in the closed disc of
radius `r`, counted with multiplicity, is `O(r ^ (ρ + ε))`, and the zeros `z_n` (again with
multiplicity) satisfy `∑ ‖z_n‖ ^ (-ρ - ε) < ∞`. Both follow from Jensen's inequality.

## Main definitions

* `Complex.HasGrowthOrderLE f ρ`: `f` has order of growth at most `ρ`.
* `Complex.HasGrowthOrder f ρ`: `f` has order of growth exactly `ρ`.

## Main statements

* `Complex.HasGrowthOrderLE.mono`, `Complex.HasGrowthOrderLE.trans_isBigO`,
  `Complex.HasGrowthOrderLE.add`, `Complex.HasGrowthOrderLE.mul`,
  `Complex.hasGrowthOrderLE_of_isBigO_one`,
  `Complex.hasGrowthOrderLE_one_of_isBigO_exp_mul_norm`: basic closure properties; in
  particular functions of exponential type have order at most `1`.
* `Complex.HasGrowthOrder.nonneg`, `Complex.HasGrowthOrder.unique`: the order is a well-defined
  nonnegative real number.
* `Complex.hasGrowthOrder_zero_iff`, `Complex.hasGrowthOrder_zero_of_isBigO_one`: order `0` is
  order at most `0`; in particular bounded functions and constants have order `0`.
* `Complex.HasGrowthOrderLE.isBigO_sum_divisor_closedBall`: the zero-counting function of an
  entire function of order at most `ρ` is `O(r ^ (ρ + ε))`.
* `Complex.HasGrowthOrderLE.summable_norm_rpow_neg`: the zeros `z_n` of an entire function of
  order at most `ρ` with `f 0 ≠ 0` satisfy `∑ ‖z_n‖ ^ (-ρ - ε) < ∞` (the exponent of
  convergence is at most the order).
-/

@[expose] public section

open Filter Asymptotics Bornology Metric Topology

namespace Complex

variable {E : Type*}

/-- `f` has *order of growth at most `ρ`*: for every `ε > 0`, `f = O(exp (‖z‖ ^ (ρ + ε)))` as
`z → ∞`. The quantifier on `ε` sits outside the `O`, so this is strictly weaker than
`f =O[cobounded ℂ] fun z => exp (‖z‖ ^ ρ)`. -/
def HasGrowthOrderLE [Norm E] (f : ℂ → E) (ρ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (ρ + ε))

/-- `f` has *order of growth `ρ`*: `ρ ≥ 0`, `f` has order at most `ρ`, and order at most no
smaller nonnegative exponent. For a nonzero entire `f` this is the classical order
`limsup log log M(r) / log r`; constants have order `0`. -/
def HasGrowthOrder [Norm E] (f : ℂ → E) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ HasGrowthOrderLE f ρ ∧ ∀ ρ' ∈ Set.Ico 0 ρ, ¬ HasGrowthOrderLE f ρ'

section Basic

variable [Norm E] {f g : ℂ → E} {ρ ρ' : ℝ}

/-- `exp (‖z‖ ^ a) ≤ exp (‖z‖ ^ b)` for `a ≤ b` once `‖z‖ ≥ 1`. -/
private lemma eventually_exp_rpow_le {a b : ℝ} (hab : a ≤ b) :
    ∀ᶠ z in cobounded ℂ, ‖Real.exp (‖z‖ ^ a)‖ ≤ 1 * ‖Real.exp (‖z‖ ^ b)‖ := by
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hz hab)

/-- Order at most `ρ` gives order at most every larger exponent. -/
theorem HasGrowthOrderLE.mono (h : HasGrowthOrderLE f ρ) (hρ : ρ ≤ ρ') :
    HasGrowthOrderLE f ρ' := fun ε hε =>
  (h ε hε).trans (IsBigO.of_bound 1 (eventually_exp_rpow_le (by linarith)))

/-- If `f = O(g)` at infinity and `g` has order at most `ρ`, so does `f`. -/
theorem HasGrowthOrderLE.trans_isBigO {F : Type*} [SeminormedAddCommGroup F] {g : ℂ → F}
    (hg : HasGrowthOrderLE g ρ) (hfg : f =O[cobounded ℂ] g) : HasGrowthOrderLE f ρ :=
  fun ε hε => hfg.trans (hg ε hε)

/-- A function bounded at infinity has order at most every `ρ`. -/
theorem hasGrowthOrderLE_of_isBigO_one (hf : f =O[cobounded ℂ] fun _ => (1 : ℝ)) (ρ : ℝ) :
    HasGrowthOrderLE f ρ := by
  intro ε _
  refine hf.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_one]
  exact Real.one_le_exp (Real.rpow_nonneg (norm_nonneg _) _)

/-- A constant function has order at most every `ρ`. -/
theorem hasGrowthOrderLE_const (c : E) (ρ : ℝ) : HasGrowthOrderLE (fun _ => c) ρ :=
  hasGrowthOrderLE_of_isBigO_one (isBigO_const_const c one_ne_zero _) ρ

/-- A function of order `ρ` has order at most `ρ`. -/
theorem HasGrowthOrder.hasGrowthOrderLE (h : HasGrowthOrder f ρ) : HasGrowthOrderLE f ρ :=
  h.2.1

/-- **The order is nonnegative.** -/
theorem HasGrowthOrder.nonneg (h : HasGrowthOrder f ρ) : 0 ≤ ρ :=
  h.1

/-- A function of order `ρ` has order at most no nonnegative `ρ' < ρ`. -/
theorem HasGrowthOrder.not_hasGrowthOrderLE (h : HasGrowthOrder f ρ) (h0 : 0 ≤ ρ')
    (hlt : ρ' < ρ) : ¬ HasGrowthOrderLE f ρ' :=
  h.2.2 ρ' ⟨h0, hlt⟩

/-- **The order is unique.** -/
theorem HasGrowthOrder.unique (h : HasGrowthOrder f ρ) (h' : HasGrowthOrder f ρ') :
    ρ = ρ' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.not_hasGrowthOrderLE h.nonneg hlt h.hasGrowthOrderLE
  · exact h.not_hasGrowthOrderLE h'.nonneg hlt h'.hasGrowthOrderLE

/-- `f` has order `0` exactly when it has order at most `0`. -/
theorem hasGrowthOrder_zero_iff : HasGrowthOrder f 0 ↔ HasGrowthOrderLE f 0 :=
  ⟨HasGrowthOrder.hasGrowthOrderLE, fun h => ⟨le_rfl, h, fun _ h' => absurd h'.1 h'.2.not_ge⟩⟩

/-- A function bounded at infinity has order `0`. -/
theorem hasGrowthOrder_zero_of_isBigO_one (hf : f =O[cobounded ℂ] fun _ => (1 : ℝ)) :
    HasGrowthOrder f 0 :=
  hasGrowthOrder_zero_iff.mpr (hasGrowthOrderLE_of_isBigO_one hf 0)

/-- A constant function has order `0`. -/
theorem hasGrowthOrder_const (c : E) : HasGrowthOrder (fun _ => c) 0 :=
  hasGrowthOrder_zero_iff.mpr (hasGrowthOrderLE_const c 0)

/-- A function with `‖f z‖ ≤ C exp (A ‖z‖)` at infinity (a function of *exponential type*) has
order at most `1`. -/
theorem hasGrowthOrderLE_one_of_isBigO_exp_mul_norm {A : ℝ}
    (hf : f =O[cobounded ℂ] fun z => Real.exp (A * ‖z‖)) : HasGrowthOrderLE f 1 := by
  intro ε hε
  refine hf.trans (IsBigO.of_bound 1 ?_)
  have hA : ∀ᶠ r : ℝ in atTop, A ≤ r ^ ε := (tendsto_rpow_atTop hε).eventually_ge_atTop A
  filter_upwards [tendsto_norm_cobounded_atTop.eventually hA,
    tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz hz1
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp, Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left hz (by linarith)

end Basic

/-- **Sums.** If `f` and `g` have order at most `ρ`, so does `f + g`. -/
theorem HasGrowthOrderLE.add {F : Type*} [SeminormedAddCommGroup F] {f g : ℂ → F} {ρ : ℝ}
    (hf : HasGrowthOrderLE f ρ) (hg : HasGrowthOrderLE g ρ) :
    HasGrowthOrderLE (fun z => f z + g z) ρ :=
  fun ε hε => (hf ε hε).add (hg ε hε)

/-- **Products.** If `f` and `g` have order at most `ρ`, so does `f * g`. -/
theorem HasGrowthOrderLE.mul {R : Type*} [SeminormedRing R] {f g : ℂ → R} {ρ : ℝ}
    (hf : HasGrowthOrderLE f ρ) (hg : HasGrowthOrderLE g ρ) :
    HasGrowthOrderLE (fun z => f z * g z) ρ := by
  intro ε hε
  refine ((hf (ε / 2) (by positivity)).mul (hg (ε / 2) (by positivity))).trans
    (IsBigO.of_bound 1 ?_)
  have h2 : ∀ᶠ r : ℝ in atTop, 2 ≤ r ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  filter_upwards [tendsto_norm_cobounded_atTop.eventually h2,
    tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz hz0
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, Real.exp_le_exp]
  have e : ‖z‖ ^ (ρ + ε) = ‖z‖ ^ (ε / 2) * ‖z‖ ^ (ρ + ε / 2) := by
    rw [← Real.rpow_add hz0]; ring_nf
  have : 0 ≤ ‖z‖ ^ (ρ + ε / 2) := Real.rpow_nonneg (norm_nonneg _) _
  rw [e]
  nlinarith

/-! ### Zeros of entire functions of finite order -/

section Zeros

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- **The zero-counting function of an entire function of finite order.** If `f` is entire of
order at most `ρ ≥ 0`, then for every `ε > 0` the number of zeros of `f` in the closed disc
`‖z‖ ≤ r`, counted with multiplicity, is `O(r ^ (ρ + ε))` as `r → ∞`.

The count is the finite sum of the divisor of `f` on the disc. If `f ≡ 0` the divisor is `0`, and
the statement is trivially true. A zero at the origin is allowed. -/
theorem HasGrowthOrderLE.isBigO_sum_divisor_closedBall (hf : Differentiable ℂ f)
    (h : HasGrowthOrderLE f ρ) (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    (fun r : ℝ => ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ))
      =O[atTop] fun r => r ^ (ρ + ε) := by
  classical
  have han : ∀ U : Set ℂ, AnalyticOnNhd ℂ f U := fun U z _ => hf.analyticAt z
  set p := ρ + ε with hp
  have hp0 : 0 < p := by linarith
  by_cases hzero : ∀ a, f a = 0
  · have hf0 : f = 0 := funext hzero
    have : ∀ r : ℝ, ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) = 0 := by
      intro r
      simp [hf0]
    simp only [this]
    exact isBigO_zero _ _
  push Not at hzero
  obtain ⟨a, ha⟩ := hzero
  obtain ⟨C, hC⟩ := (h ε hε).bound
  rw [← comap_norm_atTop, eventually_comap, eventually_atTop] at hC
  obtain ⟨R0, hR0⟩ := hC
  set A := ‖a‖ with hA
  have hfa : 0 < ‖f a‖ := norm_pos_iff.mpr ha
  set K := (3 ^ p + |Real.log (1 + |C|)| + |Real.log ‖f a‖|) / Real.log 2 with hK
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (max 1 (max R0 (3 * A)))] with r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hrR0 : R0 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3A : 3 * A ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hA0 : 0 ≤ A := norm_nonneg _
  set ρ' := r + A with hρ'
  have hρ0 : 0 < ρ' := by linarith
  -- the zeros in `‖u‖ ≤ r` lie in the disc of radius `ρ'` about `a`
  have hcount : ∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u ≤
      ∑ᶠ u, MeromorphicOn.divisor f (closedBall a |ρ'|) u := by
    apply finsum_le_finsum
    · exact (MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _)
    · exact (MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _)
    · intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) r
      · have hu' : u ∈ closedBall a |ρ'| := by
          rw [abs_of_pos hρ0]
          simp only [mem_closedBall, dist_eq_norm, sub_zero] at hu ⊢
          calc ‖u - a‖ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ ρ' := by linarith
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (han _) hu,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (han _) hu']
      · simp only [hu, not_false_eq_true,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
        exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han (closedBall a |ρ'|)) u
  set M := 1 + |C| * Real.exp ((3 * r) ^ p) with hM
  have hJ := AnalyticOnNhd.sum_divisor_le (c := a) (r := ρ') (R := 2 * ρ') (M := M)
    (by rw [abs_of_pos hρ0]; exact hρ0)
    (by rw [abs_of_pos hρ0, abs_of_pos (by linarith)]; linarith)
    (le_add_of_nonneg_right (by positivity)) (han _) ha (by
      intro z hz
      rw [abs_of_pos (by linarith), mem_sphere_iff_norm] at hz
      have hz1 : ‖z‖ ≥ 2 * ρ' - A := by
        have := norm_sub_le z a
        have := norm_sub_norm_le z a
        linarith
      have hz2 : ‖z‖ ≤ 3 * r := by
        have : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by
          calc ‖z‖ = ‖(z - a) + a‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith
      have h := hR0 ‖z‖ (by linarith) z rfl
      rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h
      have hmono : Real.exp (‖z‖ ^ p) ≤ Real.exp ((3 * r) ^ p) :=
        Real.exp_le_exp.mpr (Real.rpow_le_rpow (norm_nonneg _) hz2 hp0.le)
      calc ‖f z‖ ≤ C * Real.exp (‖z‖ ^ p) := h
        _ ≤ |C| * Real.exp (‖z‖ ^ p) := by gcongr; exact le_abs_self C
        _ ≤ |C| * Real.exp ((3 * r) ^ p) := by gcongr
        _ ≤ M := le_add_of_nonneg_left zero_le_one)
  have hlog2 : Real.log (2 * ρ' / ρ') = Real.log 2 := by
    rw [mul_div_assoc, div_self hρ0.ne', mul_one]
  rw [hlog2] at hJ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrp : 1 ≤ r ^ p := Real.one_le_rpow hr1 hp0.le
  have h3 : (3 * r) ^ p = 3 ^ p * r ^ p := Real.mul_rpow (by norm_num) (by linarith)
  have hMle : Real.log M ≤ Real.log (1 + |C|) + (3 * r) ^ p := by
    have hx : 0 ≤ (3 * r) ^ p := Real.rpow_nonneg (by linarith) _
    have hex : 1 ≤ Real.exp ((3 * r) ^ p) := Real.one_le_exp hx
    rw [← Real.log_exp ((3 * r) ^ p), ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hM]
    nlinarith [abs_nonneg C]
  have hMpos : 0 < M := by positivity
  rw [Real.log_div hMpos.ne' hfa.ne'] at hJ
  have hn0 : (0 : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) := by
    exact_mod_cast finsum_nonneg fun u =>
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han (closedBall 0 r)) u
  have hcount' : ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) ≤
      (Real.log M - Real.log ‖f a‖) / Real.log 2 :=
    le_trans (by exact_mod_cast hcount) hJ
  rw [Real.norm_of_nonneg hn0, Real.norm_of_nonneg (by linarith)]
  refine hcount'.trans ?_
  rw [hK, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hl2.le
  have e1 := le_abs_self (Real.log (1 + |C|))
  have e2 := neg_le_abs (Real.log ‖f a‖)
  have e3 : 0 ≤ |Real.log (1 + |C|)| := abs_nonneg _
  have e4 : 0 ≤ |Real.log ‖f a‖| := abs_nonneg _
  nlinarith

/-- **The exponent of convergence is at most the order.** Let `f` be entire of order at most
`ρ ≥ 0` with `f 0 ≠ 0`, and let `z : ι → ℂ` list the zeros of `f` with multiplicity, i.e. the
fibre of `z` over each `w` has `analyticOrderAt f w` elements. Then `∑ ‖z n‖ ^ (-ρ - ε)` converges
for every `ε > 0`.

The index type is arbitrary, which covers functions with finitely many zeros, and no ordering of
the zeros is needed. `f 0 ≠ 0` makes every `z n` nonzero. -/
theorem HasGrowthOrderLE.summable_norm_rpow_neg {ι : Type*} {z : ι → ℂ} {ε : ℝ}
    (hf : Differentiable ℂ f) (h : HasGrowthOrderLE f ρ) (hρ : 0 ≤ ρ) (hf0 : f 0 ≠ 0)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) (hε : 0 < ε) :
    Summable fun n => ‖z n‖ ^ (-ρ - ε) := by
  classical
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  -- every order of vanishing is finite
  have h00 : analyticOrderAt f 0 = 0 := (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0
  have hfin : ∀ w, analyticOrderAt f w ≠ ⊤ := fun w =>
    han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ w) (by rw [h00]; exact ENat.zero_ne_top)
  -- each `z n` is a zero of `f`
  have hzero : ∀ n, f (z n) = 0 := by
    intro n
    have h1 : analyticOrderAt f (z n) ≠ 0 := by
      rw [← hz (z n)]
      intro h
      have : IsEmpty {m // z m = z n} := ENat.card_eq_zero_iff_empty _ |>.mp h
      exact this.false ⟨n, rfl⟩
    by_contra h
    exact h1 ((hf.analyticAt _).analyticOrderAt_eq_zero.mpr h)
  -- the zeros stay away from the origin
  obtain ⟨r₀, hr₀, hr₀z⟩ : ∃ r₀ > 0, ∀ n, r₀ ≤ ‖z n‖ := by
    have hev : ∀ᶠ w in 𝓝 (0 : ℂ), f w ≠ 0 := hf.continuous.continuousAt.eventually_ne hf0
    obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨r₀, hr₀, fun n => ?_⟩
    by_contra h
    push Not at h
    exact hball (by simpa [dist_eq_norm] using h) (hzero n)
  -- counting the indices of a finite set against the zero-counting function
  have hcount : ∀ (t : Finset ι) (r : ℝ),
      ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) := by
    intro t r
    set T := t.filter fun n => ‖z n‖ ≤ r with hT
    set D := MeromorphicOn.divisor f (closedBall (0 : ℂ) r) with hD
    have hDnn : ∀ u, 0 ≤ D u := fun u =>
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
    have hfib : ∀ w ∈ T.image z, ((T.filter fun n => z n = w).card : ℤ) ≤ D w := by
      intro w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      have hmem : z n ∈ closedBall (0 : ℂ) r := by
        simpa [hT, dist_eq_norm] using (Finset.mem_filter.mp hn).2
      rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply (fun w _ => hf.analyticAt w) hmem]
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin (z n))
      rw [← hm]
      have hle : (((T.filter fun k => z k = z n).card : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        rw [hm, ← hz (z n)]
        rw [← Set.encard_coe_eq_coe_finsetCard]
        refine (Set.encard_le_encard (t := {k | z k = z n}) ?_).trans_eq ?_
        · intro k hk
          simpa using (Finset.mem_filter.mp hk).2
        · rfl
      have hle' : (T.filter fun k => z k = z n).card ≤ m := by exact_mod_cast hle
      simp only [ENat.map_natCast, WithTop.untop₀_coe]
      exact_mod_cast hle'
    have hsum : (T.card : ℤ) ≤ ∑ w ∈ T.image z, D w := by
      rw [Finset.card_eq_sum_card_image z T]
      push_cast
      exact Finset.sum_le_sum hfib
    have hsupp := D.finiteSupport (isCompact_closedBall (0 : ℂ) r)
    have hfs : (∑ᶠ u, D u) = ∑ u ∈ hsupp.toFinset ∪ T.image z, D u :=
      finsum_eq_sum_of_support_subset _ (by
        intro u hu
        simp only [Finset.coe_union, Set.Finite.coe_toFinset]
        exact Or.inl hu)
    have : (T.card : ℤ) ≤ ∑ᶠ u, D u := by
      rw [hfs]
      exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun u _ _ => hDnn u))
    exact_mod_cast this
  -- `n(r) ≤ L r ^ (ρ + ε / 2)` for `r ≥ r₀`
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set p := ρ + δ with hp
  have hp0 : 0 < p := by positivity
  obtain ⟨K, hK⟩ := (h.isBigO_sum_divisor_closedBall hf hρ hδ0).bound
  rw [eventually_atTop] at hK
  obtain ⟨R1, hR1⟩ := hK
  set R := max R1 r₀ with hR
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ (le_max_right _ _)
  set L := |K| * (1 + R / r₀) ^ p with hL
  have hN : ∀ (t : Finset ι) (r : ℝ), r₀ ≤ r →
      ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤ L * r ^ p := by
    intro t r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
    have h1 : ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤
        ((t.filter fun n => ‖z n‖ ≤ r + R).card : ℝ) := by
      refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, by linarith [hn.2]⟩
    have h2 := hR1 (r + R) (by linarith [le_max_left R1 r₀])
    have hrR : 0 ≤ (r + R) ^ p := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hrR] at h2
    have h3 : r + R ≤ (1 + R / r₀) * r := by
      have : R ≤ R / r₀ * r := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]
        nlinarith
      linarith
    have h4 : (r + R) ^ p ≤ (1 + R / r₀) ^ p * r ^ p := by
      rw [← Real.mul_rpow (by positivity) hr0.le]
      exact Real.rpow_le_rpow (by linarith) h3 hp0.le
    calc ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ)
        ≤ ((t.filter fun n => ‖z n‖ ≤ r + R).card : ℝ) := h1
      _ ≤ _ := hcount t _
      _ ≤ ‖((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 (r + R)) u : ℤ) : ℝ)‖ :=
          Real.le_norm_self _
      _ ≤ K * (r + R) ^ p := h2
      _ ≤ |K| * (r + R) ^ p := by gcongr; exact le_abs_self K
      _ ≤ |K| * ((1 + R / r₀) ^ p * r ^ p) := by gcongr
      _ = L * r ^ p := by rw [hL]; ring
  -- dyadic shells `r₀ 2^k ≤ ‖z n‖ ≤ r₀ 2^(k+1)`
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set kf : ι → ℕ := fun n => ⌊Real.log (‖z n‖ / r₀) / Real.log 2⌋₊ with hkf
  have hx1 : ∀ n, 1 ≤ ‖z n‖ / r₀ := fun n => by rw [le_div_iff₀ hr₀]; linarith [hr₀z n]
  have hexp : ∀ n, ‖z n‖ / r₀ = (2 : ℝ) ^ (Real.log (‖z n‖ / r₀) / Real.log 2) := by
    intro n
    rw [Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ hl2.ne',
      Real.exp_log (by linarith [hx1 n])]
  have hlo : ∀ n, r₀ * (2 : ℝ) ^ (kf n : ℝ) ≤ ‖z n‖ := by
    intro n
    have h := Nat.floor_le (div_nonneg (Real.log_nonneg (hx1 n)) hl2.le)
    have h' : (2 : ℝ) ^ (kf n : ℝ) ≤ ‖z n‖ / r₀ := by
      rw [hexp n]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h
    rw [le_div_iff₀ hr₀] at h'
    linarith
  have hhi : ∀ n, ‖z n‖ ≤ r₀ * (2 : ℝ) ^ ((kf n : ℝ) + 1) := by
    intro n
    have h := Nat.lt_floor_add_one (Real.log (‖z n‖ / r₀) / Real.log 2)
    have h' : ‖z n‖ / r₀ ≤ (2 : ℝ) ^ ((kf n : ℝ) + 1) := by
      rw [hexp n]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h.le
    rw [div_le_iff₀ hr₀] at h'
    linarith
  set q : ℝ := (2 : ℝ) ^ (-δ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set A := L * 2 ^ p * r₀ ^ (-δ) with hA
  have hshell : ∀ (s : Finset ι) (k : ℕ),
      ∑ n ∈ s.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε) ≤ A * q ^ k := by
    intro s k
    have hb0 : 0 < r₀ * (2 : ℝ) ^ (k : ℝ) := by positivity
    have hterm : ∀ n ∈ s.filter (fun n => kf n = k),
        ‖z n‖ ^ (-ρ - ε) ≤ (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      have := hlo n
      rw [hk] at this
      exact Real.rpow_le_rpow_of_nonpos hb0 this (by linarith)
    have hcard : ((s.filter (fun n => kf n = k)).card : ℝ) ≤
        L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p := by
      refine le_trans ?_ (hN s _ ?_)
      · refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
        have hk := (Finset.mem_filter.mp hn).2
        have := hhi n
        rw [hk] at this
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, this⟩
      · have : (1 : ℝ) ≤ 2 ^ ((k : ℝ) + 1) := Real.one_le_rpow one_le_two (by positivity)
        nlinarith
    have hc0 : 0 ≤ (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by positivity
    have e : L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) =
        A * q ^ k := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      rw [Real.mul_rpow hr₀.le (by positivity), Real.mul_rpow hr₀.le (by positivity),
        ← Real.rpow_mul h2, ← Real.rpow_mul h2]
      calc L * (r₀ ^ p * 2 ^ (((k : ℝ) + 1) * p)) * (r₀ ^ (-ρ - ε) * 2 ^ ((k : ℝ) * (-ρ - ε)))
          = L * (r₀ ^ p * r₀ ^ (-ρ - ε)) *
              (2 ^ (((k : ℝ) + 1) * p) * 2 ^ ((k : ℝ) * (-ρ - ε))) := by
            ring
        _ = L * r₀ ^ (p + (-ρ - ε)) * 2 ^ (((k : ℝ) + 1) * p + (k : ℝ) * (-ρ - ε)) := by
            rw [← Real.rpow_add hr₀, ← Real.rpow_add two_pos]
        _ = L * r₀ ^ (-δ) * 2 ^ (p + -δ * (k : ℝ)) := by
            rw [show p + (-ρ - ε) = -δ by rw [hp, hδ]; ring,
              show ((k : ℝ) + 1) * p + (k : ℝ) * (-ρ - ε) = p + -δ * (k : ℝ) by
                rw [hp, hδ]; ring]
        _ = A * q ^ k := by
            rw [Real.rpow_add two_pos, Real.rpow_mul h2, Real.rpow_natCast, hA, hq]
            ring
    calc ∑ n ∈ s.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε)
        ≤ ∑ n ∈ s.filter (fun n => kf n = k), (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) :=
          Finset.sum_le_sum hterm
      _ = ((s.filter (fun n => kf n = k)).card : ℝ) * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
          gcongr
      _ = A * q ^ k := e
  have hA0 : 0 ≤ A := by rw [hA, hL]; positivity
  refine summable_of_sum_le (c := ∑' k, A * q ^ k)
    (fun n => Real.rpow_nonneg (norm_nonneg _) _) ?_
  intro u
  rw [← Finset.sum_fiberwise_of_maps_to (g := kf) (t := u.image kf)
    (fun n hn => Finset.mem_image_of_mem kf hn)]
  calc ∑ k ∈ u.image kf, ∑ n ∈ u.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε)
      ≤ ∑ k ∈ u.image kf, A * q ^ k := Finset.sum_le_sum fun k _ => hshell u k
    _ ≤ ∑' k, A * q ^ k := Summable.sum_le_tsum _ (fun k _ => by positivity)
        ((summable_geometric_of_lt_one hq0 hq1).mul_left A)

end Zeros

end Complex
