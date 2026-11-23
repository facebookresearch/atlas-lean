/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import MathlibExt.Analysis.Normed.Lp.SchauderBasis

@[expose] public section

/-!
# Relative compactness in `ℓ^p (ℕ, 𝕜)`: the Riesz–Fréchet–Kolmogorov criterion

A set `K` in `ℓ^p (ℕ, 𝕜)`, `1 ≤ p < ∞`, is totally bounded (equivalently,
its closure is compact) if and only if it is bounded and its tails vanish
uniformly: for every `ε > 0` there is `N` such that every `x ∈ K` is within
`ε` of its truncation to the first `N` coordinates. This is the sequence-space
form of the Riesz–Fréchet–Kolmogorov compactness criterion.

This is the companion in the `v1` Functional Analysis book of the `L^p`-norm
material (April 6, 2021 section) and of the compactness / sequential-compactness
material (the book states that a subset of a metric space is compact if and
only if it is sequentially compact). The book proves neither the `ℓ^p`
criterion nor any of its consequences here; Mathlib provides the `ℓ^p` API
(`lp.norm_mono`, `lp.hasSum_single`) and the metric-space characterisation
`isCompact_iff_totallyBounded_isComplete`, but no compactness criterion for
`ℓ^p` sets.

The statement is false for `p = ∞`: the singleton containing the constant
sequence `1` is compact in `ℓ^∞`, but its tails do not vanish. The proofs
of the compactness criteria therefore assume `p ≠ ⊤`. The coordinate
extension `lpTrunc` is defined for every `p`, including `∞`. For finite
`p ≥ 1`, it agrees with the existing bundled Schauder-basis projection;
its contraction and convergence below use that canonical API.

## Main declarations

* `lpTrunc` : truncation of an `ℓ^p` sequence to its first `N` coordinates.
* `lpLift` : the lift of a finitely supported coordinate function to `ℓ^p`.
* `lpExtend` : the extension of a `Fin N → 𝕜` coordinate vector by `0`.
* `UniformTailVanishing` : the uniform tail-vanishing condition on a set.
* `totallyBounded_iff_bounded_and_uniformTailVanishing` : the criterion.
* `isCompact_iff_isComplete_and_bounded_and_uniformTailVanishing` : compact form.
* `isCompact_closure_iff_bounded_and_uniformTailVanishing` : relative-compact form.
-/

namespace MathlibExt.Analysis.Normed.Lp.Compactness

open scoped ENNReal Topology
open Filter Metric Set Finset
open MathlibExt.Analysis.Normed.Lp.SchauderBasis

section Defs

variable {𝕜 : Type*} [NormedAddCommGroup 𝕜] {p : ℝ≥0∞}

/-- The restriction of an `ℓ^p` sequence to its first `N` coordinates. -/
def lpRestrict (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) : Fin N → 𝕜 :=
  fun i => x i

/-- The restriction acts coordinatewise. -/
@[simp]
theorem lpRestrict_apply (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) (i : Fin N) :
    lpRestrict N x i = x i :=
  rfl

/-- The extension of a coordinate vector on `Fin N` by `0` to a total
coordinate function on `ℕ`. -/
def lpExtend (N : ℕ) (z : Fin N → 𝕜) : ℕ → 𝕜 :=
  fun i => if h : i < N then z ⟨i, h⟩ else 0

/-- The extension acts coordinatewise. -/
theorem lpExtend_apply (N : ℕ) (z : Fin N → 𝕜) (j : ℕ) :
    lpExtend N z j = if h : j < N then z ⟨j, h⟩ else 0 :=
  rfl

end Defs

section Basic

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

/-- The lift of a coordinate function on `ℕ` to an `ℓ^p` sequence, keeping
only its first `N` coordinates. -/
noncomputable def lpLift (p : ℝ≥0∞) (N : ℕ) (y : ℕ → 𝕜) :
    lp (fun _ : ℕ => 𝕜) p :=
  ∑ i ∈ Finset.range N, lp.single (E := fun _ : ℕ => 𝕜) p i (y i)

/-- The all-`p` coordinate extension of finite truncation to the first `N`
coordinates, also defined at `p = ∞`. For finite `p ≥ 1`,
`lpTrunc_eq_lpSchauderBasis_proj` identifies it with the canonical
continuous linear Schauder projection. -/
noncomputable def lpTrunc (p : ℝ≥0∞) (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    lp (fun _ : ℕ => 𝕜) p :=
  lpLift p N (fun i => x i)

/-- The lift acts coordinatewise. -/
theorem lpLift_apply (N : ℕ) (y : ℕ → 𝕜) (j : ℕ) :
    lpLift p N y j = if j < N then y j else 0 := by
  simp only [lpLift, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  by_cases hj : j < N <;> simp [hj, Finset.mem_range]

/-- Truncation acts coordinatewise. -/
theorem lpTrunc_apply (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) (j : ℕ) :
    lpTrunc p N x j = if j < N then x j else 0 :=
  lpLift_apply N (fun i => x i) j

theorem lpLift_zero (N : ℕ) : lpLift p N (0 : ℕ → 𝕜) = 0 := by
  ext j
  simp only [lpLift_apply, Pi.zero_apply, lp.coeFn_zero]
  split_ifs <;> simp

theorem lpLift_sub (N : ℕ) (y z : ℕ → 𝕜) :
    lpLift p N (y - z) = lpLift p N y - lpLift p N z := by
  ext j
  simp only [lp.coeFn_sub, Pi.sub_apply, lpLift_apply]
  split_ifs with hj <;> simp

theorem lpLift_smul (N : ℕ) (c : 𝕜) (y : ℕ → 𝕜) :
    lpLift p N (c • y) = c • lpLift p N y := by
  ext j
  simp only [lp.coeFn_smul, Pi.smul_apply, lpLift_apply]
  split_ifs with hj <;> simp

theorem lpTrunc_zero (N : ℕ) : lpTrunc p N (0 : lp (fun _ : ℕ => 𝕜) p) = 0 := by
  ext j
  simp [lpTrunc_apply]

theorem lpTrunc_sub (N : ℕ) (x y : lp (fun _ : ℕ => 𝕜) p) :
    lpTrunc p N (x - y) = lpTrunc p N x - lpTrunc p N y := by
  unfold lpTrunc
  rw [show (fun i => (x - y) i) = (fun i => x i) - (fun i => y i) from
    funext fun i => Pi.sub_apply x y i]
  rw [lpLift_sub]

theorem lpTrunc_smul (N : ℕ) (c : 𝕜) (x : lp (fun _ : ℕ => 𝕜) p) :
    lpTrunc p N (c • x) = c • lpTrunc p N x := by
  unfold lpTrunc
  rw [show (fun i => (c • x) i) = c • (fun i => x i) from
    funext fun i => Pi.smul_apply c x i]
  rw [lpLift_smul]

end Basic

section Norm

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For finite `p ≥ 1`, coordinate truncation is the canonical bundled
Schauder-basis projection. -/
theorem lpTrunc_eq_lpSchauderBasis_proj (hp : p ≠ ⊤) (N : ℕ)
    (x : lp (fun _ : ℕ => 𝕜) p) :
    lpTrunc p N x = (lpSchauderBasis (𝕜 := 𝕜) hp).proj N x := by
  rw [lpSchauderBasis_proj_apply]
  rfl

/-- Truncation is a contraction. -/
theorem norm_lpTrunc_le (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    ‖lpTrunc p N x‖ ≤ ‖x‖ := by
  by_cases hp : p = ⊤
  · subst p
    refine lp.norm_mono (by simp : (⊤ : ℝ≥0∞) ≠ 0) fun i => ?_
    by_cases hi : i < N
    · rw [lpTrunc_apply, ite_eq_left hi]
    · rw [lpTrunc_apply, ite_eq_right hi, norm_zero]
      exact norm_nonneg _
  · rw [lpTrunc_eq_lpSchauderBasis_proj hp]
    exact norm_lpSchauderBasis_classical_proj_apply_le hp N x

/-- The tail of a vector is no larger than the vector itself. -/
theorem norm_sub_lpTrunc_le (N : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    ‖x - lpTrunc p N x‖ ≤ ‖x‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  refine lp.norm_mono hp0 fun i => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lpTrunc_apply]
  by_cases hi : i < N
  · rw [ite_eq_left hi, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [ite_eq_right hi, sub_zero]

/-- Tails shrink as the truncation length grows. -/
theorem norm_sub_lpTrunc_mono {N M : ℕ} (h : N ≤ M) (x : lp (fun _ : ℕ => 𝕜) p) :
    ‖x - lpTrunc p M x‖ ≤ ‖x - lpTrunc p N x‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  refine lp.norm_mono hp0 fun i => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lpTrunc_apply, lp.coeFn_sub, Pi.sub_apply,
    lpTrunc_apply]
  by_cases hiM : i < M
  · rw [ite_eq_left hiM, sub_self, norm_zero]
    exact norm_nonneg _
  · by_cases hiN : i < N
    · exact absurd (lt_of_lt_of_le hiN h) hiM
    · rw [ite_eq_right hiM, ite_eq_right hiN, sub_zero]

/-- The target `ℓ^p` norm of the finite lift is bounded by
`N ^ (1 / p)` times the supremum norm of its first `N` coordinates.
The norm on the source Pi type `Fin N → 𝕜` is the supremum norm. -/
theorem norm_lpLift_le (hp : p ≠ ⊤) (N : ℕ) (y : ℕ → 𝕜) :
    ‖lpLift p N y‖ ≤ (N : ℝ) ^ (1 / p.toReal) * ‖fun i : Fin N => y i‖ := by
  have hp0 : 0 < p := zero_lt_one.trans_le Fact.out
  have hpq : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
  refine lp.norm_le_of_tsum_le hpq (by positivity) ?_
  have hsupp : ∀ i ∉ Finset.range N, ‖lpLift p N y i‖ ^ p.toReal = 0 := by
    intro i hi
    rw [Finset.mem_range, not_lt] at hi
    rw [lpLift_apply, ite_eq_right (by omega : ¬ i < N), norm_zero,
      Real.zero_rpow hpq.ne']
  have hRHS : ((N : ℝ) ^ (1 / p.toReal) * ‖fun i : Fin N => y i‖) ^ p.toReal
      = (N : ℝ) * ‖fun i : Fin N => y i‖ ^ p.toReal := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg N),
      div_mul_cancel₀ 1 hpq.ne', Real.rpow_one]
  rw [tsum_eq_sum hsupp, hRHS]
  calc ∑ i ∈ Finset.range N, ‖lpLift p N y i‖ ^ p.toReal
      ≤ (Finset.range N).card • ‖fun i : Fin N => y i‖ ^ p.toReal := by
        refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
        rw [lpLift_apply, ite_eq_left (Finset.mem_range.mp hi)]
        exact Real.rpow_le_rpow (norm_nonneg _)
          (norm_le_pi_norm (fun i : Fin N => y i) ⟨i, Finset.mem_range.mp hi⟩) hpq.le
    _ = (N : ℝ) * ‖fun i : Fin N => y i‖ ^ p.toReal := by
        rw [Finset.card_range, nsmul_eq_mul]

/-- The truncations of an `ℓ^p` vector converge to the vector. -/
theorem tendsto_lpTrunc (hp : p ≠ ⊤) (x : lp (fun _ : ℕ => 𝕜) p) :
    Tendsto (fun N => lpTrunc p N x) atTop (𝓝 x) := by
  simpa only [lpTrunc_eq_lpSchauderBasis_proj hp] using
    (lpSchauderBasis (𝕜 := 𝕜) hp).tendsto_proj x

/-- The tail of a single vector can be made arbitrarily small. -/
theorem exists_norm_sub_lpTrunc_lt (hp : p ≠ ⊤) (x : lp (fun _ : ℕ => 𝕜) p)
    {ε : ℝ} (hε : 0 < ε) : ∃ N, ‖x - lpTrunc p N x‖ < ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (tendsto_lpTrunc hp x)) ε hε
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  rw [dist_eq_norm, norm_sub_rev] at h
  exact h

/-- The tails of the elements of a set `K` vanish uniformly: for every
`ε > 0` there is `N` such that every `x ∈ K` is within `ε` of its truncation
to the first `N` coordinates. -/
def UniformTailVanishing (p : ℝ≥0∞) (K : Set (lp (fun _ : ℕ => 𝕜) p)) : Prop :=
  ∀ ε > 0, ∃ N, ∀ x ∈ K, ‖x - lpTrunc p N x‖ < ε

/-- The Riesz–Fréchet–Kolmogorov criterion for `ℓ^p (ℕ, 𝕜)`, `1 ≤ p < ∞`:
a set is totally bounded if and only if it is bounded and its tails vanish
uniformly. -/
theorem totallyBounded_iff_bounded_and_uniformTailVanishing (hp : p ≠ ⊤)
    {K : Set (lp (fun _ : ℕ => 𝕜) p)} :
    TotallyBounded K ↔ Bornology.IsBounded K ∧ UniformTailVanishing p K := by
  constructor
  · intro hTB
    refine ⟨hTB.isBounded, ?_⟩
    intro ε hε
    classical
    obtain ⟨t, htK, htfin, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded hTB (ε / 4) (by linarith)
    set T := htfin.toFinset with hTdef
    have hmem : ∀ y, y ∈ T ↔ y ∈ t := fun y => Set.Finite.mem_toFinset htfin
    have hN : ∃ N, ∀ y ∈ T, ‖y - lpTrunc p N y‖ < ε / 4 := by
      choose f hf using
        (fun y (hy : y ∈ T) => exists_norm_sub_lpTrunc_lt hp y (by linarith : (0:ℝ) < ε / 4))
      refine ⟨T.sup (fun y => if hy : y ∈ T then f y hy else 0), fun y hy => ?_⟩
      have hle : (if hy : y ∈ T then f y hy else 0) ≤
          T.sup (fun y => if hy : y ∈ T then f y hy else 0) :=
        Finset.le_sup (f := fun y => if hy : y ∈ T then f y hy else 0) hy
      rw [dite_eq_left hy] at hle
      exact lt_of_le_of_lt (norm_sub_lpTrunc_mono hle y) (hf y hy)
    obtain ⟨N, hN⟩ := hN
    refine ⟨N, fun x hx => ?_⟩
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hytT : y ∈ T := (hmem y).mpr hyt
    rw [Metric.mem_ball] at hxy
    calc ‖x - lpTrunc p N x‖
        = ‖((x - y) - lpTrunc p N (x - y)) + (y - lpTrunc p N y)‖ := by
          rw [lpTrunc_sub]
          congr 1
          abel
      _ ≤ ‖(x - y) - lpTrunc p N (x - y)‖ + ‖y - lpTrunc p N y‖ := norm_add_le _ _
      _ ≤ ‖x - y‖ + ε / 4 :=
          add_le_add (norm_sub_lpTrunc_le N (x - y)) (le_of_lt (hN y hytT))
      _ < ε / 4 + ε / 4 := by
          have hxy' : ‖x - y‖ < ε / 4 := by rwa [dist_eq_norm] at hxy
          linarith
      _ = ε / 2 := by ring
      _ < ε := by linarith
  · rintro ⟨hBounded, htail⟩
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hBounded
    rw [Metric.totallyBounded_iff]
    intro ε hε
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨∅, Set.finite_empty, by simp⟩
    obtain ⟨x₀, hx₀⟩ := hKne
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ hx₀)
    obtain ⟨N, hN⟩ := htail (ε / 2) (half_pos hε)
    set M : ℝ := (N : ℝ) ^ (1 / p.toReal) with hM
    have hM0 : 0 ≤ M := by positivity
    set δ : ℝ := ε / (2 * (M + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hProper : ProperSpace (Fin N → 𝕜) :=
      FiniteDimensional.proper_rclike 𝕜 (Fin N → 𝕜)
    have hsub : (fun x : lp (fun _ : ℕ => 𝕜) p => lpRestrict N x) '' K
        ⊆ Metric.closedBall (0 : Fin N → 𝕜) C := by
      rintro z ⟨x, hxK, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg hC0]
      intro i
      simp only [lpRestrict_apply]
      exact (lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' x i).trans
        (hC x hxK)
    have hTBφ : TotallyBounded
        ((fun x : lp (fun _ : ℕ => 𝕜) p => lpRestrict N x) '' K) :=
      (isCompact_closedBall (0 : Fin N → 𝕜) C).totallyBounded.subset hsub
    obtain ⟨t₀, ht₀φ, ht₀fin, hcoverφ⟩ :=
      Metric.finite_approx_of_totallyBounded hTBφ δ hδ
    have hchoose : ∀ z, ∃ x, z ∈ t₀ → x ∈ K ∧ lpRestrict N x = z := by
      intro z
      by_cases hz : z ∈ t₀
      · obtain ⟨x, hxK, hxz⟩ := ht₀φ hz
        exact ⟨x, fun _ => ⟨hxK, hxz⟩⟩
      · exact ⟨0, fun h => absurd h hz⟩
    choose g hg using hchoose
    refine ⟨(fun z => lpTrunc p N (g z)) '' t₀, ht₀fin.image _, fun x hxK => ?_⟩
    have hxφ : lpRestrict N x ∈
        (fun x : lp (fun _ : ℕ => 𝕜) p => lpRestrict N x) '' K :=
      ⟨x, hxK, rfl⟩
    obtain ⟨z, hzt₀, hxz⟩ := Set.mem_iUnion₂.mp (hcoverφ hxφ)
    rw [Metric.mem_ball, dist_eq_norm] at hxz
    have hgz : lpTrunc p N (g z) = lpLift p N (lpExtend N z) := by
      simp only [lpTrunc, lpLift]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [lpExtend_apply, dite_eq_left (Finset.mem_range.mp hi)]
      congr 1
      exact congrFun (hg z hzt₀).2 ⟨i, Finset.mem_range.mp hi⟩
    refine Set.mem_iUnion₂.mpr ⟨lpTrunc p N (g z), ⟨z, hzt₀, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hdecomp : x - lpTrunc p N (g z)
        = (x - lpTrunc p N x) + lpLift p N ((fun i => x i) - lpExtend N z) := by
      rw [hgz, lpLift_sub]
      show x - lpLift p N (lpExtend N z)
        = (x - lpLift p N (fun i => x i))
          + (lpLift p N (fun i => x i) - lpLift p N (lpExtend N z))
      abel
    rw [hdecomp]
    calc ‖(x - lpTrunc p N x) + lpLift p N ((fun i => x i) - lpExtend N z)‖
        ≤ ‖x - lpTrunc p N x‖ + ‖lpLift p N ((fun i => x i) - lpExtend N z)‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + M * ‖lpRestrict N x - z‖ := by
          refine add_le_add (le_of_lt (hN x hxK)) ?_
          have hnorm := norm_lpLift_le hp N ((fun i => x i) - lpExtend N z)
          have hfin : (fun i : Fin N => ((fun i => x i) - lpExtend N z) i)
              = lpRestrict N x - z := by
            ext i
            simp only [Pi.sub_apply, lpRestrict_apply, lpExtend_apply,
              dite_eq_left i.2]
          rwa [hfin] at hnorm
      _ ≤ ε / 2 + M * δ :=
          add_le_add (le_refl (ε / 2))
            (mul_le_mul_of_nonneg_left (le_of_lt hxz) hM0)
      _ < ε := by
          have hMδ : M * δ < ε / 2 := by
            rw [hδdef, ← mul_div_assoc,
              div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (M + 1))]
            rw [show (ε / 2) * (2 * (M + 1)) = ε * (M + 1) by ring]
            calc M * ε = ε * M := mul_comm _ _
              _ < ε * (M + 1) := mul_lt_mul_of_pos_left (lt_add_one M) hε
          linarith

/-- Compact form of the Riesz–Fréchet–Kolmogorov criterion. -/
theorem isCompact_iff_isComplete_and_bounded_and_uniformTailVanishing (hp : p ≠ ⊤)
    {K : Set (lp (fun _ : ℕ => 𝕜) p)} :
    IsCompact K ↔ IsComplete K ∧ Bornology.IsBounded K
      ∧ UniformTailVanishing p K := by
  rw [isCompact_iff_totallyBounded_isComplete,
    totallyBounded_iff_bounded_and_uniformTailVanishing hp]
  tauto

/-- Relative-compact form of the Riesz–Fréchet–Kolmogorov criterion. -/
theorem isCompact_closure_iff_bounded_and_uniformTailVanishing (hp : p ≠ ⊤)
    {K : Set (lp (fun _ : ℕ => 𝕜) p)} :
    IsCompact (closure K) ↔ Bornology.IsBounded K ∧ UniformTailVanishing p K := by
  rw [isCompact_iff_totallyBounded_isComplete]
  constructor
  · rintro ⟨hTB, -⟩
    rw [totallyBounded_closure] at hTB
    exact (totallyBounded_iff_bounded_and_uniformTailVanishing hp).mp hTB
  · rintro ⟨hB, hT⟩
    refine ⟨totallyBounded_closure.mpr
      ((totallyBounded_iff_bounded_and_uniformTailVanishing hp).mpr ⟨hB, hT⟩),
      isClosed_closure.isComplete⟩

end Norm

end MathlibExt.Analysis.Normed.Lp.Compactness
