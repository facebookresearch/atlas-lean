/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.PSeries

@[expose] public section

namespace MathlibExt.Analysis.WirsingConstant

open Real Filter Topology

/-!
# The Gauss--Kuzmin--Wirsing operator and the Wirsing constant

The transfer operator of the Gauss map, its defining series, the Gauss
density eigenfunction at eigenvalue `1` (proved by telescoping), and the
Wirsing constant as the totalized supremum of subdominant absolute
eigenvalues over holomorphic eigenfunctions on the Mayer disk.

Source: Optimization Problems, record 83a, "The Wirsing Constant",
frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/83a.md` SHA-256
`2d4fe7a9157fdc5180cdf590b203fad49ff77198025c6be07d60607482f54db6`.

The source's spectral theorem (a simple dominant eigenvalue `1`, a
negative subdominant eigenvalue attaining the constant, and the rate of
convergence of the Gauss--Kuzmin distribution) is not asserted. The
function space matters: over all *continuous* eigenfunctions the
operator has additional eigenvalues (for instance `1/3`, via
inversion-lift constructions), so the continuous-space supremum is not
the Wirsing constant and does not satisfy the catalogue upper bound.
Following Mayer--Roepstorff, `wirsingConstant` is therefore defined over
eigenfunctions holomorphic on the disk `{z : |z - 1| < 3 / 2}` in `ℂ`,
the space on which the source's spectral identification holds; the
continuous model is retained separately at `IsEigenvalue`.
-/

/-- The Gauss--Kuzmin--Wirsing operator, pointwise on arbitrary real
functions by its defining series `∑_{k≥1} (x+k)^{-2} f(1/(x+k))`
(indexed here by `k + 1`). The series converges whenever `f` is bounded
on `[0, 1]`, as proved below; off that domain `∑'` is the totalized sum. -/
noncomputable def gkwTerm (f : ℝ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  (1 / (x + (k + 1 : ℝ)) ^ 2) * f (1 / (x + (k + 1 : ℝ)))

noncomputable def gkwOperator (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, gkwTerm f x k

theorem summable_gkwTerm {f : ℝ → ℝ} {M x : ℝ} (hx : x ∈ Set.Icc 0 1)
    (hf : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ M) :
    Summable (gkwTerm f x) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf 0 (by norm_num))
  have hsum : Summable fun k : ℕ => M * (1 / ((k + 1 : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h2 := (summable_nat_add_iff 1).mpr h
    have h3 : Summable fun k : ℕ => (1 / ((k + 1 : ℝ)) ^ 2) := by
      simpa [Nat.cast_add, Nat.cast_one] using h2
    exact h3.mul_left M
  refine Summable.of_norm_bounded hsum fun k => ?_
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 k
  have hxk : (k + 1 : ℝ) ≤ x + (k + 1 : ℝ) := by linarith [hx.1]
  have hpos : (0 : ℝ) < x + (k + 1 : ℝ) := by linarith
  have hmem : 1 / (x + (k + 1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hpos]
      linarith
  rw [gkwTerm, Real.norm_eq_abs, abs_mul]
  calc |1 / (x + (k + 1 : ℝ)) ^ 2| * |f (1 / (x + (k + 1 : ℝ)))|
      ≤ (1 / ((k + 1 : ℝ)) ^ 2) * M := by
        have h1 : |1 / (x + (k + 1 : ℝ)) ^ 2| ≤ 1 / ((k + 1 : ℝ)) ^ 2 := by
          rw [abs_of_nonneg (by positivity)]
          exact one_div_le_one_div_of_le (pow_pos (by linarith) 2)
            (pow_le_pow_left₀ (by linarith) hxk 2)
        exact mul_le_mul h1 (hf _ hmem) (abs_nonneg _) (by positivity)
    _ = M * (1 / ((k + 1 : ℝ)) ^ 2) := by ring

/-- An eigenvalue of the GKW operator, with eigenfunction continuous and
nonzero on `[0, 1]` (hence bounded there, recorded explicitly). This
continuous model is *not* the source's spectral space: it admits
eigenvalues that the holomorphic theory excludes (for example `1/3`,
from eigenfunction lifts under inversion), so it is kept only as a
pointwise model exhibiting the dominant eigenvalue `1` below. The
Wirsing constant itself is defined over holomorphic eigenfunctions at
`IsHolomorphicEigenvalue`. -/
def IsEigenvalue (lam : ℝ) : Prop :=
  ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧
    (∃ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 0) ∧
    (∃ M : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ M) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, gkwOperator f x = lam * f x

/-- `1` is an eigenvalue, with the Gauss density `x ↦ 1 / (1 + x)` as
eigenfunction: the defining series telescopes. -/
theorem isEigenvalue_one : IsEigenvalue 1 := by
  have hbdd : ∀ y ∈ Set.Icc (0 : ℝ) 1, |(fun x => 1 / (1 + x)) y| ≤ 1 := by
    intro y hy
    have hy0 : (0:ℝ) ≤ y := hy.1
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by linarith)]
    linarith
  refine ⟨fun x => 1 / (1 + x), ?_, ⟨0, by norm_num, by norm_num⟩, ⟨1, hbdd⟩, ?_⟩
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuousOn_id)
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    show (1:ℝ) + x ≠ 0
    exact ne_of_gt (by linarith)
  · intro x hx
    have hterm : ∀ k : ℕ, gkwTerm (fun x => 1 / (1 + x)) x k =
        (1 / (x + (k + 1 : ℝ))) - (1 / (x + (k + 2 : ℝ))) := by
      intro k
      set a : ℝ := x + (k + 1 : ℝ) with ha
      have hk1 : (1:ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
      have ha0 : a ≠ 0 := ne_of_gt (by rw [ha]; linarith [hx.1])
      have ha1 : a + 1 ≠ 0 := ne_of_gt (by rw [ha]; linarith [hx.1])
      have h2 : x + (k + 2 : ℝ) = a + 1 := by rw [ha]; ring
      rw [gkwTerm, h2, ← ha]
      field_simp
      ring
    have hsumm : Summable (gkwTerm (fun x => 1 / (1 + x)) x) :=
      summable_gkwTerm hx hbdd
    have htend : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        gkwTerm (fun x => 1 / (1 + x)) x k) atTop (nhds (1 / (1 + x))) := by
      have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N,
          gkwTerm (fun x => 1 / (1 + x)) x k =
          (1 / (x + 1)) - (1 / (x + (N + 1 : ℝ))) := by
        intro N
        have h := Finset.sum_range_sub (fun k : ℕ => (1:ℝ) / (x + (k + 1 : ℝ))) N
        have hterm' : ∀ k ∈ Finset.range N,
            gkwTerm (fun x => 1 / (1 + x)) x k =
              -((1 / (x + ((k + 1 : ℕ) + 1 : ℝ))) - 1 / (x + (k + 1 : ℝ))) := by
          intro k _
          rw [hterm k]
          push_cast
          ring
        rw [Finset.sum_congr rfl hterm', Finset.sum_neg_distrib, h, neg_sub]
        norm_num
      rw [tendsto_congr' (Eventually.of_forall hpart)]
      have ht0 : Tendsto (fun N : ℕ => (1:ℝ) / (x + (N + 1 : ℝ))) atTop (nhds 0) := by
        have hcast : Tendsto (fun N : ℕ => (((N : ℝ) + 1) + x)) atTop atTop :=
          Filter.tendsto_atTop_add_const_right _ x
            (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        have h2 := tendsto_inv_atTop_zero.comp hcast
        refine h2.congr' ?_
        filter_upwards with N
        simp only [Function.comp_apply, one_div]
        rw [add_comm]
      have h3 : Tendsto (fun N : ℕ => (1 / (x + 1)) - 1 / (x + (N + 1 : ℝ)))
          atTop (nhds (1 / (x + 1) - 0)) :=
        tendsto_const_nhds.sub ht0
      simpa [add_comm x 1] using h3
    have htsum : ∑' k : ℕ, gkwTerm (fun x => 1 / (1 + x)) x k = 1 / (1 + x) :=
      tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat htend
    rw [gkwOperator, htsum, one_mul]

/-- The Gauss--Kuzmin--Wirsing operator on complex functions, by the same
defining series. -/
noncomputable def gkwTermHol (f : ℂ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  (1 / (z + (k + 1 : ℂ)) ^ 2) * f (1 / (z + (k + 1 : ℂ)))

noncomputable def gkwOperatorHol (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, gkwTermHol f z k

/-- An eigenvalue of the GKW operator with an eigenfunction holomorphic
on the Mayer disk `{z : |z - 1| < 3 / 2}` (and nonzero somewhere on it):
the function space of Mayer--Roepstorff, on which the operator's
spectrum below the dominant eigenvalue `1` is the source's spectral
data. The eigen-equation is required on the disk; the operator series is
the totalized one of `gkwOperatorHol`. -/
def IsHolomorphicEigenvalue (lam : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 1 (3 / 2)) ∧
    (∃ z ∈ Metric.ball (1 : ℂ) (3 / 2 : ℝ), f z ≠ 0) ∧
    ∀ z ∈ Metric.ball (1 : ℂ) (3 / 2 : ℝ), gkwOperatorHol f z = lam * f z

/-- The Wirsing constant: the largest absolute value of a holomorphic
eigenvalue other than the dominant eigenvalue `1`, totalized by real
`sSup`. The source's spectral theorem (that this is attained at the
negative eigenvalue `λ₂`, and that no other eigenvalue of the
holomorphic theory lies between it and `1`) is not asserted here; the
Mayer--Roepstorff interval for this constant is recorded as proof
requests in `WantedExt/Analysis/WirsingConstantWanted.lean`. -/
noncomputable def wirsingConstant : ℝ :=
  sSup { r : ℝ | ∃ lam : ℂ, IsHolomorphicEigenvalue lam ∧ lam ≠ 1 ∧
    r = ‖lam‖ }

end MathlibExt.Analysis.WirsingConstant
