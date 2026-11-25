/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# McCann's condition for displacement convexity of internal energies

For an internal energy `U(ρ) = ∫ A(ρ(x)) dx` of a probability density on `ℝ^d`, R. J. McCann
(*A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179) isolates the
condition (A1):

`λ ↦ λ^d A(λ^{-d})` is convex and nonincreasing on `(0, ∞)`, and `A(0) = 0`.

The function `λ ↦ λ^d A(λ^{-d})` is the energy of a uniform gas of unit mass dilated by the factor
`λ`. McCann's Theorem 2.2 shows that (A1) makes `U` convex along displacement interpolation (the
geodesics of the quadratic Wasserstein distance); that theorem is not formalized here. This file
formalizes condition (A1) itself and checks it on the two families that drive the Wasserstein
gradient-flow theory of F. Otto:

* the entropy `A(s) = s log s`, whose gradient flow is the heat (Fokker–Planck) equation: (A1)
  holds in every dimension, the dilation profile being `-d log λ`;
* the porous-medium energies `A(s) = s^m / (m - 1)`, whose Wasserstein gradient flow is
  `∂ₜρ = Δ ρ^m`: (A1)
  holds for every `m > 1`, and for `0 < m < 1` it holds exactly when `m ≥ 1 - 1/d`, the
  threshold that appears in McCann's paper as the Brunn–Minkowski case `A(s) = -s^{1 - 1/d}`.

## Main results

* `McCannCondition`: condition (A1).
* `dilationProfile_entropy`, `mcCannCondition_entropy`.
* `dilationProfile_porousMedium`, `mcCannCondition_porousMedium_of_one_lt`,
  `mcCannCondition_porousMedium_iff`.

## References

* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179,
  condition (A1) and Theorem 2.2.
-/

@[expose] public section

open Set Real

namespace MathlibExt.Analysis.Convex.McCann

/-- **Dilation profile of an internal energy.** For `A : ℝ → ℝ` and a dimension `d`, the function
`λ ↦ λ^d A(λ^{-d})`: the internal energy `∫ A(ρ)` of a unit mass spread uniformly over a region of
volume `λ^d` times its original unit volume (R. J. McCann, *A convexity principle for interacting
gases*, Adv. Math. 128 (1997), 153–179, the function in condition (A1)). -/
noncomputable def dilationProfile (d : ℕ) (A : ℝ → ℝ) (lam : ℝ) : ℝ :=
  lam ^ d * A (lam ^ d)⁻¹

/-- **McCann's condition (A1).** The internal-energy density `A : ℝ → ℝ` satisfies McCann's
condition in dimension `d` if `A(0) = 0` and `λ ↦ λ^d A(λ^{-d})` is convex and nonincreasing on
`(0, ∞)` (R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997),
153–179, condition (A1); his Theorem 2.2 shows that it makes `ρ ↦ ∫ A(ρ)` convex along
displacement interpolation of probability densities on `ℝ^d`). McCann allows `A` to take the
value `+∞`; here `A` is real-valued. -/
def McCannCondition (d : ℕ) (A : ℝ → ℝ) : Prop :=
  A 0 = 0 ∧ ConvexOn ℝ (Ioi 0) (dilationProfile d A) ∧ AntitoneOn (dilationProfile d A) (Ioi 0)

/-- **Dilation profile of the entropy.** For `A(s) = s log s`, the dilation profile is
`λ^d A(λ^{-d}) = -d log λ` for `λ > 0`. -/
theorem dilationProfile_entropy (d : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    dilationProfile d (fun s => s * log s) lam = -(d * log lam) := by
  have hpos : 0 < lam ^ d := pow_pos hlam d
  simp only [dilationProfile, log_inv, log_pow]
  field_simp

/-- **The entropy satisfies McCann's condition.** In every dimension `d`, `A(s) = s log s`
satisfies condition (A1) of R. J. McCann (Adv. Math. 128 (1997), 153–179): `A(0) = 0` and the
dilation profile `-d log λ` is convex and nonincreasing on `(0, ∞)`. With McCann's Theorem 2.2
this is the displacement convexity of the entropy `∫ ρ log ρ`, the functional whose Wasserstein
gradient flow is the heat equation (Jordan, Kinderlehrer and Otto, 1998). -/
theorem mcCannCondition_entropy (d : ℕ) : McCannCondition d (fun s => s * log s) := by
  refine ⟨by simp, ?_, ?_⟩
  · have := (strictConcaveOn_log_Ioi.concaveOn.smul (Nat.cast_nonneg (α := ℝ) d)).neg
    refine this.congr fun lam hlam => ?_
    rw [dilationProfile_entropy d hlam]
    simp only [Pi.neg_apply, smul_eq_mul]
  · intro x hx y hy hxy
    rw [dilationProfile_entropy d hx, dilationProfile_entropy d hy]
    have := log_le_log hx hxy
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith

/-- **Dilation profile of a porous-medium energy.** For `A(s) = s^m / (m - 1)` with `m > 0`, the
dilation profile is `λ^d A(λ^{-d}) = λ^{d(1 - m)} / (m - 1)` for `λ > 0`. -/
theorem dilationProfile_porousMedium (d : ℕ) {m : ℝ} {lam : ℝ} (hlam : 0 < lam) :
    dilationProfile d (fun s => s ^ m / (m - 1)) lam = lam ^ ((d : ℝ) * (1 - m)) / (m - 1) := by
  have hpos : 0 < lam ^ d := pow_pos hlam d
  simp only [dilationProfile]
  rw [inv_rpow hpos.le, ← rpow_natCast, ← rpow_mul hlam.le, mul_div_assoc', ← div_eq_mul_inv,
    ← rpow_sub hlam]
  congr 2
  ring

/-- **Convexity of negative powers.** For `a ≥ 0`, `x ↦ x^(-a)` is convex on `(0, ∞)`: it is
`exp ∘ (-a log)`, an increasing convex function of a convex function. -/
theorem convexOn_rpow_neg {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-a)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy α β hα hβ hαβ => ?_⟩
  have hxy : α • x + β • y ∈ Ioi (0 : ℝ) := convex_Ioi 0 hx hy hα hβ hαβ
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hα hβ hαβ
  simp only [smul_eq_mul, mem_Ioi] at hx hy hxy hlog ⊢
  rw [rpow_def_of_pos hx, rpow_def_of_pos hy, rpow_def_of_pos hxy]
  calc exp (log (α * x + β * y) * -a)
      ≤ exp (α * (log x * -a) + β * (log y * -a)) := by
        apply exp_le_exp.mpr; nlinarith
    _ ≤ α * exp (log x * -a) + β * exp (log y * -a) := by
        simpa [smul_eq_mul] using convexOn_exp.2 (mem_univ (log x * -a))
          (mem_univ (log y * -a)) hα hβ hαβ

/-- **Porous-medium energies with `m > 1` satisfy McCann's condition.** For every dimension `d`
and every `m > 1`, `A(s) = s^m / (m - 1)` satisfies condition (A1) of R. J. McCann (Adv. Math.
128 (1997), 153–179): its dilation profile `λ^{-d(m - 1)} / (m - 1)` is convex and nonincreasing.
McCann uses `A(s) = s^q`, `q > 1`, a positive multiple, in the proof of his Theorem 2.3. -/
theorem mcCannCondition_porousMedium_of_one_lt (d : ℕ) {m : ℝ} (hm : 1 < m) :
    McCannCondition d (fun s => s ^ m / (m - 1)) := by
  have hm1 : 0 < m - 1 := by linarith
  have ha : 0 ≤ (d : ℝ) * (m - 1) := by positivity
  have hprof : ∀ lam ∈ Ioi (0 : ℝ), dilationProfile d (fun s => s ^ m / (m - 1)) lam =
      (m - 1)⁻¹ * lam ^ (-((d : ℝ) * (m - 1))) := by
    intro lam hlam
    rw [dilationProfile_porousMedium d hlam, div_eq_inv_mul]
    congr 2
    ring
  refine ⟨by simp [zero_rpow (by linarith : m ≠ 0)], ?_, ?_⟩
  · have := (convexOn_rpow_neg ha).smul (inv_nonneg.mpr hm1.le)
    refine this.congr fun lam hlam => ?_
    rw [hprof lam hlam]
    simp only [smul_eq_mul]
  · intro x hx y hy hxy
    rw [hprof x hx, hprof y hy]
    have : y ^ (-((d : ℝ) * (m - 1))) ≤ x ^ (-((d : ℝ) * (m - 1))) :=
      rpow_le_rpow_of_nonpos hx hxy (by linarith)
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hm1.le)

/-- **McCann's threshold `m ≥ 1 - 1/d` for porous-medium energies.** Let `d ≥ 1` and `0 < m < 1`.
Then `A(s) = s^m / (m - 1)` satisfies condition (A1) of R. J. McCann (Adv. Math. 128 (1997),
153–179) if and only if `m ≥ 1 - 1/d`. The dilation profile is `-λ^{d(1 - m)} / (1 - m)`, which
is convex exactly when `d(1 - m) ≤ 1`. At the endpoint `m = 1 - 1/d`, `A` is a positive multiple of
McCann's Brunn–Minkowski choice `A(s) = -s^{(d-1)/d}` (his Remark 2.4). The energy
`∫ ρ^m / (m - 1)` drives the porous medium (`m > 1`) and fast diffusion (`m < 1`) equations
`∂ₜρ = Δρ^m` as Wasserstein gradient flows. -/
theorem mcCannCondition_porousMedium_iff {d : ℕ} (hd : 1 ≤ d) {m : ℝ} (hm0 : 0 < m)
    (hm1 : m < 1) :
    McCannCondition d (fun s => s ^ m / (m - 1)) ↔ 1 - 1 / (d : ℝ) ≤ m := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < 1 - m := by linarith
  set a : ℝ := (d : ℝ) * (1 - m) with ha
  have hapos : 0 < a := by positivity
  have hprof : ∀ lam ∈ Ioi (0 : ℝ), dilationProfile d (fun s => s ^ m / (m - 1)) lam =
      -((1 - m)⁻¹ * lam ^ a) := by
    intro lam hlam
    rw [dilationProfile_porousMedium d hlam]
    have : m - 1 = -(1 - m) := by ring
    rw [this, div_neg, div_eq_inv_mul]
  have hiff : 1 - 1 / (d : ℝ) ≤ m ↔ a ≤ 1 := by
    rw [ha]
    constructor
    · intro h
      have h' : 1 - m ≤ 1 / (d : ℝ) := by linarith
      rw [le_div_iff₀ hdpos] at h'
      linarith
    · intro h
      have h' : 1 - m ≤ 1 / (d : ℝ) := by
        rw [le_div_iff₀ hdpos]; linarith
      linarith
  rw [hiff]
  constructor
  · rintro ⟨-, hconv, -⟩
    by_contra hcon
    push Not at hcon
    -- strict convexity of `λ ↦ λ^a` at the midpoint of `1` and `2` contradicts convexity of
    -- the profile `-(1 - m)⁻¹ λ^a`
    have hstrict := (strictConvexOn_rpow hcon).2 (show (1 : ℝ) ∈ Ici 0 by norm_num)
      (show (2 : ℝ) ∈ Ici 0 by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hc2 := hconv.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hstrict hc2
    rw [hprof _ (by norm_num), hprof _ (by norm_num), hprof _ (by norm_num)] at hc2
    have hinv : 0 < (1 - m)⁻¹ := inv_pos.mpr hc
    nlinarith
  · intro ha1
    refine ⟨by simp [zero_rpow hm0.ne'], ?_, ?_⟩
    · have hconc := (concaveOn_rpow hapos.le ha1).subset Ioi_subset_Ici_self (convex_Ioi 0)
      have := (hconc.smul (inv_nonneg.mpr hc.le)).neg
      refine this.congr fun lam hlam => ?_
      rw [hprof lam hlam]
      simp only [Pi.neg_apply, smul_eq_mul]
    · intro x hx y hy hxy
      rw [hprof x hx, hprof y hy, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow (le_of_lt hx) hxy hapos.le)
        (inv_nonneg.mpr hc.le)

end MathlibExt.Analysis.Convex.McCann
