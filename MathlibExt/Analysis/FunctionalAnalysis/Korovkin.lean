/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Korovkin's theorem

Korovkin's theorem is the basic convergence criterion of approximation
theory: a sequence of positive linear operators on `C([0, 1], ℝ)` converges
to the identity on every continuous function as soon as it does so on the
three test functions `1`, `x`, and `x²`.

The proof is the classical one. Uniform continuity of `f` gives, for every
`ε > 0`, a modulus `δ > 0` and a constant `C = 2‖f‖ / δ²` with
`|f(y) - f(x)| ≤ ε + C * (y - x)²` for all `x, y`. Positivity turns this
pointwise estimate into an operator estimate: with `Aₙ`, `Bₙ`, `Dₙ` the
values of `Lₙ 1`, `Lₙ x`, `Lₙ x²` at `x`, one gets
`|Lₙ f (x) - f(x)| ≤ ε * Aₙ + C * |Dₙ - 2x * Bₙ + x² * Aₙ| + |f(x)| * |Aₙ - 1|`,
and the right-hand side tends to `ε` uniformly in `x`, since the test
functions converge in norm. As `ε > 0` is arbitrary, `Lₙ f → f` in norm.

This is a companion to the approximation material in the v1 book
`IntroductionToFunctionalAnalysis` (Fejér's theorem, density of continuous
functions in `Lᵖ`): Korovkin's theorem is not one of the 72 v1 targets and
is not in Mathlib or MathlibExt. It is the abstract principle behind the
Bernstein proof of the Weierstrass approximation theorem: Mathlib's
`bernsteinApproximation_uniform` is the special case for the Bernstein
operators, which are positive and fix the test functions asymptotically.

Source: P. P. Korovkin, *On convergence of linear positive operators in the
space of continuous functions*, Doklady Akademii Nauk SSSR 90 (1953),
961--964; see also K. DeVore and G. Lorentz, *Constructive Approximation*,
Chapter 2, Theorem 1.1.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.Korovkin

open Filter Topology
open scoped unitInterval Topology

noncomputable section

/-- The identity function on `[0, 1]`, as a continuous map. -/
def korovkinId : C(I, ℝ) :=
  ⟨fun x => (x : ℝ), continuous_subtype_val⟩

/-- The square function on `[0, 1]`, as a continuous map. -/
def korovkinIdSq : C(I, ℝ) :=
  ⟨fun x => (x : ℝ) ^ 2, by fun_prop⟩

/-- The shifted square `y ↦ (y - x)²` on `[0, 1]`, as a continuous map. -/
def korovkinShiftSq (x : I) : C(I, ℝ) :=
  ⟨fun y => ((y : ℝ) - (x : ℝ)) ^ 2, by fun_prop⟩

@[simp]
theorem korovkinId_apply (x : I) : korovkinId x = (x : ℝ) :=
  rfl

@[simp]
theorem korovkinIdSq_apply (x : I) : korovkinIdSq x = (x : ℝ) ^ 2 :=
  rfl

@[simp]
theorem korovkinShiftSq_apply (x y : I) :
    korovkinShiftSq x y = ((y : ℝ) - (x : ℝ)) ^ 2 :=
  rfl

/-- The shifted square is a linear combination of the three test functions. -/
theorem korovkinShiftSq_eq (x : I) :
    korovkinShiftSq x =
      korovkinIdSq - (2 * (x : ℝ)) • korovkinId + (x : ℝ) ^ 2 • (1 : C(I, ℝ)) := by
  ext y
  simp only [korovkinShiftSq_apply, korovkinIdSq_apply, korovkinId_apply,
    ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  ring

/-- Pointwise convergence follows from convergence in the sup norm. -/
theorem tendsto_apply_of_tendsto {u : ℕ → C(I, ℝ)} {e : C(I, ℝ)}
    (h : Tendsto u atTop (𝓝 e)) (x : I) :
    Tendsto (fun n => u n x) atTop (𝓝 (e x)) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  rw [dist_eq_norm] at hdist
  rw [Real.dist_eq]
  calc |u n x - e x| = |(u n - e) x| := by simp [ContinuousMap.sub_apply]
    _ ≤ ‖u n - e‖ := by rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
    _ < ε := hdist

/-- A positive linear operator is monotone for the pointwise order. -/
theorem le_apply_of_le {L : C(I, ℝ) →ₗ[ℝ] C(I, ℝ)}
    (hpos : ∀ f : C(I, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ L f x)
    {g h : C(I, ℝ)} (hgh : ∀ x, g x ≤ h x) (x : I) : L g x ≤ L h x := by
  have h0 : ∀ y, 0 ≤ (h - g) y := fun y => sub_nonneg.mpr (hgh y)
  have h1 := hpos (h - g) h0 x
  simp only [map_sub, ContinuousMap.sub_apply] at h1
  linarith

/-- A positive linear operator is dominated by its value on a pointwise
absolute bound. -/
theorem abs_apply_le {L : C(I, ℝ) →ₗ[ℝ] C(I, ℝ)}
    (hpos : ∀ f : C(I, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ L f x)
    {g h : C(I, ℝ)} (hg : ∀ y, |g y| ≤ h y) (x : I) : |L g x| ≤ L h x := by
  have hle1 : L g x ≤ L h x :=
    le_apply_of_le hpos (fun y => le_of_abs_le (hg y)) x
  have hle2 : L (-g) x ≤ L h x :=
    le_apply_of_le hpos (fun y => by
      simp only [ContinuousMap.neg_apply]
      have h2 := hg y
      rw [abs_le] at h2
      linarith) x
  simp only [map_neg, ContinuousMap.neg_apply] at hle2
  exact abs_le.mpr ⟨by linarith, hle1⟩

/-- The key pointwise estimate: uniform continuity plus a bound on `‖f‖`
gives `|f(y) - f(x)| ≤ ε + C * (y - x)²` with `C = 2‖f‖ / δ²`. -/
theorem abs_sub_le_add_sq {f : C(I, ℝ)} {x : I} {δ ε C : ℝ} (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hC : 2 * ‖f‖ ≤ C * δ ^ 2) (hC0 : 0 ≤ C)
    (huni : ∀ y : I, dist y x < δ → |f y - f x| < ε) (y : I) :
    |f y - f x| ≤ ε + C * ((y : ℝ) - (x : ℝ)) ^ 2 := by
  by_cases hlt : dist y x < δ
  · have h := huni y hlt
    have hnn : 0 ≤ C * ((y : ℝ) - (x : ℝ)) ^ 2 := mul_nonneg hC0 (sq_nonneg _)
    linarith
  · push Not at hlt
    have hdist : ((y : ℝ) - (x : ℝ)) ^ 2 = (dist y x) ^ 2 := by
      rw [Subtype.dist_eq, Real.dist_eq, sq_abs]
    have h1 : |f y - f x| ≤ 2 * ‖f‖ := by
      calc |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := by
          have hfy := ContinuousMap.norm_coe_le_norm f y
          have hfx := ContinuousMap.norm_coe_le_norm f x
          rw [Real.norm_eq_abs] at hfy hfx
          exact add_le_add hfy hfx
        _ = 2 * ‖f‖ := by ring
    have h2 : C * δ ^ 2 ≤ C * ((y : ℝ) - (x : ℝ)) ^ 2 := by
      rw [hdist]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hδ) hlt 2) hC0
    linarith

/-- **Korovkin's theorem.** If `Lₙ` are positive linear operators on
`C([0, 1], ℝ)` converging to the identity on the test functions `1`, `x`,
`x²`, then `Lₙ f → f` in norm for every continuous `f`. -/
theorem korovkin {L : ℕ → C(I, ℝ) →ₗ[ℝ] C(I, ℝ)}
    (hpos : ∀ (n : ℕ) (f : C(I, ℝ)), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ L n f x)
    (h1 : Tendsto (fun n => L n 1) atTop (𝓝 (1 : C(I, ℝ))))
    (hid : Tendsto (fun n => L n korovkinId) atTop (𝓝 korovkinId))
    (hsq : Tendsto (fun n => L n korovkinIdSq) atTop (𝓝 korovkinIdSq))
    (f : C(I, ℝ)) : Tendsto (fun n => L n f) atTop (𝓝 f) := by
  -- The test-function errors tend to `0` in norm.
  have ha : Tendsto (fun n => ‖L n 1 - 1‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp h1
  have hb : Tendsto (fun n => ‖L n korovkinId - korovkinId‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp hid
  have hd : Tendsto (fun n => ‖L n korovkinIdSq - korovkinIdSq‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp hsq
  rw [Metric.tendsto_atTop]
  intro η hη
  -- Choose `ε = η / 4` and a modulus `δ` of uniform continuity for `f`.
  set ε : ℝ := η / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hη (by norm_num)
  obtain ⟨δ, hδ, hδunif⟩ :=
    (Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous)) ε hε
  set C : ℝ := 2 * ‖f‖ / δ ^ 2 with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (sq_nonneg _)
  have hCeq : 2 * ‖f‖ = C * δ ^ 2 := by
    rw [hCdef, div_mul_cancel₀]
    exact ne_of_gt (pow_pos hδ 2)
  -- The pointwise estimate, made uniform: for every `x` and `n`,
  -- `‖(Lₙ f - f) x‖` is bounded by a quantity independent of `x`.
  have hbound : ∀ (n : ℕ) (x : I),
      ‖(L n f - f) x‖ ≤ ε * (1 + ‖L n 1 - 1‖) +
        C * (‖L n korovkinIdSq - korovkinIdSq‖ +
          2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) +
        ‖f‖ * ‖L n 1 - 1‖ := by
    intro n x
    have hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
    have hx1 : |(x : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hx.1]
      exact hx.2
    have hx2 : (x : ℝ) ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, sq_nonneg ((x : ℝ) - 1)]
    -- Test-function errors at the point `x`.
    have hA : |(L n 1) x - 1| ≤ ‖L n 1 - 1‖ := by
      calc |(L n 1) x - 1| = |(L n 1 - 1) x| := by simp [ContinuousMap.sub_apply]
        _ ≤ ‖L n 1 - 1‖ := by rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
    have hB : |(L n korovkinId) x - (x : ℝ)| ≤ ‖L n korovkinId - korovkinId‖ := by
      calc |(L n korovkinId) x - (x : ℝ)| = |(L n korovkinId - korovkinId) x| := by
            simp [ContinuousMap.sub_apply]
        _ ≤ ‖L n korovkinId - korovkinId‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
    have hD : |(L n korovkinIdSq) x - (x : ℝ) ^ 2| ≤
        ‖L n korovkinIdSq - korovkinIdSq‖ := by
      calc |(L n korovkinIdSq) x - (x : ℝ) ^ 2| = |(L n korovkinIdSq - korovkinIdSq) x| := by
            simp [ContinuousMap.sub_apply]
        _ ≤ ‖L n korovkinIdSq - korovkinIdSq‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
    have hA0 : 0 ≤ (L n 1) x := hpos n 1 (fun y => by simp) x
    have hA1 : (L n 1) x ≤ 1 + ‖L n 1 - 1‖ := by
      have := le_of_abs_le hA
      linarith
    -- The quadratic combination is controlled by the test-function errors.
    have hcomb : |(L n korovkinIdSq) x - 2 * (x : ℝ) * (L n korovkinId) x +
          (x : ℝ) ^ 2 * (L n 1) x| ≤
        ‖L n korovkinIdSq - korovkinIdSq‖ +
          2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖ := by
      have hEq : (L n korovkinIdSq) x - 2 * (x : ℝ) * (L n korovkinId) x +
            (x : ℝ) ^ 2 * (L n 1) x =
          ((L n korovkinIdSq) x - (x : ℝ) ^ 2) -
            2 * (x : ℝ) * ((L n korovkinId) x - (x : ℝ)) +
            (x : ℝ) ^ 2 * ((L n 1) x - 1) := by ring
      rw [hEq]
      calc |((L n korovkinIdSq) x - (x : ℝ) ^ 2) -
              2 * (x : ℝ) * ((L n korovkinId) x - (x : ℝ)) +
              (x : ℝ) ^ 2 * ((L n 1) x - 1)|
          ≤ |(L n korovkinIdSq) x - (x : ℝ) ^ 2| +
              |2 * (x : ℝ) * ((L n korovkinId) x - (x : ℝ))| +
              |(x : ℝ) ^ 2 * ((L n 1) x - 1)| := by
            exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ ‖L n korovkinIdSq - korovkinIdSq‖ +
              2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖ := by
            have h1' : |2 * (x : ℝ) * ((L n korovkinId) x - (x : ℝ))| ≤
                2 * ‖L n korovkinId - korovkinId‖ := by
              rw [abs_mul, abs_mul, abs_two]
              calc 2 * |(x : ℝ)| * |(L n korovkinId) x - (x : ℝ)|
                  ≤ 2 * 1 * ‖L n korovkinId - korovkinId‖ :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hx1 (by norm_num)) hB
                      (abs_nonneg _) (by norm_num)
                _ = 2 * ‖L n korovkinId - korovkinId‖ := by norm_num
            have h2' : |(x : ℝ) ^ 2 * ((L n 1) x - 1)| ≤ ‖L n 1 - 1‖ := by
              rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
              calc (x : ℝ) ^ 2 * |(L n 1) x - 1|
                  ≤ 1 * ‖L n 1 - 1‖ :=
                    mul_le_mul hx2 hA (abs_nonneg _) (by norm_num)
                _ = ‖L n 1 - 1‖ := one_mul _
            exact add_le_add (add_le_add hD h1') h2'
    -- The operator estimate from positivity.
    have hpoint : |(L n f) x - f x| ≤ ε * (L n 1) x +
        C * |(L n korovkinIdSq) x - 2 * (x : ℝ) * (L n korovkinId) x +
          (x : ℝ) ^ 2 * (L n 1) x| + |f x| * |(L n 1) x - 1| := by
      have huni : ∀ y : I, dist y x < δ → |f y - f x| < ε := by
        intro y hy
        have := hδunif hy
        rwa [Real.dist_eq] at this
      have hpt : ∀ y : I, |(f - f x • (1 : C(I, ℝ))) y| ≤
          (ε • (1 : C(I, ℝ)) + C • korovkinShiftSq x) y := by
        intro y
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one,
          ContinuousMap.add_apply, korovkinShiftSq_apply]
        exact abs_sub_le_add_sq hδ (le_of_lt hε) hCeq.le hC0 huni y
      have habs := abs_apply_le (hpos n) hpt x
      have hL1 : (L n (f - f x • (1 : C(I, ℝ)))) x = (L n f) x - f x * (L n 1) x := by
        simp [map_sub, map_smul]
      have hL2 : (L n (ε • (1 : C(I, ℝ)) + C • korovkinShiftSq x)) x =
          ε * (L n 1) x + C * ((L n korovkinIdSq) x -
            2 * (x : ℝ) * (L n korovkinId) x + (x : ℝ) ^ 2 * (L n 1) x) := by
        have hq : L n (korovkinShiftSq x) =
            L n korovkinIdSq - (2 * (x : ℝ)) • L n korovkinId +
              (x : ℝ) ^ 2 • L n 1 := by
          conv_lhs => rw [korovkinShiftSq_eq]
          simp [map_sub, map_add, map_smul]
        simp only [map_add, map_smul, hq, ContinuousMap.add_apply, ContinuousMap.smul_apply,
          ContinuousMap.sub_apply, smul_eq_mul]
      rw [hL1] at habs
      calc |(L n f) x - f x|
          = |(L n f) x - f x * (L n 1) x + (f x * (L n 1) x - f x)| := by
            congr 1
            ring
        _ ≤ |(L n f) x - f x * (L n 1) x| + |f x * (L n 1) x - f x| :=
          abs_add_le _ _
        _ ≤ (ε * (L n 1) x + C * |(L n korovkinIdSq) x -
              2 * (x : ℝ) * (L n korovkinId) x + (x : ℝ) ^ 2 * (L n 1) x|) +
            |f x| * |(L n 1) x - 1| := by
          apply add_le_add _ _
          · -- First term: the positivity estimate, with the middle factor
            -- replaced by its absolute value.
            have hle : (L n (ε • (1 : C(I, ℝ)) + C • korovkinShiftSq x)) x ≤
                ε * (L n 1) x + C * |(L n korovkinIdSq) x -
                  2 * (x : ℝ) * (L n korovkinId) x + (x : ℝ) ^ 2 * (L n 1) x| := by
              rw [hL2]
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left (le_abs_self _) hC0)
            exact habs.trans hle
          · have hEq : f x * (L n 1) x - f x = f x * ((L n 1) x - 1) := by ring
            rw [hEq, abs_mul]
    -- Assemble the uniform bound.
    rw [Real.norm_eq_abs, ContinuousMap.sub_apply]
    have hfx : |f x| ≤ ‖f‖ := by
      have := ContinuousMap.norm_coe_le_norm f x
      rwa [Real.norm_eq_abs] at this
    calc |(L n f) x - f x|
        ≤ ε * (L n 1) x + C * |(L n korovkinIdSq) x -
            2 * (x : ℝ) * (L n korovkinId) x + (x : ℝ) ^ 2 * (L n 1) x| +
            |f x| * |(L n 1) x - 1| := hpoint
      _ ≤ ε * (1 + ‖L n 1 - 1‖) +
            C * (‖L n korovkinIdSq - korovkinIdSq‖ +
              2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) +
            ‖f‖ * ‖L n 1 - 1‖ := by
          apply add_le_add (add_le_add _ _) _
          · exact mul_le_mul_of_nonneg_left hA1 (le_of_lt hε)
          · exact mul_le_mul_of_nonneg_left hcomb hC0
          · exact mul_le_mul hfx hA (abs_nonneg _) (norm_nonneg _)
  -- From the uniform pointwise bound to a norm bound, then let `n → ∞`.
  have hnorm : ∀ n : ℕ, ‖L n f - f‖ ≤ ε * (1 + ‖L n 1 - 1‖) +
      C * (‖L n korovkinIdSq - korovkinIdSq‖ +
        2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) +
      ‖f‖ * ‖L n 1 - 1‖ := by
    intro n
    have hnn : 0 ≤ ε * (1 + ‖L n 1 - 1‖) +
        C * (‖L n korovkinIdSq - korovkinIdSq‖ +
          2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) +
        ‖f‖ * ‖L n 1 - 1‖ := by positivity
    exact (ContinuousMap.norm_le (L n f - f) hnn).mpr (hbound n)
  have hK : 0 < C + 1 := by linarith [hC0]
  have hM : 0 < ‖f‖ + 1 := by linarith [norm_nonneg f]
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp ha) (1 : ℝ) one_pos
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp ha) (min (ε / (3 * (C + 1))) (ε / (‖f‖ + 1)))
    (lt_min (div_pos hε (by linarith [hK])) (div_pos hε hM))
  obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp hb) (ε / (6 * (C + 1)))
    (div_pos hε (by linarith [hK]))
  obtain ⟨N4, hN4⟩ := (Metric.tendsto_atTop.mp hd) (ε / (3 * (C + 1)))
    (div_pos hε (by linarith [hK]))
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have e1 := hN1 n hn1
  have e2 := hN2 n hn2
  have e3 := hN3 n hn3
  have e4 := hN4 n hn4
  have ha1 : ‖L n 1 - 1‖ < 1 := by simpa using e1
  have ha2 : ‖L n 1 - 1‖ < ε / (3 * (C + 1)) :=
    lt_of_lt_of_le (by simpa using e2) (min_le_left _ _)
  have ha3 : ‖L n 1 - 1‖ < ε / (‖f‖ + 1) :=
    lt_of_lt_of_le (by simpa using e2) (min_le_right _ _)
  have hb1 : ‖L n korovkinId - korovkinId‖ < ε / (6 * (C + 1)) := by simpa using e3
  have hd1 : ‖L n korovkinIdSq - korovkinIdSq‖ < ε / (3 * (C + 1)) := by simpa using e4
  have hsum : ‖L n korovkinIdSq - korovkinIdSq‖ +
      2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖ < ε / (C + 1) := by
    have h6 : 2 * ‖L n korovkinId - korovkinId‖ < ε / (3 * (C + 1)) := by
      have hpos6 : (0:ℝ) < 6 * (C + 1) := by linarith [hK]
      have hpos3 : (0:ℝ) < 3 * (C + 1) := by linarith [hK]
      rw [lt_div_iff₀ hpos3]
      rw [lt_div_iff₀ hpos6] at hb1
      have hEq : 2 * ‖L n korovkinId - korovkinId‖ * (3 * (C + 1)) =
          ‖L n korovkinId - korovkinId‖ * (6 * (C + 1)) := by ring
      linarith [hb1, hEq]
    have ht : 3 * (ε / (3 * (C + 1))) = ε / (C + 1) := by
      rw [← mul_div_assoc, mul_div_mul_left ε (C + 1) (by norm_num)]
    linarith [hd1, h6, ha2, ht]
  have hCterm : C * (‖L n korovkinIdSq - korovkinIdSq‖ +
      2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) < ε := by
    have hle : C * (‖L n korovkinIdSq - korovkinIdSq‖ +
        2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) ≤
        (C + 1) * (‖L n korovkinIdSq - korovkinIdSq‖ +
          2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) := by
      apply mul_le_mul_of_nonneg_right (by linarith [hC0]) (by positivity)
    have hlt : (C + 1) * (‖L n korovkinIdSq - korovkinIdSq‖ +
        2 * ‖L n korovkinId - korovkinId‖ + ‖L n 1 - 1‖) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left hsum hK
    have hcan : (C + 1) * (ε / (C + 1)) = ε := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hK)]
    linarith
  have hfterm : ‖f‖ * ‖L n 1 - 1‖ < ε := by
    have hle : ‖f‖ * ‖L n 1 - 1‖ ≤ (‖f‖ + 1) * ‖L n 1 - 1‖ := by
      apply mul_le_mul_of_nonneg_right (by linarith [norm_nonneg f]) (norm_nonneg _)
    have hlt : (‖f‖ + 1) * ‖L n 1 - 1‖ < (‖f‖ + 1) * (ε / (‖f‖ + 1)) :=
      mul_lt_mul_of_pos_left ha3 hM
    have hcan : (‖f‖ + 1) * (ε / (‖f‖ + 1)) = ε := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hM)]
    linarith
  have hmain := hnorm n
  rw [dist_eq_norm]
  have hε4 : 4 * ε = η := by rw [hεdef]; ring
  have hεterm : ε * (1 + ‖L n 1 - 1‖) ≤ 2 * ε := by
    have : (1:ℝ) + ‖L n 1 - 1‖ ≤ 2 := by linarith [ha1]
    exact (mul_le_mul_of_nonneg_left this (le_of_lt hε)).trans_eq (by ring)
  linarith

end

end MathlibExt.Analysis.FunctionalAnalysis.Korovkin
