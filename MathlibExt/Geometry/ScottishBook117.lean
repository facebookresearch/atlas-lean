/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Sign
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Connected.Clopen

/-!
# Fréchet's Problem 117 from the Scottish Book

The claim of Fréchet's Problem 117, as formalized here (`ScottishBookProblem117Claim`), is that
every `1`-periodic continuous map `γ : ℝ → ℝ³` that is injective on `[0, 1)` and has an oriented
tangent (`HasTangentLineAt`) at every parameter can be reparametrized, with the same image, by a
map with the same properties that is differentiable with nonzero derivative everywhere. The main
result, `frechet117_refuted`, is that this claim is false.

## Proof outline

The counterexample is planar. With `dir t = (sin (π t), -cos (π t), 0)` and
`zig x = x (2 + cos (π / x))`, it is `curve t = zig (sin (π t)) • dir t`: the circle
`t ↦ 2 sin (π t) • dir t` of radius `1` through the origin, rescaled from the origin by the factor
`(2 + cos (π / sin (π t))) / 2`, which lies between `1 / 2` and `3 / 2`.

* `curve` is `1`-periodic and continuous, and it is injective on `[0, 1)`: the point `curve t`
  lies on the ray from the origin in the direction `dir t`, at distance `|zig (sin (π t))|`,
  which vanishes only at the integers.
* Away from the integers, `curve` is differentiable with nonzero derivative, so it has an
  oriented tangent. Near `0` the secant directions from the origin are `dir s` for `s > 0` and
  `-dir s` for `s < 0`, which tend to `dir 0` and `-dir 0`; periodicity gives the other integers.
* Along the curve the distance `zig (sin (π s))` to the origin oscillates between `sin (π s)` and
  `3 sin (π s)`, so arbitrarily close to the origin there are parameters `0 < s₁ < s₂` with
  `‖curve s₁‖ ≥ 2 ‖curve s₂‖`.
* Let `p` be a reparametrization as in the claim, with `p t₁ = 0` and `u = p' t₁ ≠ 0`. Near `t₁`
  the norm `‖p σ‖` lies between `3 / 4 ‖u‖ |σ - t₁|` and `5 / 4 ‖u‖ |σ - t₁|`, so the arc of `p`
  from the origin to `curve s₂` stays in the ball of radius `5 / 3 ‖curve s₂‖ < ‖curve s₁‖` and
  misses `curve s₁` and `curve (1 / 2)`. But a connected subset of the curve that contains the
  origin and `curve s₂` contains one of the two arcs of `curve` between them, and these pass
  through `curve s₁` and `curve (1 / 2)` respectively.

The obstruction sits at the origin alone and uses that the derivative in the claim is finite: the
distance to the origin of a parametrization with finite nonzero derivative there grows linearly in
the parameter, which the oscillation forbids.

## References

* M. Fréchet, Problem 117 of the Scottish Book; in general, no, by A. J. Ward, Fundamenta
  Mathematicae 28 (1937), cited in the typescript addendum Ad 117. The counterexample above is
  elementary and self-contained; it is not taken from Ward's paper.
-/

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook117Wanted

open scoped InnerProductSpace

/-- Any curve `γ : ℝ → ℝ³` has an oriented tangent line at `t` if there
is a unit direction `v` such that every nearby secant vector `γ s - γ t`
is arbitrarily close, relative to its length, to `‖γ s - γ t‖ • v` for
`s > t` and to `‖γ s - γ t‖ • (-v)` for `s < t`: secant directions tend
to `v` from the right and to `-v` from the left. No periodicity,
continuity, or injectivity is assumed here; those hypotheses live in
`ScottishBookProblem117Claim`. -/
def HasTangentLineAt (γ : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ) : Prop :=
  ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ,
      0 < |s - t| → |s - t| < δ →
      ‖(γ s - γ t) - (Real.sign (s - t) * ‖γ s - γ t‖) • v‖ ≤ ε * ‖γ s - γ t‖

/-- **The claim of Fréchet's Problem 117.** The claim of Fréchet's Problem 117 from the Scottish
Book is the statement that for every $1$-periodic continuous map
$\gamma : \mathbb{R} \to \mathbb{R}^3$ that is injective on $[0, 1)$ and has an oriented tangent
at every $t \in \mathbb{R}$, there is a $1$-periodic continuous map
$p : \mathbb{R} \to \mathbb{R}^3$ that is injective on $[0, 1)$, has the same image as $\gamma$,
and is differentiable at every $t \in \mathbb{R}$ with $p'(t) \ne 0$.

Here $\gamma$ has an oriented tangent at $t$ when there is a unit vector $v$ such that the
directions of the secant vectors $\gamma(s) - \gamma(t)$ tend to $v$ as $s \to t$ from the right
and to $-v$ as $s \to t$ from the left. -/
def ScottishBookProblem117Claim : Prop :=
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin 3),
    (∀ t, γ (t + 1) = γ t) →
    Continuous γ →
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) →
    (∀ t, HasTangentLineAt γ t) →
    ∃ p : ℝ → EuclideanSpace ℝ (Fin 3),
      (∀ t, p (t + 1) = p t) ∧
      Continuous p ∧
      Set.InjOn p (Set.Ico (0 : ℝ) 1) ∧
      Set.range p = Set.range γ ∧
      ∀ t, DifferentiableAt ℝ p t ∧ deriv p t ≠ 0

open Real

/-! ### The counterexample curve -/

/-- The radial profile `x (2 + cos (π / x))`, which oscillates between `x` and `3 x` for
`x > 0`. -/
private noncomputable def zig (x : ℝ) : ℝ := x * (2 + cos (π / x))

/-- The unit vector `(sin (π t), -cos (π t), 0)`. -/
private noncomputable def dir (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  sin (π * t) • EuclideanSpace.single 0 1 - cos (π * t) • EuclideanSpace.single 1 1

/-- The counterexample: the circle `t ↦ 2 sin (π t) • dir t` through the origin, with its
distance `zig (sin (π t))` to the origin made to oscillate near `t = 0`. -/
private noncomputable def curve (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  zig (sin (π * t)) • dir t

private lemma zig_zero : zig 0 = 0 := by simp [zig]

private lemma zig_neg (x : ℝ) : zig (-x) = -zig x := by
  simp only [zig, div_neg, cos_neg, neg_mul]

private lemma one_le_two_add_cos (y : ℝ) : 1 ≤ 2 + cos y := by
  linarith [neg_one_le_cos y]

private lemma zig_pos {x : ℝ} (hx : 0 < x) : 0 < zig x :=
  mul_pos hx (by linarith [one_le_two_add_cos (π / x)])

private lemma zig_neg_of_neg {x : ℝ} (hx : x < 0) : zig x < 0 :=
  mul_neg_of_neg_of_pos hx (by linarith [one_le_two_add_cos (π / x)])

private lemma continuous_zig : Continuous zig := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / 3, by positivity, fun {y} hy => ?_⟩
    rw [Real.dist_eq, sub_zero] at hy
    rw [Real.dist_eq, zig_zero, sub_zero, zig, abs_mul]
    have h3 : |2 + cos (π / y)| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [neg_one_le_cos (π / y), cos_le_one (π / y)]
    calc |y| * |2 + cos (π / y)| ≤ |y| * 3 := by gcongr
      _ < ε := by linarith
  · exact continuousAt_id.mul (continuousAt_const.add
      (continuous_cos.continuousAt.comp (continuousAt_const.div continuousAt_id hx)))

private lemma differentiableAt_zig {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ zig x :=
  differentiableAt_id.mul ((differentiableAt_const _).add
    (differentiableAt_cos.comp x ((differentiableAt_const _).div differentiableAt_id hx)))

private lemma dir_apply_one (t : ℝ) : dir t 1 = -cos (π * t) := by simp [dir]

private lemma norm_dir (t : ℝ) : ‖dir t‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [dir, sin_sq_add_cos_sq]

private lemma continuous_dir : Continuous dir := by
  unfold dir
  fun_prop

private lemma curve_zero : curve 0 = 0 := by simp [curve, zig_zero]

private lemma norm_curve (t : ℝ) : ‖curve t‖ = |zig (sin (π * t))| := by
  rw [curve, norm_smul, norm_dir, mul_one, Real.norm_eq_abs]

private lemma curve_add_one (t : ℝ) : curve (t + 1) = curve t := by
  have hs : sin (π * (t + 1)) = -sin (π * t) := by rw [mul_add, mul_one, sin_add_pi]
  have hc : cos (π * (t + 1)) = -cos (π * t) := by rw [mul_add, mul_one, cos_add_pi]
  simp only [curve, dir, hs, hc, zig_neg]
  module

private lemma continuous_curve : Continuous curve := by
  unfold curve
  exact (continuous_zig.comp (by fun_prop)).smul continuous_dir

private lemma sin_pi_mul_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < sin (π * t) :=
  sin_pos_of_pos_of_lt_pi (by positivity) (mul_lt_of_lt_one_right pi_pos h1)

private lemma sin_pi_mul_neg {t : ℝ} (h0 : t < 0) (h1 : -1 < t) : sin (π * t) < 0 :=
  sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg pi_pos h0) (by nlinarith [pi_pos])

private lemma curve_injOn : Set.InjOn curve (Set.Ico 0 1) := by
  intro t ht t' ht' h
  have hn := congrArg norm h
  rw [norm_curve, norm_curve] at hn
  rcases ht.1.eq_or_lt with rfl | ht0 <;> rcases ht'.1.eq_or_lt with rfl | ht0'
  · rfl
  · have := abs_pos.mpr (zig_pos (sin_pi_mul_pos ht0' ht'.2)).ne'
    rw [mul_zero, sin_zero, zig_zero, abs_zero] at hn
    linarith
  · have := abs_pos.mpr (zig_pos (sin_pi_mul_pos ht0 ht.2)).ne'
    rw [mul_zero, sin_zero, zig_zero, abs_zero] at hn
    linarith
  · have hz := zig_pos (sin_pi_mul_pos ht0 ht.2)
    have hz' := zig_pos (sin_pi_mul_pos ht0' ht'.2)
    rw [abs_of_pos hz, abs_of_pos hz'] at hn
    have hd : dir t = dir t' := by
      unfold curve at h
      rw [hn] at h
      exact smul_right_injective _ hz'.ne' h
    have hc : cos (π * t) = cos (π * t') := by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hd
      simpa only [dir_apply_one, neg_inj] using this
    have := injOn_cos ⟨by positivity, mul_le_of_le_one_right pi_pos.le ht.2.le⟩
      ⟨by positivity, mul_le_of_le_one_right pi_pos.le ht'.2.le⟩ hc
    exact mul_left_cancel₀ pi_ne_zero this

private lemma sign_mul_abs_self (r : ℝ) : Real.sign r * |r| = r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- A curve that is differentiable at `t` with nonzero derivative has an oriented tangent at `t`,
in the direction of its derivative. -/
private lemma hasTangentLineAt_of_hasDerivAt {γ : ℝ → EuclideanSpace ℝ (Fin 3)} {t : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} (hγ : HasDerivAt γ u t) (hu : u ≠ 0) :
    HasTangentLineAt γ t := by
  have hU : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set v : EuclideanSpace ℝ (Fin 3) := ‖u‖⁻¹ • u with hv_def
  have hv : ‖v‖ = 1 := by
    rw [hv_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hU.ne']
  refine ⟨v, hv, fun ε hε => ?_⟩
  set η := min (ε * ‖u‖ / 4) (‖u‖ / 2) with hη_def
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ ε * ‖u‖ / 4 := min_le_left _ _
  have hη2 : η ≤ ‖u‖ / 2 := min_le_right _ _
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hγ).def hη0)
  refine ⟨δ, hδ, fun s _ hsδ => ?_⟩
  have hest : ‖γ s - γ t - (s - t) • u‖ ≤ η * |s - t| := by
    have := hball (show dist s t < δ by rwa [Real.dist_eq])
    simpa only [Real.norm_eq_abs] using this
  set w := γ s - γ t with hw
  set r := s - t with hr
  have hru : ‖r • u‖ = |r| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hru_v : r • u = (r * ‖u‖) • v := by
    rw [hv_def, smul_smul, mul_assoc, mul_inv_cancel₀ hU.ne', mul_one]
  have hgap : |(|r| * ‖u‖ - ‖w‖)| ≤ η * |r| := by
    rw [← hru]
    calc |‖r • u‖ - ‖w‖| ≤ ‖r • u - w‖ := abs_norm_sub_norm_le _ _
      _ = ‖w - r • u‖ := norm_sub_rev _ _
      _ ≤ η * |r| := hest
  have hw_lower : |r| * ‖u‖ / 2 ≤ ‖w‖ := by
    have h1 := norm_sub_norm_le (r • u) w
    rw [hru, norm_sub_rev (r • u) w] at h1
    nlinarith [abs_nonneg r]
  have habs_sign : |Real.sign r| ≤ 1 := by
    rcases Real.sign_apply_eq r with h | h | h <;> simp [h]
  have hdecomp : w - (Real.sign r * ‖w‖) • v
      = (w - r • u) + (Real.sign r * (|r| * ‖u‖ - ‖w‖)) • v := by
    have hsc : Real.sign r * (|r| * ‖u‖ - ‖w‖) = r * ‖u‖ - Real.sign r * ‖w‖ := by
      linear_combination ‖u‖ * sign_mul_abs_self r
    rw [hsc, hru_v, sub_smul]
    abel
  rw [hdecomp]
  calc ‖(w - r • u) + (Real.sign r * (|r| * ‖u‖ - ‖w‖)) • v‖
      ≤ ‖w - r • u‖ + ‖(Real.sign r * (|r| * ‖u‖ - ‖w‖)) • v‖ := norm_add_le _ _
    _ = ‖w - r • u‖ + |Real.sign r| * |(|r| * ‖u‖ - ‖w‖)| := by
        rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_mul]
    _ ≤ η * |r| + 1 * (η * |r|) := by gcongr
    _ = 2 * η * |r| := by ring
    _ ≤ 2 * (ε * ‖u‖ / 4) * |r| := by gcongr
    _ = ε * (|r| * ‖u‖ / 2) := by ring
    _ ≤ ε * ‖w‖ := by gcongr

private lemma hasDerivAt_dir (t : ℝ) : HasDerivAt dir
    ((cos (π * t) * π) • EuclideanSpace.single 0 1 -
      (-sin (π * t) * π) • EuclideanSpace.single 1 1) t := by
  have h1 : HasDerivAt (fun s => sin (π * s)) (cos (π * t) * π) t := by
    simpa using ((hasDerivAt_id t).const_mul π).sin
  have h2 : HasDerivAt (fun s => cos (π * s)) (-sin (π * t) * π) t := by
    simpa using ((hasDerivAt_id t).const_mul π).cos
  exact (h1.smul_const _).sub (h2.smul_const _)

private lemma zig_ne_zero {x : ℝ} (hx : x ≠ 0) : zig x ≠ 0 :=
  mul_ne_zero hx (by linarith [one_le_two_add_cos (π / x)])

private lemma hasTangentLineAt_curve_of_sin_ne_zero {t : ℝ} (ht : sin (π * t) ≠ 0) :
    HasTangentLineAt curve t := by
  have hd : DifferentiableAt ℝ (fun s => zig (sin (π * s))) t :=
    (differentiableAt_zig ht).comp t (f := fun s => sin (π * s)) (by fun_prop)
  have hl := hd.hasDerivAt
  refine hasTangentLineAt_of_hasDerivAt (hl.smul (hasDerivAt_dir t)) ?_
  intro h0
  have e0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h0
  have e1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h0
  simp [dir] at e0 e1
  apply zig_ne_zero ht
  apply (mul_eq_zero.mp _).resolve_right pi_ne_zero
  linear_combination cos (π * t) * e0 + sin (π * t) * e1 -
    zig (sin (π * t)) * π * sin_sq_add_cos_sq (π * t)

private lemma hasTangentLineAt_curve_zero : HasTangentLineAt curve 0 := by
  refine ⟨dir 0, norm_dir 0, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp continuous_dir.continuousAt ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun s hs0 hsδ => ?_⟩
  rw [sub_zero] at hs0 hsδ ⊢
  rw [curve_zero, sub_zero]
  have hs1 : |s| < 1 := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hsd : |s| < δ := lt_of_lt_of_le hsδ (min_le_left _ _)
  have key : Real.sign s * ‖curve s‖ = zig (sin (π * s)) := by
    rw [norm_curve]
    rcases lt_or_gt_of_ne (abs_pos.mp hs0) with hneg | hpos
    · rw [Real.sign_of_neg hneg,
        abs_of_neg (zig_neg_of_neg (sin_pi_mul_neg hneg (by linarith [neg_abs_le s])))]
      ring
    · rw [Real.sign_of_pos hpos,
        abs_of_pos (zig_pos (sin_pi_mul_pos hpos (by linarith [le_abs_self s]))), one_mul]
  have hsub : curve s - zig (sin (π * s)) • dir 0 = zig (sin (π * s)) • (dir s - dir 0) := by
    rw [curve, smul_sub]
  rw [key, hsub, norm_smul, Real.norm_eq_abs, norm_curve, mul_comm ε]
  gcongr
  have := hcont (show dist s 0 < δ by rwa [Real.dist_eq, sub_zero])
  rw [dist_eq_norm] at this
  exact this.le

private lemma hasTangentLineAt_curve_int (n : ℤ) : HasTangentLineAt curve n := by
  obtain ⟨v, hv, h⟩ := hasTangentLineAt_curve_zero
  have hper : Function.Periodic curve 1 := curve_add_one
  refine ⟨v, hv, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hs⟩ := h ε hε
  refine ⟨δ, hδ, fun s h1 h2 => ?_⟩
  have e1 : curve s = curve (s - n) := by
    simpa using (hper.sub_int_mul_eq n (x := s)).symm
  have e2 : curve (n : ℝ) = curve 0 := by
    simpa using hper.int_mul_eq n
  have := hs (s - n) (by rwa [sub_zero]) (by rwa [sub_zero])
  rw [sub_zero] at this
  rw [e1, e2]
  exact this

private lemma hasTangentLineAt_curve (t : ℝ) : HasTangentLineAt curve t := by
  by_cases ht : sin (π * t) = 0
  · obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp ht
    have htn : t = n := mul_left_cancel₀ pi_ne_zero (by rw [← hn, mul_comm])
    rw [htn]
    exact hasTangentLineAt_curve_int n
  · exact hasTangentLineAt_curve_of_sin_ne_zero ht

private lemma norm_curve_arcsin {x : ℝ} (h0 : -1 ≤ x) (h1 : x ≤ 1) :
    ‖curve (arcsin x / π)‖ = |zig x| := by
  rw [norm_curve, mul_div_cancel₀ _ pi_ne_zero, sin_arcsin h0 h1]

/-- Points of the curve at which its distance to the origin drops by a factor of at least two
while moving away from the origin along the curve, arbitrarily close to the origin. -/
private lemma exists_zigzag {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧ s₂ < 1 / 2 ∧ 0 < ‖curve s₂‖ ∧ ‖curve s₂‖ < ρ ∧
      2 * ‖curve s₂‖ ≤ ‖curve s₁‖ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ρ + 2)
  have hρ' : 0 < 1 / ρ := one_div_pos.mpr hρ
  have hm2 : (2 : ℝ) ≤ m := by linarith
  set x₁ : ℝ := 1 / (2 * m) with hx₁
  set x₂ : ℝ := 1 / (2 * m - 1) with hx₂
  have hx₁pos : 0 < x₁ := by positivity
  have hx₂pos : 0 < x₂ := one_div_pos.mpr (by linarith)
  have hx₁₂ : x₁ < x₂ := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hx₂1 : x₂ < 1 := by
    rw [hx₂, div_lt_one (by linarith)]
    linarith
  have hzig₁ : zig x₁ = 3 * x₁ := by
    have : π / x₁ = (m : ℝ) * (2 * π) := by
      rw [hx₁]
      field_simp
    rw [zig, this, cos_nat_mul_two_pi]
    ring
  have hzig₂ : zig x₂ = x₂ := by
    have : π / x₂ = (m : ℝ) * (2 * π) - π := by
      rw [hx₂]
      field_simp
    rw [zig, this, cos_sub_pi, cos_nat_mul_two_pi]
    ring
  have hn₁ : ‖curve (arcsin x₁ / π)‖ = 3 * x₁ := by
    rw [norm_curve_arcsin (by linarith) (by linarith), hzig₁, abs_of_pos (by positivity)]
  have hn₂ : ‖curve (arcsin x₂ / π)‖ = x₂ := by
    rw [norm_curve_arcsin (by linarith) (by linarith), hzig₂, abs_of_pos hx₂pos]
  refine ⟨arcsin x₁ / π, arcsin x₂ / π, div_pos (arcsin_pos.mpr hx₁pos) pi_pos,
    (div_lt_div_iff_of_pos_right pi_pos).mpr (arcsin_lt_arcsin (by linarith) hx₁₂ hx₂1.le),
    ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ pi_pos]
    linarith [arcsin_lt_pi_div_two.mpr hx₂1]
  · rw [hn₂]
    exact hx₂pos
  · rw [hn₂, hx₂, div_lt_iff₀ (by linarith)]
    have h1 : 1 / ρ < 2 * m - 1 := by linarith
    calc (1 : ℝ) = ρ * (1 / ρ) := by field_simp
      _ < ρ * (2 * m - 1) := by gcongr
  · rw [hn₁, hn₂, hx₁, hx₂, mul_one_div, mul_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
    linarith

/-- Two parameters of a `1`-periodic map that is injective on `[0, 1)` with the same value differ
by an integer. -/
private lemma exists_int_sub_eq_of_eq {γ : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hper : ∀ t, γ (t + 1) = γ t) (hinj : Set.InjOn γ (Set.Ico 0 1)) {x y : ℝ}
    (h : γ x = γ y) : ∃ z : ℤ, x - y = z := by
  have hP : Function.Periodic γ 1 := hper
  have hf : ∀ a, γ (Int.fract a) = γ a := fun a => by
    simpa using hP.sub_int_mul_eq ⌊a⌋ (x := a)
  apply Int.fract_eq_fract.mp
  apply hinj ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  rw [hf, hf, h]

/-- A connected subset of a closed curve that contains two of its points contains one of the two
arcs between them: here `A` contains `γ 0` and `γ s₂` but misses `γ s₁` and `γ s₃`, one on each
arc, which is impossible. -/
private lemma false_of_isPreconnected {γ : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hper : ∀ t, γ (t + 1) = γ t) (hcont : Continuous γ) (hinj : Set.InjOn γ (Set.Ico 0 1))
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : IsPreconnected A) (hAγ : A ⊆ Set.range γ)
    {s₁ s₂ s₃ : ℝ} (h1 : 0 < s₁) (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h3 : s₃ < 1)
    (h0A : γ 0 ∈ A) (h2A : γ s₂ ∈ A) (h1A : γ s₁ ∉ A) (h3A : γ s₃ ∉ A) : False := by
  have key := fun {x y : ℝ} (h : γ x = γ y) => exists_int_sub_eq_of_eq hper hinj h
  have hF₁ : IsClosed (γ '' Set.Icc s₁ s₃) := (isCompact_Icc.image hcont).isClosed
  have hF₂ : IsClosed (γ '' Set.Icc 0 s₁ ∪ γ '' Set.Icc s₃ 1) :=
    ((isCompact_Icc.image hcont).union (isCompact_Icc.image hcont)).isClosed
  have hcover : A ⊆ γ '' Set.Icc s₁ s₃ ∪ (γ '' Set.Icc 0 s₁ ∪ γ '' Set.Icc s₃ 1) := by
    intro a ha
    obtain ⟨x, rfl⟩ := hAγ ha
    obtain ⟨y, hy, hxy⟩ := (show Function.Periodic γ 1 from hper).exists_mem_Ico₀ one_pos x
    rw [hxy]
    rcases le_or_gt y s₁ with h | h
    · exact Or.inr (Or.inl ⟨y, ⟨hy.1, h⟩, rfl⟩)
    rcases le_or_gt y s₃ with h' | h'
    · exact Or.inl ⟨y, ⟨h.le, h'⟩, rfl⟩
    · exact Or.inr (Or.inr ⟨y, ⟨h'.le, hy.2.le⟩, rfl⟩)
  have hdisj : A ∩ (γ '' Set.Icc s₁ s₃ ∩ (γ '' Set.Icc 0 s₁ ∪ γ '' Set.Icc s₃ 1)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro a ⟨ha, ⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩⟩
    · obtain ⟨z, hz⟩ := key hyx
      have hz1 : (z : ℝ) ≤ 0 := by linarith [hy.2, hx.1]
      have hz2 : (-1 : ℝ) < z := by linarith [hy.1, hx.2]
      have hz0 : z = 0 := by
        have : z ≤ 0 := by exact_mod_cast hz1
        have : -1 < z := by exact_mod_cast hz2
        omega
      rw [hz0, Int.cast_zero, sub_eq_zero] at hz
      have hxs : x = s₁ := le_antisymm (hz ▸ hy.2) hx.1
      exact h1A (hxs ▸ ha)
    · obtain ⟨z, hz⟩ := key hyx
      have hz1 : 0 ≤ (z : ℝ) := by linarith [hy.1, hx.2]
      have hz2 : (z : ℝ) < 1 := by linarith [hy.2, hx.1]
      have hz0 : z = 0 := by
        have : 0 ≤ z := by exact_mod_cast hz1
        have : z < 1 := by exact_mod_cast hz2
        omega
      rw [hz0, Int.cast_zero, sub_eq_zero] at hz
      have hxs : x = s₃ := le_antisymm hx.2 (hz ▸ hy.1)
      exact h3A (hxs ▸ ha)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hA) _ _ hF₁ hF₂ hcover hdisj with h | h
  · obtain ⟨x, hx, hx0⟩ := h h0A
    obtain ⟨z, hz⟩ := key hx0
    have hz1 : (0 : ℝ) < z := by linarith [hx.1]
    have hz2 : (z : ℝ) < 1 := by linarith [hx.2]
    have : 0 < z := by exact_mod_cast hz1
    have : z < 1 := by exact_mod_cast hz2
    omega
  · rcases h h2A with ⟨y, hy, hys⟩ | ⟨y, hy, hys⟩
    · obtain ⟨z, hz⟩ := key hys
      have hz1 : (z : ℝ) < 0 := by linarith [hy.2]
      have hz2 : (-1 : ℝ) < z := by linarith [hy.1]
      have : z < 0 := by exact_mod_cast hz1
      have : -1 < z := by exact_mod_cast hz2
      omega
    · obtain ⟨z, hz⟩ := key hys
      have hz1 : (0 : ℝ) < z := by linarith [hy.1]
      have hz2 : (z : ℝ) < 1 := by linarith [hy.2]
      have : 0 < z := by exact_mod_cast hz1
      have : z < 1 := by exact_mod_cast hz2
      omega

private lemma norm_curve_half : ‖curve (1 / 2)‖ = 1 := by
  rw [norm_curve, mul_one_div, sin_pi_div_two]
  norm_num [zig, cos_pi]

/-- No `1`-periodic continuous map, injective on `[0, 1)`, with the same image as `curve`, is
differentiable with nonzero derivative everywhere: at the parameter `t₁` of the origin, the
distance to the origin would grow like `‖p' t₁‖ |σ - t₁|`, which the oscillation of `curve`
forbids. -/
private lemma false_of_regular_param (p : ℝ → EuclideanSpace ℝ (Fin 3))
    (hper : ∀ t, p (t + 1) = p t) (hcont : Continuous p) (hinj : Set.InjOn p (Set.Ico 0 1))
    (hrange : Set.range p = Set.range curve)
    (hdiff : ∀ t, DifferentiableAt ℝ p t ∧ deriv p t ≠ 0) : False := by
  obtain ⟨t₁, ht₁⟩ : curve 0 ∈ Set.range p := by
    rw [hrange]
    exact Set.mem_range_self 0
  rw [curve_zero] at ht₁
  set u := deriv p t₁ with hu_def
  have hU : 0 < ‖u‖ := norm_pos_iff.mpr (hdiff t₁).2
  have hd : HasDerivAt p u t₁ := (hdiff t₁).1.hasDerivAt
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hd).def (show 0 < ‖u‖ / 4 by positivity))
  have hest : ∀ σ, |σ - t₁| < δ₀ → ‖p σ - (σ - t₁) • u‖ ≤ ‖u‖ / 4 * |σ - t₁| := by
    intro σ hσ
    have h := hball (show dist σ t₁ < δ₀ by rwa [Real.dist_eq])
    simpa only [ht₁, sub_zero, Real.norm_eq_abs] using h
  have hupper : ∀ σ, |σ - t₁| < δ₀ → ‖p σ‖ ≤ 5 * ‖u‖ / 4 * |σ - t₁| := by
    intro σ hσ
    have h1 := hest σ hσ
    have h2 := norm_sub_norm_le (p σ) ((σ - t₁) • u)
    rw [norm_smul, Real.norm_eq_abs] at h2
    nlinarith
  have hlower : ∀ σ, |σ - t₁| < δ₀ → 3 * ‖u‖ / 4 * |σ - t₁| ≤ ‖p σ‖ := by
    intro σ hσ
    have h1 := hest σ hσ
    have h2 := norm_sub_norm_le ((σ - t₁) • u) (p σ)
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev ((σ - t₁) • u) (p σ)] at h2
    nlinarith
  set δ := min δ₀ (min (1 / 4) (1 / (2 * ‖u‖))) with hδ_def
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min (by norm_num) (by positivity))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ14 : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδu : δ ≤ 1 / (2 * ‖u‖) := (min_le_right _ _).trans (min_le_right _ _)
  -- Away from `t₁`, the map `p` stays away from the origin.
  set K := Set.Icc (t₁ - 1 / 2) (t₁ - δ) ∪ Set.Icc (t₁ + δ) (t₁ + 1 / 2) with hK_def
  have hKc : IsClosed (p '' K) := ((isCompact_Icc.union isCompact_Icc).image hcont).isClosed
  have h0K : (0 : EuclideanSpace ℝ (Fin 3)) ∉ p '' K := by
    rintro ⟨σ, hσ, hpσ⟩
    obtain ⟨z, hz⟩ := exists_int_sub_eq_of_eq hper hinj (hpσ.trans ht₁.symm)
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz1 : (z : ℝ) < 0 := by linarith
      have hz2 : (-1 : ℝ) < z := by linarith
      have : z < 0 := by exact_mod_cast hz1
      have : -1 < z := by exact_mod_cast hz2
      omega
    · have hz1 : (0 : ℝ) < z := by linarith
      have hz2 : (z : ℝ) < 1 := by linarith
      have : 0 < z := by exact_mod_cast hz1
      have : z < 1 := by exact_mod_cast hz2
      omega
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl 0 h0K
  obtain ⟨s₁, s₂, hs₁, hs₁₂, hs₂, hpos, hsmall, hzig⟩ := exists_zigzag hρ
  -- The parameter `σ₂` of `curve s₂` for `p` is close to `t₁`.
  obtain ⟨σ₀, hσ₀⟩ : curve s₂ ∈ Set.range p := by
    rw [hrange]
    exact Set.mem_range_self s₂
  obtain ⟨σ₂, hσ₂I, hσ₂⟩ :=
    (show Function.Periodic p 1 from hper).exists_mem_Ico one_pos σ₀ (t₁ - 1 / 2)
  have hpσ₂ : p σ₂ = curve s₂ := hσ₂.symm.trans hσ₀
  have hσ₂K : σ₂ ∉ K := by
    intro hK
    have hball₂ : p σ₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ := by
      rw [Metric.mem_ball, dist_zero_right, hpσ₂]
      exact hsmall
    exact hρK hball₂ ⟨σ₂, hK, rfl⟩
  have hσ₂δ : |σ₂ - t₁| < δ := by
    rw [abs_lt]
    by_contra hcon
    apply hσ₂K
    rcases le_or_gt (σ₂ - t₁) (-δ) with h | h
    · exact Or.inl ⟨hσ₂I.1, by linarith⟩
    · refine Or.inr ⟨?_, by linarith [hσ₂I.2]⟩
      by_contra h'
      exact hcon ⟨h, by linarith⟩
  -- The arc of `p` from the origin to `curve s₂` stays close to the origin.
  set A := p '' Set.uIcc t₁ σ₂ with hA_def
  have hA : IsPreconnected A := isPreconnected_uIcc.image p hcont.continuousOn
  have hAsub : A ⊆ Set.range curve := hrange ▸ Set.image_subset_range p _
  have hbound : ∀ y ∈ A, ‖y‖ < ‖curve s₁‖ ∧ ‖y‖ < ‖curve (1 / 2)‖ := by
    rintro y ⟨σ, hσ, rfl⟩
    have hσt : |σ - t₁| ≤ |σ₂ - t₁| := Set.abs_sub_left_of_mem_uIcc hσ
    have h1 := hupper σ (by linarith)
    have h2 := hlower σ₂ (by linarith)
    rw [hpσ₂] at h2
    have h3 : ‖p σ‖ ≤ 5 / 3 * ‖curve s₂‖ := by nlinarith
    have h4 : ‖u‖ * |σ - t₁| ≤ 1 / 2 := by
      calc ‖u‖ * |σ - t₁| ≤ ‖u‖ * (1 / (2 * ‖u‖)) := by gcongr; linarith
        _ = 1 / 2 := by field_simp
    rw [norm_curve_half]
    constructor
    · linarith
    · nlinarith
  have h0A : curve 0 ∈ A := ⟨t₁, Set.left_mem_uIcc, by rw [ht₁, curve_zero]⟩
  have h2A : curve s₂ ∈ A := ⟨σ₂, Set.right_mem_uIcc, hpσ₂⟩
  have h1A : curve s₁ ∉ A := fun h => lt_irrefl _ (hbound _ h).1
  have h3A : curve (1 / 2) ∉ A := fun h => lt_irrefl _ (hbound _ h).2
  exact false_of_isPreconnected curve_add_one continuous_curve curve_injOn hA hAsub hs₁ hs₁₂
    hs₂ (by norm_num) h0A h2A h1A h3A

/-! ### The theorem -/

/--
**Fréchet's Problem 117 has a negative answer.** There is a $1$-periodic continuous
map $\gamma : \mathbb{R} \to \mathbb{R}^3$, injective on $[0, 1)$, that has an oriented
tangent at every parameter $t$, such that no $1$-periodic continuous map
$p : \mathbb{R} \to \mathbb{R}^3$ that is injective on $[0, 1)$ and has the same image
as $\gamma$ is differentiable at every $t$ with $p'(t) \neq 0$.

Here $\gamma$ has an oriented tangent at $t$ when there is a unit vector $v$ such that for
every $\varepsilon > 0$ there is $\delta > 0$ with
$\|w - \operatorname{sign}(s - t)\,\|w\|\,v\| \le \varepsilon \|w\|$, where
$w = \gamma(s) - \gamma(t)$, whenever $0 < |s - t| < \delta$: the secant directions tend to $v$
from the right and to $-v$ from the left.

Source: M. Fréchet, Problem 117 of the Scottish Book; in
general, no, by A. J. Ward, Fundamenta Mathematicae 28 (1937), cited in the
typescript addendum Ad 117. Ward also gives a representation whose
derivatives exist and are not all zero except on a null set of parameter
values whose points have Carathéodory measure zero.
-/
theorem frechet117_refuted : ¬ ScottishBookProblem117Claim := by
  intro h
  obtain ⟨p, hper, hcont, hinj, hrange, hdiff⟩ :=
    h curve curve_add_one continuous_curve curve_injOn hasTangentLineAt_curve
  exact false_of_regular_param p hper hcont hinj hrange hdiff

end MathlibExt.Geometry.ScottishBook117Wanted
