/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz

/-!
# Hayman Problem 6.22: Sharp Convexity Radius for Starlike Order One Half

We prove the existence of a greatest radius satisfying the convexity and Carathéodory conditions.

Source record `AMR-022-6022__2306022`.

## Clause inventory for AMR-022-6022, Hayman Problem 6.22

Question: largest radius where normalized starlike order one half implies convex,
with Carathéodory reformulation on circles.

- C1: unit disc as Metric.ball (0 : ℂ) 1, open.
- C2: f holomorphic on the unit disc via DifferentiableOn ℂ f.
- C3: normalization f 0 = 0 and deriv f 0 = 1 for z plus tail with n ≥ 2.
- C4: univalence via Set.InjOn f on the unit disc.
- C5: starlike order one half: (1/2 : ℝ) ≤ Re (z * f' / f) with z ≠ 0 and f z ≠ 0.
- C6: convexity on Metric.ball 0 r: 0 < Re (1 + z * f'' / f') with z ≠ 0 and f' ≠ 0.
- C7: radius r satisfies 0 < r and r ≤ 1, uniform over the class, one shared witness.
- C8: P holomorphic on the unit disc via DifferentiableOn, P 0 = 1, 0 < Re P on disc.
- C9: circle positivity strictly below r: for every s with 0 ≤ s and s < r,
  on Metric.sphere 0 s, 0 < Re ((P+1)/2 + z * P'/(P+1)).
  Strict min > 0 is asserted only below r, not attained at r; the union of
  smaller circles is the open disc, so this matches open-disc strength.
- C10: quantifiers: one shared r, all f in C2-C5, all P in C8, z in ball or sphere,
  s ranging over radii below r.
- C11: sharpness: r works for C6 and C9-below, and no larger r' ≤ 1 works for both
  below r' (negated conjunction, i.e. some class member fails at or above r).
  The value of r is not asserted.
-/

@[expose] public section

open Metric

namespace MathlibExt.Analysis.HaymanProblem622Wanted

/-- **Conjecture: a sharp radius of convexity for starlike functions of order 1/2.** Let
$\mathbb{D}$ be the open unit disc in $\mathbb{C}$. Call $f : \mathbb{C} \to \mathbb{C}$ a
normalized starlike function of order $1/2$ if $f$ is holomorphic and injective on $\mathbb{D}$,
$f(0) = 0$, $f'(0) = 1$, and $\operatorname{Re}(z f'(z)/f(z)) \ge 1/2$ for every $z \in \mathbb{D}$
with $z \ne 0$ and $f(z) \ne 0$. Call $P : \mathbb{C} \to \mathbb{C}$ a Carathéodory function if
$P$ is holomorphic on $\mathbb{D}$, $P(0) = 1$, and $\operatorname{Re} P(z) > 0$ for every
$z \in \mathbb{D}$. Call a real number $\rho$ a good radius if
$\operatorname{Re}(1 + z f''(z)/f'(z)) > 0$ for every normalized starlike function $f$ of order
$1/2$ and every $z$ with $0 < |z| < \rho$ and $f'(z) \ne 0$, and
$\operatorname{Re}\big((P(z) + 1)/2 + z P'(z)/(P(z) + 1)\big) > 0$ for every Carathéodory
function $P$ and every $z$ with $|z| < \rho$. The conjecture is the proposition that there is a
good radius $r$ with $0 < r \le 1$ such that no real number $r'$ with $r < r' \le 1$ is a good
radius.

This is Problem 6.22 of Hayman, Research Problems in Function Theory (2018), source record
AMR-022-6022.

Source: https://arxiv.org/abs/1809.07200 -/
def conjecture : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    ((∀ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        f 0 = 0 →
        deriv f 0 = 1 →
        Set.InjOn f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), z ≠ 0 → f z ≠ 0 →
          (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) →
        ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → deriv f z ≠ 0 →
          0 < (1 + z * deriv (deriv f) z / deriv f z).re) ∧
      (∀ P : ℂ → ℂ,
        DifferentiableOn ℂ P (Metric.ball (0 : ℂ) (1 : ℝ)) →
        P 0 = 1 →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), 0 < (P z).re) →
        ∀ s : ℝ, 0 ≤ s → s < r → ∀ z ∈ Metric.sphere (0 : ℂ) s,
          0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re)) ∧
    ∀ r' : ℝ, r < r' → r' ≤ 1 →
      ¬ ((∀ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        f 0 = 0 →
        deriv f 0 = 1 →
        Set.InjOn f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), z ≠ 0 → f z ≠ 0 →
          (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) →
        ∀ z ∈ Metric.ball (0 : ℂ) r', z ≠ 0 → deriv f z ≠ 0 →
          0 < (1 + z * deriv (deriv f) z / deriv f z).re) ∧
      (∀ P : ℂ → ℂ,
        DifferentiableOn ℂ P (Metric.ball (0 : ℂ) (1 : ℝ)) →
        P 0 = 1 →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), 0 < (P z).re) →
        ∀ s : ℝ, 0 ≤ s → s < r' → ∀ z ∈ Metric.sphere (0 : ℂ) s,
          0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re))

private lemma halfPlane_pos {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hF₀ : F 0 = 1) (hRe : ∀ w ∈ ball 0 1, (1 / 2 : ℝ) ≤ (F w).re)
    {z : ℂ} (hz : ‖z‖ < 1 / 8) :
    0 < (F z + z * deriv F z / F z).re := by
  let q : ℂ → ℂ := fun w ↦ (F w - 1) / F w
  have hne : ∀ w ∈ ball 0 1, F w ≠ 0 := by
    intro w hw he
    have := hRe w hw
    norm_num [he] at this
  have hq : DifferentiableOn ℂ q (ball 0 1) := (hF.sub_const 1).div hF hne
  have hq₀ : q 0 = 0 := by simp [q, hF₀]
  have hmaps : Set.MapsTo q (ball 0 1) (closedBall 0 1) := by
    intro w hw
    have hsq : ‖F w - 1‖ ^ 2 ≤ ‖F w‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, sub_zero]
      nlinarith [hRe w hw]
    have hnorm : ‖F w - 1‖ ≤ ‖F w‖ := by
      nlinarith [norm_nonneg (F w - 1), norm_nonneg (F w)]
    rw [mem_closedBall_zero_iff, show q w = (F w - 1) / F w from rfl, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr (hne w hw)), one_mul]
    exact hnorm
  have hz₁ : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
  have hqz : ‖q z‖ ≤ ‖z‖ := Complex.norm_le_norm_of_mapsTo_ball hq hmaps hq₀
    (mem_ball_zero_iff.mp hz₁)
  -- Use a ball about z contained in the unit disc for the derivative estimate.
  have hsub : ball z (1 / 2) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    have hw' := (dist_triangle w z 0).trans_lt (add_lt_add
      (mem_ball.mp hw) (by simpa using hz : dist z 0 < 1 / 8))
    exact mem_ball.mpr (hw'.trans (by norm_num))
  have hq' : ‖deriv q z‖ ≤ 4 := by
    have hm : Set.MapsTo q (ball z (1 / 2)) (closedBall (q z) 2) := by
      intro w hw
      apply mem_closedBall.mpr
      calc
        dist (q w) (q z) ≤ dist (q w) 0 + dist (q z) 0 := dist_triangle_right _ _ _
        _ ≤ 1 + 1 := add_le_add (mem_closedBall.mp (hmaps (hsub hw)))
          (mem_closedBall.mp (hmaps hz₁))
        _ = 2 := by norm_num
    have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hq.mono hsub) hm (by norm_num)
    norm_num at hd
    exact hd
  have hden : 1 - ‖q z‖ ≤ ‖1 - q z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (q z)
  have hnum : ‖q z + z * deriv q z‖ < ‖1 - q z‖ := by
    have hmul : ‖z‖ * ‖deriv q z‖ ≤ ‖z‖ * 4 :=
      mul_le_mul_of_nonneg_left hq' (norm_nonneg z)
    have hadd := norm_add_le (q z) (z * deriv q z)
    rw [norm_mul] at hadd
    linarith
  have hdz := (hF.differentiableAt (isOpen_ball.mem_nhds hz₁)).hasDerivAt
  have hqd : deriv q z = deriv F z / F z ^ 2 := by
    calc
      deriv q z = (deriv F z * F z - (F z - 1) * deriv F z) / F z ^ 2 :=
        ((hdz.sub_const 1).div hdz (hne z hz₁)).deriv
      _ = _ := by ring
  have hform : F z + z * deriv F z / F z - 1 = (q z + z * deriv q z) / (1 - q z) := by
    rw [hqd]
    have hqden : 1 - q z = (F z)⁻¹ := by
      dsimp [q]
      field_simp [hne z hz₁]
      ring
    rw [hqden]
    dsimp [q]
    field_simp [hne z hz₁]
    ring
  have hnorm : ‖F z + z * deriv F z / F z - 1‖ < 1 := by
    rw [hform, norm_div, div_lt_iff₀ ((norm_nonneg _).trans_lt hnum), one_mul]
    exact hnum
  have hre := Complex.abs_re_le_norm (F z + z * deriv F z / F z - 1)
  have hneg := neg_le_abs (F z + z * deriv F z / F z - 1).re
  simp only [Complex.sub_re, Complex.one_re] at hre hneg
  linarith

private lemma starlike_pos {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf₀ : f 0 = 0) (hf'₀ : deriv f 0 = 1) (hinj : Set.InjOn f (ball 0 1))
    (hstar : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → f z ≠ 0 →
      (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) {z : ℂ} (hz : ‖z‖ < 1 / 8)
    (hf'z : deriv f z ≠ 0) : 0 < (1 + z * deriv (deriv f) z / deriv f z).re := by
  have h₀ : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  -- The divided slope removes the singularity of f(z) / z at the origin.
  let g := dslope f 0
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds h₀)).mpr hf
  have hg₀ : g 0 = 1 := (dslope_same f 0).trans hf'₀
  have hfactor (w : ℂ) : w * g w = f w := by
    simpa [g, smul_eq_mul] using sub_smul_dslope_of_zero hf₀ w
  have hfne (w : ℂ) (hw : w ∈ ball 0 1) (hw₀ : w ≠ 0) : f w ≠ 0 := by
    intro he
    exact hw₀ (hinj hw h₀ (he.trans hf₀.symm))
  have hgne (w : ℂ) (hw : w ∈ ball 0 1) : g w ≠ 0 := by
    rcases eq_or_ne w 0 with rfl | hw₀
    · simp [hg₀]
    · exact right_ne_zero_of_mul (hfactor w ▸ hfne w hw hw₀)
  let F : ℂ → ℂ := fun w ↦ deriv f w / g w
  have hf' := hf.deriv isOpen_ball
  have hF : DifferentiableOn ℂ F (ball 0 1) := hf'.div hg hgne
  have hF₀ : F 0 = 1 := by simp [F, hf'₀, hg₀]
  have hRe (w : ℂ) (hw : w ∈ ball 0 1) : (1 / 2 : ℝ) ≤ (F w).re := by
    rcases eq_or_ne w 0 with rfl | hw₀
    · norm_num [hF₀]
    · have he : F w = w * deriv f w / f w := by
        dsimp [F]
        rw [← hfactor w, mul_div_mul_left _ _ hw₀]
      rw [he]
      exact hstar w hw hw₀ (hfne w hw hw₀)
  have hz₁ : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
  have hzf := isOpen_ball.mem_nhds hz₁
  have hgd := (hg.differentiableAt hzf).hasDerivAt
  have hf'prod : deriv f z = g z + z * deriv g z := by
    have hd := ((hasDerivAt_id z).mul hgd).deriv
    change deriv (fun w ↦ w * g w) z = _ at hd
    rw [funext hfactor] at hd
    simpa using hd
  have hFd := ((hf'.differentiableAt hzf).hasDerivAt.div hgd (hgne z hz₁)).deriv
  have he : F z + z * deriv F z / F z = 1 + z * deriv (deriv f) z / deriv f z := by
    calc
      _ = (deriv f z - z * deriv g z) / g z + z * deriv (deriv f) z / deriv f z := by
        change deriv f z / g z + z * deriv (deriv f / g) z / (deriv f z / g z) = _
        rw [hFd]
        field_simp [hf'z, hgne z hz₁]
        ring
      _ = _ := by
        rw [sub_eq_iff_eq_add.mpr hf'prod, div_self (hgne z hz₁)]
  simpa only [he] using halfPlane_pos hF hF₀ hRe hz

private lemma caratheodory_pos {P : ℂ → ℂ} (hP : DifferentiableOn ℂ P (ball 0 1))
    (hP₀ : P 0 = 1) (hRe : ∀ z ∈ ball (0 : ℂ) 1, 0 < (P z).re)
    {z : ℂ} (hz : ‖z‖ < 1 / 8) :
    0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re := by
  let F : ℂ → ℂ := fun w ↦ (P w + 1) / 2
  have hF : DifferentiableOn ℂ F (ball 0 1) := (hP.add_const 1).div_const 2
  have hF₀ : F 0 = 1 := by norm_num [F, hP₀]
  have hhalf (w : ℂ) (hw : w ∈ ball 0 1) : (1 / 2 : ℝ) ≤ (F w).re := by
    simp [F]
    linarith [hRe w hw]
  have hFd : deriv F z = deriv P z / 2 := by
    simp [F, deriv_div_const, deriv_add_const]
  have h := halfPlane_pos hF hF₀ hhalf hz
  rw [hFd] at h
  dsimp [F] at h
  rwa [← mul_div_assoc, div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0)] at h

/--
**A sharp radius of convexity for starlike functions of order 1/2 exists.** Let $\mathbb{D}$ be
the open unit disc in $\mathbb{C}$. Call $f : \mathbb{C} \to \mathbb{C}$ a normalized starlike
function of order $1/2$ if $f$ is holomorphic and injective on $\mathbb{D}$, $f(0) = 0$,
$f'(0) = 1$, and $\operatorname{Re}(z f'(z)/f(z)) \ge 1/2$ for every $z \in \mathbb{D}$ with
$z \ne 0$ and $f(z) \ne 0$. Call $P : \mathbb{C} \to \mathbb{C}$ a Carathéodory function if $P$
is holomorphic on $\mathbb{D}$, $P(0) = 1$, and $\operatorname{Re} P(z) > 0$ for every
$z \in \mathbb{D}$. Call a real number $\rho$ a good radius if
$\operatorname{Re}(1 + z f''(z)/f'(z)) > 0$ for every normalized starlike function $f$ of order
$1/2$ and every $z$ with $0 < |z| < \rho$ and $f'(z) \ne 0$, and
$\operatorname{Re}\big((P(z) + 1)/2 + z P'(z)/(P(z) + 1)\big) > 0$ for every Carathéodory
function $P$ and every $z$ with $|z| < \rho$. Then there is a good radius $r$ with
$0 < r \le 1$ such that no real $r'$ with $r < r' \le 1$ is a good radius.

MacGregor (Proc. AMS 14 (1963) 71-76, Theorem 1) proved that the sharp radius of convexity of
normalized starlike functions of order $1/2$ is $\sqrt{2\sqrt{3}-3} \approx 0.681$; this value is
such a radius $r$. The statement above does not assert the value of $r$.

Source: B. Bhowmik and
S. Biswas, Radius of convexity of certain classes of functions defined by convolution, preprint
(2026), arXiv:2606.20872, https://arxiv.org/abs/2606.20872. Moved from
`OpenConjectures/Analysis/HaymanProblem622`.
-/
public theorem conjecture_holds : conjecture := by
  let good (r : ℝ) : Prop :=
    (∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f (ball 0 1) → f 0 = 0 → deriv f 0 = 1 →
      Set.InjOn f (ball 0 1) →
      (∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → f z ≠ 0 →
        (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) →
      ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → deriv f z ≠ 0 →
        0 < (1 + z * deriv (deriv f) z / deriv f z).re) ∧
    (∀ P : ℂ → ℂ,
      DifferentiableOn ℂ P (ball 0 1) → P 0 = 1 →
      (∀ z ∈ ball (0 : ℂ) 1, 0 < (P z).re) →
      ∀ s : ℝ, 0 ≤ s → s < r → ∀ z ∈ sphere (0 : ℂ) s,
        0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re)
  change ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ good r ∧ ∀ r' : ℝ, r < r' → r' ≤ 1 → ¬ good r'
  let S : Set ℝ := {r | r ≤ 1 ∧ good r}
  have hsmall : (1 / 8 : ℝ) ∈ S := by
    refine ⟨by norm_num, ?_, ?_⟩
    · intro f hf hf₀ hf'₀ hinj hstar z hz _ hf'z
      exact starlike_pos hf hf₀ hf'₀ hinj hstar (mem_ball_zero_iff.mp hz) hf'z
    · intro P hP hP₀ hRe s _ hs z hz
      exact caratheodory_pos hP hP₀ hRe ((mem_sphere_zero_iff_norm.mp hz).trans_lt hs)
  have hS : S.Nonempty := ⟨_, hsmall⟩
  have hbounded : BddAbove S := ⟨1, fun _ hr ↦ hr.1⟩
  refine ⟨sSup S, (by norm_num : (0 : ℝ) < 1 / 8).trans_le (le_csSup hbounded hsmall),
    csSup_le hS (fun _ hr ↦ hr.1), ⟨?_, ?_⟩, ?_⟩
  · intro f hf hf₀ hf'₀ hinj hstar z hz hz₀ hf'z
    obtain ⟨r, hr, hzr⟩ := exists_lt_of_lt_csSup hS (mem_ball_zero_iff.mp hz)
    exact hr.2.1 f hf hf₀ hf'₀ hinj hstar z (mem_ball_zero_iff.mpr hzr) hz₀ hf'z
  · intro P hP hP₀ hRe s hs₀ hs z hz
    obtain ⟨r, hr, hsr⟩ := exists_lt_of_lt_csSup hS hs
    exact hr.2.2 P hP hP₀ hRe s hs₀ hsr z hz
  · intro r' hr' hr'₁ hg
    exact (not_lt_of_ge (le_csSup hbounded ⟨hr'₁, hg⟩)) hr'

end MathlibExt.Analysis.HaymanProblem622Wanted
