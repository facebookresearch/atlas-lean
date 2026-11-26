/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.ResidueTheorem
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Residue theorem on a disc

`MathlibExt.Analysis.Complex.ResidueTheoremWanted.residueTheorem_closedBall` states that the
circle integral of a function holomorphic on a closed disc except at finitely many isolated
points is the sum of its circle integrals around those points. The proof applies the residue
theorem for curves in an open set (`Complex.curveIntegral_eq_sum_circleIntegral`) to a
concentric circle of slightly smaller radius, and then moves the outer integral back out to
the boundary circle by Cauchy's theorem on the annulus between the two circles.
-/

set_option autoImplicit false

open scoped BigOperators

open Complex

namespace MathlibExt.Analysis.Complex.ResidueTheoremWanted

-- The circle-integrability hypotheses are part of the stated theorem but are not needed
-- for the proof: the curve-integral and annulus arguments below use only differentiability.
set_option linter.unusedVariables false in
/--
**Residue theorem on a disc.** Let $c\in\mathbb{C}$ and $R>0$, and let $S$ be a finite set of
points of the open disc $\{z:|z-c|<R\}$. For each $s\in S$ let $r_s>0$ be such that the closed
disc $\{z:|z-s|\le r_s\}$ lies in $\{z:|z-c|<R\}$ and contains no point of $S$ other than $s$.
Let $f:\mathbb{C}\to\mathbb{C}$ be complex differentiable on $\{z:|z-c|\le R\}\setminus S$ and
integrable on the circle $|z-c|=R$ and on each circle $|z-s|=r_s$. Then, with all circles
oriented counterclockwise,
$$\oint_{|z-c|=R} f(z)\,dz=\sum_{s\in S}\oint_{|z-s|=r_s} f(z)\,dz.$$

Each integral on the right is $2\pi i$ times the residue of $f$ at $s$.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "residue theorem"; L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §5.1
(the residue theorem).
-/
public theorem residueTheorem_closedBall
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ} {S : Finset ℂ} {rad : ℂ → ℝ}
    (hS : ∀ s ∈ S, s ∈ Metric.ball c R)
    (hrad : ∀ s ∈ S, 0 < rad s ∧ Metric.closedBall s (rad s) ⊆ Metric.ball c R ∧
      ∀ s' ∈ S, s' ≠ s → s' ∉ Metric.closedBall s (rad s))
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R \ ↑S))
    (hint : CircleIntegrable f c R)
    (hintS : ∀ s ∈ S, CircleIntegrable f s (rad s)) :
    (∮ z in C(c, R), f z) = ∑ s ∈ S, ∮ z in C(s, rad s), f z := by
  classical
  have hex : ∀ T : Finset ℂ, (∀ s ∈ T, s ∈ Metric.ball c R) →
      ∃ R₁ : ℝ, 0 < R₁ ∧ R₁ < R ∧ ∀ s ∈ T, dist s c < R₁ := by
    intro T
    induction T using Finset.induction with
    | empty =>
      intro _
      exact ⟨R / 2, by linarith, by linarith, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haR : dist a c < R := Metric.mem_ball.1 (hT a (Finset.mem_insert_self a T))
      obtain ⟨R₁, hR₁pos, hR₁R, hdist⟩ := ih fun s hs =>
        hT s (Finset.mem_insert_of_mem hs)
      have hle1 : dist a c ≤ max (dist a c) R₁ := le_max_left _ _
      have hle2 : R₁ ≤ max (dist a c) R₁ := le_max_right _ _
      have hmaxR : max (dist a c) R₁ < R := max_lt haR hR₁R
      refine ⟨(max (dist a c) R₁ + R) / 2, by linarith, by linarith, ?_⟩
      intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hsT
      · linarith
      · have h2 := hdist s hsT
        linarith
  obtain ⟨R₁, hR₁pos, hR₁R, hdist⟩ := hex S hS
  set Ω : Set ℂ := Metric.ball c R \ ↑S with hΩdef
  have hΩopen : IsOpen Ω := Metric.isOpen_ball.sdiff S.finite_toSet.isClosed
  have hfΩ : DifferentiableOn ℂ f Ω :=
    hf.mono (Set.sdiff_subset_sdiff_left Metric.ball_subset_closedBall)
  have hγΩ : Set.range (circlePath c R₁) ⊆ Ω := by
    intro w hw
    have hw' : w ∈ Metric.sphere c R₁ := by
      have h := Complex.range_circlePath_subset c R₁ hw
      rwa [abs_of_pos hR₁pos] at h
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Metric.mem_sphere.1 hw']
      exact hR₁R
    · intro hwS
      have h1 := hdist w (Finset.mem_coe.1 hwS)
      rw [Metric.mem_sphere.1 hw'] at h1
      exact lt_irrefl R₁ h1
  have hF : ∀ a ∈ S, Metric.sphere a |rad a| ⊆ Ω := by
    intro a ha w hw
    rw [abs_of_pos (hrad a ha).1] at hw
    have hwball : w ∈ Metric.closedBall a (rad a) :=
      Metric.mem_closedBall.2 (Metric.mem_sphere.1 hw).le
    refine ⟨(hrad a ha).2.1 hwball, ?_⟩
    intro hwS
    rcases eq_or_ne w a with rfl | hne
    · rw [Metric.mem_sphere, dist_self] at hw
      exact (hrad w ha).1.ne' hw.symm
    · exact (hrad a ha).2.2 w (Finset.mem_coe.1 hwS) hne hwball
  have hhom : ∀ z ∉ Ω, Complex.windingNumber (circlePath c R₁) z =
      ∑ a ∈ S, Complex.windingNumber (circlePath a (rad a)) z := by
    intro z hz
    by_cases hzS : z ∈ S
    · have hzball : z ∈ Metric.ball c R₁ := Metric.mem_ball.2 (hdist z hzS)
      rw [Complex.windingNumber_circlePath_of_mem_ball hzball]
      have hsum : ∑ a ∈ S, Complex.windingNumber (circlePath a (rad a)) z =
          Complex.windingNumber (circlePath z (rad z)) z := by
        refine Finset.sum_eq_single z ?_ ?_
        · intro a ha hne
          refine Complex.windingNumber_circlePath_of_notMem_closedBall
            (hrad a ha).1.le ?_
          exact (hrad a ha).2.2 z hzS (Ne.symm hne)
        · intro hznot
          exact absurd hzS hznot
      rw [hsum, Complex.windingNumber_circlePath_of_mem_ball
        (Metric.mem_ball_self (hrad z hzS).1)]
    · have hzball : z ∉ Metric.ball c R := by
        intro hzb
        exact hz ⟨hzb, fun h => hzS (Finset.mem_coe.1 h)⟩
      have hzclosed : z ∉ Metric.closedBall c R₁ := by
        intro hzc
        exact hzball (Metric.mem_ball.2
          (lt_of_le_of_lt (Metric.mem_closedBall.1 hzc) hR₁R))
      rw [Complex.windingNumber_circlePath_of_notMem_closedBall hR₁pos.le hzclosed]
      refine (Finset.sum_eq_zero fun a ha => ?_).symm
      refine Complex.windingNumber_circlePath_of_notMem_closedBall
        (hrad a ha).1.le ?_
      intro hza
      exact hzball ((hrad a ha).2.1 hza)
  have key := Complex.curveIntegral_eq_sum_circleIntegral hΩopen
    (Complex.isPiecewiseC1_circlePath c R₁) hγΩ hF hhom hfΩ
  rw [Complex.curveIntegral_circlePath] at key
  have hAnn : (∮ z in C(c, R), f z) = ∮ z in C(c, R₁), f z := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hR₁pos
      hR₁R.le S.finite_toSet.countable ?_ ?_
    · exact hf.continuousOn.mono fun w hw => by
        refine ⟨hw.1, fun hwS => ?_⟩
        have h1 := hdist w (Finset.mem_coe.1 hwS)
        exact hw.2 (Metric.mem_ball.2 h1)
    · intro z hz
      exact hfΩ.differentiableAt (hΩopen.mem_nhds ⟨hz.1.1, hz.2⟩)
  exact hAnn.trans key

end MathlibExt.Analysis.Complex.ResidueTheoremWanted
