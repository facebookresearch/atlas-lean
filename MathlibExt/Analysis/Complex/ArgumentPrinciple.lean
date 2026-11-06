/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Argument principle on a disc

Proves `Wanted` entry `argumentPrinciple_closedBall`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.ArgumentPrinciple

private theorem divisor_closedBall_support_subset_ball
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hbd : ∀ z ∈ Metric.sphere c R,
      MeromorphicOn.divisor f (Metric.closedBall c R) z = 0) :
    (MeromorphicOn.divisor f (Metric.closedBall c R)).support ⊆ Metric.ball c R := by
  intro u hu
  have hUne : (MeromorphicOn.divisor f (Metric.closedBall c R)) u ≠ 0 :=
    Function.mem_support.mp hu
  have hU : u ∈ Metric.closedBall c R :=
    (MeromorphicOn.divisor f (Metric.closedBall c R)).supportWithinDomain hu
  rw [Metric.mem_closedBall] at hU
  by_contra hball
  rw [Metric.mem_ball, not_lt] at hball
  have hsph : u ∈ Metric.sphere c R := Metric.mem_sphere.mpr (le_antisymm hU hball)
  exact hUne (hbd u hsph)

private theorem divisor_ball_eq_divisor_closedBall
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (hbd : ∀ z ∈ Metric.sphere c R,
      MeromorphicOn.divisor f (Metric.closedBall c R) z = 0) :
    ⇑(MeromorphicOn.divisor f (Metric.ball c R))
      = ⇑(MeromorphicOn.divisor f (Metric.closedBall c R)) := by
  ext z
  by_cases hz : z ∈ Metric.ball c R
  · have hzU : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz
    rw [MeromorphicOn.divisor_apply
      (fun x hx => hf x (Metric.ball_subset_closedBall hx)) hz,
      MeromorphicOn.divisor_apply hf hzU]
  · by_cases hzU : z ∈ Metric.closedBall c R
    · have hle : dist z c ≤ R := Metric.mem_closedBall.mp hzU
      have hge : R ≤ dist z c :=
        not_lt.mp (fun h => hz (Metric.mem_ball.mpr h))
      have hsph : z ∈ Metric.sphere c R := Metric.mem_sphere.mpr (le_antisymm hle hge)
      rw [hbd z hsph]
      exact (MeromorphicOn.divisor f (Metric.ball c R)).apply_eq_zero_of_notMem hz
    · rw [(MeromorphicOn.divisor f (Metric.ball c R)).apply_eq_zero_of_notMem hz,
        (MeromorphicOn.divisor f (Metric.closedBall c R)).apply_eq_zero_of_notMem hzU]

/-- **Argument principle on a closed disc.** Let $c \in \mathbb{C}$, $R > 0$, and let
$f : \mathbb{C} \to \mathbb{C}$ be meromorphic on the closed disc $|z - c| \le R$ with finite order
at every point of that disc (so $f$ vanishes identically near no point). Suppose the order of $f$
is zero at every point of the circle $|z - c| = R$. Then the integral of $f'/f$ over the circle
$|z - c| = R$, traversed once counterclockwise, equals $2\pi i$ times the sum of the orders of $f$
at the points of the open disc $|z - c| < R$ (zeros counted positively and poles negatively, with
multiplicity). -/
theorem argumentPrinciple_closedBall_general
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (hf_top : ∀ z ∈ Metric.closedBall c R,
      meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ z ∈ Metric.sphere c R,
      MeromorphicOn.divisor f (Metric.closedBall c R) z = 0) :
    (∮ z in C(c, R), logDeriv f z) =
      2 * Real.pi * Complex.I *
        ↑(∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRle : 0 ≤ R := le_of_lt hR
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall c R)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport
      (isCompact_closedBall c R)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ :=
    hf.extract_zeros_poles (fun u => hf_top u u.2) hfin
  have hsub : (MeromorphicOn.divisor f (Metric.closedBall c R)).support
      ⊆ Metric.ball c R :=
    divisor_closedBall_support_subset_ball hbd
  have hballEq : ⇑(MeromorphicOn.divisor f (Metric.ball c R))
      = ⇑(MeromorphicOn.divisor f (Metric.closedBall c R)) :=
    divisor_ball_eq_divisor_closedBall hf hbd
  set D : Function.locallyFinsuppWithin (Metric.closedBall c R) ℤ :=
    MeromorphicOn.divisor f (Metric.closedBall c R) with hDdef
  set Rr : ℂ → ℂ := (∏ᶠ u, (· - u) ^ (D u)) with hRrdef
  set H : ℂ → ℂ := (fun z =>
    (∑ u ∈ hfin.toFinset, ((D u : ℂ) * (z - u)⁻¹)) + logDeriv g z) with hHdef
  have hfg' : f =ᶠ[Filter.codiscreteWithin (Metric.closedBall c R)] (Rr * g) := by
    refine hfg.trans (Filter.Eventually.of_forall fun y => ?_)
    exact smul_eq_mul _ _
  have hRr_mero : MeromorphicOn Rr (Metric.closedBall c R) :=
    (Function.FactorizedRational.meromorphicNFOn _ _).meromorphicOn
  have hmem_ball : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball c R := by
    intro u hu
    exact hsub ((Set.Finite.mem_toFinset hfin).mp hu)
  have hmulsub : Function.mulSupport (fun u => (fun x => x - u) ^ (D u))
      ⊆ ↑(hfin.toFinset) := by
    rw [Function.FactorizedRational.mulSupport]
    intro u hu
    exact Finset.mem_coe.mpr
      ((Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mp hu))
  have hRr_eq : Rr = ∏ u ∈ hfin.toFinset, (fun x => x - u) ^ (D u) := by
    rw [hRrdef, finprod_eq_prod_of_mulSupport_subset _ hmulsub]
  have hS_sub : Function.support ⇑D ⊆ ↑(hfin.toFinset) := by
    intro u hu
    have huS : u ∈ D.support := hu
    exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset hfin).mpr huS)
  have hpp : Preperfect (Metric.closedBall c R) := by
    rw [← closure_ball c hRne]
    exact (Metric.isOpen_ball.perfect_closure).2
  have hEq : logDeriv f =ᶠ[Filter.codiscreteWithin (Metric.sphere c R)] H := by
    rw [eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE]
    intro x hx
    have hxU : x ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hx
    have hDx : D x = 0 := hbd x hx
    have hmat_f1 : MeromorphicAt (Rr * g) x :=
      MeromorphicAt.mul (hRr_mero x hxU) ((hg_an x hxU).meromorphicAt)
    have hrig : f =ᶠ[nhdsWithin x {x}ᶜ] (Rr * g) :=
      (hf x hxU).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        hmat_f1 hxU hpp hfg'
    have hsm : logDeriv (Rr * g) =ᶠ[nhds x] H := by
      have hg_an_ev : ∀ᶠ y in nhds x, AnalyticAt ℂ g y :=
        (hg_an x hxU).eventually_analyticAt
      have hg_ne_ev : ∀ᶠ y in nhds x, g y ≠ 0 :=
        (hg_an x hxU).continuousAt.eventually_ne (hg_ne ⟨x, hxU⟩)
      have hxS : x ∉ (↑(hfin.toFinset) : Set ℂ) := by
        intro hcon
        rw [Finset.mem_coe] at hcon
        have hsup : x ∈ D.support := (Set.Finite.mem_toFinset hfin).mp hcon
        exact (Function.mem_support.mp hsup) hDx
      have hclosed : IsClosed (↑(hfin.toFinset) : Set ℂ) :=
        (Finset.finite_toSet _).isClosed
      have hS_ev : ∀ᶠ y in nhds x, y ∉ (↑(hfin.toFinset) : Set ℂ) :=
        Filter.eventually_of_mem (hclosed.compl_mem_nhds hxS) (fun y hy => hy)
      filter_upwards [hg_an_ev, hg_ne_ev, hS_ev] with y hgy hgyne hyS
      have hyS' : y ∉ hfin.toFinset := fun h => hyS (Finset.mem_coe.mpr h)
      have hRr_an : AnalyticAt ℂ Rr y := by
        rw [hRrdef]
        apply analyticAt_finprod
        intro u
        by_cases hu : u ∈ hfin.toFinset
        · have hne : y ≠ u := by
            rintro rfl
            exact hyS' hu
          exact ((analyticAt_id.sub analyticAt_const).fun_zpow (sub_ne_zero.mpr hne))
        · have hDu : D u = 0 := by
            by_contra hne
            exact hu ((Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hne))
          simp only [hDu, zpow_zero]
          exact analyticAt_const
      have hRr_ne : Rr y ≠ 0 := by
        rw [hRr_eq, Finset.prod_apply, Finset.prod_ne_zero_iff]
        intro u hu
        have hne : y ≠ u := by
          rintro rfl
          exact hyS' hu
        exact zpow_ne_zero _ (sub_ne_zero.mpr hne)
      have hRr_ld : logDeriv Rr y
          = ∑ u ∈ hfin.toFinset, ((D u : ℂ) * (y - u)⁻¹) := by
        have h1 : ∀ u ∈ hfin.toFinset, ((fun x => x - u) ^ (D u)) y ≠ 0 := by
          intro u hu
          have hne : y ≠ u := by
            rintro rfl
            exact hyS' hu
          exact zpow_ne_zero _ (sub_ne_zero.mpr hne)
        have h2 : ∀ u ∈ hfin.toFinset,
            DifferentiableAt ℂ ((fun x => x - u) ^ (D u)) y := by
          intro u hu
          have hne : y ≠ u := by
            rintro rfl
            exact hyS' hu
          exact ((analyticAt_id.sub analyticAt_const).fun_zpow
            (sub_ne_zero.mpr hne)).differentiableAt
        rw [hRr_eq, logDeriv_prod h1 h2]
        apply Finset.sum_congr rfl
        intro u hu
        have hdfy : DifferentiableAt ℂ (fun x : ℂ => x - u) y :=
          (analyticAt_id.sub analyticAt_const).differentiableAt
        have hzp := logDeriv_fun_zpow hdfy (D u)
        rw [show logDeriv ((fun x : ℂ => x - u) ^ (D u)) y
            = logDeriv (fun x => (fun x : ℂ => x - u) x ^ (D u)) y from rfl, hzp]
        congr 1
        have hderiv : deriv (fun x : ℂ => x - u) y = 1 :=
          ((hasDerivAt_id y).sub_const u).deriv
        rw [logDeriv_apply, hderiv, one_div]
      change logDeriv (Rr * g) y
        = (∑ u ∈ hfin.toFinset, ((D u : ℂ) * (y - u)⁻¹)) + logDeriv g y
      rw [logDeriv_mul y hRr_ne hgyne hRr_an.differentiableAt hgy.differentiableAt,
        hRr_ld]
    have hlog : logDeriv f =ᶠ[nhdsWithin x {x}ᶜ] logDeriv (Rr * g) :=
      logDeriv_congr_nhdsNE hrig
    filter_upwards [hlog, hsm.filter_mono nhdsWithin_le_nhds] with y h1 h2 _
    exact h1.trans h2
  have hint_eq : (∮ z in C(c, R), logDeriv f z)
      = (∮ z in C(c, R),
        ((∑ u ∈ hfin.toFinset, ((D u : ℂ) * (z - u)⁻¹)) + logDeriv g z)) :=
    circleIntegral.circleIntegral_congr_codiscreteWithin (by rwa [abs_of_pos hR]) hRne
  have hInt_term : ∀ u ∈ hfin.toFinset,
      CircleIntegrable (fun z => ((D u : ℂ) * (z - u)⁻¹)) c R := by
    intro u hu
    have huB : u ∈ Metric.ball c R := hmem_ball u hu
    have huS : u ∉ Metric.sphere c |R| := by
      rw [abs_of_pos hR]
      intro hcon
      have h1 : dist u c = R := Metric.mem_sphere.mp hcon
      have h2 : dist u c < R := Metric.mem_ball.mp huB
      exact (ne_of_lt h2) h1
    have hbase : CircleIntegrable (fun z => (z - u)⁻¹) c R :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr huS)
    have hsmul : (fun z => ((D u : ℂ) * (z - u)⁻¹))
        = ((D u : ℂ)) • (fun z => (z - u)⁻¹) := by
      funext z
      exact (smul_eq_mul _ _).symm
    rw [hsmul]
    exact hbase.const_smul
  have hInt_sum : CircleIntegrable
      (fun z => ∑ u ∈ hfin.toFinset, ((D u : ℂ) * (z - u)⁻¹)) c R := by
    have h := CircleIntegrable.sum (hfin.toFinset) (fun u hu => hInt_term u hu)
    have hfun : (∑ i ∈ hfin.toFinset, (fun z => ((D i : ℂ) * (z - i)⁻¹)))
        = (fun z => ∑ u ∈ hfin.toFinset, ((D u : ℂ) * (z - u)⁻¹)) :=
      funext fun z => Finset.sum_apply z hfin.toFinset
        (fun i z => ((D i : ℂ) * (z - i)⁻¹))
    rwa [hfun] at h
  have han_g : AnalyticOnNhd ℂ (fun x => deriv g x / g x) (Metric.closedBall c R) :=
    hg_an.deriv.div hg_an (fun x hx => hg_ne ⟨x, hx⟩)
  have hInt_g : CircleIntegrable (logDeriv g) c R := by
    have hcont : ContinuousOn (fun x => deriv g x / g x) (Metric.sphere c R) :=
      han_g.continuousOn.mono Metric.sphere_subset_closedBall
    have hci := hcont.circleIntegrable hRle
    exact hci
  have hDiff : DiffContOnCl ℂ (logDeriv g) (Metric.ball c R) := by
    refine ⟨?_, ?_⟩
    · have hd : DifferentiableOn ℂ (fun x => deriv g x / g x) (Metric.ball c R) :=
        (han_g.differentiableOn).mono Metric.ball_subset_closedBall
      exact hd
    · rw [closure_ball c hRne]
      exact han_g.continuousOn
  have hg0 : (∮ z in C(c, R), logDeriv g z) = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hRle hDiff
  have hterm : ∀ u ∈ hfin.toFinset,
      (∮ z in C(c, R), ((D u : ℂ) * (z - u)⁻¹))
        = ((D u : ℂ) * (2 * Real.pi * Complex.I)) := by
    intro u hu
    have huB : u ∈ Metric.ball c R := hmem_ball u hu
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball huB]
  have hsum : (∑ u ∈ hfin.toFinset,
        (∮ z in C(c, R), ((D u : ℂ) * (z - u)⁻¹)))
      = (∑ u ∈ hfin.toFinset, ((D u : ℂ) * (2 * Real.pi * Complex.I))) :=
    Finset.sum_congr rfl (fun u hu => hterm u hu)
  rw [hint_eq, circleIntegral.integral_add hInt_sum hInt_g,
    circleIntegral.integral_fun_sum (fun u hu => hInt_term u hu), hsum, hg0, add_zero,
    ← Finset.sum_mul, mul_comm _ (2 * Real.pi * Complex.I), ← Int.cast_sum]
  congr 1
  rw [hballEq]
  congr 1
  exact (finsum_eq_sum_of_support_subset _ hS_sub).symm

set_option linter.unusedVariables false in
/--
**Argument principle on a closed disc, with an integrability hypothesis.** Let $c \in \mathbb{C}$,
$R > 0$, and let $f : \mathbb{C} \to \mathbb{C}$ be meromorphic on the closed disc $|z - c| \le R$
with finite order at every point of that disc. Suppose the order of $f$ is zero at every point of
the circle $|z - c| = R$ and $f'/f$ is integrable on that circle. Then the integral of $f'/f$ over
the circle, traversed once counterclockwise, equals $2\pi i$ times the sum of the orders of $f$ at
the points of the open disc $|z - c| < R$ (zeros counted positively and poles negatively, with
multiplicity).

Source: L. V. Ahlfors, Complex Analysis, 3rd ed., §5.2.
It follows from `argumentPrinciple_closedBall_general`; the hypothesis `hint` is unused and keeps
the source's shape.
Proves `Wanted` entry `argumentPrinciple_closedBall`.
-/
theorem argumentPrinciple_closedBall
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (hf_top : ∀ z ∈ Metric.closedBall c R,
      meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ z ∈ Metric.sphere c R,
      MeromorphicOn.divisor f (Metric.closedBall c R) z = 0)
    (hint : CircleIntegrable (logDeriv f) c R) :
    (∮ z in C(c, R), logDeriv f z) =
      2 * Real.pi * Complex.I *
        ↑(∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z) :=
  argumentPrinciple_closedBall_general hR hf hf_top hbd

end MathlibExt.Analysis.Complex.ArgumentPrinciple
