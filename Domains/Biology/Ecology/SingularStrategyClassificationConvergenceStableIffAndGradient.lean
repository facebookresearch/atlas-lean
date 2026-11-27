/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
public import Domains.Biology.Ecology.SingularStrategyClassificationBranchingPoint

/-!
# Convergence stability of singular strategies

In adaptive dynamics with one-dimensional strategies, `s x y` is the invasion fitness of a rare
mutant `y` in a resident population `x`, with `s x x = 0` (Geritz, Kisdi, Meszéna and Metz
1998). The local fitness gradient is `D(x) = ∂s/∂y (x, x)`, and `x*` is singular when
`D(x*) = 0`. With second partial derivatives `s_xx, s_xy, s_yy` at `(x*, x*)`, `x*` is
convergence-stable when `D'(x*) = s_xy + s_yy < 0` (Eshel 1983), equivalently `s_xx > s_yy`
because `s_xx + 2 s_xy + s_yy = 0` at `(x*, x*)`; near a convergence-stable `x*` the fitness
gradient points towards `x*`.

This module re-exports `fitnessGradient`, `sxx`, `sxy`, `syy` and `IsSingular` from
`Domains.Biology.Ecology.SingularStrategyClassificationBranchingPoint` and proves
`convergenceStable_iff_and_gradient`: for an invasion fitness of class `C²`, `s_xy + s_yy < 0`
iff `s_yy < s_xx` at `(x*, x*)`, and if `s_xy + s_yy < 0` then `(x* - x) D(x) > 0` for
residents `x` near but distinct from `x*`.

Sources: S. A. H. Geritz, É. Kisdi, G. Meszéna and J. A. J. Metz, "Evolutionarily singular
strategies and the adaptive growth and branching of the evolutionary tree", Evol. Ecol. 12
(1998) 35–57, eqs. (7)–(8); I. Eshel, "Evolutionary and continuous stability",
J. Theor. Biol. 103 (1983) 99–111.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

private noncomputable def PD1 (s : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => s x p.2) p.1

private noncomputable def PD2 (s : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => s p.1 y) p.2

private theorem sxx_eq (s : ℝ → ℝ → ℝ) (a b : ℝ) :
    sxx s a b = deriv (fun x => PD1 s (x, b)) a := rfl

private theorem sxy_eq (s : ℝ → ℝ → ℝ) (a b : ℝ) :
    sxy s a b = deriv (fun x => PD2 s (x, b)) a := rfl

private theorem syy_eq (s : ℝ → ℝ → ℝ) (a b : ℝ) :
    syy s a b = deriv (fun y => PD2 s (a, y)) b := rfl

private theorem slice1_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (b : ℝ) :
    ContDiff ℝ 2 fun x => s x b :=
  h.comp (contDiff_id.prodMk contDiff_const)

private theorem slice2_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (a : ℝ) :
    ContDiff ℝ 2 fun y => s a y :=
  h.comp (contDiff_const.prodMk contDiff_id)

private theorem hasDerivAt_slice1 (g : ℝ × ℝ → ℝ) (h : Differentiable ℝ g) (p : ℝ × ℝ) :
    HasDerivAt (fun x => g (x, p.2)) ((fderiv ℝ g p) (1, 0)) p.1 := by
  have hinner : HasDerivAt (fun x : ℝ => (x, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (h p).hasFDerivAt.comp_hasDerivAt (f := fun x : ℝ => (x, p.2)) p.1 hinner

private theorem hasDerivAt_slice2 (g : ℝ × ℝ → ℝ) (h : Differentiable ℝ g) (p : ℝ × ℝ) :
    HasDerivAt (fun y => g (p.1, y)) ((fderiv ℝ g p) (0, 1)) p.2 := by
  have hinner : HasDerivAt (fun y : ℝ => (p.1, y)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (h p).hasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => (p.1, y)) p.2 hinner

private theorem PD1_eq_fderiv (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (p : ℝ × ℝ) :
    PD1 s p = (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) p) (1, 0) :=
  (hasDerivAt_slice1 _ (h.differentiable two_ne_zero) p).deriv

private theorem PD2_eq_fderiv (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (p : ℝ × ℝ) :
    PD2 s p = (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) p) (0, 1) :=
  (hasDerivAt_slice2 _ (h.differentiable two_ne_zero) p).deriv

private theorem PD1_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) : ContDiff ℝ 1 (PD1 s) := by
  have hF : ContDiff ℝ 1 (fderiv ℝ fun p : ℝ × ℝ => s p.1 p.2) :=
    h.fderiv_right (by decide)
  have hEq : PD1 s = fun p : ℝ × ℝ => (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) p) (1, 0) :=
    funext fun p => PD1_eq_fderiv s h p
  rw [hEq]
  exact hF.clm_apply (g := fun _ : ℝ × ℝ => (1, 0)) contDiff_const

private theorem PD2_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) : ContDiff ℝ 1 (PD2 s) := by
  have hF : ContDiff ℝ 1 (fderiv ℝ fun p : ℝ × ℝ => s p.1 p.2) :=
    h.fderiv_right (by decide)
  have hEq : PD2 s = fun p : ℝ × ℝ => (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) p) (0, 1) :=
    funext fun p => PD2_eq_fderiv s h p
  rw [hEq]
  exact hF.clm_apply (g := fun _ : ℝ × ℝ => (0, 1)) contDiff_const

private theorem P1P2_continuous (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) :
    Continuous fun p : ℝ × ℝ => (fderiv ℝ (PD2 s) p) (1, 0) :=
  ((PD2_contDiff s h).continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem P1P2_eq_deriv (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (p : ℝ × ℝ) :
    (fderiv ℝ (PD2 s) p) (1, 0) = deriv (fun x => PD2 s (x, p.2)) p.1 :=
  (hasDerivAt_slice1 _ ((PD2_contDiff s h).differentiable one_ne_zero) p).deriv.symm

private theorem hasDerivAt_slice1_PD1 (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (b x : ℝ) :
    HasDerivAt (fun x => s x b) (PD1 s (x, b)) x :=
  (hasDerivAt_slice1 _ (h.differentiable two_ne_zero) (x, b)).congr_deriv
    (PD1_eq_fderiv s h (x, b)).symm

private theorem hasDerivAt_slice2_PD2 (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (a y : ℝ) :
    HasDerivAt (fun y => s a y) (PD2 s (a, y)) y :=
  (hasDerivAt_slice2 _ (h.differentiable two_ne_zero) (a, y)).congr_deriv
    (PD2_eq_fderiv s h (a, y)).symm

private theorem hasDerivAt_PD2_slice1 (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (b x : ℝ) :
    HasDerivAt (fun x => PD2 s (x, b)) ((fderiv ℝ (PD2 s) (x, b)) (1, 0)) x :=
  hasDerivAt_slice1 _ ((PD2_contDiff s h).differentiable one_ne_zero) (x, b)

private theorem hasDerivAt_comp_add_const_at (g : ℝ → ℝ) (g' : ℝ) (c x : ℝ)
    (h : HasDerivAt g g' (c + x)) :
    HasDerivAt (fun r => g (c + r)) g' x :=
  (h.comp x ((hasDerivAt_id' x).const_add c)).congr_deriv (mul_one _)

private theorem mvt_uIcc (f f' : ℝ → ℝ) (u v : ℝ) (huv : u ≠ v)
    (hfc : ContinuousOn f (uIcc u v))
    (hff' : ∀ x ∈ uIoo u v, HasDerivAt f (f' x) x) :
    ∃ c ∈ uIoo u v, f' c = (f v - f u) / (v - u) := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [uIcc_of_le h.le] at hfc
    rw [uIoo_of_le h.le] at hff' ⊢
    exact exists_hasDerivAt_eq_slope f f' h hfc hff'
  · rw [uIcc_of_ge h.le] at hfc
    rw [uIoo_of_ge h.le] at hff' ⊢
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h hfc hff'
    refine ⟨c, hc, ?_⟩
    rw [hc', show f u - f v = -(f v - f u) by ring, show u - v = -(v - u) by ring,
      neg_div_neg_eq]

private theorem abs_lt_of_mem_uIoo_zero (t ξ : ℝ) (ht : t ≠ 0) (hξ : ξ ∈ uIoo (0 : ℝ) t) :
    |ξ| < |t| := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [uIoo_of_ge h.le] at hξ
    rw [abs_of_neg h, abs_of_neg hξ.2]
    exact neg_lt_neg hξ.1
  · rw [uIoo_of_le h.le] at hξ
    rw [abs_of_pos h, abs_of_pos hξ.1]
    exact hξ.2

private noncomputable def rectDiff (s : ℝ → ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ :=
  (s (a + t) (b + t) - s (a + t) b - s a (b + t) + s a b) / (t * t)

private theorem rect_eq_P1P2 (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (a b t : ℝ) (ht : t ≠ 0) :
    ∃ ξ ∈ uIoo (0 : ℝ) t, ∃ η ∈ uIoo (0 : ℝ) t,
      rectDiff s a b t = (fderiv ℝ (PD2 s) (a + ξ, b + η)) (1, 0) := by
  have hwc : ContinuousOn (fun r => s (a + t) (b + r) - s a (b + r)) (uIcc 0 t) := by
    have hc1 : Continuous fun r => s (a + t) (b + r) :=
      (slice2_contDiff s h (a + t)).continuous.comp (continuous_const.add continuous_id)
    have hc2 : Continuous fun r => s a (b + r) :=
      (slice2_contDiff s h a).continuous.comp (continuous_const.add continuous_id)
    exact (hc1.sub hc2).continuousOn
  have hw' : ∀ x ∈ uIoo (0 : ℝ) t,
      HasDerivAt (fun r => s (a + t) (b + r) - s a (b + r))
        (PD2 s (a + t, b + x) - PD2 s (a, b + x)) x := by
    intro x _
    exact (hasDerivAt_comp_add_const_at _ _ _ _ (hasDerivAt_slice2_PD2 s h (a + t) (b + x))).sub
      (hasDerivAt_comp_add_const_at _ _ _ _ (hasDerivAt_slice2_PD2 s h a (b + x)))
  obtain ⟨η, hη, hηe⟩ := mvt_uIcc (fun r => s (a + t) (b + r) - s a (b + r))
    (fun r => PD2 s (a + t, b + r) - PD2 s (a, b + r)) 0 t (Ne.symm ht) hwc hw'
  simp only [sub_zero, add_zero] at hηe
  have hzc : ∀ η : ℝ, ContinuousOn (fun r => PD2 s (a + r, b + η)) (uIcc 0 t) := by
    intro η
    exact ((PD2_contDiff s h).continuous.comp
      ((continuous_const.add continuous_id).prodMk continuous_const)).continuousOn
  have hz' : ∀ η : ℝ, ∀ x ∈ uIoo (0 : ℝ) t,
      HasDerivAt (fun r => PD2 s (a + r, b + η))
        ((fderiv ℝ (PD2 s) (a + x, b + η)) (1, 0)) x := by
    intro η x _
    exact hasDerivAt_comp_add_const_at _ _ _ _ (hasDerivAt_PD2_slice1 s h (b + η) (a + x))
  obtain ⟨ξ, hξ, hξe⟩ := mvt_uIcc (fun r => PD2 s (a + r, b + η))
    (fun r => (fderiv ℝ (PD2 s) (a + r, b + η)) (1, 0)) 0 t (Ne.symm ht) (hzc η) (hz' η)
  simp only [sub_zero, add_zero] at hξe
  refine ⟨ξ, hξ, η, hη, ?_⟩
  rw [hξe, hηe]
  simp only [rectDiff]
  rw [div_div]
  congr 1
  ring

private theorem tendsto_rect_P1P2 (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (a b : ℝ) :
    Tendsto (rectDiff s a b) (𝓝[≠] 0) (𝓝 ((fderiv ℝ (PD2 s) (a, b)) (1, 0))) := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ => (fderiv ℝ (PD2 s) p) (1, 0)) (a, b) :=
    (P1P2_continuous s h).continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have hmem : ({0}ᶜ : Set ℝ) ∩ {t : ℝ | dist t 0 < δ} ∈ 𝓝[≠] (0 : ℝ) :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds 0 hδpos)
  filter_upwards [hmem] with t ht
  have ht0 : t ≠ 0 := by simpa using ht.1
  obtain ⟨ξ, hξ, η, hη, hξη⟩ := rect_eq_P1P2 s h a b t ht0
  have htab : |t| < δ := by simpa [Real.dist_eq, sub_zero] using ht.2
  have hξb : |ξ| < δ := (abs_lt_of_mem_uIoo_zero t ξ ht0 hξ).trans htab
  have hηb : |η| < δ := (abs_lt_of_mem_uIoo_zero t η ht0 hη).trans htab
  have hdist : dist (a + ξ, b + η) (a, b) < δ := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    rw [show a + ξ - a = ξ by ring, show b + η - b = η by ring]
    exact max_lt hξb hηb
  have hclose := hδ hdist
  rw [hξη]
  exact hclose

private theorem diag_first_order (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    PD1 s (xs, xs) + PD2 s (xs, xs) = 0 := by
  have hγ0 : HasDerivAt (fun t => s (xs + t) (xs + t)) 0 0 := by
    have heq : (fun t => s (xs + t) (xs + t)) = fun _ => (0 : ℝ) :=
      funext fun t => h.diag (xs + t)
    rw [heq]
    exact hasDerivAt_const 0 0
  have hδ : HasDerivAt (fun t : ℝ => (xs + t, xs + t)) (1, 1) 0 :=
    ((hasDerivAt_id' 0).const_add xs).prodMk ((hasDerivAt_id' 0).const_add xs)
  have hγ1 : HasDerivAt (fun t => s (xs + t) (xs + t))
      ((fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs)) (1, 1)) 0 :=
    (h.contDiff.differentiable two_ne_zero (xs, xs)).hasFDerivAt.comp_hasDerivAt_of_eq
      (f := fun t : ℝ => (xs + t, xs + t)) 0 hδ (by simp)
  have hderiv := hγ0.deriv
  rw [hγ1.deriv] at hderiv
  have hsum : (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs)) (1, 1)
      = PD1 s (xs, xs) + PD2 s (xs, xs) := by
    have h11 : ((1, 0) : ℝ × ℝ) + (0, 1) = (1, 1) := by ext <;> simp
    rw [← h11, map_add, ← PD1_eq_fderiv s h.contDiff (xs, xs),
      ← PD2_eq_fderiv s h.contDiff (xs, xs)]
  rw [hsum] at hderiv
  exact hderiv

private noncomputable def diagSum (s : ℝ → ℝ → ℝ) (xs : ℝ) (t : ℝ) : ℝ :=
  s (xs + t) xs + s xs (xs + t)

private theorem diagSum_contDiff (s : ℝ → ℝ → ℝ) (xs : ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) :
    ContDiff ℝ 2 (diagSum s xs) := by
  have h1 : ContDiff ℝ 2 fun t => s (xs + t) xs :=
    (slice1_contDiff s h xs).comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ 2 fun t => s xs (xs + t) :=
    (slice2_contDiff s h xs).comp (contDiff_const.add contDiff_id)
  exact h1.add h2

private theorem deriv_diagSum (s : ℝ → ℝ → ℝ) (xs : ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (t : ℝ) :
    deriv (diagSum s xs) t = PD1 s (xs + t, xs) + PD2 s (xs, xs + t) := by
  have h1 : HasDerivAt (fun t => s (xs + t) xs) (PD1 s (xs + t, xs)) t :=
    hasDerivAt_comp_add_const_at _ _ _ _ (hasDerivAt_slice1_PD1 s h xs (xs + t))
  have h2 : HasDerivAt (fun t => s xs (xs + t)) (PD2 s (xs, xs + t)) t :=
    hasDerivAt_comp_add_const_at _ _ _ _ (hasDerivAt_slice2_PD2 s h xs (xs + t))
  exact (h1.add h2).deriv

private theorem diagSum_zero (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    diagSum s xs 0 = 0 := by
  simp [diagSum, h.diag]

private theorem deriv_diagSum_zero (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    deriv (diagSum s xs) 0 = 0 := by
  rw [deriv_diagSum s xs h.contDiff 0, add_zero]
  exact diag_first_order s xs h

private theorem PD1_slice1_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (b : ℝ) :
    ContDiff ℝ 1 fun x => PD1 s (x, b) :=
  (PD1_contDiff s h).comp (contDiff_id.prodMk contDiff_const)

private theorem PD2_slice2_contDiff (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (a : ℝ) :
    ContDiff ℝ 1 fun y => PD2 s (a, y) :=
  (PD2_contDiff s h).comp (contDiff_const.prodMk contDiff_id)

private theorem deriv2_diagSum_zero (s : ℝ → ℝ → ℝ) (xs : ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) :
    deriv (deriv (diagSum s xs)) 0 = sxx s xs xs + syy s xs xs := by
  have hfun : deriv (diagSum s xs) = fun t => PD1 s (xs + t, xs) + PD2 s (xs, xs + t) :=
    funext fun t => deriv_diagSum s xs h t
  rw [hfun]
  have e1 : HasDerivAt (fun x => PD1 s (x, xs)) (deriv (fun x => PD1 s (x, xs)) xs)
      (xs + 0) := by
    have e : DifferentiableAt ℝ (fun x => PD1 s (x, xs)) xs :=
      ((PD1_slice1_contDiff s h xs).differentiable one_ne_zero).differentiableAt
    simpa using e.hasDerivAt
  have e2 : HasDerivAt (fun y => PD2 s (xs, y)) (deriv (fun y => PD2 s (xs, y)) xs)
      (xs + 0) := by
    have e : DifferentiableAt ℝ (fun y => PD2 s (xs, y)) xs :=
      ((PD2_slice2_contDiff s h xs).differentiable one_ne_zero).differentiableAt
    simpa using e.hasDerivAt
  have g1 : HasDerivAt (fun t => PD1 s (xs + t, xs)) (deriv (fun x => PD1 s (x, xs)) xs) 0 :=
    hasDerivAt_comp_add_const_at _ _ _ _ e1
  have g2 : HasDerivAt (fun t => PD2 s (xs, xs + t)) (deriv (fun y => PD2 s (xs, y)) xs) 0 :=
    hasDerivAt_comp_add_const_at _ _ _ _ e2
  have hadd := g1.add g2
  rw [sxx_eq s xs xs, syy_eq s xs xs]
  exact hadd.deriv

private theorem deriv_eq_fderiv_one (g : ℝ → ℝ) (h : Differentiable ℝ g) (t : ℝ) :
    deriv g t = (fderiv ℝ g t) 1 :=
  ((h t).hasFDerivAt.hasDerivAt).deriv

private theorem continuous_deriv_of_contDiff1 (g : ℝ → ℝ) (h : ContDiff ℝ 1 g) :
    Continuous (deriv g) := by
  have hEq : deriv g = fun t => (fderiv ℝ g t) 1 :=
    funext fun t => deriv_eq_fderiv_one _ (h.differentiable one_ne_zero) t
  rw [hEq]
  exact (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem deriv_diagSum_contDiff (s : ℝ → ℝ → ℝ) (xs : ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) :
    ContDiff ℝ 1 (deriv (diagSum s xs)) := by
  have hF : ContDiff ℝ 1 (fderiv ℝ (diagSum s xs)) :=
    (diagSum_contDiff s xs h).fderiv_right (by decide)
  have hEq : deriv (diagSum s xs) = fun t => (fderiv ℝ (diagSum s xs) t) 1 :=
    funext fun t => deriv_eq_fderiv_one _ ((diagSum_contDiff s xs h).differentiable two_ne_zero) t
  rw [hEq]
  exact hF.clm_apply (g := fun _ : ℝ => (1 : ℝ)) contDiff_const

private theorem tendsto_deriv_diagSum_div (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    Tendsto (fun t => deriv (diagSum s xs) t / (2 * t)) (𝓝[≠] 0)
      (𝓝 ((deriv (deriv (diagSum s xs)) 0) / 2)) := by
  have hC1 := deriv_diagSum_contDiff s xs h.contDiff
  have hdiff : Differentiable ℝ (deriv (diagSum s xs)) := hC1.differentiable one_ne_zero
  refine HasDerivAt.lhopital_zero_nhdsNE (f := deriv (diagSum s xs))
    (f' := deriv (deriv (diagSum s xs))) (g := fun t => 2 * t) (g' := fun _ => 2) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (hdiff x).hasDerivAt
  · exact Eventually.of_forall fun x => ((hasDerivAt_id' x).const_mul 2).congr_deriv (mul_one 2)
  · exact Eventually.of_forall fun _ => two_ne_zero
  · have hT : Tendsto (deriv (diagSum s xs)) (𝓝 0) (𝓝 (deriv (diagSum s xs) 0)) :=
      hC1.continuous.continuousAt
    rw [deriv_diagSum_zero s xs h] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hT : Tendsto (fun t : ℝ => 2 * t) (𝓝 (0 : ℝ)) (𝓝 ((2 : ℝ) * 0)) :=
      (continuous_const.mul continuous_id).continuousAt
    rw [mul_zero] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hT : Tendsto (deriv (deriv (diagSum s xs))) (𝓝 (0 : ℝ))
        (𝓝 (deriv (deriv (diagSum s xs)) 0)) :=
      (continuous_deriv_of_contDiff1 _ hC1).continuousAt
    exact (hT.div_const 2).mono_left nhdsWithin_le_nhds

private theorem tendsto_diagSum_div (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    Tendsto (fun t => diagSum s xs t / (t * t)) (𝓝[≠] 0)
      (𝓝 ((deriv (deriv (diagSum s xs)) 0) / 2)) := by
  have hC2 := diagSum_contDiff s xs h.contDiff
  have hdiff : Differentiable ℝ (diagSum s xs) := hC2.differentiable two_ne_zero
  refine HasDerivAt.lhopital_zero_nhdsNE (f := diagSum s xs) (f' := deriv (diagSum s xs))
    (g := fun t => t * t) (g' := fun t => 2 * t) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (hdiff x).hasDerivAt
  · exact Eventually.of_forall fun x =>
      ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).congr_deriv (by ring)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero two_ne_zero hx0
  · have hT : Tendsto (diagSum s xs) (𝓝 0) (𝓝 (diagSum s xs 0)) := hC2.continuous.continuousAt
    rw [diagSum_zero s xs h] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hT : Tendsto (fun t : ℝ => t * t) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) * 0)) :=
      (continuous_id.mul continuous_id).continuousAt
    rw [mul_zero] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · exact tendsto_deriv_diagSum_div s xs h

private theorem tendsto_diagSum_div_neg (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    Tendsto (fun t => diagSum s xs t / (t * t)) (𝓝[≠] 0) (𝓝 (-sxy s xs xs)) := by
  have hrect := tendsto_rect_P1P2 s h.contDiff xs xs
  have hsxy : (fderiv ℝ (PD2 s) (xs, xs)) (1, 0) = sxy s xs xs := by
    rw [P1P2_eq_deriv s h.contDiff (xs, xs)]
    exact (sxy_eq s xs xs).symm
  rw [hsxy] at hrect
  have hneg := hrect.neg
  have heq : (fun t => diagSum s xs t / (t * t)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t => -(rectDiff s xs xs t)) := by
    filter_upwards with t
    have hdt : diagSum s xs t
        = -(s (xs + t) (xs + t) - s (xs + t) xs - s xs (xs + t) + s xs xs) := by
      simp only [diagSum]
      rw [h.diag, h.diag]
      ring
    simp only [rectDiff]
    rw [hdt, neg_div]
  exact hneg.congr' heq.symm

private theorem diag_identity (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    sxx s xs xs + 2 * sxy s xs xs + syy s xs xs = 0 := by
  have h1 := tendsto_diagSum_div s xs h
  have h2 := tendsto_diagSum_div_neg s xs h
  have heq := tendsto_nhds_unique h1 h2
  rw [deriv2_diagSum_zero s xs h.contDiff] at heq
  linarith

private theorem P2P2_eq_deriv (s : ℝ → ℝ → ℝ)
    (h : ContDiff ℝ 2 fun p : ℝ × ℝ => s p.1 p.2) (p : ℝ × ℝ) :
    (fderiv ℝ (PD2 s) p) (0, 1) = deriv (fun y => PD2 s (p.1, y)) p.2 :=
  (hasDerivAt_slice2 _ ((PD2_contDiff s h).differentiable one_ne_zero) p).deriv.symm

private theorem hasDerivAt_gradient (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    HasDerivAt (fitnessGradient s) (sxy s xs xs + syy s xs xs) xs := by
  have hδ : HasDerivAt (fun x : ℝ => (x, x)) (1, 1) xs :=
    (hasDerivAt_id' xs).prodMk (hasDerivAt_id' xs)
  have hC : HasDerivAt (fun x => PD2 s (x, x))
      ((fderiv ℝ (PD2 s) (xs, xs)) (1, 1)) xs :=
    ((PD2_contDiff s h.contDiff).differentiable one_ne_zero (xs, xs)).hasFDerivAt.comp_hasDerivAt
      (f := fun x : ℝ => (x, x)) xs hδ
  have hval : (fderiv ℝ (PD2 s) (xs, xs)) (1, 1) = sxy s xs xs + syy s xs xs := by
    have h11 : ((1, 0) : ℝ × ℝ) + (0, 1) = (1, 1) := by ext <;> simp
    have hx : (fderiv ℝ (PD2 s) (xs, xs)) (1, 0) = sxy s xs xs := by
      rw [P1P2_eq_deriv s h.contDiff (xs, xs)]
      exact (sxy_eq s xs xs).symm
    have hy : (fderiv ℝ (PD2 s) (xs, xs)) (0, 1) = syy s xs xs := by
      rw [P2P2_eq_deriv s h.contDiff (xs, xs)]
      exact (syy_eq s xs xs).symm
    rw [← h11, map_add, hx, hy]
  have hC' := hC.congr_deriv hval
  have hfun : (fun x => PD2 s (x, x)) = fitnessGradient s := rfl
  rw [hfun] at hC'
  exact hC'

private theorem part1_iff (s : ℝ → ℝ → ℝ) (xs : ℝ) (h : IsSingular s xs) :
    sxy s xs xs + syy s xs xs < 0 ↔ syy s xs xs < sxx s xs xs := by
  have hdiag := diag_identity s xs h
  constructor <;> intro hlt <;> linarith

private theorem exists_pos_mul_of_neg_deriv (D : ℝ → ℝ) (D' xs : ℝ)
    (hD : HasDerivAt D D' xs) (h0 : D xs = 0) (hneg : D' < 0) :
    ∃ δ > 0, ∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * D x := by
  have hT := hasDerivAt_iff_tendsto_slope.1 hD
  have hev : ∀ᶠ x in 𝓝[≠] xs, slope D xs x < 0 := hT.eventually_lt_const hneg
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, fun x hx0 hxδ => ?_⟩
  have hne : x ≠ xs := by
    intro heq
    rw [heq, sub_self, abs_zero] at hx0
    exact lt_irrefl 0 hx0
  have hdist : dist x xs < δ := by
    rw [Real.dist_eq]
    exact hxδ
  have hmem : x ∈ Metric.ball xs δ := Metric.mem_ball.2 hdist
  have hxs : x ∈ ({xs}ᶜ : Set ℝ) := by simpa using hne
  have hslope := hδ x hmem hxs
  have hneg' : D x / (x - xs) < 0 := by simpa [slope_def_field, h0] using hslope
  rcases (div_neg_iff.1 hneg') with ⟨hDpos, hxneg⟩ | ⟨hDneg, hxpos⟩
  · have hpos : 0 < xs - x := sub_pos.2 (sub_neg.1 hxneg)
    exact mul_pos hpos hDpos
  · have hneg'' : xs - x < 0 := sub_neg.2 (sub_pos.1 hxpos)
    exact mul_pos_of_neg_of_neg hneg'' hDneg

/-- **Convergence stability** (Eshel 1983; Geritz et al. 1998, eq. (8)). For an invasion
fitness `s` with singular strategy `x*`: `s_xy + s_yy < 0` iff `s_yy < s_xx` (all at
`(x*, x*)`), and if `s_xy + s_yy < 0` then there is `δ > 0` such that every resident `x` with
`0 < |x - x*| < δ` has fitness gradient pointing towards `x*`: `(x* - x) D(x) > 0`.

Sources: Eshel (1983); Geritz et al. (1998), eq. (8). -/
public theorem convergenceStable_iff_and_gradient {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (h : IsSingular s xs) :
    (sxy s xs xs + syy s xs xs < 0 ↔ syy s xs xs < sxx s xs xs) ∧
      (sxy s xs xs + syy s xs xs < 0 →
        ∃ δ > 0, ∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * fitnessGradient s x) := by
  refine ⟨part1_iff s xs h, fun hneg => ?_⟩
  exact exists_pos_mul_of_neg_deriv _ _ _ (hasDerivAt_gradient s xs h) h.gradient_eq_zero hneg

end WantedExt.Biology.Ecology.SingularStrategyClassificationWanted
