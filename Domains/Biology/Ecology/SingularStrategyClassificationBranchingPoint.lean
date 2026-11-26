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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.NhdsWithin
import MathlibExt.Analysis.Calculus.LineHessian
import MathlibExt.Analysis.Calculus.StrictSecondDerivativeTest
import MathlibExt.Topology.Order.LocalExtr

/-!
# Evolutionary branching points

For an invasion fitness `s` with singular strategy `x*`, a strategy that is
convergence-stable (`s_xy + s_yy < 0`) but not ESS-stable (`s_yy > 0`) is an evolutionary
branching point: nearby residents have fitness gradient pointing towards `x*`, nearby mutants
invade `x*`, and nearby strategies on opposite sides of `x*` invade each other.

## Main definitions

* `fitnessGradient s x`: the local fitness gradient `D(x) = ∂s/∂y (x, x)`.
* `sxx s a b`, `sxy s a b` and `syy s a b`: the resident, mixed and mutant second partial
  derivatives at `(a, b)`.
* `IsSingular s xs`: the standing hypotheses that `s` is `C²`, `s x x = 0` for every `x`,
  and `D(x*) = 0`.

## Main results

* `diagonal_identity_and_hasDerivAt`: the Hessian identity on the diagonal and the derivative
  of the fitness gradient.
* `branchingPoint`: convergence-stable but not ESS-stable singular strategies are
  evolutionary branching points.

Sources: S. A. H. Geritz, É. Kisdi, G. Meszéna and J. A. J. Metz, "Evolutionarily singular
strategies and the adaptive growth and branching of the evolutionary tree", Evol. Ecol. 12
(1998) 35–57, eqs. (1)–(11), Table 1; I. Eshel, "Evolutionary and continuous stability",
J. Theor. Biol. 103 (1983) 99–111.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

/-- The **local fitness gradient** `D(x) = ∂s/∂y (x, y)` at `y = x`. -/
noncomputable def fitnessGradient (s : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun y => s x y) x

/-- The second partial derivative `∂²s/∂x²` (resident variable) at `(a, b)`. -/
noncomputable def sxx (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun x => deriv (fun x' => s x' b) x) a

/-- The mixed second partial derivative `∂²s/∂x∂y` at `(a, b)`. -/
noncomputable def sxy (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => s x y) b) a

/-- The second partial derivative `∂²s/∂y²` (mutant variable) at `(a, b)`. -/
noncomputable def syy (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun y => deriv (fun y' => s a y') y) b

/-- Standing hypotheses on an **invasion fitness** with a singular strategy `x*`: `s` is `C²` as
a function of `(x, y)`, `s x x = 0` for every `x`, and `D(x*) = 0`. -/
structure IsSingular (s : ℝ → ℝ → ℝ) (xs : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)
  diag : ∀ x, s x x = 0
  gradient_eq_zero : fitnessGradient s xs = 0

/-- The `y`-slice derivative of a `C²` function is its Fréchet derivative in direction `(0, 1)`. -/
private lemma deriv_slice_snd {s : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hS : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)) :
    deriv (fun y => s p.1 y) p.2 = fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) p (0, 1) := by
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => s p.1 p.2) p :=
    hS.differentiable (by simp) p
  have hline : HasDerivAt (fun y : ℝ => (p.1, y)) (0, 1) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hcomp := (hdiff.hasFDerivAt.comp_hasDerivAt
    (f := fun y : ℝ => (p.1, y)) p.2 hline).deriv
  simpa only [Function.comp_def] using hcomp

/-- The Fréchet derivative in direction `v`, composed with a curve, has derivative given by the
second Fréchet derivative. -/
private lemma hasDerivAt_sndFDeriv_comp {s : ℝ → ℝ → ℝ} {c : ℝ → ℝ × ℝ} {c' : ℝ × ℝ}
    {t : ℝ} {v : ℝ × ℝ} (hS : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2))
    (hc : HasDerivAt c c' t) :
    HasDerivAt (fun t => fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (c t) v)
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (c t) c' v) t := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (c t) :=
    hS.contDiffAt.fderiv_right (m := 1) (by decide)
  have h2 : DifferentiableAt ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (c t) :=
    h1.differentiableAt (by simp)
  have hF : HasFDerivAt (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (c t)) (c t) := h2.hasFDerivAt
  have hcomp : HasDerivAt ((fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) ∘ c)
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (c t) c') t :=
    hF.comp_hasDerivAt (f := c) t hc
  have hmain := hcomp.clm_apply (hasDerivAt_const t v)
  simpa using hmain

/-- The resident second partial `s_xx` applies the second Fréchet derivative twice to `(1, 0)`. -/
private lemma sxx_eq {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (hS : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)) :
    sxx s xs xs = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (1, 0) := by
  have hpoint (x : ℝ) : ((0, xs) : ℝ × ℝ) + x • (1, 0) = (x, xs) := by
    ext <;> simp
  have hline : (fun x : ℝ => (fun p : ℝ × ℝ => s p.1 p.2) ((0, xs) + x • (1, 0))) =
      fun x => s x xs := by
    funext x
    rw [hpoint x]
  have hdd := LineHessian.deriv_deriv_line (fun p : ℝ × ℝ => s p.1 p.2) (0, xs) (1, 0)
    (t := xs) hS.contDiffAt
  rw [hline, hpoint xs] at hdd
  exact hdd

/-- The mixed partial `s_xy` is the second Fréchet derivative applied to `(1, 0)` then `(0, 1)`. -/
private lemma sxy_eq {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (hS : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)) :
    sxy s xs xs = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (0, 1) := by
  have hline : HasDerivAt (fun x : ℝ => (x, xs)) (1, 0) xs :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have hmain := (hasDerivAt_sndFDeriv_comp (v := (0, 1)) hS hline).deriv
  have heq : (fun x => deriv (fun y => s x y) xs)
      = fun x => fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (x, xs) (0, 1) := by
    funext x
    exact deriv_slice_snd (p := (x, xs)) hS
  change deriv (fun x => deriv (fun y => s x y) xs) xs = _
  rw [heq]
  exact hmain

/-- The mutant second partial `s_yy` is the second Fréchet derivative applied twice to `(0, 1)`. -/
private lemma syy_eq {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (hS : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)) :
    syy s xs xs = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (0, 1) := by
  have hline : HasDerivAt (fun y : ℝ => (xs, y)) (0, 1) xs :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hmain := (hasDerivAt_sndFDeriv_comp (v := (0, 1)) hS hline).deriv
  have heq : (fun y => deriv (fun y' => s xs y') y)
      = fun y => fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, y) (0, 1) := by
    funext y
    exact deriv_slice_snd (p := (xs, y)) hS
  change deriv (fun y => deriv (fun y' => s xs y') y) xs = _
  rw [heq]
  exact hmain

/-- The fitness gradient has derivative `s_xy + s_yy` at the singular strategy. -/
private lemma hasDerivAt_fitnessGradient {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs) :
    HasDerivAt (fitnessGradient s) (sxy s xs xs + syy s xs xs) xs := by
  have hD : fitnessGradient s
      = fun x => fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (x, x) (0, 1) := by
    funext x
    exact deriv_slice_snd (p := (x, x)) h.contDiff
  have hdiag : HasDerivAt (fun x : ℝ => (x, x)) (1, 1) xs :=
    (hasDerivAt_id _).prodMk (hasDerivAt_id _)
  have hmain := hasDerivAt_sndFDeriv_comp (v := (0, 1)) h.contDiff hdiag
  have hval : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 1) (0, 1)
      = sxy s xs xs + syy s xs xs := by
    have e3 : ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) := by ext <;> simp
    rw [e3, map_add]
    simp only [add_apply]
    rw [sxy_eq h.contDiff, syy_eq h.contDiff]
  rw [hD, ← hval]
  exact hmain

/-- The diagonal second derivative is zero, expanded in the two coordinate directions. -/
private lemma diagonal_hessian_sum_eq_zero {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs) :
    fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (0, 1)
      + fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (1, 0)
      + fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (0, 1) = 0 := by
  have hdiag : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 1) (1, 1) = 0 := by
    have hline : (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + u • (1, 1))) =
        fun _ => 0 := by
      funext u
      have hpoint : (xs, xs) + u • ((1, 1) : ℝ × ℝ) = (xs + u, xs + u) := by
        ext <;> simp
      rw [hpoint]
      exact h.diag (xs + u)
    have hval := LineHessian.deriv_deriv_line (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 1)
      (t := 0) h.contDiff.contDiffAt
    have hzero : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext fun x => deriv_const x 0
    rw [hline, hzero, deriv_const] at hval
    simpa only [zero_smul, add_zero] using hval.symm
  have e11 : ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) := by ext <;> simp
  simp only [e11, map_add, add_apply] at hdiag
  linarith only [hdiag]

/-- **Diagonal identity and the derivative of the fitness gradient** (Geritz et al. 1998).
For an invasion fitness `s` with singular strategy `x*` (`s` is `C²`, `s x x = 0`, `D(x*) = 0`):
`s_xx + 2 s_xy + s_yy = 0` at `(x*, x*)`, and `D` has derivative `s_xy + s_yy` at `x*`.

Source: Geritz et al. (1998), eq. (7) for the identity and the equality in eq. (6) for the
fitness-gradient derivative. -/
public theorem diagonal_identity_and_hasDerivAt {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (h : IsSingular s xs) :
    sxx s xs xs + 2 * sxy s xs xs + syy s xs xs = 0 ∧
      HasDerivAt (fitnessGradient s) (sxy s xs xs + syy s xs xs) xs := by
  refine ⟨?_, hasDerivAt_fitnessGradient h⟩
  rw [sxx_eq h.contDiff, sxy_eq h.contDiff, syy_eq h.contDiff]
  have hsym : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) :=
    h.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)
  linarith only [diagonal_hessian_sum_eq_zero h, hsym.eq (1, 0) (0, 1)]

/-- Convergence stability: near `x*`, the fitness gradient points towards `x*`. -/
private lemma grad_part {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs)
    (hconv : sxy s xs xs + syy s xs xs < 0) :
    ∃ δ > 0, ∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * fitnessGradient s x := by
  have hD := hasDerivAt_fitnessGradient h
  have hneg : deriv (fitnessGradient s) xs < 0 := by rw [hD.deriv]; exact hconv
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hneg h.gradient_eq_zero
  rw [Metric.eventually_nhds_iff] at hsign
  obtain ⟨δ, hδ, hsign⟩ := hsign
  refine ⟨δ, hδ, fun x hx0 hxδ => ?_⟩
  have hsg := hsign (by rwa [Real.dist_eq])
  have hne : x ≠ xs := by intro heq; rw [heq] at hx0; simp at hx0
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpos : 0 < xs - x := sub_pos.mpr hlt
    rw [sign_pos hpos] at hsg
    have hDpos : 0 < fitnessGradient s x := sign_eq_one_iff.mp hsg
    exact mul_pos hpos hDpos
  · have hneg' : xs - x < 0 := sub_neg.mpr hgt
    rw [sign_neg hneg'] at hsg
    have hDneg : fitnessGradient s x < 0 := sign_eq_neg_one_iff.mp hsg
    exact mul_pos_of_neg_of_neg hneg' hDneg

/-- Positive `s_yy`: nearby mutants invade the singular strategy. -/
private lemma invadable_part {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs)
    (hyy : 0 < syy s xs xs) :
    ∃ δ > 0, ∀ y, 0 < |y - xs| → |y - xs| < δ → 0 < s xs y := by
  have hg2 : ContDiff ℝ 2 (fun y : ℝ => s xs y) :=
    h.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hpos : 0 < deriv (deriv (fun y : ℝ => s xs y)) xs := hyy
  have hd : deriv (fun y : ℝ => s xs y) xs = 0 := h.gradient_eq_zero
  have hc : ContinuousAt (fun y : ℝ => s xs y) xs :=
    (hg2.differentiable (by simp)).continuous.continuousAt
  have hmin := isStrictLocalMin_of_deriv_deriv_pos hpos hd hc
  simp only [IsStrictLocalMin, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hmin
  obtain ⟨δ, hδ, hmin⟩ := hmin
  refine ⟨δ, hδ, fun y hy0 hyδ => ?_⟩
  have hne : y ≠ xs := by intro heq; rw [heq] at hy0; simp at hy0
  have hlt := hmin (by rwa [Real.dist_eq]) (by simpa using hne)
  simpa [h.diag xs] using hlt

/-- Mutual invasibility: nearby strategies on opposite sides of `x*` invade each other. -/
private lemma mutual_part {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs)
    (hconv : sxy s xs xs + syy s xs xs < 0) (hyy : 0 < syy s xs xs) :
    ∃ δ > 0, ∀ e, 0 < e → e < δ → 0 < s (xs - e) (xs + e) ∧ 0 < s (xs + e) (xs - e) := by
  have hS01 : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (0, 1) = 0 := by
    have hslice := deriv_slice_snd (p := (xs, xs)) h.contDiff
    rw [← hslice]
    exact h.gradient_eq_zero
  have hdiag1 : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 1) = 0 := by
    have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) :=
      h.contDiff.differentiable (by simp) (xs, xs)
    have hdiag : HasDerivAt (fun x : ℝ => (x, x)) (1, 1) xs :=
      (hasDerivAt_id _).prodMk (hasDerivAt_id _)
    have hcomp := (hdiff.hasFDerivAt.comp_hasDerivAt
      (f := fun x : ℝ => (x, x)) xs hdiag).deriv
    have hF0 : (fun p : ℝ × ℝ => s p.1 p.2) ∘ (fun x : ℝ => (x, x)) = fun _ => 0 :=
      funext fun x => h.diag x
    rw [hF0, deriv_const] at hcomp
    exact hcomp.symm
  have hS10 : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 0) = 0 := by
    have e3 : ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) := by ext <;> simp
    have hexp : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 1)
        = fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 0)
          + fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (0, 1) := by
      rw [e3, map_add]
    linarith [hdiag1, hS01, hexp]
  have hsym : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) :=
    h.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsymm : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (0, 1)
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (1, 0) :=
    hsym.eq _ _
  have hsxy : sxy s xs xs
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (0, 1) :=
    sxy_eq h.contDiff
  have hsxy_neg : sxy s xs xs < 0 := by linarith [hconv, hyy]
  have hΦ2 : ContDiff ℝ 2 (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2)
      ((xs, xs) + u • ((-1, 1) : ℝ × ℝ))) :=
    h.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have h00 : (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + (0 : ℝ) • ((-1, 1) : ℝ × ℝ)) = 0 := by
    rw [zero_smul, add_zero]
    exact h.diag xs
  have hvalφ1 : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (-1, 1) = 0 := by
    have e1 : ((-1, 1) : ℝ × ℝ) = (-1, 0) + (0, 1) := by ext <;> simp
    have e2 : ((-1, 0) : ℝ × ℝ) = -(1, 0) := by ext <;> simp
    have hexp : fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (-1, 1)
        = -fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (1, 0)
          + fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (0, 1) := by
      rw [e1, map_add, e2, map_neg]
    linarith [hS10, hS01, hexp]
  have hΦ1 : deriv (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + u • ((-1, 1) : ℝ × ℝ)))
      0 = 0 := by
    have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => s p.1 p.2)
        ((xs, xs) + (0 : ℝ) • ((-1, 1) : ℝ × ℝ)) :=
      h.contDiff.differentiable (by simp) _
    have hline : HasDerivAt (fun u : ℝ => (xs, xs) + u • ((-1, 1) : ℝ × ℝ))
        ((-1, 1) : ℝ × ℝ) 0 := by
      have h1 : HasDerivAt (fun u : ℝ => u • ((-1, 1) : ℝ × ℝ)) ((1 : ℝ) • ((-1, 1) : ℝ × ℝ)) 0 :=
        HasDerivAt.smul_const (hasDerivAt_id' 0) ((-1, 1) : ℝ × ℝ)
      have h2 := HasDerivAt.const_add (xs, xs) h1
      simpa using h2
    have hcomp := (hdiff.hasFDerivAt.comp_hasDerivAt
      (f := fun u : ℝ => (xs, xs) + u • ((-1, 1) : ℝ × ℝ)) 0 hline).deriv
    simp only [Function.comp_def] at hcomp
    rw [zero_smul, add_zero, hvalφ1] at hcomp
    exact hcomp
  have hE2 : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (-1, 1) (-1, 1)
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (1, 0)
        - fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (1, 0) (0, 1)
        - fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (1, 0)
        + fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (0, 1) (0, 1) := by
    have e1 : ((-1, 1) : ℝ × ℝ) = (-1, 0) + (0, 1) := by ext <;> simp
    have e2 : ((-1, 0) : ℝ × ℝ) = -(1, 0) := by ext <;> simp
    simp only [e1, map_add, e2, map_neg, add_apply, neg_apply, sub_eq_add_neg]
    ring
  have hφ2val : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (-1, 1) (-1, 1)
      = -4 * sxy s xs xs := by
    linarith only [hE2, diagonal_hessian_sum_eq_zero h, hsymm, hsxy]
  have hφ2 : deriv (deriv (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2)
      ((xs, xs) + u • ((-1, 1) : ℝ × ℝ)))) 0
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => s p.1 p.2)) (xs, xs) (-1, 1) (-1, 1) := by
    have hval := LineHessian.deriv_deriv_line (fun p : ℝ × ℝ => s p.1 p.2) (xs, xs) (-1, 1)
      (t := 0) (h.contDiff.contDiffAt)
    simpa using hval
  have hpos : 0 < deriv (deriv (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2)
      ((xs, xs) + u • ((-1, 1) : ℝ × ℝ)))) 0 := by
    rw [hφ2, hφ2val]
    linarith
  have hc : ContinuousAt (fun u : ℝ => (fun p : ℝ × ℝ => s p.1 p.2)
      ((xs, xs) + u • ((-1, 1) : ℝ × ℝ))) 0 :=
    (hΦ2.differentiable (by simp)).continuous.continuousAt
  have hmin := isStrictLocalMin_of_deriv_deriv_pos hpos hΦ1 hc
  simp only [IsStrictLocalMin, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hmin
  obtain ⟨δ, hδ, hmin⟩ := hmin
  refine ⟨δ, hδ, fun e he0 heδ => ?_⟩
  have hpt1 : (xs, xs) + e • ((-1, 1) : ℝ × ℝ) = (xs - e, xs + e) := by
    ext <;> simp [sub_eq_add_neg]
  have hpt2 : (xs, xs) + (-e) • ((-1, 1) : ℝ × ℝ) = (xs + e, xs - e) := by
    ext <;> simp [sub_eq_add_neg]
  have hne1 : e ≠ 0 := ne_of_gt he0
  have hdist1 : dist e 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he0]
    exact heδ
  have hne2 : -e ≠ 0 := neg_ne_zero.mpr hne1
  have hdist2 : dist (-e) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos he0]
    exact heδ
  have g1 : 0 < s (xs - e) (xs + e) := by
    have h1 := hmin hdist1 (by simpa using hne1)
    change (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + (0 : ℝ) • ((-1, 1) : ℝ × ℝ))
        < (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + e • ((-1, 1) : ℝ × ℝ)) at h1
    rw [h00, hpt1] at h1
    exact h1
  have g2 : 0 < s (xs + e) (xs - e) := by
    have h2 := hmin hdist2 (by simpa using hne2)
    change (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + (0 : ℝ) • ((-1, 1) : ℝ × ℝ))
        < (fun p : ℝ × ℝ => s p.1 p.2) ((xs, xs) + (-e) • ((-1, 1) : ℝ × ℝ)) at h2
    rw [h00, hpt2] at h2
    exact h2
  exact ⟨g1, g2⟩

/-- **Evolutionary branching point** (Geritz et al. 1998, Table 1). For an invasion fitness `s`
with singular strategy `x*` that is convergence-stable (`s_xy + s_yy < 0`) but not ESS-stable
(`s_yy > 0`): there is `δ > 0` such that every resident `x` with `0 < |x - x*| < δ` has
`(x* - x) D(x) > 0`, every mutant `y` with `0 < |y - x*| < δ` invades `x*` (`s x* y > 0`), and
for every `e` with `0 < e < δ` the strategies `x* - e` and `x* + e` invade each other.

Source: Geritz et al. (1998), Table 1 and Fig. 2. -/
public theorem branchingPoint {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs)
    (hconv : sxy s xs xs + syy s xs xs < 0) (hyy : 0 < syy s xs xs) :
    ∃ δ > 0, (∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * fitnessGradient s x) ∧
      (∀ y, 0 < |y - xs| → |y - xs| < δ → 0 < s xs y) ∧
      ∀ e, 0 < e → e < δ → 0 < s (xs - e) (xs + e) ∧ 0 < s (xs + e) (xs - e) := by
  obtain ⟨δ₁, hδ₁, hgrad⟩ := grad_part h hconv
  obtain ⟨δ₂, hδ₂, hinv⟩ := invadable_part h hyy
  obtain ⟨δ₃, hδ₃, hmut⟩ := mutual_part h hconv hyy
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_, ?_, ?_⟩
  · intro x hx0 hxδ
    exact hgrad x hx0 (lt_of_lt_of_le hxδ (min_le_left _ _))
  · intro y hy0 hyδ
    exact hinv y hy0 (lt_of_lt_of_le hyδ (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro e he0 heδ
    exact hmut e he0 (lt_of_lt_of_le heδ (le_trans (min_le_right _ _) (min_le_right _ _)))

end WantedExt.Biology.Ecology.SingularStrategyClassificationWanted
