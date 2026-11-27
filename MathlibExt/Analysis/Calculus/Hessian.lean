/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Data.Matrix.Basic

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Hessian matrices

This file relates coordinatewise Hessian matrices to second Fréchet derivatives, proves their
symmetry for twice continuously differentiable functions, and proves positive semidefiniteness at
local minima.
-/

open scoped BigOperators

open Set

@[expose] public section

namespace MetaMathlibExt

/-- **Hessian matrix.** For a function $f : \mathbb{R}^n \to \mathbb{R}$ and a point
$x \in \mathbb{R}^n$, the Hessian matrix of $f$ at $x$ is the $n \times n$ real matrix whose
$(i, j)$ entry is $\frac{d}{ds}\big|_{s=0} \frac{d}{dt}\big|_{t=0} f(x + s e_i + t e_j)$, where
$e_1, \dots, e_n$ is the standard basis of $\mathbb{R}^n$ and a derivative that does not exist is
taken to be $0$.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Hessian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9;
stable ref https://en.wikipedia.org/wiki/Hessian_matrix. -/
noncomputable def hessianMatrix {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => deriv (fun s : ℝ => deriv (fun t : ℝ =>
    f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0

/-- **Entries of the Hessian matrix.** For $f : \mathbb{R}^n \to \mathbb{R}$, a point
$x \in \mathbb{R}^n$ and indices $i, j$, the $(i, j)$ entry of the Hessian matrix of $f$ at $x$ is
$\frac{d}{ds}\big|_{s=0} \frac{d}{dt}\big|_{t=0} f(x + s e_i + t e_j)$, where $e_1, \dots, e_n$ is
the standard basis of $\mathbb{R}^n$ and a derivative that does not exist is taken to be $0$:
differentiate first along $e_j$, then along $e_i$.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Hessian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
theorem hessianMatrix_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    hessianMatrix f x i j =
      deriv (fun s : ℝ => deriv (fun t : ℝ =>
        f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0 := rfl

private theorem hessian_deriv_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : Differentiable ℝ f)
    (x v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (x + s • v)) t = fderiv ℝ f (x + t • v) v := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) t).smul_const v).const_add x
  simpa [Function.comp_def] using
    ((hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline).deriv

private theorem hessian_deriv_fderiv_line {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (hf : ContDiff ℝ 2 f) (x v w : E) :
    deriv (fun t : ℝ => fderiv ℝ f (x + t • v) w) 0 =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hfderiv : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heval : Differentiable ℝ (fun y => fderiv ℝ f y w) :=
    hfderiv.clm_apply (differentiable_const w)
  rw [hessian_deriv_line _ heval]
  simp only [zero_smul, add_zero]
  have happ := congrArg (fun L : E →L[ℝ] F => L v)
    (fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => w)
      (hfderiv x) (differentiableAt_const w))
  simpa using happ

private theorem hessian_deriv_deriv_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst : deriv (fun t : ℝ => f (x + t • v)) =
      fun t => fderiv ℝ f (x + t • v) v := by
    funext t
    exact hessian_deriv_line f hfdiff x v t
  rw [hfirst]
  exact hessian_deriv_fderiv_line f hf x v v

private theorem hessian_clm_apply_self_eq_sum {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    B v v = ∑ i, ∑ j, v i * B (Pi.single i 1) (Pi.single j 1) * v j := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- **Hessian entries as second Fréchet derivatives.** Let $f : \mathbb{R}^n \to \mathbb{R}$ be
twice continuously differentiable and let $x \in \mathbb{R}^n$. For all indices $i, j$, the
$(i, j)$ entry of the Hessian matrix of $f$ at $x$ equals $D(Df)(x)(e_i)(e_j)$, the derivative of
the Fréchet derivative $Df$ at $x$ in the direction $e_i$, applied to $e_j$, where
$e_1, \dots, e_n$ is the standard basis of $\mathbb{R}^n$. -/
theorem hessianMatrix_eq_fderiv_fderiv {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) (i j : Fin n) :
    hessianMatrix f x i j =
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  rw [hessianMatrix_apply]
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  simp_rw [hessian_deriv_line f hfdiff]
  simp only [zero_smul, add_zero]
  exact hessian_deriv_fderiv_line f hf x (Pi.single i 1) (Pi.single j 1)

/-- **Symmetry of the Hessian.** If $f : \mathbb{R}^n \to \mathbb{R}$ is twice continuously
differentiable, then for every $x \in \mathbb{R}^n$ the Hessian matrix of $f$ at $x$ is symmetric:
it equals its transpose.

Proof: Rewrite the matrix entries as evaluations of the second Fréchet derivative and apply
Schwarz's theorem on the symmetry of second derivatives, as proved in Mathlib, following
Wikipedia's “Symmetry of second derivatives”.

Proves `Wanted` entry `hessianMatrix_symmetric`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Hessian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
-/
theorem hessianMatrix_symmetric {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) :
    (hessianMatrix f x).transpose = hessianMatrix f x := by
  ext i j
  rw [Matrix.transpose_apply, hessianMatrix_eq_fderiv_fderiv f hf x j i,
    hessianMatrix_eq_fderiv_fderiv f hf x i j]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- At a local minimum of a twice continuously differentiable real function, the second
derivative is nonnegative. This is the necessary direction of the one-variable second derivative
test. -/
theorem _root_.IsLocalMin.deriv_deriv_nonneg {g : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin g x) (hg : ContDiff ℝ 2 g) : 0 ≤ deriv (deriv g) x := by
  by_contra h
  have hneg : deriv (deriv g) x < 0 := lt_of_not_ge h
  have hg' : ContDiff ℝ 1 (deriv g) := by
    simpa using (hg.deriv' : ContDiff ℝ 1 (deriv g))
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x := by fun_prop
  have hsecond : ∀ᶠ y in nhds x, deriv (deriv g) y < 0 :=
    (hg'.continuous_deriv (by norm_num)).continuousAt.eventually_lt hzero hneg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hmin.and hsecond)
  have hzball : x + r / 2 ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos]
    · linarith
    · linarith
  have hxz : x < x + r / 2 := by linarith
  have hxmem : x ∈ Icc x (x + r / 2) := ⟨le_rfl, hxz.le⟩
  have hzmem : x + r / 2 ∈ Icc x (x + r / 2) := ⟨hxz.le, le_rfl⟩
  have hderivAnti : StrictAntiOn (deriv g) (Icc x (x + r / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x (x + r / 2))
      (hg.continuous_deriv (by norm_num)).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rcases hy with ⟨hxy, hyz⟩
    apply (hball ?_).2
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
    linarith
  have hgAnti : StrictAntiOn g (Icc x (x + r / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x (x + r / 2))
      (hg.differentiable (by norm_num)).continuous.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rcases hy with ⟨hxy, hyz⟩
    have hymem : y ∈ Icc x (x + r / 2) := ⟨hxy.le, hyz.le⟩
    simpa [hmin.deriv_eq_zero] using hderivAnti hxmem hymem hxy
  exact (not_lt_of_ge (hball hzball).1) (hgAnti hxmem hzmem hxz)

/-- **Second-derivative test, necessary condition.** Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice
continuously differentiable and let $x$ be a local minimum of $f$. Then the Hessian quadratic
form of $f$ at $x$ is nonnegative: writing $H$ for the Hessian matrix of $f$ at $x$, every
$v \in \mathbb{R}^n$ satisfies $\sum_{i, j} v_i H_{ij} v_j \ge 0$.

Proof: Restrict the function to the affine line through $x$ in direction $v$, apply the necessary
direction of the one-variable second derivative test, then expand the second Fréchet derivative in
the standard basis. The one-variable step argues by contradiction as in the proof of the
second-derivative test in Wikipedia's “Derivative test”: a negative second derivative makes the
first derivative negative just right of the critical point, so the function decreases there.

Proves `Wanted` entry `isLocalMin_hessian_quadratic_nonneg`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Hessian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
-/
theorem isLocalMin_hessian_quadratic_nonneg {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) (hmin : IsLocalMin f x)
    (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * hessianMatrix f x i j * v j := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    fun_prop
  have hline : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hgmin : IsLocalMin g 0 := by
    have hmin0 : IsLocalMin f (x + (0 : ℝ) • v) := by simpa using hmin
    simpa [g, Function.comp_def] using
      hmin0.comp_continuous (g := fun t : ℝ => x + t • v) hline
  have hnonneg := hgmin.deriv_deriv_nonneg hg
  change 0 ≤ deriv (deriv (fun t : ℝ => f (x + t • v))) 0 at hnonneg
  rw [hessian_deriv_deriv_line f hf x v, hessian_clm_apply_self_eq_sum] at hnonneg
  simpa only [hessianMatrix_eq_fderiv_fderiv f hf x] using hnonneg

end MetaMathlibExt
