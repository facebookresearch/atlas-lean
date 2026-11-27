/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import MathlibExt.Analysis.Calculus.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Empirical neural tangent kernel

Finite-width empirical neural tangent kernel of a `C¹` (`ContDiff`) or `C²`
parametrization evaluated on a fixed sample: the gradient-flow identity for
square loss (assuming the trajectory satisfies the gradient-flow ODE and `F`
is globally `C¹`) and a one-step descent remainder bound (assuming `F` is
globally `C²` with a Hessian bound). There is no infinite-width limit and no
claim that the NTK stays constant during training.

## References

* Arthur Jacot, Franck Gabriel and Clement Hongler, *Neural Tangent Kernel:
Convergence and Generalization in Neural Networks*, Advances in Neural
Information Processing Systems 31 (2018), arXiv:1806.07572, Section 4.
* Matan Telgarsky, *Deep Learning Theory*, lecture notes, Sections 4.1 and 4.3.

These references fix the finite-width kernel and linearization conventions
used here.
-/

@[expose] public section

open scoped Matrix

namespace Cslib.MachineLearning.NeuralTangentKernel

/-- Jacobian of `F` at parameters `θ`: the canonical Jacobian matrix of the
plain finite-function transport of `F`, evaluated at the plain coercion of `θ`. -/
noncomputable def jac (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) : Matrix (Fin n) (Fin P) ℝ :=
  MetaMathlibExt.jacobianMatrix (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ

/-- Empirical neural tangent kernel at parameters `θ`: the sum over the
parameters of outer products of output gradients, in matrix form `J Jᵀ`. -/
noncomputable def ntk (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) : Matrix (Fin n) (Fin n) ℝ :=
  jac P n F θ * (jac P n F θ)ᵀ

/-- Square loss against fixed targets `y`: half the squared distance
between the outputs `F θ` and the targets. -/
noncomputable def sqLoss (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin P)) : ℝ :=
  (1 / 2) * ∑ i, (F θ i - y i) ^ 2

/-- A `C^1` map has the expected Fréchet derivative. -/
private theorem hasFDerivAt_of_contDiff_one (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (hF : ContDiff ℝ 1 F) :
    HasFDerivAt F (fderiv ℝ F θ) θ :=
  hF.differentiable_one.differentiableAt.hasFDerivAt

/-- Fréchet derivative of an output coordinate. -/
private theorem hasFDerivAt_coord (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (i : Fin n) (hF : ContDiff ℝ 1 F) :
    HasFDerivAt (fun θ' => F θ' i)
      ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F θ)) θ :=
  HasFDerivAt.comp θ
    (ContinuousLinearMap.hasFDerivAt
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i))
    (hasFDerivAt_of_contDiff_one P n F θ hF)

/-- The derivative of an output coordinate is the matching coordinate of
the Fréchet derivative. -/
private theorem fderiv_coord_apply (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (i : Fin n)
    (v : EuclideanSpace ℝ (Fin P)) (hF : ContDiff ℝ 1 F) :
    fderiv ℝ (fun θ' => F θ' i) θ v = (fderiv ℝ F θ v) i := by
  rw [(hasFDerivAt_coord P n F θ i hF).fderiv]
  rfl

/-- Fréchet derivative of the plain finite-function transport of `F`. -/
private theorem hasFDerivAt_transport (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (hF : ContDiff ℝ 1 F) :
    HasFDerivAt (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x)))
      (ContinuousLinearMap.comp
        (ContinuousLinearEquiv.toContinuousLinearMap
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)))
        (ContinuousLinearMap.comp (fderiv ℝ F θ)
          (ContinuousLinearEquiv.toContinuousLinearMap (ContinuousLinearEquiv.symm
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin P => ℝ))))))
      ⇑θ := by
  have hF' : HasFDerivAt F (fderiv ℝ F θ) θ :=
    hF.differentiable_one.differentiableAt.hasFDerivAt
  have hto :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin P => ℝ) ⇑θ
  have hFo := HasFDerivAt.comp ⇑θ hF' hto
  have hof :=
    PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n => ℝ) (F θ)
  exact HasFDerivAt.comp ⇑θ hof hFo

/-- The transported canonical Jacobian entries agree with the Fréchet
derivative of the output coordinates. -/
private theorem jac_apply_eq_fderiv_coord (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (hF : ContDiff ℝ 1 F)
    (i : Fin n) (p : Fin P) :
    jac P n F θ i p
      = fderiv ℝ (fun θ' => F θ' i) θ (EuclideanSpace.single p 1) := by
  have hdiff : DifferentiableAt ℝ (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ :=
    (hasFDerivAt_transport P n F θ hF).differentiableAt
  have hentry := MetaMathlibExt.jacobianMatrix_apply_of_differentiableAt
    (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ hdiff i p
  have hval : (fderiv ℝ (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ)
      (Pi.single p 1) i = (fderiv ℝ F θ (EuclideanSpace.single p 1)) i := by
    rw [(hasFDerivAt_transport P n F θ hF).fderiv]
    rfl
  rw [hval] at hentry
  rw [fderiv_coord_apply P n F θ i _ hF]
  exact hentry

/-- The Fréchet derivative acts by the Jacobian matrix: characteristic
interface lemma for `jac`. -/
theorem fderiv_eq_jac_mulVec (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (θ : EuclideanSpace ℝ (Fin P)) (v : EuclideanSpace ℝ (Fin P))
    (hF : ContDiff ℝ 1 F) :
    fderiv ℝ F θ v = WithLp.toLp 2 ((jac P n F θ) *ᵥ ⇑v) := by
  have hdiff : DifferentiableAt ℝ (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ :=
    (hasFDerivAt_transport P n F θ hF).differentiableAt
  have hmul : (jac P n F θ) *ᵥ ⇑v = ⇑(fderiv ℝ F θ v) := by
    have h := MetaMathlibExt.jacobianMatrix_mulVec_eq_fderiv
      (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ hdiff ⇑v
    rw [(hasFDerivAt_transport P n F θ hF).fderiv] at h
    exact h
  calc fderiv ℝ F θ v = WithLp.toLp 2 ⇑(fderiv ℝ F θ v) :=
        (WithLp.toLp_ofLp 2 _).symm
    _ = WithLp.toLp 2 ((jac P n F θ) *ᵥ ⇑v) := by rw [hmul]

/-- Derivative of the scaled square. -/
private theorem hasDerivAt_half_sq (c : ℝ) :
    HasDerivAt (fun t : ℝ => (1 / 2) * t ^ 2) c c := by
  have h := (hasDerivAt_pow 2 c).const_mul (1 / 2)
  have e : (2 : ℕ) - 1 = 1 := rfl
  rw [e] at h
  simp only [pow_one, Nat.cast_ofNat] at h
  rw [show (1 / 2 : ℝ) * (2 * c) = c by ring] at h
  exact h

/-- Coordinate characterization of Mathlib's `gradient` (proof-only). -/
private theorem gradient_coord (P : ℕ) (L : EuclideanSpace ℝ (Fin P) → ℝ)
    (θ : EuclideanSpace ℝ (Fin P)) :
    gradient L θ
      = WithLp.toLp 2 (fun p => fderiv ℝ L θ (EuclideanSpace.single p 1)) := by
  apply PiLp.ext
  intro p
  have h1 := inner_gradient_right (𝕜 := ℝ) (f := L)
    (x := EuclideanSpace.single p (1 : ℝ)) (y := θ)
  rw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul,
    RCLike.conj_to_real] at h1
  rw [h1]

/-- Gradient of the square loss: the transposed Jacobian applied to the
residual. -/
theorem gradient_sqLoss (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin P))
    (hF : ContDiff ℝ 1 F) :
    gradient (sqLoss P n F y) θ
      = WithLp.toLp 2 ((jac P n F θ)ᵀ *ᵥ ⇑(F θ - y)) := by
  rw [gradient_coord P (sqLoss P n F y) θ]
  have hJ : ∀ i : Fin n, HasFDerivAt (fun θ' => F θ' i - y i)
      ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F θ)) θ :=
    fun i => by
    have h : HasFDerivAt ((fun θ' => F θ' i) - fun _ => y i)
        ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F θ) - 0) θ :=
      HasFDerivAt.sub (hasFDerivAt_coord P n F θ i hF)
        (hasFDerivAt_const _ _)
    rwa [sub_zero] at h
  have hsq : ∀ i : Fin n,
      HasFDerivAt (fun θ' => (1 / 2) * (F θ' i - y i) ^ 2)
        ((F θ i - y i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp
          (fderiv ℝ F θ))
        θ := by
    intro i
    have h := HasDerivAt.comp_hasFDerivAt θ
      (hasDerivAt_half_sq (F θ i - y i)) (hJ i)
    exact h
  have hsum : HasFDerivAt
      (∑ i ∈ Finset.univ, fun θ' => (1 / 2) * (F θ' i - y i) ^ 2)
      (∑ i ∈ Finset.univ,
        ((F θ i - y i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp
          (fderiv ℝ F θ)))
      θ :=
    HasFDerivAt.sum (fun i _ => hsq i)
  have hfun : (∑ i ∈ Finset.univ, fun θ' => (1 / 2) * (F θ' i - y i) ^ 2)
      = sqLoss P n F y := by
    funext θ'
    simp [sqLoss, Finset.mul_sum]
  have hderiv : fderiv ℝ (sqLoss P n F y) θ
      = ∑ i ∈ Finset.univ,
        ((F θ i - y i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp
          (fderiv ℝ F θ)) := by
    rw [← hfun]
    exact hsum.fderiv
  have hcoord : (fun p => fderiv ℝ (sqLoss P n F y) θ
      (EuclideanSpace.single p 1))
      = (jac P n F θ)ᵀ *ᵥ ⇑(F θ - y) := by
    funext p
    rw [hderiv, sum_apply, Matrix.mulVec_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci : ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F θ))
        (EuclideanSpace.single p 1) = (jac P n F θ) i p := by
      rw [jac_apply_eq_fderiv_coord P n F θ hF i p]
      exact (fderiv_coord_apply P n F θ i _ hF).symm
    simp only [smul_apply, smul_eq_mul, Matrix.transpose_apply,
      PiLp.sub_apply, hci]
    exact mul_comm _ _
  rw [hcoord]

/-- Coercing a `toLp` vector back to a function. -/
private theorem coe_toLp (n : ℕ) (f : Fin n → ℝ) : ⇑(WithLp.toLp 2 f) = f :=
  WithLp.ofLp_toLp 2 f

/-- Gradient-flow identity: if a trajectory satisfies the gradient-flow ODE
at time `t` (in particular, the hypothesis holds at each positive time of
such a forward gradient-flow trajectory on `t ≥ 0`, and at `t = 0` when the
trajectory extends differentiably through `0`), the outputs evolve by the
negative NTK applied to the residual. The ODE at `t` and global `C¹`
regularity of `F` are hypotheses; existence and uniqueness of the flow, and
constancy of the NTK during training, are not claimed. -/
theorem gradient_flow_identity (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : ℝ → EuclideanSpace ℝ (Fin P))
    (hF : ContDiff ℝ 1 F) (t : ℝ)
    (hθ : HasDerivAt θ (-gradient (sqLoss P n F y) (θ t)) t) :
    HasDerivAt (fun s => F (θ s))
      (-(WithLp.toLp 2 ((ntk P n F (θ t)) *ᵥ ⇑(F (θ t) - y)))) t := by
  have hFAt : HasFDerivAt F (fderiv ℝ F (θ t)) (θ t) :=
    hasFDerivAt_of_contDiff_one P n F (θ t) hF
  have hcomp := HasFDerivAt.comp_hasDerivAt t hFAt hθ
  have hval : (fderiv ℝ F (θ t)) (-gradient (sqLoss P n F y) (θ t))
      = -(WithLp.toLp 2 ((ntk P n F (θ t)) *ᵥ ⇑(F (θ t) - y))) := by
    unfold ntk
    rw [map_neg, fderiv_eq_jac_mulVec _ _ _ _ _ hF,
      gradient_sqLoss _ _ _ _ _ hF, coe_toLp, Matrix.mulVec_mulVec]
  rw [hval] at hcomp
  exact hcomp

/-- One gradient-descent step: first-order NTK prediction with an explicit
second-order remainder under a Hessian bound on the segment. -/
theorem one_step_gd_remainder (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin P))
    (η β : ℝ) (hF : ContDiff ℝ 2 F) (hβ : 0 ≤ β)
    (hH : ∀ θ' ∈ segment ℝ θ (θ - η • gradient (sqLoss P n F y) θ),
      ∀ u v, ‖(fderiv ℝ (fderiv ℝ F) θ' u) v‖ ≤ β * ‖u‖ * ‖v‖) :
    ‖F (θ - η • gradient (sqLoss P n F y) θ) - F θ
        + η • WithLp.toLp 2 ((ntk P n F θ) *ᵥ ⇑(F θ - y))‖
      ≤ (β / 2) * η ^ 2 * ‖gradient (sqLoss P n F y) θ‖ ^ 2 := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hFO : fderiv ℝ F θ (-η • gradient (sqLoss P n F y) θ)
      = -η • WithLp.toLp 2 ((ntk P n F θ) *ᵥ ⇑(F θ - y)) := by
    rw [map_smul, fderiv_eq_jac_mulVec _ _ _ _ _ hF1,
      gradient_sqLoss _ _ _ _ _ hF1, coe_toLp]
    unfold ntk
    rw [Matrix.mulVec_mulVec]
  set g : EuclideanSpace ℝ (Fin P) := gradient (sqLoss P n F y) θ with hg
  set h : EuclideanSpace ℝ (Fin P) := -η • g with hh
  have hstep : θ - η • g = θ + h := by rw [hh, sub_eq_add_neg, ← neg_smul]
  rw [hstep] at hH
  set R : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun s => F (θ + s • h) - F θ - s • fderiv ℝ F θ h with hR
  set R' : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun s => (fderiv ℝ F (θ + s • h) - fderiv ℝ F θ) h with hR'
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, θ + s • h ∈ segment ℝ θ (θ + h) := by
    intro s hs
    have hseg := segment_eq_image' ℝ θ (θ + h)
    have hsub : (θ + h) - θ = h := add_sub_cancel_left θ h
    rw [hseg, hsub]
    exact Set.mem_image_of_mem _ hs
  have hHop : ∀ x ∈ segment ℝ θ (θ + h),
      ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ β := by
    intro x hx
    refine ContinuousLinearMap.opNorm_le_bound _ hβ fun u => ?_
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hβ (norm_nonneg _)) fun v => ?_
    calc ‖(fderiv ℝ (fderiv ℝ F) x u) v‖ ≤ β * ‖u‖ * ‖v‖ := hH x hx u v
      _ = (β * ‖u‖) * ‖v‖ := by ring
  have hMVT : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ F (θ + s • h) - fderiv ℝ F θ‖
        ≤ β * ‖(θ + s • h) - θ‖ := by
    intro s hs
    have hf : ∀ x ∈ segment ℝ θ (θ + h),
        HasFDerivWithinAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x)
          (segment ℝ θ (θ + h)) x :=
      fun x _ => (hFd.differentiable_one.differentiableAt.hasFDerivAt).hasFDerivWithinAt
    exact (convex_segment θ (θ + h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hf (fun x hx => hHop x hx) (left_mem_segment ℝ θ (θ + h)) (hmem s hs)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt R (R' s) s := by
    intro s _
    have hpath : HasDerivAt (fun s : ℝ => θ + s • h) h s := by
      have hid : HasDerivAt (fun s : ℝ => s • h) ((1 : ℝ) • h) s :=
        (hasDerivAt_id s).smul_const h
      rw [one_smul] at hid
      exact hid.const_add θ
    have hcomp : HasDerivAt (fun s : ℝ => F (θ + s • h))
        ((fderiv ℝ F (θ + s • h)) h) s :=
      (hasFDerivAt_of_contDiff_one P n F _ hF1).comp_hasDerivAt s hpath
    have hlin : HasDerivAt (fun s : ℝ => s • fderiv ℝ F θ h)
        ((1 : ℝ) • fderiv ℝ F θ h) s :=
      (hasDerivAt_id s).smul_const _
    rw [one_smul] at hlin
    have hsub : HasDerivAt (fun s => F (θ + s • h) - F θ - s • fderiv ℝ F θ h)
        ((fderiv ℝ F (θ + s • h)) h - fderiv ℝ F θ h) s :=
      (hcomp.sub_const (F θ)).sub hlin
    simp only [hR, hR']
    rw [sub_apply]
    exact hsub
  have hcont : Continuous R' := by
    rw [hR']
    have hpathc : Continuous fun s : ℝ => θ + s • h :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hD1 : Continuous fun s : ℝ => fderiv ℝ F (θ + s • h) :=
      hFd.differentiable_one.continuous.comp hpathc
    have hD : Continuous fun s : ℝ => fderiv ℝ F (θ + s • h) - fderiv ℝ F θ :=
      hD1.sub continuous_const
    exact Continuous.clm_apply hD continuous_const
  have hintR' : IntervalIntegrable R' MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hbound_int : IntervalIntegrable (fun s : ℝ => β * s * ‖h‖ ^ 2)
      MeasureTheory.volume 0 1 :=
    ((continuous_const.mul continuous_id).mul
      continuous_const).intervalIntegrable 0 1
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖R' s‖ ≤ β * s * ‖h‖ ^ 2 := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, hs.2⟩
    simp only [hR']
    have hle : ‖(fderiv ℝ F (θ + s • h) - fderiv ℝ F θ) h‖
        ≤ ‖fderiv ℝ F (θ + s • h) - fderiv ℝ F θ‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hseglen : ‖(θ + s • h) - θ‖ = s * ‖h‖ := by
      have heq : (θ + s • h) - θ = s • h := add_sub_cancel_left θ (s • h)
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs.1)]
    calc ‖(fderiv ℝ F (θ + s • h) - fderiv ℝ F θ) h‖
        ≤ ‖fderiv ℝ F (θ + s • h) - fderiv ℝ F θ‖ * ‖h‖ := hle
      _ ≤ (β * ‖(θ + s • h) - θ‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (hMVT s hsIcc) (norm_nonneg _)
      _ = β * s * ‖h‖ ^ 2 := by rw [hseglen]; ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintR'
  have hInt : (∫ s in (0 : ℝ)..1, β * s * ‖h‖ ^ 2) = (β / 2) * ‖h‖ ^ 2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_id]
    ring
  have hnorm : ‖R 1 - R 0‖ ≤ (β / 2) * ‖h‖ ^ 2 := by
    rw [← hFTC]
    calc ‖∫ y in (0 : ℝ)..1, R' y‖
        ≤ ∫ s in (0 : ℝ)..1, β * s * ‖h‖ ^ 2 :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            (Filter.Eventually.of_forall fun s hs => hbound s hs) hbound_int
      _ = (β / 2) * ‖h‖ ^ 2 := hInt
  have hR0 : R 0 = 0 := by simp [hR]
  have hR1 : R 1
      = F (θ - η • g) - F θ + η • WithLp.toLp 2 ((ntk P n F θ) *ᵥ ⇑(F θ - y)) := by
    simp only [hR]
    rw [one_smul, one_smul, ← hstep, hFO, neg_smul, sub_neg_eq_add]
  have hnorm0 : ‖R 1‖ ≤ (β / 2) * ‖h‖ ^ 2 := by
    rw [hR0, sub_zero] at hnorm
    exact hnorm
  have hhnorm : ‖h‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
    rw [hh, norm_smul, Real.norm_eq_abs, mul_pow, abs_neg, sq_abs]
  rw [← hR1]
  calc ‖R 1‖ ≤ (β / 2) * ‖h‖ ^ 2 := hnorm0
    _ = (β / 2) * η ^ 2 * ‖g‖ ^ 2 := by rw [hhnorm]; ring

/-- A linear model has constant NTK equal to the linear kernel `X Xᵀ`. -/
theorem ntk_linear (P n : ℕ) (X : Matrix (Fin n) (Fin P) ℝ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (hF : F = fun θ : EuclideanSpace ℝ (Fin P) => WithLp.toLp 2 (X *ᵥ ⇑θ))
    (θ : EuclideanSpace ℝ (Fin P)) :
    ntk P n F θ = X * Xᵀ := by
  have hJ : jac P n F θ = X := by
    have hfun : (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x)))
        = fun x => X *ᵥ x := by
      funext x
      simp only [hF, coe_toLp]
    change MetaMathlibExt.jacobianMatrix
      (fun x : Fin P → ℝ => ⇑(F (WithLp.toLp 2 x))) ⇑θ = X
    rw [hfun]
    exact MetaMathlibExt.jacobianMatrix_fun_mulVec X ⇑θ
  change jac P n F θ * (jac P n F θ)ᵀ = X * Xᵀ
  rw [hJ]

end Cslib.MachineLearning.NeuralTangentKernel
