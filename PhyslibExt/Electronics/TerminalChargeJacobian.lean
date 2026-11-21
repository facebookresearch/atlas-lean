/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

/-!
# Terminal-charge Jacobians

## i. Overview

For differentiable terminal charge maps on an open voltage
domain, charge conservation makes every Jacobian column sum zero,
and local invariance under common-mode voltage shifts makes every
Jacobian row sum zero. Pairwise capacitor charges are the positive
validation case; a charge-leaking map and a ground-referenced map
show that the two premises are distinct.

## ii. Key results

- `jacobian_col_sum_eq_zero_of_charge_conservation`: zero column
  sums from charge conservation.
- `jacobian_row_sum_eq_zero_of_common_mode_invariance`: zero row
  sums from local common-mode invariance.
- `terminal_charge_jacobian_sums_eq_zero`: both conclusions under
  both premises.

## iii. Table of contents

- A. Terminal-charge Jacobians
- A.1 Pairwise capacitor charges
- A.2 Violated premises

## iv. References

- S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: terminal-charge models
  for compact semiconductor devices.

## A. Terminal-charge Jacobians

-/

@[expose] public section

namespace PhyslibExt.Electronics.TerminalChargeJacobian

open MetaMathlibExt
open scoped Filter Topology

/-- Derivative of an affine line `t ↦ v + t • w` at `0` is `w`. -/
private lemma hasDerivAt_affine_line (n : ℕ) (v w : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => v + t • w) w 0 := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id' 0
  have hs : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using HasDerivAt.smul_const h1 w
  exact HasDerivAt.const_add v hs

/-- Chain rule for `g` along an affine line through `v` in direction `w`. -/
private lemma hasDerivAt_comp_affine (n : ℕ) (g : (Fin n → ℝ) → ℝ) (v w : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g v) :
    HasDerivAt (g ∘ (fun t : ℝ => v + t • w)) ((fderiv ℝ g v) w) 0 := by
  have hγ := hasDerivAt_affine_line n v w
  have h0 : (fun t : ℝ => v + t • w) 0 = v := by simp only [zero_smul, add_zero]
  have hgc : HasFDerivAt g (fderiv ℝ g v) v := hg.hasFDerivAt
  have hgc0 : HasFDerivAt g (fderiv ℝ g v) ((fun t : ℝ => v + t • w) 0) := by
    rw [h0]; exact hgc
  exact hgc0.comp_hasDerivAt 0 hγ

/-- The derivative of `g` along an affine line is the Fréchet derivative applied. -/
private lemma deriv_comp_affine_eq_fderiv (n : ℕ) (g : (Fin n → ℝ) → ℝ) (v w : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g v) :
    deriv (fun t : ℝ => g (v + t • w)) 0 = fderiv ℝ g v w :=
  (hasDerivAt_comp_affine n g v w hg).deriv

/-- The standard basis sums to the all-ones vector. -/
private lemma sum_pi_single_eq_one (n : ℕ) :
    (∑ j : Fin n, Pi.single j (1 : ℝ)) = fun _ => (1 : ℝ) := by
  funext k
  simp only [Finset.sum_apply]
  have h0 : ∀ x, x ≠ k → Pi.single (M := fun _ => ℝ) x (1 : ℝ) k = 0 :=
    fun x hx => Pi.single_eq_of_ne' hx 1
  exact (Fintype.sum_eq_single k h0).trans (Pi.single_eq_same k 1)

/-- An affine line through a point of an open set stays in the set near `0`. -/
private lemma eventually_affine_mem (n : ℕ) (U : Set (Fin n → ℝ)) (v w : Fin n → ℝ)
    (hU : IsOpen U) (hv : v ∈ U) : ∀ᶠ t in 𝓝 (0 : ℝ), v + t • w ∈ U := by
  have hγ := hasDerivAt_affine_line n v w
  have hcont : ContinuousAt (fun t : ℝ => v + t • w) 0 := hγ.differentiableAt.continuousAt
  have h0 : (fun t : ℝ => v + t • w) 0 = v := by simp only [zero_smul, add_zero]
  have hmem : U ∈ 𝓝 ((fun t : ℝ => v + t • w) 0) := by rw [h0]; exact hU.mem_nhds hv
  have hp : ∀ᶠ y in 𝓝 ((fun t : ℝ => v + t • w) 0), y ∈ U := by
    filter_upwards [hmem] with y hy; exact hy
  exact Filter.Tendsto.eventually hcont hp

/-- A coordinate projection has Fréchet derivative `ContinuousLinearMap.proj`. -/
private lemma hasFDerivAt_proj_apply (n : ℕ) (a : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun v : Fin n → ℝ => v a)
      (ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ) x := by
  have h : HasFDerivAt
      (((ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ)) : (Fin n → ℝ) → ℝ)
      (ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj a : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  apply h.congr_of_eventuallyEq
  filter_upwards with t
  rfl

/-- A pairwise-capacitor component is Fréchet differentiable everywhere. -/
private lemma hasFDerivAt_pairwise_component (n : ℕ) (Cap : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (fun v : Fin n → ℝ => ∑ k, Cap i k * (v i - v k)) x := by
  have hsub (k) :=
    HasFDerivAt.sub (hasFDerivAt_proj_apply n i x) (hasFDerivAt_proj_apply n k x)
  have hmul (k) := HasFDerivAt.mul (hasFDerivAt_const (Cap i k) x) (hsub k)
  exact (HasFDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => hmul k)).differentiableAt

/-- Column `j` of the terminal-charge Jacobian sums to the derivative of total charge along
the `j`-th voltage axis. -/
lemma jacobian_col_sum_eq_fderiv_total_charge (n : ℕ) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (v : Fin n → ℝ) (hq : ∀ i, DifferentiableAt ℝ (fun w => q w i) v) (j : Fin n) :
    ∑ i, jacobianMatrix q v i j =
      fderiv ℝ (fun w => ∑ i, q w i) v (Pi.single j (1 : ℝ)) := by
  have hcomp : ∀ i, HasDerivAt ((fun w => q w i) ∘ (fun t : ℝ => v + t • Pi.single j (1 : ℝ)))
      ((fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ))) 0 :=
    fun i => hasDerivAt_comp_affine n (fun w => q w i) v (Pi.single j (1 : ℝ)) (hq i)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i, ((fun w => q w i) ∘ (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t)
      (∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ))) 0 :=
    HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hcomp i)
  have hsumd := hsum.deriv
  have hS : DifferentiableAt ℝ (fun w => ∑ i, q w i) v :=
    (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => (hq i).hasFDerivAt)).differentiableAt
  have hSconv :
      deriv (fun t : ℝ => (fun w => ∑ i, q w i) (v + t • Pi.single j (1 : ℝ))) 0 =
        fderiv ℝ (fun w => ∑ i, q w i) v (Pi.single j (1 : ℝ)) :=
    deriv_comp_affine_eq_fderiv n (fun w => ∑ i, q w i) v (Pi.single j (1 : ℝ)) hS
  have hbridge :
      (fun t : ℝ => ∑ i, ((fun w => q w i) ∘ (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t) =
        (fun t : ℝ => (fun w => ∑ i, q w i) (v + t • Pi.single j (1 : ℝ))) := rfl
  have hcongr : ∑ i, jacobianMatrix q v i j =
      ∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => (hcomp i).deriv)
  calc ∑ i, jacobianMatrix q v i j
      = ∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) := hcongr
    _ = deriv (fun t : ℝ => ∑ i, ((fun w => q w i) ∘
        (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t) 0 := hsumd.symm
    _ = deriv (fun t : ℝ => (fun w => ∑ i, q w i) (v + t • Pi.single j (1 : ℝ))) 0 := by
        rw [hbridge]
    _ = fderiv ℝ (fun w => ∑ i, q w i) v (Pi.single j (1 : ℝ)) := hSconv

/-- Row `i` of the terminal-charge Jacobian sums to the derivative of `c ↦ q_i(v + c 1)` at
`c = 0` (the common-mode derivative). -/
lemma jacobian_row_sum_eq_deriv_common_mode (n : ℕ) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (v : Fin n → ℝ) (hq : ∀ i, DifferentiableAt ℝ (fun w => q w i) v) (i : Fin n) :
    ∑ j, jacobianMatrix q v i j =
      deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 := by
  have hconv : ∀ j, jacobianMatrix q v i j =
      (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
    fun j => deriv_comp_affine_eq_fderiv n (fun w => q w i) v (Pi.single j (1 : ℝ)) (hq i)
  have hsum1 : (∑ j : Fin n, Pi.single j (1 : ℝ)) = (fun _ => (1 : ℝ)) :=
    sum_pi_single_eq_one n
  have hconv1 : deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 =
      (fderiv ℝ (fun w => q w i) v) (fun _ => (1 : ℝ)) :=
    deriv_comp_affine_eq_fderiv n (fun w => q w i) v (fun _ => (1 : ℝ)) (hq i)
  calc ∑ j, jacobianMatrix q v i j
      = ∑ j, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
        Finset.sum_congr rfl (fun j _ => hconv j)
    _ = (fderiv ℝ (fun w => q w i) v) (∑ j, Pi.single j (1 : ℝ)) := by rw [map_sum]
    _ = (fderiv ℝ (fun w => q w i) v) (fun _ => (1 : ℝ)) := by rw [hsum1]
    _ = deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 := hconv1.symm

/-- **Zero column sums from charge conservation.** If the terminal charges are differentiable
on an open voltage domain and sum to zero there, every Jacobian column sums to zero at every
point of the domain. -/
lemma jacobian_col_sum_eq_zero_of_charge_conservation (n : ℕ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (hq : ∀ i, DifferentiableOn ℝ (fun v => q v i) U)
    (hcons : ∀ v ∈ U, ∑ i, q v i = 0) (v : Fin n → ℝ) (hv : v ∈ U) (j : Fin n) :
    ∑ i, jacobianMatrix q v i j = 0 := by
  have hAt : ∀ i, DifferentiableAt ℝ (fun w => q w i) v :=
    fun i => (hq i v hv).differentiableAt (hU.mem_nhds hv)
  have hcomp : ∀ i, HasDerivAt ((fun w => q w i) ∘ (fun t : ℝ => v + t • Pi.single j (1 : ℝ)))
      ((fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ))) 0 :=
    fun i => hasDerivAt_comp_affine n (fun w => q w i) v (Pi.single j (1 : ℝ)) (hAt i)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i, ((fun w => q w i) ∘ (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t)
      (∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ))) 0 :=
    HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hcomp i)
  have hsumd := hsum.deriv
  have hUev : ∀ᶠ t in 𝓝 (0 : ℝ), v + t • Pi.single j (1 : ℝ) ∈ U :=
    eventually_affine_mem n U v (Pi.single j (1 : ℝ)) hU hv
  have heq : (fun t : ℝ => ∑ i, ((fun w => q w i) ∘
      (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hUev] with t ht
    exact hcons (v + t • Pi.single j (1 : ℝ)) ht
  have h0 : deriv (fun t : ℝ => ∑ i, ((fun w => q w i) ∘
      (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t) 0 = 0 := by
    rw [heq.deriv_eq]; simp only [deriv_const]
  have hcongr : ∑ i, jacobianMatrix q v i j =
      ∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => (hcomp i).deriv)
  calc ∑ i, jacobianMatrix q v i j
      = ∑ i, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) := hcongr
    _ = deriv (fun t : ℝ => ∑ i, ((fun w => q w i) ∘
        (fun t : ℝ => v + t • Pi.single j (1 : ℝ))) t) 0 := hsumd.symm
    _ = 0 := h0

/-- **Zero row sums from local common-mode invariance.** If the terminal charges are
differentiable on an open voltage domain and invariant under every sufficiently small
common-mode shift that stays in the domain, every Jacobian row sums to zero at every point of
the domain. -/
lemma jacobian_row_sum_eq_zero_of_common_mode_invariance (n : ℕ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (hq : ∀ i, DifferentiableOn ℝ (fun v => q v i) U)
    (hgauge : ∀ v ∈ U, ∃ δ > 0, ∀ c : ℝ, |c| < δ → v + c • (fun _ => (1 : ℝ)) ∈ U →
      q (v + c • (fun _ => (1 : ℝ))) = q v)
    (v : Fin n → ℝ) (hv : v ∈ U) (i : Fin n) :
    ∑ j, jacobianMatrix q v i j = 0 := by
  have hAt : ∀ i, DifferentiableAt ℝ (fun w => q w i) v :=
    fun i => (hq i v hv).differentiableAt (hU.mem_nhds hv)
  have hconv : ∀ j, jacobianMatrix q v i j =
      (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
    fun j => deriv_comp_affine_eq_fderiv n (fun w => q w i) v (Pi.single j (1 : ℝ)) (hAt i)
  have hsum1 : (∑ j : Fin n, Pi.single j (1 : ℝ)) = (fun _ => (1 : ℝ)) :=
    sum_pi_single_eq_one n
  have hconv1 : deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 =
      (fderiv ℝ (fun w => q w i) v) (fun _ => (1 : ℝ)) :=
    deriv_comp_affine_eq_fderiv n (fun w => q w i) v (fun _ => (1 : ℝ)) (hAt i)
  have hbridge : ∑ j, jacobianMatrix q v i j =
      deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 := by
    calc ∑ j, jacobianMatrix q v i j
        = ∑ j, (fderiv ℝ (fun w => q w i) v) (Pi.single j (1 : ℝ)) :=
          Finset.sum_congr rfl (fun j _ => hconv j)
      _ = (fderiv ℝ (fun w => q w i) v) (∑ j, Pi.single j (1 : ℝ)) := by rw [map_sum]
      _ = (fderiv ℝ (fun w => q w i) v) (fun _ => (1 : ℝ)) := by rw [hsum1]
      _ = deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 := hconv1.symm
  obtain ⟨δ, hδ, hinv⟩ := hgauge v hv
  have hUev : ∀ᶠ c in 𝓝 (0 : ℝ), v + c • (fun _ => (1 : ℝ)) ∈ U :=
    eventually_affine_mem n U v (fun _ => (1 : ℝ)) hU hv
  have hball : ∀ᶠ c in 𝓝 (0 : ℝ), |c| < δ := by
    rw [Metric.eventually_nhds_iff_ball]
    exact ⟨δ, hδ, fun y hy => by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy⟩
  have heq : (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => q v i) := by
    filter_upwards [hball, hUev] with c hc1 hc2
    exact congrFun (hinv c hc1 hc2) i
  have h0 : deriv (fun c : ℝ => q (v + c • (fun _ => (1 : ℝ))) i) 0 = 0 := by
    rw [heq.deriv_eq]; simp only [deriv_const]
  rw [hbridge]; exact h0

/-- **Charge-conserving, gauge-invariant terminal-charge Jacobian.** For differentiable
terminal charge maps on an open voltage domain, charge conservation `Σ_i q_i = 0` gives zero
Jacobian column sums and local common-mode invariance `q(v + c 1) = q(v)` gives zero row sums,
at every point of the domain. -/
lemma terminal_charge_jacobian_sums_eq_zero (n : ℕ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (hq : ∀ i, DifferentiableOn ℝ (fun v => q v i) U)
    (hcons : ∀ v ∈ U, ∑ i, q v i = 0)
    (hgauge : ∀ v ∈ U, ∃ δ > 0, ∀ c : ℝ, |c| < δ → v + c • (fun _ => (1 : ℝ)) ∈ U →
      q (v + c • (fun _ => (1 : ℝ))) = q v) :
    ∀ v ∈ U, (∀ j, ∑ i, jacobianMatrix q v i j = 0) ∧
      (∀ i, ∑ j, jacobianMatrix q v i j = 0) := by
  intro v hv
  exact ⟨fun j => jacobian_col_sum_eq_zero_of_charge_conservation n U hU q hq hcons v hv j,
    fun i => jacobian_row_sum_eq_zero_of_common_mode_invariance n U hU q hq hgauge v hv i⟩

/-! ### A.1 Pairwise capacitor charges -/

/-- Pairwise (two-terminal) capacitor charges: terminal `i` carries
`q_i = Σ_k C_ik (v_i - v_k)`. -/
def pairwiseCapacitorCharge (n : ℕ) (Cap : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∑ k, Cap i k * (v i - v k)

/-- Validation: with symmetric pairwise capacitances, total terminal charge is zero. -/
lemma pairwiseCapacitorCharge_sum_eq_zero (n : ℕ) (Cap : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ i k, Cap i k = Cap k i) (v : Fin n → ℝ) :
    ∑ i, pairwiseCapacitorCharge n Cap v i = 0 := by
  simp only [pairwiseCapacitorCharge]
  have hterm : ∀ i k, Cap i k * (v i - v k) + Cap k i * (v k - v i) = 0 :=
    fun i k => by rw [hsymm k i]; ring
  have hSr : (∑ i, ∑ k, Cap i k * (v i - v k)) =
      (∑ i, ∑ k, Cap k i * (v k - v i)) := by rw [Finset.sum_comm]
  have h2 : (∑ i, ∑ k, Cap i k * (v i - v k)) +
      (∑ i, ∑ k, Cap k i * (v k - v i)) = 0 := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun k _ => hterm i k))
  have hSS : (∑ i, ∑ k, Cap i k * (v i - v k)) +
      (∑ i, ∑ k, Cap i k * (v i - v k)) = 0 := by rw [← hSr] at h2; exact h2
  linarith

/-- Validation: pairwise capacitor charges are invariant under every common-mode shift. -/
lemma pairwiseCapacitorCharge_common_mode (n : ℕ) (Cap : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (c : ℝ) :
    pairwiseCapacitorCharge n Cap (v + c • (fun _ => (1 : ℝ))) =
      pairwiseCapacitorCharge n Cap v := by
  funext i
  simp only [pairwiseCapacitorCharge]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have e1 : (v + c • (fun _ : Fin n => (1 : ℝ))) i = v i + c • (1 : ℝ) := rfl
  have e2 : (v + c • (fun _ : Fin n => (1 : ℝ))) k = v k + c • (1 : ℝ) := rfl
  rw [e1, e2]
  simp only [smul_eq_mul]
  ring

/-- Validation (positive case): the pairwise-capacitor Jacobian has zero column and row sums
at every voltage. -/
lemma pairwiseCapacitorCharge_jacobian_sums_eq_zero (n : ℕ)
    (Cap : Matrix (Fin n) (Fin n) ℝ) (hsymm : ∀ i k, Cap i k = Cap k i) (v : Fin n → ℝ) :
    (∀ j, ∑ i, jacobianMatrix (pairwiseCapacitorCharge n Cap) v i j = 0) ∧
      (∀ i, ∑ j, jacobianMatrix (pairwiseCapacitorCharge n Cap) v i j = 0) := by
  have hq : ∀ i, DifferentiableOn ℝ (fun v => pairwiseCapacitorCharge n Cap v i) Set.univ :=
    fun i x _ => (hasFDerivAt_pairwise_component n Cap i x).differentiableWithinAt
  have hcons : ∀ v ∈ (Set.univ : Set (Fin n → ℝ)),
      ∑ i, pairwiseCapacitorCharge n Cap v i = 0 :=
    fun v _ => pairwiseCapacitorCharge_sum_eq_zero n Cap hsymm v
  have hgauge : ∀ v ∈ (Set.univ : Set (Fin n → ℝ)), ∃ δ > 0, ∀ c : ℝ, |c| < δ →
      v + c • (fun _ => (1 : ℝ)) ∈ Set.univ →
      pairwiseCapacitorCharge n Cap (v + c • (fun _ => (1 : ℝ))) =
        pairwiseCapacitorCharge n Cap v :=
    fun v _ => ⟨1, one_pos, fun c _ _ => pairwiseCapacitorCharge_common_mode n Cap v c⟩
  exact terminal_charge_jacobian_sums_eq_zero n Set.univ isOpen_univ
    (pairwiseCapacitorCharge n Cap) hq hcons hgauge v (Set.mem_univ v)

/-! ### A.2 Violated premises -/

/-- Violated premise (charge leak): `q(v) = (v₀ - v₁, v₀ - v₁)` is common-mode invariant but
does not conserve charge, and its Jacobian column `0` sums to `2`, not `0`. -/
lemma leaky_charge_column_sum_ne_zero :
    (∀ (v : Fin 2 → ℝ) (c : ℝ),
        (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) (v + c • (fun _ => (1 : ℝ))) =
          (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) v) ∧
      (∃ v : Fin 2 → ℝ, ∑ i, (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) v i ≠ 0) ∧
      ∑ i, jacobianMatrix (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) 0 i 0 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v c
    have h : ∀ i, (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1])
        (v + c • (fun _ => (1 : ℝ))) i =
        (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) v i := by
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        rw [show ((v + c • (fun _ : Fin 2 => (1 : ℝ))) 0) = v 0 + c • (1 : ℝ) from rfl,
          show ((v + c • (fun _ : Fin 2 => (1 : ℝ))) 1) = v 1 + c • (1 : ℝ) from rfl] <;>
        simp only [smul_eq_mul] <;> ring
    exact funext h
  · refine ⟨![1, 0], ?_⟩
    simp only [Fin.sum_univ_two]
    show (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) ![1, 0] 0 +
        (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) ![1, 0] 1 ≠ 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · have hfun : (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) =
        fun w => Matrix.mulVec (!![1, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) w := by
      funext w i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hfun, MetaMathlibExt.jacobianMatrix_fun_mulVec]
    simp only [Fin.sum_univ_two]
    norm_num

/-- Violated premise (ground reference): `q(v) = (v₀, -v₀)` conserves charge but is not
common-mode invariant, and its Jacobian row `0` sums to `1`, not `0`. -/
lemma ground_referenced_row_sum_ne_zero :
    (∀ v : Fin 2 → ℝ, ∑ i, (fun w : Fin 2 → ℝ => ![w 0, -w 0]) v i = 0) ∧
      (∃ v : Fin 2 → ℝ, ∀ δ > 0, ∃ c : ℝ, |c| < δ ∧
        (fun w : Fin 2 → ℝ => ![w 0, -w 0]) (v + c • (fun _ => (1 : ℝ))) ≠
          (fun w : Fin 2 → ℝ => ![w 0, -w 0]) v) ∧
      ∑ j, jacobianMatrix (fun w : Fin 2 → ℝ => ![w 0, -w 0]) 0 0 j = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp only [Fin.sum_univ_two]
    show ![v 0, -v 0] 0 + ![v 0, -v 0] 1 = 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · refine ⟨0, fun δ hδ => ?_⟩
    refine ⟨δ / 2, ?_, ?_⟩
    · rw [abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
      linarith
    · intro h
      have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_one] at h0
      have hne : (δ : ℝ) / 2 ≠ 0 := by positivity
      exact hne (by linarith)
  · have hfun : (fun w : Fin 2 → ℝ => ![w 0, -w 0]) =
        fun w => Matrix.mulVec (!![1, 0; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) w := by
      funext w i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hfun, MetaMathlibExt.jacobianMatrix_fun_mulVec]
    simp only [Fin.sum_univ_two]
    norm_num

end PhyslibExt.Electronics.TerminalChargeJacobian
