/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Russo

/-!
# Russo's formula as a sum of covariances, and influences

For an increasing event `A` on a finite set `E` and `0 < p < 1`,
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e Cov_p(1_A, 1_{ω_e = 1})`, and each covariance equals
`p(1 - p)` times
the probability that `e` is pivotal (the influence of `e`). For `p ∈ [ε, 1 - ε]` this gives the
lower bound `d/dp ℙ_p(A) ≥ ε(1 - ε) ∑_e I_e(A)` used in sharp-threshold arguments.

## Main definitions

* `StatMech.BeffaraDC.openEdge`: the event that the edge `e` is open.
* `StatMech.BeffaraDC.influence`: the influence `I_e^p(A) = ℙ_p(e is pivotal for A)`.

## Main results

* `StatMech.BeffaraDC.cov_eq`: `Cov_p(1_A, 1_{ω_e = 1}) = p(1 - p) ℙ_p(e pivotal for A)`.
* `StatMech.BeffaraDC.russoFormula`: Russo's formula in covariance form.
* `StatMech.BeffaraDC.deriv_eq_total_influence`: `d/dp ℙ_p(A) = ∑_e I_e^p(A)`.
* `StatMech.BeffaraDC.deriv_ge_total_influence`, `StatMech.BeffaraDC.cov_ge_influence`: bounds
  for `p ∈ [ε, 1 - ε]`.

## References

* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981),
  229–237.
* H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, 2017.
-/

@[expose] public section

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The event `{ω_e = 1}` that the edge `e` is open. -/
def openEdge (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

omit [Fintype E] [DecidableEq E] in
lemma openEdge_indicator (e : E) (ω : ConfigSpace E) :
    (openEdge e).indicator (fun _ => (1 : ℝ)) ω = (if ω e then (1 : ℝ) else 0) := by
  classical
  rw [Set.indicator_apply]
  by_cases h : ω e
  · rw [ite_eq_left (show ω ∈ openEdge e from h), ite_eq_left h]
  · rw [ite_eq_right (show ω ∉ openEdge e from h), ite_eq_right h]

lemma sum_weightOff_true_eta (p : ℝ) (e : E) :
    ∑ η : {j : E // j ≠ e} → Bool,
      weightOff p e ((Equiv.funSplitAt e Bool).symm (true, η)) = 1 := by
  have key : ∀ η : {j : E // j ≠ e} → Bool,
      weightOff p e ((Equiv.funSplitAt e Bool).symm (true, η))
      = ∏ j : {x : E // x ≠ e}, (if η j then p else 1 - p) := by
    intro η
    unfold weightOff edgeWeight
    rw [Finset.prod_subtype (univ.erase e) (p := fun x => x ≠ e)
          (fun x => by simp [Finset.mem_erase, and_comm])
          (fun j => if ((Equiv.funSplitAt e Bool).symm (true, η)) j then p else 1 - p)]
    apply Finset.prod_congr rfl
    intro j _
    have hval : ((Equiv.funSplitAt e Bool).symm (true, η)) (j : E) = η j := by
      simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
    rw [hval]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun (j : {x : E // x ≠ e}) (b : Bool) => if b then p else 1 - p)]
  apply Finset.prod_eq_one
  intro j _; rw [Fintype.sum_bool]; simp

lemma sum_filter_true_eq_eta (e : E) (f : ConfigSpace E → ℝ) :
    ∑ ω : ConfigSpace E, (if ω e then f ω else 0)
    = ∑ η : {j : E // j ≠ e} → Bool, f ((Equiv.funSplitAt e Bool).symm (true, η)) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm (fun ω => if ω e then f ω else 0)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hT : ∀ η : {j : E // j ≠ e} → Bool,
      ((Equiv.funSplitAt e Bool).symm (true, η)) e = true := fun η => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hF : ∀ η : {j : E // j ≠ e} → Bool,
      ((Equiv.funSplitAt e Bool).symm (false, η)) e = false := fun η => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [show (∑ η, if ((Equiv.funSplitAt e Bool).symm (true, η)) e
              then f ((Equiv.funSplitAt e Bool).symm (true, η)) else 0)
        = ∑ η, f ((Equiv.funSplitAt e Bool).symm (true, η)) from by
        apply Finset.sum_congr rfl; intro η _; rw [hT η]; rfl]
  rw [show (∑ η, if ((Equiv.funSplitAt e Bool).symm (false, η)) e
              then f ((Equiv.funSplitAt e Bool).symm (false, η)) else 0)
        = (0 : ℝ) from by
        apply Finset.sum_eq_zero; intro η _; rw [hF η]; rfl]
  ring

lemma sum_weightOff_filter (p : ℝ) (e : E) :
    ∑ ω : ConfigSpace E, (if ω e then weightOff p e ω else 0) = 1 := by
  rw [sum_filter_true_eq_eta e (fun ω => weightOff p e ω)]
  exact sum_weightOff_true_eta p e

lemma prob_openEdge (p : ℝ) (e : E) : prob p (openEdge e) = p := by
  unfold prob
  have step : ∀ ω : ConfigSpace E,
      (openEdge e).indicator (fun _ => (1 : ℝ)) ω * configWeight p ω
      = p * (if ω e then weightOff p e ω else 0) := by
    intro ω
    rw [openEdge_indicator, configWeight_eq p e ω]
    unfold edgeWeight
    by_cases h : ω e <;> simp [h]
  simp_rw [step]
  rw [← Finset.mul_sum, sum_weightOff_filter]; ring

lemma prob_inter_openEdge (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    prob p (A ∩ openEdge e)
    = p * ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω *
        (if ω e then (1 : ℝ) else 0) := by
  unfold prob
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeight_eq p e ω]
  unfold edgeWeight
  classical
  by_cases h : ω e
  · have hmem : ω ∈ A ∩ openEdge e ↔ ω ∈ A := by simp [openEdge, h]
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hA : ω ∈ A
    · simp [hA, (hmem.mpr hA), h]
    · have : ω ∉ A ∩ openEdge e := fun hc => hA hc.1
      simp [hA, this, h]
  · have hnotmem : ω ∉ A ∩ openEdge e := fun hc => h hc.2
    rw [Set.indicator_of_notMem hnotmem]
    simp [h]

lemma prob_decompose (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    prob p A
    = p * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω *
          (if ω e then (1 : ℝ) else 0))
      + (1 - p)
        * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω *
          (if ω e then (0 : ℝ) else 1)) := by
  unfold prob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeight_eq p e ω]
  unfold edgeWeight
  by_cases h : ω e <;> simp [h] <;> ring

lemma russo_per_edge_diff (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0))
    - (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1))
    = pivotalProb p A e := by
  rw [← russo_per_edge p A hA e, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω e <;> simp [h]

theorem cov_eq (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A
      = p * (1 - p) * pivotalProb p A e := by
  set Sp := ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0)
    with hSp
  set Sm := ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1)
    with hSm
  rw [prob_inter_openEdge p A e, prob_openEdge p e, prob_decompose p A e,
      ← hSp, ← hSm, ← russo_per_edge_diff p A hA e, ← hSp, ← hSm]
  ring

theorem sum_cov_eq (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A)
      = p * (1 - p) * ∑ e, pivotalProb p A e := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => cov_eq p A hA e)

/-- **Russo's formula**, covariance form: for increasing `A` and `p ∉ {0, 1}`,
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e (ℙ_p(A ∩ {ω_e = 1}) - ℙ_p(ω_e = 1) ℙ_p(A))`. -/
theorem russoFormula (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p)))
          * ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A) := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p, sum_cov_eq p A hA]
  have hne : p * (1 - p) ≠ 0 := mul_ne_zero hp0 (by intro h; exact hp1 (by linarith))
  field_simp

/-- The influence `I_e^p(A) = ℙ_p(e is pivotal for A)` of the coordinate `e` on the event `A`
under the `p`-biased product measure.

See also `MathlibExt.Analysis.Fourier.BooleanCubeInfluence.boolInfluence`, the influence of a
real function on the uniform Boolean cube (the case `p = 1/2`, in Fourier normalization). -/
noncomputable def influence (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  pivotalProb p A e

lemma influence_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ influence p A e :=
  pivotalProb_nonneg hp0 hp1 A e

theorem cov_ge_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    ε * (1 - ε) * influence p A e
      ≤ prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A := by
  rw [cov_eq p A hA e]
  unfold influence
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  have hpiv : 0 ≤ pivotalProb p A e := pivotalProb_nonneg hp0 hp1 A e
  have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
  nlinarith [hpiv, hfac]

theorem deriv_ge_total_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    ε * (1 - ε) * ∑ e, influence p A e ≤ deriv (fun p => prob p A) p := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  unfold influence
  rw [Finset.mul_sum]
  calc ∑ e, ε * (1 - ε) * pivotalProb p A e
      ≤ ∑ e, p * (1 - p) * pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        nlinarith [hfac, hpiv]
    _ ≤ ∑ e, pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        have hle1 : p * (1 - p) ≤ 1 := by nlinarith [hp0, hp1]
        nlinarith [hle1, hpiv]

theorem deriv_eq_total_influence (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    deriv (fun p => prob p A) p = ∑ e, influence p A e := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  rfl

end BeffaraDC

end StatMech
