/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGray
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExtTest.Probability.Statistics.FineGray

/-! ### Fine–Gray risk sets and partial likelihood on a three-subject example

Subjects observed at times `1, 2, 3`: subject `0` fails from the competing cause `1`, subject
`1` fails from the cause of interest `0`, subject `2` is censored. -/

/-- Observed times. -/
def X₀ : Fin 3 → ℝ := ![1, 2, 3]

/-- Statuses: competing failure, cause-`0` failure, censored. -/
def ε₀ : Fin 3 → Option (Fin 2) := ![some 1, some 0, none]

/-- The Fine–Gray risk set at the cause-`0` failure keeps the earlier competing-event subject. -/
theorem fgRiskSet_ex : fgRiskSet X₀ ε₀ 0 1 = Finset.univ := by
  ext l
  simp only [mem_fgRiskSet, Finset.mem_univ, iff_true]
  fin_cases l <;> norm_num [X₀, ε₀]

/-- The Cox risk set at the same time drops it. -/
theorem riskSet_ex : riskSet X₀ 1 = {1, 2} := by
  ext l
  simp only [riskSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases l <;> norm_num [X₀]

/-- The Fine–Gray risk set is strictly larger than the Cox risk set here. -/
example : riskSet X₀ 1 ≠ fgRiskSet X₀ ε₀ 0 1 := by
  rw [fgRiskSet_ex, riskSet_ex]
  intro h
  have : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := h ▸ Finset.mem_univ 0
  simp at this

private lemma filter_cause_ex :
    Finset.univ.filter (fun i : Fin 3 => ε₀ i = some 0) = {1} := by
  decide

/-- The competing-event time is moved to `|1| + |2| + |3| = 6`; the others are kept. -/
example : fgTime X₀ ε₀ 0 0 = 6 ∧ fgTime X₀ ε₀ 0 1 = 2 ∧ fgTime X₀ ε₀ 0 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [fgTime, X₀, ε₀, Fin.sum_univ_three]

/-- At `β = 0` the Fine–Gray partial likelihood is `1 / |R*| = 1 / 3`. -/
theorem fgPartialLikelihood_ex (x : Fin 3 → Fin 1 → ℝ) :
    fgPartialLikelihood X₀ ε₀ 0 x 0 = 1 / 3 := by
  rw [fgPartialLikelihood, filter_cause_ex, Finset.prod_singleton, fgRiskSet_ex]
  simp

private lemma filter_causeIndicator_ex :
    Finset.univ.filter (fun i : Fin 3 => causeIndicator ε₀ 0 i = true) = {1} := by
  decide

/-- At `β = 0` the Cox partial likelihood that drops the competing-event subject is `1 / 2`, so
the two partial likelihoods differ. -/
theorem partialLikelihood_ex (x : Fin 3 → Fin 1 → ℝ) :
    partialLikelihood X₀ (causeIndicator ε₀ 0) x 0 = 1 / 2 := by
  rw [partialLikelihood, filter_causeIndicator_ex, Finset.prod_singleton, riskSet_ex]
  simp

/-- Censoring survival `G(t) = 1 / t`: the competing-event subject gets weight
`G(2) / G(1) = 1 / 2` at time `2`. -/
theorem fgWeight_ex : fgWeight X₀ ε₀ 0 (fun t => 1 / t) 0 1 = 1 / 2 := by
  norm_num [fgWeight, X₀, ε₀]

/-- The weighted Fine–Gray partial likelihood at `β = 0` is `1 / (1/2 + 1 + 1) = 2 / 5`. -/
theorem fgWeightedPartialLikelihood_ex (x : Fin 3 → Fin 1 → ℝ) :
    fgWeightedPartialLikelihood X₀ ε₀ 0 (fun t => 1 / t) x 0 = 2 / 5 := by
  rw [fgWeightedPartialLikelihood, filter_cause_ex, Finset.prod_singleton, Fin.sum_univ_three]
  norm_num [fgWeight, X₀, ε₀]

/-- Boundary: without cause-`c` failures the Fine–Gray partial likelihood is the empty product. -/
example {n p : ℕ} (X : Fin n → ℝ) (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    fgPartialLikelihood X (fun _ => (none : Option (Fin 2))) 0 x β = 1 := by
  simp [fgPartialLikelihood]

/-- The concavity theorem applies to the example. -/
example (x : Fin 3 → Fin 1 → ℝ) : ConcaveOn ℝ univ (fgLogPartialLikelihood X₀ ε₀ 0 x) :=
  concaveOn_fgLogPartialLikelihood X₀ ε₀ 0 x

/-! ### Subdistribution hazards computed from the definition -/

section Boundary

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- A subject that failed from a competing cause before `t` is in the risk event at `t`. -/
example (T : Ω → ℝ) (J : Ω → ι) (c : ι) (t : ℝ) (ω : Ω) (h1 : T ω < t) (h2 : J ω ≠ c) :
    ω ∈ subdistRiskSet T J c t :=
  Or.inr ⟨h1, h2⟩

/-- Boundary: if every failure is from another cause, the subdistribution hazard of `c` is `0`
at every time (computed from the definition). -/
theorem hasSubdistHazardAt_zero_of_ne (P : Measure Ω) (T : Ω → ℝ) {J : Ω → ι} {c : ι}
    (hJ : ∀ ω, J ω ≠ c) (t : ℝ) : HasSubdistHazardAt P T J c t 0 := by
  have h : ∀ h, subdistHazardQuotient P T J c t h = 0 := fun h => by
    have hE : causeEventIn T J c t h = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => hJ ω hω.2.2
    simp [subdistHazardQuotient, hE]
  have hf : subdistHazardQuotient P T J c t = fun _ => 0 := funext h
  rw [HasSubdistHazardAt, hf]
  exact tendsto_const_nhds

/-- The proportional subdistribution hazards model is satisfiable (zero baseline hazard). -/
example (P : (Fin 1 → ℝ) → Measure Ω) (T : Ω → ℝ) {J : Ω → ι} {c : ι} (hJ : ∀ ω, J ω ≠ c)
    (β : Fin 1 → ℝ) : IsPropSubdistHazards P T J c (fun _ => 0) β := fun x t _ => by
  simpa using hasSubdistHazardAt_zero_of_ne (P x) T hJ t

end Boundary

/-! ### The uniform failure time on `[0, 1]` with a single cause -/

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Icc]⟩

/-- The single failure cause. -/
def J₁ : ℝ → Unit := fun _ => ()

theorem unif_real_Ico {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) : unif.real (Ico 0 h) = h := by
  have hI : Ico 0 h ∩ Icc 0 1 = Ico 0 h :=
    inter_eq_left.2 (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl h1))
  rw [unif, measureReal_def, Measure.restrict_apply measurableSet_Ico, hI, Real.volume_Ico,
    sub_zero, ENNReal.toReal_ofReal h0]

/-- The cumulative incidence of the uniform failure time is `F(t) = t` on `[0, 1]`. -/
theorem cif_unif {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cif unif id J₁ () t = t := by
  have hs : {ω : ℝ | id ω ≤ t ∧ J₁ ω = ()} = Iic t := by ext ω; simp
  have hI : Iic t ∩ Icc 0 1 = Icc 0 t := by
    ext ω
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans h1⟩⟩
  rw [cif, hs, unif, measureReal_def, Measure.restrict_apply measurableSet_Iic, hI,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal h0]

/-- **The subdistribution hazard of the uniform failure time at `0` is `1`**, computed from the
limit definition: for `0 < h < 1` the conditional difference quotient is `(h / 1) / h = 1`. -/
theorem hasSubdistHazardAt_unif_zero : HasSubdistHazardAt unif id J₁ () 0 1 := by
  have hR : subdistRiskSet id J₁ () 0 = Ici 0 := by
    ext ω; simp [subdistRiskSet, J₁]
  have hR1 : unif (Ici 0) = 1 := by
    rw [unif, Measure.restrict_apply measurableSet_Ici, inter_eq_right.2 Icc_subset_Ici_self,
      Real.volume_Icc]
    simp
  have hq : ∀ h ∈ Ioo (0 : ℝ) 1, subdistHazardQuotient unif id J₁ () 0 h = 1 := by
    intro h hh
    have hE : causeEventIn id J₁ () 0 h = Ico 0 h := by
      ext ω; simp [causeEventIn, J₁]
    have hI : Ici (0 : ℝ) ∩ Ico 0 h = Ico 0 h := inter_eq_right.2 Ico_subset_Ici_self
    rw [subdistHazardQuotient, hR, hE, measureReal_def, cond_apply measurableSet_Ici, hR1, hI,
      inv_one, one_mul, ← measureReal_def, unif_real_Ico hh.1.le hh.2.le, div_self hh.1.ne']
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
  exact (hq h hh).symm

/-- The limit-defined `subdistHazard` takes the value `1`. -/
example : subdistHazard unif id J₁ () 0 = 1 :=
  hasSubdistHazardAt_unif_zero.subdistHazard_eq

/-- Boundary: an atom separates `F_c(t-)` from `F_c(t)`. For `T = 1` almost surely with a single
cause, `F_c(1-) = 0` while `F_c(1) = 1`. -/
example : cifBefore (Measure.dirac (1 : ℝ)) id J₁ () 1 = 0 ∧
    cif (Measure.dirac (1 : ℝ)) id J₁ () 1 = 1 := by
  have h1 : {ω : ℝ | id ω < 1 ∧ J₁ ω = ()} = Iio 1 := by ext ω; simp
  have h2 : {ω : ℝ | id ω ≤ 1 ∧ J₁ ω = ()} = Iic 1 := by ext ω; simp
  refine ⟨?_, ?_⟩
  · rw [cifBefore, h1, measureReal_def, Measure.dirac_apply' _ measurableSet_Iio]
    simp
  · rw [cif, h2, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
    simp

/-- The hypotheses of the CIF link are met by the uniform failure time on `[0, 1/2]`, and the link
gives `Λ*(1/2) = log 2`. -/
example : cumSubdistHazard unif id J₁ () (1 / 2) = Real.log 2 := by
  have hJ : MeasurableSet {ω : ℝ | J₁ ω = ()} := by simp [J₁]
  have hpos : ∀ᵐ ω ∂unif, 0 < id ω := by
    rw [unif, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with ω h0 hω
    exact lt_of_le_of_ne hω.1 (Ne.symm h0)
  have hc : ContinuousOn (cif unif id J₁ ()) (Icc 0 (1 / 2)) :=
    continuousOn_id.congr fun s hs => cif_unif hs.1 (by linarith [hs.2])
  have hd : ∀ s ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt (cif unif id J₁ ()) 1 s := fun s hs => by
    refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs.1 (by linarith [hs.2] : s < 1)] with u hu
    exact cif_unif hu.1.le hu.2.le
  have h := cif_eq_one_sub_exp measurable_id hJ hpos (by norm_num) hc hd
    (intervalIntegrable_const (c := (1 : ℝ))) (by rw [cif_unif] <;> norm_num)
  rw [cif_unif (by norm_num) (by norm_num)] at h
  have he : Real.exp (-cumSubdistHazard unif id J₁ () (1 / 2)) = 2⁻¹ := by linarith
  have := congrArg Real.log he
  rw [Real.log_exp, Real.log_inv] at this
  linarith

end MathlibExtTest.Probability.Statistics.FineGray
