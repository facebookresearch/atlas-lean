/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform

open scoped BigOperators

namespace Cslib.Security.QuantitativeInformationFlow

/-!
# Min-entropy leakage

Vulnerability, posterior vulnerability and min-entropy leakage for finite
secrets and observations, with the `log2 |O|` upper bound and the exact
leakage of deterministic channels under the uniform prior.

## References

The formalized notions follow Geoffrey Smith, *On the Foundations of
Quantitative Information Flow*, FoSSaCS 2009:

- `vulnerability`: prior vulnerability, the maximum prior mass of any secret.
- `posteriorVulnerability`: posterior vulnerability, the sum over observations
  of the maximum joint mass of any secret with that observation.
- `minEntropyLeakage`: min-entropy leakage, the binary log of posterior over
  prior vulnerability.
- `posterior_le_card_mul` and `leakage_le_log_card`: the `|O|` bound on
  posterior vulnerability and the resulting `log2 |O|` bound on leakage.
- `posterior_det_uniform` and `leakage_det_uniform`: exact posterior and
  leakage of deterministic channels under the uniform prior.
- `posterior_const_channel` and `leakage_const_channel`: channels independent
  of the secret preserve vulnerability and leak nothing.
-/

noncomputable section

/-- Prior vulnerability: the maximum prior mass of any secret. -/
@[expose] public def vulnerability {X : Type*} [Fintype X] [Nonempty X]
  (pi : PMF X) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun x => (pi x).toReal

/-- Posterior vulnerability: total over observations of the maximum joint
mass of any secret with that observation. -/
@[expose] public def posteriorVulnerability {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] (pi : PMF X) (C : X → PMF Y) : Real :=
  ∑ y, Finset.univ.sup' Finset.univ_nonempty
    fun x => (pi x).toReal * ((C x y).toReal)

/-- Min-entropy leakage: binary log of posterior over prior vulnerability. -/
@[expose] public def minEntropyLeakage {X Y : Type*} [Fintype X] [Nonempty X]
  [Fintype Y] (pi : PMF X) (C : X → PMF Y) : Real :=
  Real.logb 2 (posteriorVulnerability pi C / vulnerability pi)

/-- Every secret has mass `1 / |X|` under the uniform prior. -/
public theorem uniformFintype_apply_toReal (X : Type*) [Fintype X]
  [Nonempty X] (x : X) :
  ((PMF.uniformFintype X x).toReal) = 1 / (Fintype.card X : Real) := by
  simp [PMF.uniformFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    one_div]

/-- Vulnerability of the uniform prior is `1 / |X|`. -/
public theorem vulnerability_uniformFintype (X : Type*) [Fintype X]
  [Nonempty X] :
  vulnerability (PMF.uniformFintype X) = 1 / (Fintype.card X : Real) := by
  unfold vulnerability
  apply Finset.sup'_eq_of_forall
  intro x _
  exact uniformFintype_apply_toReal X x

/-- A single real mass of a `PMF` is at most one. -/
theorem PMF_toReal_le_one {X : Type*} (p : PMF X) (x : X) :
  (p x).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one x)
  simpa using h

/-- The real masses of a `PMF` on a finite type sum to one. -/
theorem PMF_sum_toReal_eq_one (Y : Type*) [Fintype Y] (p : PMF Y) :
  (∑ y, (p y).toReal) = 1 := by
  have hsum : (∑ y, p y) = 1 := by simpa using p.tsum_coe
  have h := congrArg ENNReal.toReal hsum
  have h2 : (∑ y, p y).toReal = ∑ y, (p y).toReal :=
    ENNReal.toReal_sum (fun y _ => p.apply_ne_top y)
  rw [h2] at h
  simpa using h

/-- `sup'` of a function scaled by a nonnegative constant. -/
theorem sup'_mul_const_nonneg {X : Type*} [Fintype X] [Nonempty X]
  (f : X → Real) (c : Real) (hc : 0 ≤ c) :
  Finset.univ.sup' Finset.univ_nonempty (fun x => f x * c) =
  Finset.univ.sup' Finset.univ_nonempty f * c := by
  apply le_antisymm
  · refine Finset.sup'_le Finset.univ_nonempty (fun x => f x * c) ?_
    intro x _
    have hle : f x ≤ Finset.univ.sup' Finset.univ_nonempty f :=
      Finset.le_sup' _ (Finset.mem_univ x)
    exact mul_le_mul_of_nonneg_right hle hc
  · obtain ⟨x0, hx0, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    rw [hmax]
    exact Finset.le_sup' (fun x => f x * c) hx0

/-- Posterior vulnerability is at most `|Y|` times the prior. -/
public theorem posterior_le_card_mul {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] (pi : PMF X) (C : X → PMF Y) :
  posteriorVulnerability pi C ≤
  (Fintype.card Y : Real) * vulnerability pi := by
  have hle : ∀ y ∈ (Finset.univ : Finset Y),
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => (pi x).toReal * ((C x y).toReal)) ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => (pi x).toReal) := by
    intro y _
    apply Finset.sup'_le
    intro x _
    calc (pi x).toReal * ((C x y).toReal) ≤ (pi x).toReal :=
      mul_le_of_le_one_right ENNReal.toReal_nonneg (PMF_toReal_le_one (C x) y)
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun x => (pi x).toReal) :=
      Finset.le_sup' (fun x => (pi x).toReal) (Finset.mem_univ x)
  unfold posteriorVulnerability vulnerability
  have hsum := Finset.sum_le_sum hle
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum

/-- Min-entropy leakage is at most `log2 |Y|`. -/
public theorem leakage_le_log_card {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] [Nonempty Y] (pi : PMF X) (C : X → PMF Y)
  (hv : 0 < vulnerability pi) :
  minEntropyLeakage pi C ≤ Real.logb 2 (Fintype.card Y) := by
  have hQ4 := posterior_le_card_mul pi C
  have hpost_nonneg : 0 ≤ posteriorVulnerability pi C := by
    unfold posteriorVulnerability
    apply Finset.sum_nonneg
    intro y _
    obtain ⟨x, hx⟩ := Finset.univ_nonempty (α := X)
    calc (0 : Real) ≤ (pi x).toReal * ((C x y).toReal) :=
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun x => (pi x).toReal * ((C x y).toReal)) :=
      Finset.le_sup' (fun x => (pi x).toReal * ((C x y).toReal)) hx
  have hnonneg : 0 ≤ posteriorVulnerability pi C / vulnerability pi :=
    div_nonneg hpost_nonneg (le_of_lt hv)
  have hle : posteriorVulnerability pi C / vulnerability pi ≤
    (Fintype.card Y : Real) := by
    rw [div_le_iff₀ hv]
    exact hQ4
  unfold minEntropyLeakage
  by_cases hr : posteriorVulnerability pi C / vulnerability pi = 0
  · rw [hr, Real.logb_zero]
    apply Real.logb_nonneg (by norm_num)
    have h1 : 1 ≤ Fintype.card Y := Fintype.card_pos
    exact_mod_cast h1
  · exact Real.logb_le_logb_of_le (by norm_num) (lt_of_le_of_ne hnonneg (Ne.symm hr)) hle

/-- Posterior of a deterministic channel under the uniform prior. -/
public theorem posterior_det_uniform {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
  posteriorVulnerability (PMF.uniformFintype X) (fun x => PMF.pure (f x)) =
  (Finset.card (Finset.image f Finset.univ) : Real) *
  (1 / (Fintype.card X : Real)) := by
  set C : X → PMF Y := (fun x => PMF.pure (f x)) with hCdef
  have hcard : (0 : Real) < (Fintype.card X : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcpos : (0 : Real) < 1 / (Fintype.card X : Real) :=
    div_pos zero_lt_one hcard
  have hpure : ∀ (x : X) (y : Y),
    ((C x y).toReal) = (if y = f x then (1 : Real) else 0) := by
    intro x y
    rw [hCdef]
    show ((PMF.pure (f x) y).toReal) = _
    by_cases h : y = f x <;> simp [h, PMF.pure_apply]
  have hterm : ∀ (x : X) (y : Y),
    ((PMF.uniformFintype X x).toReal) * ((C x y).toReal) =
    (if y = f x then 1 / (Fintype.card X : Real) else 0) := by
    intro x y
    rw [uniformFintype_apply_toReal X x, hpure x y]
    by_cases h : y = f x <;> simp [h]
  have hmem : ∀ y : Y,
    y ∈ Finset.image f Finset.univ ↔ ∃ x : X, f x = y := by
    intro y
    simp [Finset.mem_image]
  have per_y : ∀ y : Y,
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal)) =
    (if y ∈ Finset.image f Finset.univ then
      1 / (Fintype.card X : Real) else 0) := by
    intro y
    by_cases hy : y ∈ Finset.image f Finset.univ
    · simp only [hy, ite_true]
      obtain ⟨x0, hx0⟩ := (hmem y).mp hy
      apply le_antisymm
      · apply Finset.sup'_le
        intro x _
        have hx : ((PMF.uniformFintype X x).toReal) * ((C x y).toReal) ≤
          1 / (Fintype.card X : Real) := by
          rw [hterm x y]
          split_ifs with h
          · exact le_rfl
          · exact hcpos.le
        exact hx
      · have h0 : (1 / (Fintype.card X : Real)) =
          ((PMF.uniformFintype X x0).toReal) * ((C x0 y).toReal) := by
          rw [hterm x0 y]
          simp [hx0.symm]
        rw [h0]
        exact Finset.le_sup' (fun x =>
          ((PMF.uniformFintype X x).toReal) * ((C x y).toReal)) (Finset.mem_univ x0)
    · simp only [hy, ite_false]
      apply Finset.sup'_eq_of_forall
      intro x _
      have hx0 : ((PMF.uniformFintype X x).toReal) * ((C x y).toReal) = 0 := by
        rw [hterm x y]
        have hne : ¬ y = f x :=
          fun hcon => hy ((hmem y).mpr ⟨x, hcon.symm⟩)
        simp only [hne, ite_false]
      exact hx0
  have hzero : ∀ y : Y, y ∉ Finset.image f Finset.univ →
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal)) =
    0 := by
    intro y hy
    rw [per_y y]
    simp only [hy, ite_false]
  have hon : ∀ y ∈ Finset.image f Finset.univ,
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal)) =
    1 / (Fintype.card X : Real) := by
    intro y hy
    rw [per_y y]
    simp only [hy, ite_true]
  have hsub : (∑ y ∈ Finset.image f Finset.univ,
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal))) =
    (∑ y, Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal))) :=
    Finset.sum_subset (Finset.subset_univ (Finset.image f Finset.univ)) (fun y _ hy => hzero y hy)
  have hpost : (∑ y, Finset.univ.sup' Finset.univ_nonempty
      (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal))) =
    (Finset.card (Finset.image f Finset.univ) : Real) *
    (1 / (Fintype.card X : Real)) := by
    rw [← hsub]
    calc (∑ y ∈ Finset.image f Finset.univ,
        Finset.univ.sup' Finset.univ_nonempty
          (fun x => ((PMF.uniformFintype X x).toReal) * ((C x y).toReal))) =
      ∑ _ ∈ Finset.image f Finset.univ,
        (1 / (Fintype.card X : Real)) :=
      Finset.sum_congr rfl hon
    _ = (Finset.card (Finset.image f Finset.univ) : Real) *
        (1 / (Fintype.card X : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
  unfold posteriorVulnerability
  exact hpost

/-- Leakage of a deterministic channel under the uniform prior. -/
public theorem leakage_det_uniform {X Y : Type*} [Fintype X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] (f : X → Y) :
  minEntropyLeakage (PMF.uniformFintype X) (fun x => PMF.pure (f x)) =
  Real.logb 2 (Finset.card (Finset.image f Finset.univ)) := by
  have hcard : (0 : Real) < (Fintype.card X : Real) := by
    exact_mod_cast Fintype.card_pos
  have hc0 : (1 / (Fintype.card X : Real)) ≠ 0 :=
    ne_of_gt (div_pos zero_lt_one hcard)
  unfold minEntropyLeakage
  rw [posterior_det_uniform, vulnerability_uniformFintype,
    mul_div_cancel_right₀ _ hc0]

/-- A channel independent of the secret preserves vulnerability. -/
public theorem posterior_const_channel {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] (pi : PMF X) (C : X → PMF Y) (x0 : X)
  (hC : ∀ x, C x = C x0) :
  posteriorVulnerability pi C = vulnerability pi := by
  have hDy : ∀ (x : X) (y : Y),
    ((C x y).toReal) = ((C x0 y).toReal) := by
    intro x y
    rw [hC x]
  have per_y : ∀ y : Y,
    Finset.univ.sup' Finset.univ_nonempty
      (fun x => (pi x).toReal * ((C x y).toReal)) =
    Finset.univ.sup' Finset.univ_nonempty (fun x => (pi x).toReal) *
      ((C x0 y).toReal) := by
    intro y
    have hfun : (fun x => (pi x).toReal * ((C x y).toReal)) =
      (fun x => (pi x).toReal * ((C x0 y).toReal)) := by
      funext x
      rw [hDy x y]
    rw [hfun]
    exact sup'_mul_const_nonneg _ _ ENNReal.toReal_nonneg
  unfold posteriorVulnerability vulnerability
  simp only [per_y]
  rw [← Finset.mul_sum, PMF_sum_toReal_eq_one, mul_one]

/-- A channel independent of the secret leaks nothing. -/
public theorem leakage_const_channel {X Y : Type*} [Fintype X]
  [Nonempty X] [Fintype Y] (pi : PMF X) (C : X → PMF Y) (x0 : X)
  (hC : ∀ x, C x = C x0) (hv : 0 < vulnerability pi) :
  minEntropyLeakage pi C = 0 := by
  unfold minEntropyLeakage
  rw [posterior_const_channel pi C x0 hC, div_self (ne_of_gt hv),
    Real.logb_one]

end

end Cslib.Security.QuantitativeInformationFlow
