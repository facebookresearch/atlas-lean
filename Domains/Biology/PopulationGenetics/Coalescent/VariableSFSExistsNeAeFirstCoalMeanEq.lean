/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Survival.MeanWaitingTime
import MathlibExt.Analysis.FunctionalAnalysis.MuntzSzasz
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Non-identifiability of population-size histories

Source: S. Myers, C. Fefferman and N. Patterson, "Can one learn history from the allelic
spectrum?" Theoret. Population Biol. 73 (2008), 342–348.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private def exponents : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1).choose 2 + 1

private theorem exponents_strictMono : StrictMono exponents := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => norm_num [exponents]
  | succ n =>
    simp only [exponents]
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, Nat.choose_succ_succ' (n + 1) 1,
      Nat.choose_one_right]
    norm_num at *

private theorem exponents_summable :
    Summable (fun n : ℕ => ((exponents (n + 1) : ℝ)⁻¹)) := by
  have hp : Summable (fun n : ℕ => (4 : ℝ) * ((n + 1 : ℝ) ^ 2)⁻¹) := by
    have h := (Real.summable_nat_pow_inv.mpr (by omega : 1 < 2)).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.mul_left 4
  apply Summable.of_nonneg_of_le (fun n => inv_nonneg.mpr (Nat.cast_nonneg _)) _ hp
  intro n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hd : (0 : ℝ) < (exponents (n + 1) : ℝ) := by
    simp only [exponents, Nat.cast_add, Nat.cast_one]
    positivity
  have hsq : 0 < (n + 1 : ℝ) ^ 2 := sq_pos_of_pos hn
  have hb : (n + 1 : ℝ) ^ 2 ≤ 4 * (exponents (n + 1) : ℝ) := by
    simp only [exponents, Nat.cast_add, Nat.cast_one, Nat.cast_choose_two]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  rw [inv_le_iff_one_le_mul₀ hd]
  calc
    1 = ((n + 1 : ℝ) ^ 2)⁻¹ * (n + 1 : ℝ) ^ 2 :=
      (inv_mul_cancel₀ hsq.ne').symm
    _ ≤ ((n + 1 : ℝ) ^ 2)⁻¹ * (4 * (exponents (n + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hsq.le)
    _ = _ := by ring

private theorem exists_annihilator :
    ∃ L : C(I, ℝ) →L[ℝ] ℝ, L ≠ 0 ∧
      ∀ n : ℕ, L (((Polynomial.X : Polynomial ℝ) ^ exponents n).toContinuousMapOn I) = 0 := by
  classical
  let S := (Submodule.span ℝ (Set.range (fun n : ℕ =>
    ((Polynomial.X : Polynomial ℝ) ^ exponents n).toContinuousMapOn I))).topologicalClosure
  have hS : S ≠ ⊤ := by
    intro h
    have := (MathlibExt.Analysis.FunctionalAnalysis.MuntzSzaszWanted.muntz_szasz_nat
      exponents exponents_strictMono rfl).mp h
    exact this exponents_summable
  obtain ⟨x, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hS)
  obtain ⟨L, u, hLu, hux⟩ := geometric_hahn_banach_closed_point
    S.convex (Submodule.isClosed_topologicalClosure _) hx.2
  have hu : 0 < u := by simpa using hLu 0 S.zero_mem
  have hzero : ∀ y ∈ S, L y = 0 := by
    intro y hy
    by_contra hne
    have h := hLu ((u / L y) • y) (S.smul_mem (u / L y) hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    exact (lt_irrefl u) h
  refine ⟨L, ?_, fun n => hzero _ ?_⟩
  · intro h
    simp [h] at hux
    linarith
  · exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

private noncomputable def kernel (t : ℝ) : C(I, ℝ) :=
  ⟨fun x => max ((x : ℝ) - Real.exp (-t)) 0,
    (continuous_subtype_val.sub continuous_const).max continuous_const⟩

private theorem kernel_norm_le (t : ℝ) : ‖kernel t‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  change |max ((x : ℝ) - Real.exp (-t)) 0| ≤ 1
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · linarith [x.property.2, Real.exp_pos (-t)]
  · exact zero_le_one

private theorem kernel_eq_zero (t : ℝ) (ht : t ≤ 0) : kernel t = 0 := by
  ext x
  change max ((x : ℝ) - Real.exp (-t)) 0 = 0
  rw [max_eq_right]
  have h : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (by linarith)
  linarith [x.property.2]

private theorem continuous_kernel : Continuous kernel := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × I => max ((p.2 : ℝ) - Real.exp (-p.1)) 0)
  fun_prop

private theorem continuous_perturbation (L : C(I, ℝ) →L[ℝ] ℝ) :
    Continuous (fun t => L (kernel t)) :=
  L.continuous.comp continuous_kernel

private theorem perturbation_bound (L : C(I, ℝ) →L[ℝ] ℝ) (t : ℝ) :
    |L (kernel t)| ≤ ‖L‖ := by
  exact (L.le_opNorm (kernel t)).trans
    (by simpa using mul_le_mul_of_nonneg_left (kernel_norm_le t) (norm_nonneg L))

private theorem kernel_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t => Real.exp (-c * t) • kernel t) (Set.Ioi 0) := by
  apply (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      continuous_kernel).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (kernel_norm_le t)

private theorem kernel_laplace_nat (n : ℕ) (hn : 0 < n) (x : I) :
    (∫ t in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * kernel t x) =
      (x : ℝ) ^ (n + 1) / ((n : ℝ) * (n + 1 : ℝ)) := by
  by_cases hx : (x : ℝ) = 0
  · simp [kernel, hx, (Real.exp_pos _).le, hn.ne']
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
  let a : ℝ := -Real.log x
  have ha : 0 ≤ a := by
    exact neg_nonneg.mpr (Real.log_nonpos hxpos.le x.property.2)
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcut : (∫ t in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * kernel t x) =
      ∫ t in Set.Ioi a, Real.exp (-(n : ℝ) * t) * kernel t x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi ha)
    intro t ht
    have ht' : t ≤ a := le_of_not_gt ht.2
    have h : (x : ℝ) ≤ Real.exp (-t) := by
      rw [← Real.exp_log hxpos]
      exact Real.exp_le_exp.mpr (by dsimp [a] at ht'; linarith)
    simp [kernel, max_eq_right (sub_nonpos.mpr h)]
  have hform : ∀ t ∈ Set.Ioi a,
      Real.exp (-(n : ℝ) * t) * kernel t x =
        (x : ℝ) * Real.exp (-(n : ℝ) * t) - Real.exp (-(n + 1 : ℝ) * t) := by
    intro t ht
    have h : Real.exp (-t) ≤ (x : ℝ) := by
      rw [← Real.exp_log hxpos]
      exact Real.exp_le_exp.mpr (by change -Real.log (x : ℝ) < t at ht; linarith)
    simp only [kernel, ContinuousMap.coe_mk, max_eq_left (sub_nonneg.mpr h)]
    rw [mul_sub, ← Real.exp_add]
    congr 1
    · ring
    · congr 1; ring
  rw [hcut, setIntegral_congr_fun measurableSet_Ioi hform,
    integral_sub ((integrableOn_exp_mul_Ioi (by linarith : -(n : ℝ) < 0) a).const_mul x)
      (integrableOn_exp_mul_Ioi (by linarith : -(n + 1 : ℝ) < 0) a),
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -(n : ℝ) < 0),
    integral_exp_mul_Ioi (by linarith : -(n + 1 : ℝ) < 0)]
  have he : ∀ k : ℕ, Real.exp (-(k : ℝ) * a) = (x : ℝ) ^ k := by
    intro k
    dsimp [a]
    rw [neg_mul_neg, Real.exp_nat_mul, Real.exp_log hxpos]
  rw [he n, show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, he (n + 1)]
  push_cast
  field_simp
  ring

private theorem kernel_laplace (n : ℕ) (hn : 0 < n) :
    (∫ t in Set.Ioi 0, Real.exp (-(n : ℝ) * t) • kernel t) =
      ((n : ℝ) * (n + 1 : ℝ))⁻¹ •
        ((Polynomial.X : Polynomial ℝ) ^ (n + 1)).toContinuousMapOn I := by
  ext x
  rw [ContinuousMap.integral_apply (kernel_integrable n (Nat.cast_pos.mpr hn)) x]
  change (∫ t in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * kernel t x) = _
  rw [kernel_laplace_nat n hn x]
  simp [Polynomial.toContinuousMapOn, div_eq_mul_inv, mul_comm]

private theorem perturbation_laplace (L : C(I, ℝ) →L[ℝ] ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ t in Set.Ioi 0, Real.exp (-(n : ℝ) * t) * L (kernel t)) =
      ((n : ℝ) * (n + 1 : ℝ))⁻¹ *
        L (((Polynomial.X : Polynomial ℝ) ^ (n + 1)).toContinuousMapOn I) := by
  have he : (fun t => Real.exp (-(n : ℝ) * t) * L (kernel t)) =
      (fun t => L (Real.exp (-(n : ℝ) * t) • kernel t)) := by
    ext t
    simp
  rw [he, L.integral_comp_comm (kernel_integrable n (Nat.cast_pos.mpr hn)),
    kernel_laplace n hn, map_smul, smul_eq_mul]

private theorem perturbation_nonzero (L : C(I, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (hconst : L (((Polynomial.X : Polynomial ℝ) ^ 0).toContinuousMapOn I) = 0)
    (hlinear : L ((Polynomial.X : Polynomial ℝ).toContinuousMapOn I) = 0) :
    ∃ t : ℝ, 0 < t ∧ L (kernel t) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hg : ∀ t : ℝ, L (kernel t) = 0 := by
    intro t
    by_cases ht : 0 < t
    · exact h t ht
    · rw [kernel_eq_zero t (le_of_not_gt ht), map_zero]
  have hpow : ∀ n : ℕ, L (((Polynomial.X : Polynomial ℝ) ^ n).toContinuousMapOn I) = 0 := by
    intro n
    cases n with
    | zero => exact hconst
    | succ n =>
      by_cases hn : n = 0
      · subst n
        simpa using hlinear
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hl := perturbation_laplace L n hnpos
        simp only [hg, mul_zero, integral_zero] at hl
        have hc : ((n : ℝ) * (n + 1 : ℝ))⁻¹ ≠ 0 := by positivity
        exact (mul_eq_zero.mp hl.symm).resolve_left hc
  have hpol : ∀ p : Polynomial ℝ, L (p.toContinuousMapOn I) = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [← Polynomial.toContinuousMapOnAlgHom_apply, map_add, map_add]
      change L (p.toContinuousMapOn I) + L (q.toContinuousMapOn I) = 0
      rw [hp, hq, add_zero]
    | monomial n a =>
      have he : (Polynomial.monomial n a).toContinuousMapOn I =
          a • ((Polynomial.X : Polynomial ℝ) ^ n).toContinuousMapOn I := by
        ext x
        simp
      rw [he, map_smul, hpow n, smul_zero]
  have hz : ∀ f : C(I, ℝ), L f = 0 := by
    intro f
    have hmem : f ∈ (polynomialFunctions I).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top']
      trivial
    have hclosed : IsClosed {f : C(I, ℝ) | L f = 0} :=
      isClosed_eq L.continuous continuous_const
    apply (closure_minimal (t := {f : C(I, ℝ) | L f = 0}) ?_ hclosed) hmem
    intro f hf
    change f ∈ (polynomialFunctions I : Set C(I, ℝ)) at hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p, rfl⟩ := hf
    exact hpol p
  apply hL
  ext f
  exact hz f

private theorem exists_time_change (k : ℝ → ℝ) (hk : Continuous k)
    (hkbound : ∀ t, (1 : ℝ) / 2 ≤ k t ∧ k t ≤ 3 / 2) :
    ∃ e : ℝ ≃o ℝ, e 0 = 0 ∧ (∀ t, HasDerivAt e (k t) t) := by
  let F : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, k r
  have hderiv : ∀ t, HasDerivAt F (k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hderiv
    (fun t => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hkbound t).1)
  have hbound : ∀ x y : ℝ, x ≤ y → (y - x) / 2 ≤ ∫ r in x..y, k r := by
    intro x y hxy
    have h := intervalIntegral.integral_mono (μ := volume) (f := fun _ : ℝ => 1 / 2) hxy
      (continuous_const.intervalIntegrable x y) (hk.intervalIntegrable x y)
      (fun t => (hkbound t).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using h
  have htop : Filter.Tendsto F Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop
      ((Filter.eventually_ge_atTop (0 : ℝ)).mono (fun t ht => ?_))
      ((Filter.tendsto_mul_const_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr
        Filter.tendsto_id)
    dsimp [F]
    simpa only [sub_zero, mul_one_div] using hbound 0 t ht
  have hbot : Filter.Tendsto F Filter.atBot Filter.atBot := by
    apply Filter.tendsto_atBot_mono' Filter.atBot
      ((Filter.eventually_le_atBot (0 : ℝ)).mono (fun t ht => ?_))
      ((Filter.tendsto_mul_const_atBot_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr
        Filter.tendsto_id)
    dsimp [F]
    have h := hbound t 0 ht
    rw [intervalIntegral.integral_symm] at h
    simp only [zero_sub] at h
    linarith
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective F (hcont.surjective htop hbot)
  exact ⟨e, by simp [e, F], hderiv⟩

private theorem time_change_mean (k : ℝ → ℝ) (hk : Continuous k)
    (hkpos : ∀ t, 0 < k t) (e : ℝ ≃o ℝ) (he0 : e 0 = 0)
    (he : ∀ t, HasDerivAt e (k t) t) (c : ℝ) :
    meanWaitingTime (fun t => (k (e.symm t))⁻¹) c =
      ∫ t in Set.Ioi 0, Real.exp (-c * t) * k t := by
  have hη : Continuous (fun t => (k (e.symm t))⁻¹) :=
    (hk.comp e.symm.continuous).inv₀ (fun t => (hkpos _).ne')
  have hcum : ∀ t, (∫ r in (0 : ℝ)..e t, (k (e.symm r))⁻¹) = t := by
    intro t
    have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := t)
      (fun x _ => he x) hk.continuousOn hη
    simp only [Function.comp_def, OrderIso.symm_apply_apply, inv_mul_cancel₀ (hkpos _).ne',
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, he0] at h
    exact h.symm
  unfold meanWaitingTime
  have himage : e '' Set.Ioi 0 = Set.Ioi (0 : ℝ) := by
    rw [e.image_Ioi, he0]
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (he t).hasDerivWithinAt) e.injective.injOn]
  rw [himage]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change |k t| • Real.exp (-c * (∫ r in (0 : ℝ)..e t, (k (e.symm r))⁻¹)) =
    Real.exp (-c * t) * k t
  rw [hcum, abs_of_pos (hkpos t), smul_eq_mul, mul_comm]

/-- **Non-identifiability of general histories** (Myers, Fefferman & Patterson 2008): there
are two measurable population-size functions, bounded between positive constants, that differ
on a set of positive Lebesgue measure in `[0, ∞)` and have the same expected first-coalescence
time `c_m` for every `m ≥ 2` (hence the same expected SFS for every sample size).

Source: Myers, Fefferman & Patterson (2008). -/
theorem exists_ne_ae_firstCoalMean_eq :
    ∃ η₁ η₂ : ℝ → ℝ, Measurable η₁ ∧ Measurable η₂ ∧
      (∃ a b : ℝ, 0 < a ∧ ∀ s, a ≤ η₁ s ∧ η₁ s ≤ b ∧ a ≤ η₂ s ∧ η₂ s ≤ b) ∧
      ¬ (η₁ =ᵐ[volume.restrict (Set.Ici 0)] η₂) ∧
      ∀ m : ℕ, 2 ≤ m → meanWaitingTime (fun t => (η₁ t)⁻¹) (m.choose 2) =
        meanWaitingTime (fun t => (η₂ t)⁻¹) (m.choose 2)
    := by
  obtain ⟨L, hL, hann⟩ := exists_annihilator
  let d : ℝ := 2 * (‖L‖ + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let k : ℝ → ℝ := fun t => 1 + L (kernel t) / d
  have hk : Continuous k := continuous_const.add
    ((continuous_perturbation L).div_const d)
  have hkbound : ∀ t, (1 : ℝ) / 2 ≤ k t ∧ k t ≤ 3 / 2 := by
    intro t
    have hb : |L (kernel t) / d| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
      have h := perturbation_bound L t
      dsimp [d]
      linarith
    have h := abs_le.mp hb
    dsimp [k]
    constructor <;> linarith
  have hkpos : ∀ t, 0 < k t := fun t =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hkbound t).1
  obtain ⟨e, he0, he⟩ := exists_time_change k hk hkbound
  let η : ℝ → ℝ := fun t => k (e.symm t)
  have hη : Continuous η := hk.comp e.symm.continuous
  refine ⟨fun _ => 1, η, measurable_const, hη.measurable,
    ⟨1 / 2, 3 / 2, by norm_num, fun s => ?_⟩, ?_, fun m hm => ?_⟩
  · exact ⟨by norm_num, by norm_num, (hkbound (e.symm s)).1, (hkbound (e.symm s)).2⟩
  · intro hae
    have hpoint := Measure.eqOn_of_ae_eq hae continuous_const.continuousOn hη.continuousOn
      (by simp : Set.Ici (0 : ℝ) ⊆ closure (interior (Set.Ici 0)))
    obtain ⟨t, ht, hne⟩ := perturbation_nonzero L hL (hann 0)
      (by simpa [exponents] using hann 1)
    have h : (1 : ℝ) = η (e t) :=
      hpoint (by change 0 ≤ e t; rw [← he0]; exact (e.strictMono ht).le)
    dsimp [η] at h
    rw [e.symm_apply_apply] at h
    dsimp [k] at h
    apply hne
    have hz : L (kernel t) / d = 0 := by linarith
    exact (div_eq_zero_iff).mp hz |>.resolve_right hd.ne'
  · have hq : 0 < m.choose 2 := Nat.choose_pos hm
    have hqreal : (0 : ℝ) < (m.choose 2 : ℝ) := Nat.cast_pos.mpr hq
    have hannm : L (((Polynomial.X : Polynomial ℝ) ^ (m.choose 2 + 1)).toContinuousMapOn I) = 0 := by
      have h := hann m
      cases m with
      | zero => omega
      | succ m => exact h
    have hzero := perturbation_laplace L (m.choose 2) hq
    rw [hannm, mul_zero] at hzero
    have hint : IntegrableOn (fun t => Real.exp (-(m.choose 2 : ℝ) * t)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith : -(m.choose 2 : ℝ) < 0) 0
    have hg : IntegrableOn
        (fun t => Real.exp (-(m.choose 2 : ℝ) * t) * L (kernel t) / d) (Set.Ioi 0) := by
      have h := L.integrable_comp (kernel_integrable (m.choose 2) hqreal)
      simpa only [IntegrableOn, map_smul, smul_eq_mul, Function.comp_def] using h.div_const d
    rw [time_change_mean k hk hkpos e he0 he]
    have heq : (fun t => Real.exp (-(m.choose 2 : ℝ) * t) * k t) =
        (fun t => Real.exp (-(m.choose 2 : ℝ) * t) +
          Real.exp (-(m.choose 2 : ℝ) * t) * L (kernel t) / d) := by
      ext t
      dsimp [k]
      ring
    rw [heq, integral_add hint hg, integral_div, hzero, zero_div, add_zero]
    simp [meanWaitingTime, intervalIntegral.integral_const]

end MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted
