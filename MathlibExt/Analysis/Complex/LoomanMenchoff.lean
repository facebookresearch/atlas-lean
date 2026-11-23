/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/

@[expose] public section

namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset
open BoxIntegral
open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

/-- Combine derivatives of the real and imaginary parts of a complex-valued real path. -/
private theorem hasDerivAt_complex_of_re_im {g : ℝ → ℂ} {a b t : ℝ}
    (hre : HasDerivAt (fun x ↦ (g x).re) a t)
    (him : HasDerivAt (fun x ↦ (g x).im) b t) :
    HasDerivAt g (a + b * Complex.I) t := by
  convert hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I) using 1
  · ext x
    exact (Complex.re_add_im (g x)).symm

private def loomanBoundedAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  ∀ h : ℝ, ‖h‖ < r / (n + 1) →
    ‖f (z + (h : ℂ)) - f z‖ ≤ (n + 1) * ‖h‖ ∧
      ‖f (z + (h : ℂ) * Complex.I) - f z‖ ≤ (n + 1) * ‖h‖

private theorem looman_exists_boundedAt {f : ℂ → ℂ} {z : ℂ} {r : ℝ} {ax ay : ℂ}
    (hx : HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ))) ax 0)
    (hy : HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ) * Complex.I)) ay 0) :
    ∃ n, loomanBoundedAt f r n z := by
  rcases hx.isBigO_sub.bound with ⟨cx, hcx⟩
  rcases hy.isBigO_sub.bound with ⟨cy, hcy⟩
  rcases Metric.eventually_nhds_iff_ball.mp (hcx.and hcy) with ⟨δ, hδ, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max cx cy) (r / δ))
  refine ⟨n, fun h hh ↦ ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hδh : ‖h‖ < δ := by
    calc
      ‖h‖ < r / (n + 1) := hh
      _ < δ := (div_lt_iff₀ hn1).2 <| by
        calc
          r < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 <|
            lt_of_le_of_lt (le_max_right _ _) hn
          _ < (n + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one (n : ℝ)) hδ
          _ = δ * (n + 1) := mul_comm _ _
  have hb :
      ‖f (z + (h : ℂ)) - f z‖ ≤ cx * ‖h‖ ∧
        ‖f (z + (h : ℂ) * Complex.I) - f z‖ ≤ cy * ‖h‖ := by
    simpa [Real.dist_eq] using hbound h (by simpa [Real.dist_eq] using hδh)
  have hn1' : (n : ℝ) ≤ n + 1 := by linarith
  have hcxn : cx ≤ (n : ℝ) + 1 :=
    le_trans (le_max_left _ _) <| le_trans (le_max_left _ _) <| le_trans hn.le hn1'
  have hcyn : cy ≤ (n : ℝ) + 1 :=
    le_trans (le_max_right _ _) <| le_trans (le_max_left _ _) <| le_trans hn.le hn1'
  constructor
  · exact hb.1.trans <| mul_le_mul_of_nonneg_right hcxn (norm_nonneg h)
  · exact hb.2.trans <| mul_le_mul_of_nonneg_right hcyn (norm_nonneg h)

private theorem looman_isClosed_boundedAt {f : ℂ → ℂ} {s C : Set ℂ} {r : ℝ} {n : ℕ}
    (hf : ContinuousOn f s) (hCs : C ⊆ s)
    (hshift : ∀ z ∈ C, ∀ h : ℝ, ‖h‖ < r / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s) :
    IsClosed {z : C | loomanBoundedAt f r n z} := by
  have hset : {z : C | loomanBoundedAt f r n z} =
      ⋂ h : ℝ, ⋂ (_ : ‖h‖ < r / (n + 1)),
        {z : C | ‖f (z + (h : ℂ)) - f z‖ ≤ (n + 1) * ‖h‖} ∩
          {z : C | ‖f (z + (h : ℂ) * Complex.I) - f z‖ ≤ (n + 1) * ‖h‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, loomanBoundedAt]
  rw [hset]
  apply isClosed_iInter
  intro h
  apply isClosed_iInter
  intro hh
  have hcont : Continuous (fun z : C ↦ f z) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono hCs)
  have hcontx : Continuous (fun z : C ↦ f (z + (h : ℂ))) :=
    continuousOn_iff_continuous_domRestrict.mp <|
      hf.comp (by fun_prop) fun z hz ↦ (hshift z hz h hh).1
  have hconty : Continuous (fun z : C ↦ f (z + (h : ℂ) * Complex.I)) :=
    continuousOn_iff_continuous_domRestrict.mp <|
      hf.comp (by fun_prop) fun z hz ↦ (hshift z hz h hh).2
  exact (isClosed_le (hcontx.sub hcont).norm continuous_const).inter
    (isClosed_le (hconty.sub hcont).norm continuous_const)

private theorem looman_baire_boundedAt {f : ℂ → ℂ} {s C : Set ℂ} {r : ℝ}
    [BaireSpace C] (hf : ContinuousOn f s) (hCne : C.Nonempty) (hCs : C ⊆ s)
    (hshift : ∀ (n : ℕ) (z : ℂ), z ∈ C → ∀ h : ℝ, ‖h‖ < r / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s)
    (hx : ∀ z ∈ C, ∃ a, HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ))) a 0)
    (hy : ∀ z ∈ C, ∃ a, HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ) * Complex.I)) a 0) :
    ∃ n, (interior {z : C | loomanBoundedAt f r n z}).Nonempty := by
  let A : ℕ → Set C := fun n ↦ {z | loomanBoundedAt f r n z}
  let _ : Nonempty C := hCne.to_subtype
  have hAclosed (n : ℕ) : IsClosed (A n) := looman_isClosed_boundedAt hf hCs (hshift n)
  have hAuniv : ⋃ n, A n = Set.univ := by
    apply Set.eq_univ_of_forall
    rintro ⟨z, hz⟩
    rcases hx z hz with ⟨ax, hax⟩
    rcases hy z hz with ⟨ay, hay⟩
    rcases looman_exists_boundedAt hax hay with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  simpa [A] using nonempty_interior_of_iUnion_of_closed hAclosed hAuniv

private theorem looman_oneDimensional_estimate
    {w : ℝ → ℝ} {F : Set ℝ} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hFclosed : IsClosed F) (hFne : F.Nonempty)
    (hF : F ⊆ Icc a b)
    (hdiff : ∀ x ∈ F, DifferentiableAt ℝ w x)
    (hLip : ∀ x ∈ F, ∀ y ∈ Icc a b,
      dist (w x) (w y) ≤ K * dist x y) :
    |w b - w a - ∫ x in F, deriv w x| ≤
      K * (volume (Icc a b \ F)).toReal := by
  obtain ⟨c, hcF⟩ := hFne
  have hc := hF hcF
  let F' := F ∪ {a, b}
  have habLip : dist (w a) (w b) ≤ K * dist a b := by
    calc
      dist (w a) (w b) ≤ dist (w a) (w c) + dist (w c) (w b) := dist_triangle _ _ _
      _ ≤ K * dist a c + K * dist c b := by
        gcongr
        · simpa [dist_comm] using hLip c hcF a ⟨le_rfl, hab⟩
        · exact hLip c hcF b ⟨hab, le_rfl⟩
      _ = K * dist a b := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hc.1),
          abs_of_nonpos (sub_nonpos.2 hc.2), abs_of_nonpos (sub_nonpos.2 hab)]
        ring
  have hLip' : LipschitzOnWith K w F' := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [F', mem_union, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hLip x hx y (hF hy)
    · rcases hy with hya | hyb
      · subst y
        exact hLip x hx a ⟨le_rfl, hab⟩
      · subst y
        exact hLip x hx b ⟨hab, le_rfl⟩
    · rcases hx with hxa | hxb
      · subst x
        simpa [dist_comm] using hLip y hy a ⟨le_rfl, hab⟩
      · subst x
        simpa [dist_comm] using hLip y hy b ⟨hab, le_rfl⟩
    · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
      · subst x; subst y; simp
      · subst x; subst y; exact habLip
      · subst x; subst y; simpa [dist_comm] using habLip
      · subst x; subst y; simp
  obtain ⟨g, hgLip, hwg⟩ := hLip'.extend_real
  have hga : g a = w a := (hwg (by simp [F'])).symm
  have hgb : g b = w b := (hwg (by simp [F'])).symm
  have hgAC : AbsolutelyContinuousOnInterval g a b := by
    apply hgLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hderiv : ∀ᵐ x ∂volume.restrict F, deriv g x = deriv w x := by
    have hcount : {x | x ∈ F ∧ nhdsWithin x (F ∩ Ioi x) = ⊥}.Countable :=
      countable_setOfPred_isolated_right_within
    apply (ae_restrict_iff' hFclosed.measurableSet).2
    filter_upwards [hgLip.ae_differentiableAt_real,
      measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero volume)] with x hgdiff hxnot hxF
    have huniq : UniqueDiffWithinAt ℝ F x := by
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin]
      have hnb : (nhdsWithin x (F ∩ Ioi x)).NeBot := by
        rw [neBot_iff]
        exact fun hbot ↦ hxnot ⟨hxF, hbot⟩
      exact hnb.mono (nhdsWithin_mono x fun y hy ↦
        ⟨hy.1, fun h ↦ by subst y; exact (lt_irrefl x) hy.2⟩)
    exact huniq.eq_deriv F
      (hgdiff.hasDerivAt.hasDerivWithinAt.congr
        (fun y hy ↦ hwg (by exact Or.inl hy)) (hwg (by exact Or.inl hxF)))
      ((hdiff x hxF).hasDerivAt.hasDerivWithinAt)
  have hgInt : IntegrableOn (deriv g) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hgAC.intervalIntegrable_deriv
  have hgFInt : IntegrableOn (deriv g) F := hgInt.mono_set hF
  have hwFInt : IntegrableOn (deriv w) F := by
    apply hgFInt.congr
    filter_upwards [hderiv] with x hx
    simpa using hx
  have hdecomp := integral_inter_add_sdiff hFclosed.measurableSet hgInt
  have hinter : Icc a b ∩ F = F := inter_eq_right.2 hF
  rw [hinter] at hdecomp
  have hFTC : ∫ x in Icc a b, deriv g x = g b - g a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact hgAC.integral_deriv_eq_sub
  have hFg : (∫ x in F, deriv g x) = ∫ x in F, deriv w x :=
    integral_congr_ae hderiv
  have hrem : w b - w a - ∫ x in F, deriv w x =
      ∫ x in Icc a b \ F, deriv g x := by
    rw [← hFg, ← hga, ← hgb, ← hFTC, ← hdecomp]
    ring
  rw [hrem]
  simpa only [Real.norm_eq_abs, measureReal_def] using
    (norm_setIntegral_le_of_norm_le_const_ae
      ((lt_top_iff_ne_top).2 (measure_ne_top_of_subset Set.sdiff_subset (by simp)))
      (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hgLip) :
      ‖∫ x in Icc a b \ F, deriv g x‖ ≤
        (K : ℝ) * volume.real (Icc a b \ F))

private theorem looman_integral_fiber_measureReal {S : Set (ℝ × ℝ)} {c d : ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ Set.univ ×ˢ Icc c d) :
    ∫ x : ℝ, volume.real (Prod.mk x ⁻¹' S) = (volume.prod volume).real S := by
  rw [measureReal_def, Measure.prod_apply hS]
  rw [← integral_toReal (measurable_measure_prodMk_left hS).aemeasurable]
  · congr 1
  · filter_upwards with x
    exact lt_top_iff_ne_top.2 <| measure_ne_top_of_subset
      (fun y hy ↦ (hsub hy).2) (by simp)

private theorem looman_vertical_estimate
    {φ : ℝ × ℝ → ℝ} {E : Set (ℝ × ℝ)}
    {A B C D a b c d K L κ : ℝ}
    (hAa : A ≤ a) (hbB : b ≤ B)
    (hCc : C ≤ c) (hcd : c ≤ d) (hdD : d ≤ D)
    (hCD : C < D)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L) (hLheight : L ≤ κ * (D - C))
    (hcont : Continuous φ) (hEclosed : IsClosed E) (hEcompact : IsCompact E)
    (hEsub : E ⊆ Icc a b ×ˢ Icc c d)
    (hbot : ∃ x, (x, c) ∈ E) (htop : ∃ x, (x, d) ∈ E)
    (hdiff : ∀ p ∈ E, DifferentiableAt ℝ (fun y ↦ φ (p.1, y)) p.2)
    (hderiv : ∀ p ∈ E, |deriv (fun y ↦ φ (p.1, y)) p.2| ≤ K)
    (hLipX : ∀ p ∈ E, ∀ x ∈ Icc A B,
      |φ (x, p.2) - φ p| ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ E, ∀ y ∈ Icc C D,
      |φ (p.1, y) - φ p| ≤ K * |y - p.2|) :
    |(∫ x in Icc a b, φ (x, d) - φ (x, c)) -
        ∫ p in E, deriv (fun y ↦ φ (p.1, y)) p.2 ∂(volume.prod volume)| ≤
      (1 + 4 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ E) := by
  let P : Set ℝ := Prod.fst '' E
  have hPcompact : IsCompact P := hEcompact.image continuous_fst
  have hPclosed : IsClosed P := hPcompact.isClosed
  have hPsub : P ⊆ Icc a b := by
    rintro x ⟨p, hpE, rfl⟩
    exact (hEsub hpE).1
  let R : Set (ℝ × ℝ) := Icc A B ×ˢ Icc C D
  let S : Set (ℝ × ℝ) := R \ E
  have hRmeas : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hSmeas : MeasurableSet S := hRmeas.diff hEclosed.measurableSet
  have hSsub : S ⊆ Set.univ ×ˢ Icc C D := by
    intro p hp
    exact ⟨mem_univ _, hp.1.2⟩
  let dy : ℝ × ℝ → ℝ := fun p ↦ deriv (fun y ↦ φ (p.1, y)) p.2
  have hdymeas : Measurable dy := by
    exact measurable_deriv_with_param (f := fun x y ↦ φ (x, y)) (by
      change Continuous (fun p : ℝ × ℝ ↦ φ p)
      exact hcont)
  have hdyInt : IntegrableOn dy E (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := K) hEcompact.measure_lt_top.ne
      hdymeas.aestronglyMeasurable ?_
    exact (ae_restrict_iff' hEclosed.measurableSet).2 <| by
      filter_upwards with p hp
      simpa [dy, Real.norm_eq_abs] using hderiv p hp
  let G : ℝ × ℝ → ℝ := E.indicator dy
  have hGInt : Integrable G (volume.prod volume) :=
    hdyInt.integrable_indicator hEclosed.measurableSet
  let q : ℝ → ℝ := fun x ↦ ∫ y : ℝ, G (x, y)
  have hqInt : Integrable q volume := hGInt.integral_prod_left
  have hEIntegral : (∫ p in E, dy p ∂(volume.prod volume)) = ∫ x, q x := by
    rw [← integral_indicator hEclosed.measurableSet, integral_prod _ hGInt]
  have hq_zero {x : ℝ} (hx : x ∉ P) : q x = 0 := by
    simp only [q]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have hxy : (x, y) ∉ E := fun h ↦ hx ⟨(x, y), h, rfl⟩
    simp [G, hxy]
  have hqIntegralP : (∫ x, q x) = ∫ x in P, q x := by
    rw [← integral_indicator hPclosed.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ P
    · simp [hx]
    · simp [hx, hq_zero hx]
  let v : ℝ → ℝ := fun x ↦ φ (x, d) - φ (x, c)
  have hvcont : Continuous v := by
    dsimp [v]
    fun_prop
  have hvInt : IntegrableOn v (Icc a b) volume :=
    hvcont.continuousOn.integrableOn_compact isCompact_Icc
  have hqPInt : IntegrableOn q P volume := hqInt.integrableOn
  let e : ℝ → ℝ := fun x ↦ v x - q x
  have hePInt : IntegrableOn e P volume :=
    (hvInt.mono_set hPsub).sub hqPInt
  let T : Set ℝ := Icc a b \ P
  have hTmeas : MeasurableSet T := measurableSet_Icc.diff hPclosed.measurableSet
  have hvTInt : IntegrableOn v T volume := hvInt.mono_set Set.sdiff_subset
  have hdecomp : (∫ x in Icc a b, v x) - ∫ x, q x =
      (∫ x in P, e x) + ∫ x in T, v x := by
    have hsplit := integral_inter_add_sdiff hPclosed.measurableSet hvInt
    rw [inter_eq_right.2 hPsub] at hsplit
    rw [hqIntegralP, ← hsplit]
    rw [integral_sub (hvInt.mono_set hPsub) hqPInt]
    ring
  let m : ℝ → ℝ := fun x ↦ volume.real (Prod.mk x ⁻¹' S)
  have hmmeas : Measurable m := (measurable_measure_prodMk_left hSmeas).ennreal_toReal
  have hm_nonneg (x : ℝ) : 0 ≤ m x := measureReal_nonneg
  have hm_zero {x : ℝ} (hx : x ∉ Icc A B) : m x = 0 := by
    change volume.real (Prod.mk x ⁻¹' S) = 0
    rw [show Prod.mk x ⁻¹' S = ∅ by
      ext y
      simp only [Set.mem_preimage, mem_empty_iff_false, iff_false]
      intro hy
      exact hx hy.1.1]
    simp
  have hm_bound (x : ℝ) : m x ≤ D - C := by
    change volume.real (Prod.mk x ⁻¹' S) ≤ D - C
    rw [measureReal_def]
    have hvol : D - C = (volume (Icc C D)).toReal := by simp [hCD.le]
    rw [hvol]
    apply ENNReal.toReal_mono (by simp)
    exact measure_mono fun y hy ↦ (hSsub hy).2
  have hmInt : Integrable m volume := by
    have hi : IntegrableOn m (Icc A B) volume := by
      refine Measure.integrableOn_of_bounded (M := D - C) (by simp)
        hmmeas.aestronglyMeasurable ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 <| by
        filter_upwards with x _
        rw [Real.norm_eq_abs, abs_of_nonneg (hm_nonneg x)]
        exact hm_bound x
    apply (hi.integrable_indicator measurableSet_Icc).congr
    filter_upwards with x
    by_cases hx : x ∈ Icc A B
    · simp [hx]
    · simp [hx, hm_zero hx]
  have hmIntegral : (∫ x, m x) = (volume.prod volume).real S := by
    exact looman_integral_fiber_measureReal hSmeas hSsub
  have he_bound : ∀ x ∈ P, |e x| ≤ K * m x := by
    rintro x ⟨p, hpE, rfl⟩
    let Fx : Set ℝ := Prod.mk p.1 ⁻¹' E
    have hFxclosed : IsClosed Fx := hEclosed.preimage (by fun_prop)
    have hFxne : Fx.Nonempty := ⟨p.2, hpE⟩
    have hFxsub : Fx ⊆ Icc c d := fun y hy ↦ (hEsub hy).2
    have hone := looman_oneDimensional_estimate (w := fun y ↦ φ (p.1, y))
      (K := ⟨K, hK⟩) hcd hFxclosed hFxne hFxsub
      (fun y hy ↦ hdiff (p.1, y) hy)
      (fun y hy z hz ↦ by
        change |φ (p.1, y) - φ (p.1, z)| ≤ K * |y - z|
        simpa only [Real.dist_eq, abs_sub_comm] using hLipY (p.1, y) hy z
          ⟨hCc.trans hz.1, hz.2.trans hdD⟩)
    have hqeq : q p.1 = ∫ y in Fx, deriv (fun y ↦ φ (p.1, y)) y := by
      simp only [q]
      rw [← integral_indicator hFxclosed.measurableSet]
      apply integral_congr_ae
      filter_upwards with y
      rfl
    have hsubset : Icc c d \ Fx ⊆ Prod.mk p.1 ⁻¹' S := by
      rintro y ⟨hycd, hyE⟩
      exact ⟨⟨⟨hAa.trans (hEsub hpE).1.1, (hEsub hpE).1.2.trans hbB⟩,
        ⟨hCc.trans hycd.1, hycd.2.trans hdD⟩⟩, hyE⟩
    have hmeasure : (volume (Icc c d \ Fx)).toReal ≤ m p.1 := by
      change volume.real (Icc c d \ Fx) ≤ volume.real (Prod.mk p.1 ⁻¹' S)
      exact measureReal_mono hsubset (h₂ :=
        measure_ne_top_of_subset (fun y hy ↦ (hSsub hy).2) (by simp))
    change |φ (p.1, d) - φ (p.1, c) - q p.1| ≤ K * m p.1
    rw [hqeq]
    have hone' : |φ (p.1, d) - φ (p.1, c) -
        ∫ y in Fx, deriv (fun y ↦ φ (p.1, y)) y| ≤
        K * (volume (Icc c d \ Fx)).toReal := by
      change _ ≤ K * (volume (Icc c d \ Fx)).toReal at hone
      exact hone
    exact hone'.trans (mul_le_mul_of_nonneg_left hmeasure hK)
  have he_norm : ‖∫ x in P, e x‖ ≤ K * (volume.prod volume).real S := by
    calc
      ‖∫ x in P, e x‖ ≤ ∫ x in P, ‖e x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in P, K * m x := by
        exact setIntegral_mono_on hePInt.norm ((hmInt.const_mul K).integrableOn)
          hPclosed.measurableSet fun x hx ↦ by
            simpa [Real.norm_eq_abs] using he_bound x hx
      _ ≤ ∫ x, K * m x := by
        rw [← integral_indicator hPclosed.measurableSet]
        apply integral_mono_ae
          ((hmInt.const_mul K).integrableOn.integrable_indicator hPclosed.measurableSet)
          (hmInt.const_mul K)
        filter_upwards with x
        by_cases hx : x ∈ P
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          exact mul_nonneg hK (hm_nonneg x)
      _ = K * (volume.prod volume).real S := by
        rw [integral_const_mul, hmIntegral]
  obtain ⟨x₀, hx₀⟩ := hbot
  obtain ⟨x₁, hx₁⟩ := htop
  have hx₀ab := (hEsub hx₀).1
  have hx₁ab := (hEsub hx₁).1
  have hv_bound (x : ℝ) (hx : x ∈ Icc a b) : |v x| ≤ 4 * K * L := by
    have h1 := hLipX (x₁, d) hx₁ x ⟨hAa.trans hx.1, hx.2.trans hbB⟩
    have h2 := hLipX (x₁, d) hx₁ x₀ ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩
    have h3 := hLipY (x₀, c) hx₀ d ⟨hCc.trans hcd, hdD⟩
    have h4 := hLipX (x₀, c) hx₀ x ⟨hAa.trans hx.1, hx.2.trans hbB⟩
    have hxL (u v : ℝ) (hu : u ∈ Icc A B) (hv : v ∈ Icc A B) : |u - v| ≤ L := by
      calc
        |u - v| ≤ B - A := by
          rw [abs_le]
          constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
        _ ≤ L := hLx
    have hyL : |d - c| ≤ L := by
      rw [abs_of_nonneg (sub_nonneg.2 hcd)]
      exact (sub_le_sub hdD hCc).trans hLy
    have habs (r s t u : ℝ) : |r + s + t + u| ≤ |r| + |s| + |t| + |u| := by
      linarith [abs_add_le r s, abs_add_le (r + s) t, abs_add_le (r + s + t) u]
    have h1L : |φ (x, d) - φ (x₁, d)| ≤ K * L :=
      h1.trans (mul_le_mul_of_nonneg_left
        (hxL x x₁ ⟨hAa.trans hx.1, hx.2.trans hbB⟩
          ⟨hAa.trans hx₁ab.1, hx₁ab.2.trans hbB⟩) hK)
    have h2L : |φ (x₁, d) - φ (x₀, d)| ≤ K * L := by
      rw [abs_sub_comm]
      exact h2.trans (mul_le_mul_of_nonneg_left
        (hxL x₀ x₁ ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩
          ⟨hAa.trans hx₁ab.1, hx₁ab.2.trans hbB⟩) hK)
    have h3L : |φ (x₀, d) - φ (x₀, c)| ≤ K * L :=
      h3.trans (mul_le_mul_of_nonneg_left hyL hK)
    have h4L : |φ (x₀, c) - φ (x, c)| ≤ K * L := by
      rw [abs_sub_comm]
      exact h4.trans (mul_le_mul_of_nonneg_left
        (hxL x x₀ ⟨hAa.trans hx.1, hx.2.trans hbB⟩
          ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩) hK)
    calc
      |v x| = |(φ (x, d) - φ (x₁, d)) + (φ (x₁, d) - φ (x₀, d)) +
          (φ (x₀, d) - φ (x₀, c)) + (φ (x₀, c) - φ (x, c))| := by
        dsimp [v]
        congr 1
        ring
      _ ≤ |φ (x, d) - φ (x₁, d)| + |φ (x₁, d) - φ (x₀, d)| +
          |φ (x₀, d) - φ (x₀, c)| + |φ (x₀, c) - φ (x, c)| := by
        exact habs _ _ _ _
      _ ≤ K * L + K * L + K * L + K * L := by
        exact add_le_add (add_le_add (add_le_add h1L h2L) h3L) h4L
      _ = 4 * K * L := by ring
  have hTprod : T ×ˢ Icc C D ⊆ S := by
    rintro ⟨x, y⟩ ⟨hxT, hyCD⟩
    refine ⟨⟨?_, hyCD⟩, ?_⟩
    · exact ⟨hAa.trans hxT.1.1, hxT.1.2.trans hbB⟩
    · intro hxyE
      exact hxT.2 ⟨(x, y), hxyE, rfl⟩
  have hstrip : L * volume.real T ≤ κ * (volume.prod volume).real S := by
    have hDClen : volume.real (Icc C D) = D - C := by simp [hCD.le]
    calc
      L * volume.real T ≤ κ * (D - C) * volume.real T :=
        mul_le_mul_of_nonneg_right hLheight measureReal_nonneg
      _ = κ * (volume.prod volume).real (T ×ˢ Icc C D) := by
        rw [measureReal_prod_prod, hDClen]
        ring
      _ ≤ κ * (volume.prod volume).real S := by
        apply mul_le_mul_of_nonneg_left _ hκ
        have hRcompact : IsCompact R := isCompact_Icc.prod isCompact_Icc
        have hSfinite : (volume.prod volume) S ≠ ∞ :=
          measure_ne_top_of_subset Set.sdiff_subset hRcompact.measure_lt_top.ne
        exact measureReal_mono hTprod (h₂ := hSfinite)
  have hv_norm : ‖∫ x in T, v x‖ ≤ 4 * K * κ * (volume.prod volume).real S := by
    calc
      ‖∫ x in T, v x‖ ≤ 4 * K * L * volume.real T := by
        apply norm_setIntegral_le_of_norm_le_const_ae
        · exact (measure_ne_top_of_subset Set.sdiff_subset (by simp)).lt_top
        · apply (ae_restrict_iff' hTmeas).2
          filter_upwards with x hx
          simpa [Real.norm_eq_abs] using hv_bound x hx.1
      _ = 4 * K * (L * volume.real T) := by ring
      _ ≤ 4 * K * (κ * (volume.prod volume).real S) := by gcongr
      _ = 4 * K * κ * (volume.prod volume).real S := by ring
  rw [show (∫ p in E, deriv (fun y ↦ φ (p.1, y)) p.2 ∂(volume.prod volume)) =
      ∫ p in E, dy p ∂(volume.prod volume) by rfl]
  rw [hEIntegral, hdecomp]
  calc
    |(∫ x in P, e x) + ∫ x in T, v x| =
        ‖(∫ x in P, e x) + ∫ x in T, v x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖∫ x in P, e x‖ + ‖∫ x in T, v x‖ := norm_add_le _ _
    _ ≤ K * (volume.prod volume).real S +
        4 * K * κ * (volume.prod volume).real S := add_le_add he_norm hv_norm
    _ = (1 + 4 * κ) * K * (volume.prod volume).real S := by ring
    _ = _ := rfl

private theorem looman_horizontal_estimate
    {φ : ℝ × ℝ → ℝ} {E : Set (ℝ × ℝ)}
    {A B C D a b c d K L κ : ℝ}
    (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hCc : C ≤ c) (hdD : d ≤ D)
    (hAB : A < B)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L) (hLwidth : L ≤ κ * (B - A))
    (hcont : Continuous φ) (hEclosed : IsClosed E) (hEcompact : IsCompact E)
    (hEsub : E ⊆ Icc a b ×ˢ Icc c d)
    (hleft : ∃ y, (a, y) ∈ E) (hright : ∃ y, (b, y) ∈ E)
    (hdiff : ∀ p ∈ E, DifferentiableAt ℝ (fun x ↦ φ (x, p.2)) p.1)
    (hderiv : ∀ p ∈ E, |deriv (fun x ↦ φ (x, p.2)) p.1| ≤ K)
    (hLipX : ∀ p ∈ E, ∀ x ∈ Icc A B,
      |φ (x, p.2) - φ p| ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ E, ∀ y ∈ Icc C D,
      |φ (p.1, y) - φ p| ≤ K * |y - p.2|) :
    |(∫ y in Icc c d, φ (b, y) - φ (a, y)) -
        ∫ p in E, deriv (fun x ↦ φ (x, p.2)) p.1 ∂(volume.prod volume)| ≤
      (1 + 4 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ E) := by
  let ψ : ℝ × ℝ → ℝ := fun p ↦ φ p.swap
  let F : Set (ℝ × ℝ) := Prod.swap '' E
  have hFcompact : IsCompact F := hEcompact.image continuous_swap
  have hFclosed : IsClosed F := hFcompact.isClosed
  have hFsub : F ⊆ Icc c d ×ˢ Icc a b := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨(hEsub hq).2, (hEsub hq).1⟩
  have hFbot : ∃ x, (x, a) ∈ F := by
    obtain ⟨y, hy⟩ := hleft
    exact ⟨y, ⟨(a, y), hy, rfl⟩⟩
  have hFtop : ∃ x, (x, b) ∈ F := by
    obtain ⟨y, hy⟩ := hright
    exact ⟨y, ⟨(b, y), hy, rfl⟩⟩
  have hψcont : Continuous ψ := hcont.comp continuous_swap
  have hFdiff : ∀ p ∈ F, DifferentiableAt ℝ (fun y ↦ ψ (p.1, y)) p.2 := by
    rintro p ⟨q, hq, rfl⟩
    simpa [ψ] using hdiff q hq
  have hFderiv : ∀ p ∈ F, |deriv (fun y ↦ ψ (p.1, y)) p.2| ≤ K := by
    rintro p ⟨q, hq, rfl⟩
    simpa [ψ] using hderiv q hq
  have hFLipX : ∀ p ∈ F, ∀ x ∈ Icc C D,
      |ψ (x, p.2) - ψ p| ≤ K * |x - p.1| := by
    rintro p ⟨q, hq, rfl⟩ x hx
    simpa [ψ] using hLipY q hq x hx
  have hFLipY : ∀ p ∈ F, ∀ y ∈ Icc A B,
      |ψ (p.1, y) - ψ p| ≤ K * |y - p.2| := by
    rintro p ⟨q, hq, rfl⟩ y hy
    simpa [ψ] using hLipX q hq y hy
  have h := looman_vertical_estimate (A := C) (B := D) (C := A) (D := B)
    (a := c) (b := d) (c := a) (d := b) (K := K) (L := L) (κ := κ)
    hCc hdD hAa hab hbB hAB hK hκ hLy hLx hLwidth
    hψcont hFclosed hFcompact hFsub hFbot hFtop hFdiff hFderiv hFLipX hFLipY
  have hintergral :
      (∫ p in F, deriv (fun y ↦ ψ (p.1, y)) p.2 ∂(volume.prod volume)) =
        ∫ p in E, deriv (fun x ↦ φ (x, p.2)) p.1 ∂(volume.prod volume) := by
    rw [show F = Prod.swap '' E by rfl]
    rw [(Measure.measurePreserving_swap (μ := volume) (ν := volume)).setIntegral_image_emb
      MeasurableEquiv.prodComm.measurableEmbedding]
    apply setIntegral_congr_fun hEclosed.measurableSet
    intro p hp
    simp [ψ]
  have hsets : (Icc C D ×ˢ Icc A B) \ F =
      Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E) := by
    ext p
    simp only [F, Set.mem_sdiff, mem_prod, Set.mem_Icc, Set.mem_image]
    constructor
    · rintro ⟨hpR, hpF⟩
      refine ⟨p.swap, ⟨⟨hpR.2, hpR.1⟩, ?_⟩, by simp⟩
      intro hpE
      exact hpF ⟨p.swap, hpE, by simp⟩
    · rintro ⟨q, ⟨hqR, hqE⟩, rfl⟩
      refine ⟨⟨hqR.2, hqR.1⟩, ?_⟩
      rintro ⟨r, hrE, hrswap⟩
      have : r = q := by
        apply Prod.swap_injective
        simpa using hrswap
      exact hqE (this ▸ hrE)
  have hmeasure : (volume.prod volume).real ((Icc C D ×ˢ Icc A B) \ F) =
      (volume.prod volume).real ((Icc A B ×ˢ Icc C D) \ E) := by
    rw [hsets, measureReal_def, measureReal_def]
    congr 1
    let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
    let hp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
    calc
      μ (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E)) =
          (Measure.map Prod.swap μ) (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E)) := by
        rw [hp.map_eq]
      _ = μ (Prod.swap ⁻¹' (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E))) :=
        MeasurableEquiv.prodComm.measurableEmbedding.map_apply _ _
      _ = μ ((Icc A B ×ˢ Icc C D) \ E) := by
        congr 1
        ext p
        simp
  rw [hintergral, hmeasure] at h
  simpa [ψ] using h

private def loomanPoint (x y : ℝ) : ℂ := x + y * Complex.I

private def loomanRectBoundary (f : ℂ → ℂ) (A B C D : ℝ) : ℂ :=
  (∫ x in A..B, f (loomanPoint x C) - f (loomanPoint x D)) +
    Complex.I * ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint A y)

private theorem looman_rectBoundary_split_x {f : ℂ → ℂ} (hf : Continuous f)
    {A x B C D : ℝ} :
    loomanRectBoundary f A x C D + loomanRectBoundary f x B C D =
      loomanRectBoundary f A B C D := by
  have hh₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t D)) volume A x :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t D)) volume x B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint x y) - f (loomanPoint A y)) volume C D :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint x y) - f (loomanPoint A y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint B y) - f (loomanPoint x y)) volume C D :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint B y) - f (loomanPoint x y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  unfold loomanRectBoundary
  calc
    ((∫ t in A..x, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
        ((∫ t in x..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) =
        ((∫ t in A..x, f (loomanPoint t C) - f (loomanPoint t D)) +
          ∫ t in x..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ((∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
            ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) := by ring
    _ = (∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t D)) +
          Complex.I * ((∫ y in C..D, f (loomanPoint x y) - f (loomanPoint A y)) +
            ∫ y in C..D, f (loomanPoint B y) - f (loomanPoint x y)) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hh₁ hh₂]
    _ = _ := by
      rw [← intervalIntegral.integral_add hv₁ hv₂]
      congr 2
      apply intervalIntegral.integral_congr
      intro y _
      ring

private theorem looman_rectBoundary_split_y {f : ℂ → ℂ} (hf : Continuous f)
    {A B C y D : ℝ} :
    loomanRectBoundary f A B C y + loomanRectBoundary f A B y D =
      loomanRectBoundary f A B C D := by
  have hh₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t C) - f (loomanPoint t y)) volume A B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t C) - f (loomanPoint t y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint t y) - f (loomanPoint t D)) volume A B :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint t y) - f (loomanPoint t D)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint B t) - f (loomanPoint A t)) volume C y :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint B t) - f (loomanPoint A t)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun t : ℝ ↦ f (loomanPoint B t) - f (loomanPoint A t)) volume y D :=
    (show Continuous (fun t : ℝ ↦
      f (loomanPoint B t) - f (loomanPoint A t)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  unfold loomanRectBoundary
  calc
    ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          Complex.I * ∫ t in C..y, f (loomanPoint B t) - f (loomanPoint A t)) +
        ((∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ∫ t in y..D, f (loomanPoint B t) - f (loomanPoint A t)) =
        ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          ∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ((∫ t in C..y, f (loomanPoint B t) - f (loomanPoint A t)) +
            ∫ t in y..D, f (loomanPoint B t) - f (loomanPoint A t)) := by ring
    _ = ((∫ t in A..B, f (loomanPoint t C) - f (loomanPoint t y)) +
          ∫ t in A..B, f (loomanPoint t y) - f (loomanPoint t D)) +
          Complex.I * ∫ t in C..D, f (loomanPoint B t) - f (loomanPoint A t) := by
      rw [intervalIntegral.integral_add_adjacent_intervals hv₁ hv₂]
    _ = _ := by
      rw [← intervalIntegral.integral_add hh₁ hh₂]
      congr 2
      funext t
      ring

private theorem looman_rectBoundary_eq_zero_of_differentiableOn
    {f : ℂ → ℂ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hcont : Continuous f)
    (hdiff : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D,
      DifferentiableAt ℂ f (loomanPoint x y)) :
    loomanRectBoundary f A B C D = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (loomanPoint A C) (loomanPoint B D) hcont.continuousOn (by
      intro z hz
      have hzre : z.re ∈ Ioo A B := by simpa [loomanPoint, hAB] using hz.1
      have hzim : z.im ∈ Ioo C D := by simpa [loomanPoint, hCD] using hz.2
      rw [show z = loomanPoint z.re z.im by
        rw [loomanPoint]
        exact (Complex.re_add_im z).symm]
      exact (hdiff z.re hzre z.im hzim).differentiableWithinAt)
  have hh₁ : IntervalIntegrable (fun x : ℝ ↦ f (loomanPoint x C)) volume A B :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x C)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable (fun x : ℝ ↦ f (loomanPoint x D)) volume A B :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x D)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable (fun y : ℝ ↦ f (loomanPoint B y)) volume C D :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint B y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable (fun y : ℝ ↦ f (loomanPoint A y)) volume C D :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint A y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  rw [loomanRectBoundary, intervalIntegral.integral_sub hh₁ hh₂,
    intervalIntegral.integral_sub hv₁ hv₂]
  have h' := h
  simp [loomanPoint, smul_eq_mul] at h'
  simp only [loomanPoint]
  linear_combination h'

private theorem looman_rectBoundary_eq_hull
    {f : ℂ → ℂ} {F : Set (ℝ × ℝ)} {A B C D a b c d : ℝ}
    (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hCc : C ≤ c) (hcd : c ≤ d) (hdD : d ≤ D)
    (hcont : Continuous f) (hFsub : F ⊆ Icc a b ×ˢ Icc c d)
    (hdiff : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D, (x, y) ∉ F →
      DifferentiableAt ℂ f (loomanPoint x y)) :
    loomanRectBoundary f A B C D = loomanRectBoundary f a b c d := by
  have hleft : loomanRectBoundary f A a C D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hAa
      (hCc.trans <| hcd.trans hdD) hcont <| by
        intro x hx y hy
        exact hdiff x ⟨hx.1, hx.2.trans_le (hab.trans hbB)⟩ y hy fun hF ↦
          (not_le_of_gt hx.2) (hFsub hF).1.1
  have hright : loomanRectBoundary f b B C D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hbB
      (hCc.trans <| hcd.trans hdD) hcont <| by
        intro x hx y hy
        exact hdiff x ⟨(hAa.trans hab).trans_lt hx.1, hx.2⟩ y hy fun hF ↦
          (not_le_of_gt hx.1) (hFsub hF).1.2
  have hbottom : loomanRectBoundary f a b C c = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hab hCc hcont <| by
      intro x hx y hy
      exact hdiff x ⟨hAa.trans_lt hx.1, hx.2.trans_le hbB⟩ y
        ⟨hy.1, hy.2.trans_le (hcd.trans hdD)⟩ fun hF ↦
          (not_le_of_gt hy.2) (hFsub hF).2.1
  have htop : loomanRectBoundary f a b d D = 0 :=
    looman_rectBoundary_eq_zero_of_differentiableOn hab hdD hcont <| by
      intro x hx y hy
      exact hdiff x ⟨hAa.trans_lt hx.1, hx.2.trans_le hbB⟩ y
        ⟨(hCc.trans hcd).trans_lt hy.1, hy.2⟩ fun hF ↦
          (not_le_of_gt hy.1) (hFsub hF).2.2
  calc
    loomanRectBoundary f A B C D =
        loomanRectBoundary f A a C D + loomanRectBoundary f a B C D :=
      (looman_rectBoundary_split_x hcont).symm
    _ = loomanRectBoundary f a B C D := by rw [hleft, zero_add]
    _ = loomanRectBoundary f a b C D + loomanRectBoundary f b B C D :=
      (looman_rectBoundary_split_x hcont).symm
    _ = loomanRectBoundary f a b C D := by rw [hright, add_zero]
    _ = loomanRectBoundary f a b C c + loomanRectBoundary f a b c D :=
      (looman_rectBoundary_split_y hcont).symm
    _ = loomanRectBoundary f a b c D := by rw [hbottom, zero_add]
    _ = loomanRectBoundary f a b c d + loomanRectBoundary f a b d D :=
      (looman_rectBoundary_split_y hcont).symm
    _ = loomanRectBoundary f a b c d := by rw [htop, add_zero]

private theorem looman_rectBoundary_re_eq {f : ℂ → ℂ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (loomanRectBoundary f a b c d).re =
      -(∫ x in Icc a b, (f (loomanPoint x d)).re - (f (loomanPoint x c)).re) -
        ∫ y in Icc c d, (f (loomanPoint b y)).im - (f (loomanPoint a y)).im := by
  have hh : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x c) - f (loomanPoint x d)) volume a b :=
    (show Continuous (fun x : ℝ ↦
      f (loomanPoint x c) - f (loomanPoint x d)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint b y) - f (loomanPoint a y)) volume c d :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint b y) - f (loomanPoint a y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh_re : (∫ x in a..b,
      f (loomanPoint x c) - f (loomanPoint x d)).re =
      ∫ x in a..b, (f (loomanPoint x c) - f (loomanPoint x d)).re := by
    symm
    simpa using intervalIntegral.intervalIntegral_re hh
  have hv_im : (∫ y in c..d,
      f (loomanPoint b y) - f (loomanPoint a y)).im =
      ∫ y in c..d, (f (loomanPoint b y) - f (loomanPoint a y)).im := by
    symm
    simpa using intervalIntegral.intervalIntegral_im hv
  rw [loomanRectBoundary]
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, hh_re, hv_im]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply congrArg₂ Sub.sub
  · rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp
  · rfl

private theorem looman_rectBoundary_im_eq {f : ℂ → ℂ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (loomanRectBoundary f a b c d).im =
      -(∫ x in Icc a b, (f (loomanPoint x d)).im - (f (loomanPoint x c)).im) +
        ∫ y in Icc c d, (f (loomanPoint b y)).re - (f (loomanPoint a y)).re := by
  have hh : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x c) - f (loomanPoint x d)) volume a b :=
    (show Continuous (fun x : ℝ ↦
      f (loomanPoint x c) - f (loomanPoint x d)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hv : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint b y) - f (loomanPoint a y)) volume c d :=
    (show Continuous (fun y : ℝ ↦
      f (loomanPoint b y) - f (loomanPoint a y)) by
        unfold loomanPoint
        fun_prop).intervalIntegrable _ _
  have hh_im : (∫ x in a..b,
      f (loomanPoint x c) - f (loomanPoint x d)).im =
      ∫ x in a..b, (f (loomanPoint x c) - f (loomanPoint x d)).im := by
    symm
    simpa using intervalIntegral.intervalIntegral_im hh
  have hv_re : (∫ y in c..d,
      f (loomanPoint b y) - f (loomanPoint a y)).re =
      ∫ y in c..d, (f (loomanPoint b y) - f (loomanPoint a y)).re := by
    symm
    simpa using intervalIntegral.intervalIntegral_re hv
  rw [loomanRectBoundary]
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, hh_im, hv_re]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply congrArg₂ Add.add
  · rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp
  · rfl

private theorem looman_exists_coordinate_hull {F : Set (ℝ × ℝ)} {A B C D : ℝ}
    (hFcompact : IsCompact F) (hFne : F.Nonempty)
    (hFsub : F ⊆ Icc A B ×ˢ Icc C D) :
    ∃ a b c d,
      A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
      F ⊆ Icc a b ×ˢ Icc c d ∧
      (∃ y, (a, y) ∈ F) ∧ (∃ y, (b, y) ∈ F) ∧
      (∃ x, (x, c) ∈ F) ∧ (∃ x, (x, d) ∈ F) := by
  obtain ⟨pa, hpaF, hpa⟩ :=
    hFcompact.exists_isMinOn hFne continuous_fst.continuousOn
  obtain ⟨pb, hpbF, hpb⟩ :=
    hFcompact.exists_isMaxOn hFne continuous_fst.continuousOn
  obtain ⟨pc, hpcF, hpc⟩ :=
    hFcompact.exists_isMinOn hFne continuous_snd.continuousOn
  obtain ⟨pd, hpdF, hpd⟩ :=
    hFcompact.exists_isMaxOn hFne continuous_snd.continuousOn
  refine ⟨pa.1, pb.1, pc.2, pd.2, (hFsub hpaF).1.1, hpa hpbF,
    (hFsub hpbF).1.2, (hFsub hpcF).2.1, hpc hpdF, (hFsub hpdF).2.2, ?_,
    ⟨pa.2, hpaF⟩, ⟨pb.2, hpbF⟩, ⟨pc.1, hpcF⟩, ⟨pd.1, hpdF⟩⟩
  intro p hp
  exact ⟨⟨hpa hp, hpb hp⟩, hpc hp, hpd hp⟩

private theorem looman_rectBoundary_norm_le
    {f : ℂ → ℂ} {F : Set (ℝ × ℝ)}
    {A B C D K L κ : ℝ} {ux uy vx vy : ℝ × ℝ → ℝ}
    (hAB : A < B) (hCD : C < D) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L)
    (hLheight : L ≤ κ * (D - C)) (hLwidth : L ≤ κ * (B - A))
    (hcont : Continuous f) (hFcompact : IsCompact F) (hFne : F.Nonempty)
    (hFsub : F ⊆ Icc A B ×ˢ Icc C D)
    (hhol : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo C D, (x, y) ∉ F →
      DifferentiableAt ℂ f (loomanPoint x y))
    (hux : ∀ p ∈ F,
      HasDerivAt (fun x ↦ (f (loomanPoint x p.2)).re) (ux p) p.1)
    (huy : ∀ p ∈ F,
      HasDerivAt (fun y ↦ (f (loomanPoint p.1 y)).re) (uy p) p.2)
    (hvx : ∀ p ∈ F,
      HasDerivAt (fun x ↦ (f (loomanPoint x p.2)).im) (vx p) p.1)
    (hvy : ∀ p ∈ F,
      HasDerivAt (fun y ↦ (f (loomanPoint p.1 y)).im) (vy p) p.2)
    (huxK : ∀ p ∈ F, |ux p| ≤ K) (huyK : ∀ p ∈ F, |uy p| ≤ K)
    (hvxK : ∀ p ∈ F, |vx p| ≤ K) (hvyK : ∀ p ∈ F, |vy p| ≤ K)
    (hcr₁ : ∀ p ∈ F, ux p = vy p) (hcr₂ : ∀ p ∈ F, uy p = -(vx p))
    (hLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ ≤ K * |y - p.2|) :
    ‖loomanRectBoundary f A B C D‖ ≤
      (4 + 16 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ F) := by
  obtain ⟨a, b, c, d, hAa, hab, hbB, hCc, hcd, hdD, hFhull,
    hleft, hright, hbot, htop⟩ :=
    looman_exists_coordinate_hull hFcompact hFne hFsub
  let u : ℝ × ℝ → ℝ := fun p ↦ (f (loomanPoint p.1 p.2)).re
  let v : ℝ × ℝ → ℝ := fun p ↦ (f (loomanPoint p.1 p.2)).im
  have hucont : Continuous u := by unfold u loomanPoint; fun_prop
  have hvcont : Continuous v := by unfold v loomanPoint; fun_prop
  have huLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      |u (x, p.2) - u p| ≤ K * |x - p.1| := by
    intro p hp x hx
    calc
      |u (x, p.2) - u p| =
          |(f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)).re| := by rfl
      _ ≤ ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ K * |x - p.1| := hLipX p hp x hx
  have huLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      |u (p.1, y) - u p| ≤ K * |y - p.2| := by
    intro p hp y hy
    calc
      |u (p.1, y) - u p| =
          |(f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)).re| := by rfl
      _ ≤ ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ K * |y - p.2| := hLipY p hp y hy
  have hvLipX : ∀ p ∈ F, ∀ x ∈ Icc A B,
      |v (x, p.2) - v p| ≤ K * |x - p.1| := by
    intro p hp x hx
    calc
      |v (x, p.2) - v p| =
          |(f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)).im| := by rfl
      _ ≤ ‖f (loomanPoint x p.2) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ K * |x - p.1| := hLipX p hp x hx
  have hvLipY : ∀ p ∈ F, ∀ y ∈ Icc C D,
      |v (p.1, y) - v p| ≤ K * |y - p.2| := by
    intro p hp y hy
    calc
      |v (p.1, y) - v p| =
          |(f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)).im| := by rfl
      _ ≤ ‖f (loomanPoint p.1 y) - f (loomanPoint p.1 p.2)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ K * |y - p.2| := hLipY p hp y hy
  let m := (1 + 4 * κ) * K * (volume.prod volume).real
    ((Icc A B ×ˢ Icc C D) \ F)
  have huY := looman_vertical_estimate hAa hbB hCc hcd hdD hCD hK hκ
    hLx hLy hLheight hucont hFcompact.isClosed hFcompact hFhull hbot htop
    (fun p hp ↦ (huy p hp).differentiableAt)
    (fun p hp ↦ by rw [(huy p hp).deriv]; exact huyK p hp) huLipX huLipY
  have hvY := looman_vertical_estimate hAa hbB hCc hcd hdD hCD hK hκ
    hLx hLy hLheight hvcont hFcompact.isClosed hFcompact hFhull hbot htop
    (fun p hp ↦ (hvy p hp).differentiableAt)
    (fun p hp ↦ by rw [(hvy p hp).deriv]; exact hvyK p hp) hvLipX hvLipY
  have huX := looman_horizontal_estimate hAa hab hbB hCc hdD hAB hK hκ
    hLx hLy hLwidth hucont hFcompact.isClosed hFcompact hFhull hleft hright
    (fun p hp ↦ (hux p hp).differentiableAt)
    (fun p hp ↦ by rw [(hux p hp).deriv]; exact huxK p hp) huLipX huLipY
  have hvX := looman_horizontal_estimate hAa hab hbB hCc hdD hAB hK hκ
    hLx hLy hLwidth hvcont hFcompact.isClosed hFcompact hFhull hleft hright
    (fun p hp ↦ (hvx p hp).differentiableAt)
    (fun p hp ↦ by rw [(hvx p hp).deriv]; exact hvxK p hp) hvLipX hvLipY
  let UY := ∫ p in F, deriv (fun y ↦ u (p.1, y)) p.2 ∂(volume.prod volume)
  let VY := ∫ p in F, deriv (fun y ↦ v (p.1, y)) p.2 ∂(volume.prod volume)
  let UX := ∫ p in F, deriv (fun x ↦ u (x, p.2)) p.1 ∂(volume.prod volume)
  let VX := ∫ p in F, deriv (fun x ↦ v (x, p.2)) p.1 ∂(volume.prod volume)
  have hcrY : UY = -VX := by
    rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun hFcompact.isClosed.measurableSet
    intro p hp
    change deriv (fun y ↦ (f (loomanPoint p.1 y)).re) p.2 =
      -deriv (fun x ↦ (f (loomanPoint x p.2)).im) p.1
    rw [(huy p hp).deriv, (hvx p hp).deriv, hcr₂ p hp]
  have hcrX : UX = VY := by
    apply setIntegral_congr_fun hFcompact.isClosed.measurableSet
    intro p hp
    change deriv (fun x ↦ (f (loomanPoint x p.2)).re) p.1 =
      deriv (fun y ↦ (f (loomanPoint p.1 y)).im) p.2
    rw [(hux p hp).deriv, (hvy p hp).deriv, hcr₁ p hp]
  let Vu := ∫ x in Icc a b, u (x, d) - u (x, c)
  let Vv := ∫ x in Icc a b, v (x, d) - v (x, c)
  let Hu := ∫ y in Icc c d, u (b, y) - u (a, y)
  let Hv := ∫ y in Icc c d, v (b, y) - v (a, y)
  have huY' : |Vu - UY| ≤ m := by simpa [Vu, UY, m] using huY
  have hvY' : |Vv - VY| ≤ m := by simpa [Vv, VY, m] using hvY
  have huX' : |Hu - UX| ≤ m := by simpa [Hu, UX, m] using huX
  have hvX' : |Hv - VX| ≤ m := by simpa [Hv, VX, m] using hvX
  have hre : |-Vu - Hv| ≤ m + m := by
    rw [show -Vu - Hv = -(Vu - UY) - (Hv - VX) by rw [hcrY]; ring]
    calc
      |-(Vu - UY) - (Hv - VX)| = |(Vu - UY) + (Hv - VX)| := by
        rw [show -(Vu - UY) - (Hv - VX) = -((Vu - UY) + (Hv - VX)) by ring,
          abs_neg]
      _ ≤ |Vu - UY| + |Hv - VX| := abs_add_le _ _
      _ ≤ m + m := add_le_add huY' hvX'
  have him : |-Vv + Hu| ≤ m + m := by
    rw [show -Vv + Hu = -(Vv - VY) + (Hu - UX) by rw [hcrX]; ring]
    calc
      |-(Vv - VY) + (Hu - UX)| ≤ |-(Vv - VY)| + |Hu - UX| := abs_add_le _ _
      _ = |Vv - VY| + |Hu - UX| := by rw [abs_neg]
      _ ≤ m + m := add_le_add hvY' huX'
  have hhull := looman_rectBoundary_eq_hull hAa hab hbB hCc hcd hdD
    hcont hFhull hhol
  rw [hhull]
  calc
    ‖loomanRectBoundary f a b c d‖ ≤
        |(loomanRectBoundary f a b c d).re| +
          |(loomanRectBoundary f a b c d).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |-Vu - Hv| + |-Vv + Hu| := by
      rw [looman_rectBoundary_re_eq hcont hab hcd,
        looman_rectBoundary_im_eq hcont hab hcd]
    _ ≤ (m + m) + (m + m) := add_le_add hre him
    _ = (4 + 16 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ F) := by
      dsimp [m]
      ring

private def loomanBoxPoint (x y : ℝ) : ℂ := x + y * Complex.I

private def loomanBoundary (f : ℂ → ℂ) (J : Box (Fin 2)) : ℂ :=
  (∫ x in J.lower 0..J.upper 0,
      f (loomanBoxPoint x (J.lower 1)) - f (loomanBoxPoint x (J.upper 1))) +
    Complex.I * ∫ y in J.lower 1..J.upper 1,
      f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)

private noncomputable def loomanBoundary_boxAdditive (f : ℂ → ℂ) (hf : Continuous f)
    (I : Box (Fin 2)) : Fin 2 →ᵇᵃ[I] ℂ := by
  apply BoxAdditiveMap.ofMapSplitAdd (loomanBoundary f) I
  intro J hJI i x hx
  fin_cases i
  · rw [Box.splitLower_def hx, Box.splitUpper_def hx]
    simp only [Option.elim']
    simp only [Fin.zero_eta, Fin.isValue]
    have hh₁ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
          f (loomanBoxPoint t (J.upper 1))) volume (J.lower 0) x :=
      (show Continuous (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
        f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hh₂ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
          f (loomanBoxPoint t (J.upper 1))) volume x (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
        f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₁ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint x y) -
          f (loomanBoxPoint (J.lower 0) y)) volume (J.lower 1) (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint x y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₂ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint x y)) volume (J.lower 1) (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint x y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    calc
      ((∫ t in J.lower 0..x,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
        ((∫ t in x..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) =
        ((∫ t in J.lower 0..x,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          ∫ t in x..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in J.lower 1..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) := by ring
      _ = (∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in J.lower 1..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hh₁ hh₂]
      _ = _ := by
        rw [← intervalIntegral.integral_add hv₁ hv₂]
        congr 2
        apply intervalIntegral.integral_congr
        intro y _
        ring
  · rw [Box.splitLower_def hx, Box.splitUpper_def hx]
    simp only [Option.elim']
    simp only [Fin.mk_one, Fin.isValue]
    have hh₁ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x))
        volume (J.lower 0) (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦
        f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hh₂ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1)))
        volume (J.lower 0) (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦
        f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₁ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint (J.lower 0) y)) volume (J.lower 1) x :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₂ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint (J.lower 0) y)) volume x (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    calc
      ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
          Complex.I * ∫ y in J.lower 1..x,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) +
        ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in x..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) =
          ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
            ∫ t in J.lower 0..J.upper 0,
              f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..x,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in x..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) := by
        ring
      _ = ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
            ∫ t in J.lower 0..J.upper 0,
              f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hv₁ hv₂]
      _ = _ := by
        rw [← intervalIntegral.integral_add hh₁ hh₂]
        congr 2
        funext t
        ring

private theorem looman_boxAdditive_eq_zero
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Box ι} {F : Set (ι → ℝ)} (hF : IsClosed F)
    (g : ι →ᵇᵃ[I] E) {C : ℝ} (hC : 0 ≤ C)
    (r₀ : (ι → ℝ) → Ioi (0 : ℝ))
    (hzero : ∀ x ∈ Box.Icc I, x ∉ F → ∀ J ≤ I,
      Box.Icc J ⊆ closedBall x (r₀ x) → g J = 0)
    (hbound : ∀ J ≤ I, J.distortion ≤ I.distortion → ∀ x ∈ Box.Icc J, x ∈ F →
      ‖g J‖ ≤ C * volume.real ((J : Set (ι → ℝ)) \ F)) :
    g I = 0 := by
  classical
  let q : (ι → ℝ) → ℝ := Fᶜ.indicator (fun _ ↦ 1)
  have hqLeb : IntegrableOn q (I : Set (ι → ℝ)) volume := by
    apply IntegrableOn.indicator
      (integrableOn_const (I.measure_coe_lt_top volume).ne) hF.measurableSet.compl
  have hqBox : BoxIntegral.Integrable I IntegrationParams.GP q
      volume.toBoxAdditive.toSMul :=
    (hqLeb.hasBoxIntegral IntegrationParams.GP rfl).integrable
  have hqIntegral (J : Box ι) (hJI : J ≤ I) :
      BoxIntegral.integral J IntegrationParams.GP q volume.toBoxAdditive.toSMul =
        volume.real ((J : Set (ι → ℝ)) \ F) := by
    rw [(hqLeb.mono_set (Box.coe_subset_coe.2 hJI)).hasBoxIntegral
      IntegrationParams.GP rfl |>.integral_eq]
    simp only [q]
    rw [setIntegral_indicator hF.measurableSet.compl, setIntegral_one_eq_measureReal]
    congr 1
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    let ε' := ε / (C + 1)
    have hC1 : 0 < C + 1 := by linarith
    have hε' : 0 < ε' := div_pos hε hC1
    let c : ℝ≥0 := I.distortion
    let r : (ι → ℝ) → Ioi (0 : ℝ) := fun x ↦
      min (hqBox.convergenceR ε' c x) (r₀ x)
    obtain ⟨π, hπ, hπpart⟩ := IntegrationParams.GP.exists_memBaseSet_isPartition
      I (by exact le_rfl) r
    have hπq : IntegrationParams.GP.MemBaseSet I c
        (hqBox.convergenceR ε' c) π :=
      hπ.mono I le_rfl le_rfl fun _ _ ↦ min_le_left _ _
    let πF := π.filter fun J ↦ π.tag J ∈ F
    have hπFq : IntegrationParams.GP.MemBaseSet I c
        (hqBox.convergenceR ε' c) πF := hπq.filter _
    have hsacks := hqBox.dist_integralSum_sum_integral_le_of_memBaseSet hε' hπFq
    have hsumVol :
        (∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F)) ≤ ε' := by
      have hsum0 : BoxIntegral.integralSum q volume.toBoxAdditive.toSMul πF = 0 := by
        rw [BoxIntegral.integralSum]
        apply sum_eq_zero
        intro J hJ
        have hJ' : J ∈ π.filter (fun J ↦ π.tag J ∈ F) := by
          simpa [πF] using hJ
        have hJF : π.tag J ∈ F := (π.mem_filter.1 hJ').2
        have hq0 : q (πF.tag J) = 0 := by
          change q (π.tag J) = 0
          simp [q, hJF]
        simp [hq0]
      rw [hsum0] at hsacks
      have hint : (∑ J ∈ πF.boxes,
          BoxIntegral.integral J IntegrationParams.GP q volume.toBoxAdditive.toSMul) =
          ∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F) := by
        apply sum_congr rfl
        intro J hJ
        exact hqIntegral J (πF.le_of_mem hJ)
      rw [hint] at hsacks
      rw [dist_zero_left, Real.norm_eq_abs] at hsacks
      exact (le_abs_self _).trans hsacks
    have hnotF (J : Box ι) (hJ : J ∈ π.boxes) (ht : π.tag J ∉ F) : g J = 0 := by
      apply hzero (π.tag J) (π.tag_mem_Icc J) ht J (π.le_of_mem hJ)
      exact (hπ.1 J hJ).trans fun y hy ↦ closedBall_subset_closedBall
        (min_le_right _ _) hy
    have hgI : g I = ∑ J ∈ πF.boxes, g J := by
      have : (∑ J ∈ π.boxes with π.tag J ∉ F, g J) = 0 := by
        apply sum_eq_zero
        intro J hJ
        exact hnotF J (Finset.mem_filter.1 hJ).1 (Finset.mem_filter.1 hJ).2
      calc
        g I = ∑ J ∈ π.boxes, g J := (g.sum_partition_boxes le_rfl hπpart).symm
        _ = (∑ J ∈ π.boxes with π.tag J ∈ F, g J) +
            ∑ J ∈ π.boxes with π.tag J ∉ F, g J :=
          (sum_filter_add_sum_filter_not π.boxes (fun J ↦ π.tag J ∈ F) g).symm
        _ = ∑ J ∈ πF.boxes, g J := by
          rw [this, add_zero]
          rfl
    rw [hgI]
    calc
      ‖∑ J ∈ πF.boxes, g J‖ ≤ ∑ J ∈ πF.boxes, ‖g J‖ := norm_sum_le _ _
      _ ≤ ∑ J ∈ πF.boxes, C * volume.real ((J : Set (ι → ℝ)) \ F) := by
        gcongr with J hJ
        have hJ' : J ∈ π.filter (fun J ↦ π.tag J ∈ F) := by
          simpa [πF] using hJ
        have hJπ : J ∈ π := (π.mem_filter.1 hJ').1
        apply hbound J (π.le_of_mem hJπ)
          ((π.distortion_le_of_mem hJπ).trans (hπ.3 (by change true = true; rfl)))
          (π.tag J)
        · exact hπ.2 (by change true = true; rfl) J hJπ
        · exact (π.mem_filter.1 hJ').2
      _ = C * ∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F) := by
        rw [mul_sum]
      _ ≤ C * ε' := mul_le_mul_of_nonneg_left hsumVol hC
      _ ≤ ε := by
        calc
          C * ε' ≤ (C + 1) * ε' :=
            mul_le_mul_of_nonneg_right (by linarith) hε'.le
          _ = ε := by
            dsimp [ε']
            field_simp
      _ = 0 + ε := (zero_add ε).symm
  · exact norm_nonneg _

private theorem looman_rectBoundary_swap_x (f : ℂ → ℂ) (A B C D : ℝ) :
    loomanRectBoundary f B A C D = -loomanRectBoundary f A B C D := by
  unfold loomanRectBoundary
  rw [intervalIntegral.integral_symm B A]
  have hv : (∫ y in C..D, f (loomanPoint A y) - f (loomanPoint B y)) =
      -∫ y in C..D, f (loomanPoint B y) - f (loomanPoint A y) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [hv]
  ring

private theorem looman_rectBoundary_swap_y (f : ℂ → ℂ) (A B C D : ℝ) :
    loomanRectBoundary f A B D C = -loomanRectBoundary f A B C D := by
  unfold loomanRectBoundary
  rw [intervalIntegral.integral_symm D C]
  have hh : (∫ x in A..B, f (loomanPoint x D) - f (loomanPoint x C)) =
      -∫ x in A..B, f (loomanPoint x C) - f (loomanPoint x D) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [hh]
  ring

private theorem looman_differentiableOn_Ioo_of_rectBoundary_eq_zero
    {f : ℂ → ℂ} {A B C D : ℝ} (hcont : Continuous f)
    (hzero : ∀ a b c d, A < a → a < b → b < B →
      C < c → c < d → d < D → loomanRectBoundary f a b c d = 0) :
    DifferentiableOn ℂ f (Ioo A B ×ℂ Ioo C D) := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    (isOpen_Ioo.reProdIm isOpen_Ioo)).1
  refine ⟨?_, hcont.continuousOn⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hzre : z.re = w.re
  · simp [hzre]
  by_cases hzim : z.im = w.im
  · simp [hzim]
  let a := min z.re w.re
  let b := max z.re w.re
  let c := min z.im w.im
  let d := max z.im w.im
  have hab : a < b := min_lt_max.2 hzre
  have hcd : c < d := min_lt_max.2 hzim
  have hmin : loomanPoint a c ∈ Complex.Rectangle z w := by
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [loomanPoint, a, Set.uIcc],
      by simp [loomanPoint, c, Set.uIcc]⟩
  have hmax : loomanPoint b d ∈ Complex.Rectangle z w := by
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [loomanPoint, b, Set.uIcc],
      by simp [loomanPoint, d, Set.uIcc]⟩
  have hminU := hzw hmin
  have hmaxU := hzw hmax
  have hAa : A < a := by simpa [loomanPoint] using hminU.1.1
  have hbB : b < B := by simpa [loomanPoint] using hmaxU.1.2
  have hCc : C < c := by simpa [loomanPoint] using hminU.2.1
  have hdD : d < D := by simpa [loomanPoint] using hmaxU.2.2
  have h0 := hzero a b c d hAa hab hbB hCc hcd hdD
  have horiented : loomanRectBoundary f z.re w.re z.im w.im = 0 := by
    rcases le_total z.re w.re with hx | hx <;>
      rcases le_total z.im w.im with hy | hy
    · simpa [a, b, c, d, min_eq_left hx, max_eq_right hx,
        min_eq_left hy, max_eq_right hy] using h0
    · have h0' : loomanRectBoundary f z.re w.re w.im z.im = 0 := by
        simpa [a, b, c, d, min_eq_left hx, max_eq_right hx,
          min_eq_right hy, max_eq_left hy] using h0
      rw [looman_rectBoundary_swap_y]
      simpa using congrArg Neg.neg h0'
    · have h0' : loomanRectBoundary f w.re z.re z.im w.im = 0 := by
        simpa [a, b, c, d, min_eq_right hx, max_eq_left hx,
          min_eq_left hy, max_eq_right hy] using h0
      rw [looman_rectBoundary_swap_x]
      simpa using congrArg Neg.neg h0'
    · have h0' : loomanRectBoundary f w.re z.re w.im z.im = 0 := by
        simpa [a, b, c, d, min_eq_right hx, max_eq_left hx,
          min_eq_right hy, max_eq_left hy] using h0
      rw [looman_rectBoundary_swap_x, looman_rectBoundary_swap_y]
      simpa using h0'
  have hh₁ : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x z.im)) volume z.re w.re :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x z.im)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x w.im)) volume z.re w.re :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x w.im)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint w.re y)) volume z.im w.im :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint w.re y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint z.re y)) volume z.im w.im :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint z.re y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  rw [loomanRectBoundary, intervalIntegral.integral_sub hh₁ hh₂,
    intervalIntegral.integral_sub hv₁ hv₂] at horiented
  simp only [loomanPoint] at horiented
  simp only [smul_eq_mul]
  linear_combination horiented

private def loomanHolomorphicNeighborhood (s : Set ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ t, IsOpen t ∧ z ∈ t ∧ t ⊆ s ∧ DifferentiableOn ℂ f t}

private theorem looman_isOpen_holomorphicNeighborhood {s : Set ℂ} {f : ℂ → ℂ} :
    IsOpen (loomanHolomorphicNeighborhood s f) := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨t, ht, hzt, hts, hdiff⟩
  exact ⟨t, fun w hw ↦ ⟨t, ht, hw, hts, hdiff⟩, ht, hzt⟩

private theorem looman_differentiableAt_of_mem_holomorphicNeighborhood
    {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ loomanHolomorphicNeighborhood s f) : DifferentiableAt ℂ f z := by
  rcases hz with ⟨t, ht, hzt, -, hdiff⟩
  exact (hdiff z hzt).differentiableAt (ht.mem_nhds hzt)

private theorem looman_abs_deriv_re_le_of_norm_sub_le {g : ℝ → ℂ} {a K : ℝ}
    (hg : HasDerivAt (fun t ↦ (g t).re) a 0) (hK : 0 ≤ K)
    (hlip : ∀ᶠ t in nhds 0, ‖g t - g 0‖ ≤ K * ‖t‖) : |a| ≤ K := by
  rw [← Real.norm_eq_abs]
  apply hg.le_of_lip' hK
  filter_upwards [hlip] with t ht
  calc
    ‖(g t).re - (g 0).re‖ = |(g t - g 0).re| := by simp [Real.norm_eq_abs]
    _ ≤ ‖g t - g 0‖ := Complex.abs_re_le_norm _
    _ ≤ K * ‖t - 0‖ := by simpa using ht

private theorem looman_abs_deriv_im_le_of_norm_sub_le {g : ℝ → ℂ} {a K : ℝ}
    (hg : HasDerivAt (fun t ↦ (g t).im) a 0) (hK : 0 ≤ K)
    (hlip : ∀ᶠ t in nhds 0, ‖g t - g 0‖ ≤ K * ‖t‖) : |a| ≤ K := by
  rw [← Real.norm_eq_abs]
  apply hg.le_of_lip' hK
  filter_upwards [hlip] with t ht
  calc
    ‖(g t).im - (g 0).im‖ = |(g t - g 0).im| := by simp [Real.norm_eq_abs]
    _ ≤ ‖g t - g 0‖ := Complex.abs_im_le_norm _
    _ ≤ K * ‖t - 0‖ := by simpa using ht

private def loomanCoordPoint (p : Fin 2 → ℝ) : ℂ :=
  loomanPoint (p 0) (p 1)

private def loomanRectBox (A B C D : ℝ) (hAB : A < B) (hCD : C < D) :
    Box (Fin 2) where
  lower := ![A, C]
  upper := ![B, D]
  lower_lt_upper i := by fin_cases i <;> simp [hAB, hCD]

private theorem looman_rectBox_Icc (A B C D : ℝ) (hAB : A < B) (hCD : C < D) :
    Box.Icc (loomanRectBox A B C D hAB hCD) =
      {p | p 0 ∈ Icc A B ∧ p 1 ∈ Icc C D} := by
  ext p
  simp only [Box.Icc_def, Set.mem_Icc]
  constructor <;> rintro ⟨h₀, h₁⟩
  · exact ⟨⟨h₀ 0, h₁ 0⟩, h₀ 1, h₁ 1⟩
  · exact ⟨fun i ↦ by fin_cases i <;> simp_all [loomanRectBox],
      fun i ↦ by fin_cases i <;> simp_all [loomanRectBox]⟩

private theorem looman_rectBox_boundary (f : ℂ → ℂ) (A B C D : ℝ)
    (hAB : A < B) (hCD : C < D) :
    loomanBoundary f (loomanRectBox A B C D hAB hCD) =
      loomanRectBoundary f A B C D := by
  rfl

private theorem looman_dist_point_le (x y : ℝ) (z : ℂ) :
    dist (loomanPoint x y) z ≤ |x - z.re| + |y - z.im| := by
  rw [dist_eq_norm]
  have hsub : loomanPoint x y - z =
      (x - z.re : ℂ) + (y - z.im : ℂ) * Complex.I := by
    change (x : ℂ) + (y : ℂ) * Complex.I - z = _
    apply Complex.ext <;> simp
  rw [hsub]
  have hxnorm : ‖(x : ℂ) - (z.re : ℂ)‖ = |x - z.re| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hynorm : ‖(y : ℂ) - (z.im : ℂ)‖ = |y - z.im| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖(x - z.re : ℂ) + (y - z.im : ℂ) * Complex.I‖ ≤
        ‖(x - z.re : ℂ)‖ + ‖(y - z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |x - z.re| + |y - z.im| := by
      rw [hxnorm, norm_mul, Complex.norm_I, mul_one, hynorm]

private theorem looman_exists_baire_square {s C : Set ℂ} {P : C → Prop}
    (hs : IsOpen s) (hCs : C ⊆ s) {w : C}
    (hw : w ∈ interior {z : C | P z}) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∃ δ > 0,
      (∀ x y : ℝ, |x - (w : ℂ).re| ≤ 2 * δ → |y - (w : ℂ).im| ≤ 2 * δ →
        loomanPoint x y ∈ s) ∧
      (∀ z : C, |(z : ℂ).re - (w : ℂ).re| ≤ δ →
        |(z : ℂ).im - (w : ℂ).im| ≤ δ → P z) ∧
      2 * δ < r / (n + 1) := by
  obtain ⟨εP, hεP, hballP⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
  obtain ⟨εs, hεs, hballs⟩ := Metric.isOpen_iff.1 hs (w : ℂ) (hCs w.property)
  let m := min εP (min εs (r / (n + 1)))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min hεP (lt_min hεs (div_pos hr (by positivity)))
  refine ⟨m / 8, by positivity, ?_, ?_, ?_⟩
  · intro x y hx hy
    apply hballs
    have hd := looman_dist_point_le x y (w : ℂ)
    calc
      dist (loomanPoint x y) (w : ℂ) ≤
          |x - (w : ℂ).re| + |y - (w : ℂ).im| := hd
      _ ≤ 4 * (m / 8) := by linarith
      _ < εs := by
        have hmle : m ≤ εs := le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
  · intro z hx hy
    apply interior_subset (hballP ?_)
    have hd := looman_dist_point_le (z : ℂ).re (z : ℂ).im (w : ℂ)
    rw [show loomanPoint (z : ℂ).re (z : ℂ).im = (z : ℂ) by
      exact Complex.re_add_im (z : ℂ)] at hd
    calc
      dist z w ≤ |(z : ℂ).re - (w : ℂ).re| +
          |(z : ℂ).im - (w : ℂ).im| := hd
      _ ≤ 2 * (m / 8) := by linarith
      _ < εP := by
        have hmle : m ≤ εP := min_le_left _ _
        linarith
  · have hmle : m ≤ r / (n + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith

private theorem looman_exists_continuous_extension {K : Set ℂ} (hK : IsClosed K)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) :
    ∃ fe : ℂ → ℂ, Continuous fe ∧ EqOn fe f K := by
  let fK : C(K, ℂ) :=
    ⟨fun z ↦ f z, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨fe, hfe⟩ := fK.exists_restrict_eq hK
  refine ⟨fe, fe.continuous, ?_⟩
  intro z hz
  have h := DFunLike.congr_fun hfe ⟨z, hz⟩
  exact h

set_option maxHeartbeats 1000000 in
-- The Baire and tagged-partition argument needs a larger elaboration budget.
/-- **Looman–Menchoff theorem.** Let $s \subseteq \mathbb{C}$ be open and let
$f : \mathbb{C} \to \mathbb{C}$ be continuous on $s$. Write $u = \operatorname{Re} f$ and
$v = \operatorname{Im} f$ as functions of $z = x + iy$, and suppose that at every $z \in s$ the
partial derivatives $u_x(z)$, $u_y(z)$, $v_x(z)$, $v_y(z)$ exist and satisfy the Cauchy–Riemann
equations $u_x(z) = v_y(z)$ and $u_y(z) = -v_x(z)$. Then $f$ is complex differentiable on $s$.

Proof: Baire category gives a square with uniform axis-wise Lipschitz bounds on the
exceptional set. A Goursat rectangle estimate and Morera's theorem eliminate that set.

Proves `Wanted` entry `looman_menchoff`.

Source: https://en.wikipedia.org/wiki/Looman%E2%80%93Menchoff_theorem
(statement id `looman-menchoff-s1`, canonical name "Looman-Menchoff theorem").
-/
theorem looman_menchoff : ∀ {s : Set ℂ} {f : ℂ → ℂ} {ux uy vx vy : ℂ → ℝ},
    IsOpen s →
    ContinuousOn f s →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).re) (ux z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).re) (uy z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).im) (vx z) 0) →
    (∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).im) (vy z) 0) →
    (∀ z ∈ s, ux z = vy z) →
    (∀ z ∈ s, uy z = -(vx z)) →
    DifferentiableOn ℂ f s := by
  intro s f ux uy vx vy hs hf hux huy hvx hvy hcr₁ hcr₂ z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  by_contra hz₀diff
  let H := loomanHolomorphicNeighborhood s f
  have hHopen : IsOpen H := looman_isOpen_holomorphicNeighborhood
  have hz₀H : z₀ ∉ H := fun hzH ↦
    hz₀diff (looman_differentiableAt_of_mem_holomorphicNeighborhood hzH)
  obtain ⟨R, hR, hballR⟩ := Metric.isOpen_iff.1 hs z₀ hz₀
  let ρ := R / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have h2ρR : 2 * ρ < R := by dsimp [ρ]; linarith
  let B := ball z₀ ρ
  let E := B ∩ Hᶜ
  have hBopen : IsOpen B := isOpen_ball
  have hEclosedPart : IsClosed Hᶜ := hHopen.isClosed_compl
  have hElc : IsLocallyClosed E := by
    exact hBopen.isLocallyClosed.inter hEclosedPart.isLocallyClosed
  let _ : LocallyCompactSpace E := hElc.locallyCompactSpace
  let _ : BaireSpace E := inferInstance
  have hEne : E.Nonempty := ⟨z₀, by exact ⟨mem_ball_self hρ, hz₀H⟩⟩
  have hBs : B ⊆ s := by
    intro z hz
    apply hballR
    exact hz.trans hρR
  have hEs : E ⊆ s := by
    intro z hz
    exact hBs hz.1
  have hshift : ∀ (n : ℕ) (z : ℂ), z ∈ E → ∀ h : ℝ,
      ‖h‖ < ρ / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s := by
    intro n z hz h hh
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hhρ : ‖h‖ < ρ := hh.trans_le (div_le_self hρ.le (by linarith))
    have hzρ : dist z z₀ < ρ := by simpa [B] using hz.1
    constructor <;> apply hballR
    · calc
        dist (z + (h : ℂ)) z₀ ≤ dist (z + (h : ℂ)) z + dist z z₀ :=
          dist_triangle _ _ _
        _ = ‖h‖ + dist z z₀ := by rw [dist_eq_norm]; simp
        _ < 2 * ρ := by linarith
        _ < R := h2ρR
    · calc
        dist (z + (h : ℂ) * Complex.I) z₀ ≤
            dist (z + (h : ℂ) * Complex.I) z + dist z z₀ := dist_triangle _ _ _
        _ = ‖h‖ + dist z z₀ := by rw [dist_eq_norm]; simp
        _ < 2 * ρ := by linarith
        _ < R := h2ρR
  obtain ⟨n, hn⟩ := looman_baire_boundedAt hf hEne hEs hshift
    (fun z hz ↦ ⟨ux z + vx z * Complex.I,
      hasDerivAt_complex_of_re_im (hux z (hEs hz)) (hvx z (hEs hz))⟩)
    (fun z hz ↦ ⟨uy z + vy z * Complex.I,
      hasDerivAt_complex_of_re_im (huy z (hEs hz)) (hvy z (hEs hz))⟩)
  rcases hn with ⟨w, hw⟩
  obtain ⟨δ, hδ, houterB, hinnerBounded, hside⟩ :=
    looman_exists_baire_square hBopen inter_subset_left hw hρ n
  let K : Set ℂ := Icc ((w : ℂ).re - 2 * δ) ((w : ℂ).re + 2 * δ) ×ℂ
    Icc ((w : ℂ).im - 2 * δ) ((w : ℂ).im + 2 * δ)
  have hKclosed : IsClosed K := isClosed_Icc.reProdIm isClosed_Icc
  have hKs : K ⊆ s := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    apply hBs
    have hzB := houterB z.re z.im (by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2]) (by
      rw [abs_le]
      constructor <;> linarith [hz.2.1, hz.2.2])
    simpa only [loomanPoint, Complex.re_add_im] using hzB
  obtain ⟨fe, hfecont, hfe⟩ :=
    looman_exists_continuous_extension hKclosed (hf.mono hKs)
  let A := (w : ℂ).re - δ
  let B₁ := (w : ℂ).re + δ
  let C := (w : ℂ).im - δ
  let D := (w : ℂ).im + δ
  have hAB : A < B₁ := by dsimp [A, B₁]; linarith
  have hCD : C < D := by dsimp [C, D]; linarith
  let I := loomanRectBox A B₁ C D hAB hCD
  let F : Set (Fin 2 → ℝ) := loomanCoordPoint ⁻¹' Hᶜ
  have hFclosed : IsClosed F := hHopen.isClosed_compl.preimage (by
    unfold loomanCoordPoint loomanPoint
    fun_prop)
  have hfe_eq_nhds {z : ℂ} (hzre : z.re ∈ Icc A B₁) (hzim : z.im ∈ Icc C D) :
      fe =ᶠ[nhds z] f := by
    have hzopen : z ∈ Ioo ((w : ℂ).re - 2 * δ) ((w : ℂ).re + 2 * δ) ×ℂ
        Ioo ((w : ℂ).im - 2 * δ) ((w : ℂ).im + 2 * δ) := by
      rw [Complex.mem_reProdIm]
      dsimp [A, B₁, C, D] at hzre hzim
      constructor <;> constructor <;> linarith [hzre.1, hzre.2, hzim.1, hzim.2]
    filter_upwards [((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hzopen)] with y hy
    apply hfe
    rw [Complex.mem_reProdIm] at hy ⊢
    exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2.1.le, hy.2.2.le⟩
  have hr_exists (x : Fin 2 → ℝ) : ∃ r > 0,
      x ∈ Box.Icc I → x ∉ F →
        ∀ y ∈ closedBall x r, DifferentiableAt ℂ f (loomanCoordPoint y) := by
    by_cases hx : x ∈ Box.Icc I ∧ x ∉ F
    · have hxH : loomanCoordPoint x ∈ H := by simpa [F] using hx.2
      rcases hxH with ⟨t, htopen, hxt, -, hdifft⟩
      have hpreopen : IsOpen (loomanCoordPoint ⁻¹' t) := htopen.preimage (by
        unfold loomanCoordPoint loomanPoint
        fun_prop)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpreopen x hxt
      refine ⟨r / 2, by positivity, fun _ _ y hy ↦ ?_⟩
      apply (hdifft (loomanCoordPoint y) ?_).differentiableAt
        (htopen.mem_nhds ?_)
      · apply hball
        rw [mem_ball]
        exact (mem_closedBall.1 hy).trans_lt (by linarith)
      · apply hball
        rw [mem_ball]
        exact (mem_closedBall.1 hy).trans_lt (by linarith)
    · refine ⟨1, zero_lt_one, fun hxI hxF ↦ ?_⟩
      exact (hx ⟨hxI, hxF⟩).elim
  choose r₀ hr₀ hdiff_r₀ using hr_exists
  let gauge : (Fin 2 → ℝ) → Ioi (0 : ℝ) := fun x ↦ ⟨r₀ x, hr₀ x⟩
  have hbox (J : Box (Fin 2)) (hJI : J ≤ I) : loomanBoundary fe J = 0 := by
    let g := loomanBoundary_boxAdditive fe hfecont J
    have hCnonneg : 0 ≤ (4 + 16 * (J.distortion : ℝ)) * (n + 1) := by positivity
    have hg : g J = 0 := looman_boxAdditive_eq_zero hFclosed g hCnonneg gauge (by
      intro x hxJ hxF L hLJ hLball
      change loomanBoundary fe L = 0
      change loomanRectBoundary fe (L.lower 0) (L.upper 0) (L.lower 1) (L.upper 1) = 0
      apply looman_rectBoundary_eq_zero_of_differentiableOn
        (L.lower_lt_upper 0).le (L.lower_lt_upper 1).le hfecont
      intro a ha b hb
      let y : Fin 2 → ℝ := ![a, b]
      have hyL : y ∈ Box.Icc L := by
        rw [Box.Icc_def]
        exact ⟨fun i ↦ by fin_cases i <;> simp [y, ha.1.le, hb.1.le],
          fun i ↦ by fin_cases i <;> simp [y, ha.2.le, hb.2.le]⟩
      have hyI : y ∈ Box.Icc I := Box.le_iff_Icc.1 (hLJ.trans hJI) hyL
      have hycoords : y 0 ∈ Icc A B₁ ∧ y 1 ∈ Icc C D := by
        simpa [I, looman_rectBox_Icc] using hyI
      have hfdiff : DifferentiableAt ℂ f (loomanCoordPoint y) :=
        hdiff_r₀ x (Box.le_iff_Icc.1 hJI hxJ) hxF y (hLball hyL)
      have hyre : (loomanCoordPoint y).re = y 0 := by
        unfold loomanCoordPoint loomanPoint
        simp
      have hyim : (loomanCoordPoint y).im = y 1 := by
        unfold loomanCoordPoint loomanPoint
        simp
      have heq : fe =ᶠ[nhds (loomanCoordPoint y)] f := hfe_eq_nhds
        (by rw [hyre]; exact hycoords.1) (by rw [hyim]; exact hycoords.2)
      simpa [loomanCoordPoint, loomanPoint, y] using
        hfdiff.congr_of_eventuallyEq heq) (by
      intro L hLJ hdist x hxL hxF
      let toVec : ℝ × ℝ → Fin 2 → ℝ := fun p ↦ ![p.1, p.2]
      let rect : Set (ℝ × ℝ) :=
        Icc (L.lower 0) (L.upper 0) ×ˢ Icc (L.lower 1) (L.upper 1)
      let bad : Set (ℝ × ℝ) := toVec ⁻¹' F
      let FL : Set (ℝ × ℝ) := rect ∩ bad
      have hbadclosed : IsClosed bad := hFclosed.preimage (by
        unfold toVec
        fun_prop)
      have hrectcompact : IsCompact rect := isCompact_Icc.prod isCompact_Icc
      have hFLcompact : IsCompact FL := hrectcompact.inter_right hbadclosed
      have hxvec : toVec (x 0, x 1) = x := by
        funext i
        fin_cases i <;> rfl
      have hxrect : (x 0, x 1) ∈ rect := by
        change x 0 ∈ Icc (L.lower 0) (L.upper 0) ∧
          x 1 ∈ Icc (L.lower 1) (L.upper 1)
        rw [Box.Icc_def] at hxL
        exact ⟨⟨hxL.1 0, hxL.2 0⟩, hxL.1 1, hxL.2 1⟩
      have hFLne : FL.Nonempty := ⟨(x 0, x 1), hxrect, by
        change toVec (x 0, x 1) ∈ F
        rwa [hxvec]⟩
      have hFLsub : FL ⊆ rect := inter_subset_left
      have hbounded (p : ℝ × ℝ) (hp : p ∈ FL) :
          loomanBoundedAt f ρ n (loomanPoint p.1 p.2) := by
        have hqL : toVec p ∈ Box.Icc L := by
          rw [Box.Icc_def]
          constructor
          · intro i
            fin_cases i
            · exact hp.1.1.1
            · exact hp.1.2.1
          · intro i
            fin_cases i
            · exact hp.1.1.2
            · exact hp.1.2.2
        have hqI : toVec p ∈ Box.Icc I :=
          Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hqcoords : toVec p 0 ∈ Icc A B₁ ∧ toVec p 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        have hpH : loomanPoint p.1 p.2 ∉ H := by
          have : toVec p ∈ F := hp.2
          simpa [F, loomanCoordPoint, loomanPoint, toVec] using this
        have hpabsx : |p.1 - (w : ℂ).re| ≤ δ := by
          have hlo := hqcoords.1.1
          have hhi := hqcoords.1.2
          dsimp [A, B₁, toVec] at hlo hhi
          rw [abs_le]
          constructor <;> linarith
        have hpabsy : |p.2 - (w : ℂ).im| ≤ δ := by
          have hlo := hqcoords.2.1
          have hhi := hqcoords.2.2
          dsimp [C, D, toVec] at hlo hhi
          rw [abs_le]
          constructor <;> linarith
        have hpB : loomanPoint p.1 p.2 ∈ B := houterB p.1 p.2
          (hpabsx.trans (by linarith)) (hpabsy.trans (by linarith))
        apply hinnerBounded ⟨loomanPoint p.1 p.2, hpB, hpH⟩
        · simpa [loomanPoint] using hpabsx
        · simpa [loomanPoint] using hpabsy
      have hLx : L.upper 0 - L.lower 0 ≤ dist L.lower L.upper := by
        have hd := dist_le_pi_dist L.lower L.upper 0
        calc
          L.upper 0 - L.lower 0 = |L.lower 0 - L.upper 0| := by
            rw [abs_of_neg (sub_neg.mpr (L.lower_lt_upper 0))]
            ring
          _ ≤ dist L.lower L.upper := by simpa [Real.dist_eq] using hd
      have hLy : L.upper 1 - L.lower 1 ≤ dist L.lower L.upper := by
        have hd := dist_le_pi_dist L.lower L.upper 1
        calc
          L.upper 1 - L.lower 1 = |L.lower 1 - L.upper 1| := by
            rw [abs_of_neg (sub_neg.mpr (L.lower_lt_upper 1))]
            ring
          _ ≤ dist L.lower L.upper := by simpa [Real.dist_eq] using hd
      have hLheight : dist L.lower L.upper ≤
          (J.distortion : ℝ) * (L.upper 1 - L.lower 1) := by
        calc
          dist L.lower L.upper ≤
              (L.distortion : ℝ) * (L.upper 1 - L.lower 1) :=
            L.dist_le_distortion_mul 1
          _ ≤ (J.distortion : ℝ) * (L.upper 1 - L.lower 1) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hdist
            · exact sub_nonneg.mpr (L.lower_lt_upper 1).le
      have hLwidth : dist L.lower L.upper ≤
          (J.distortion : ℝ) * (L.upper 0 - L.lower 0) := by
        calc
          dist L.lower L.upper ≤
              (L.distortion : ℝ) * (L.upper 0 - L.lower 0) :=
            L.dist_le_distortion_mul 0
          _ ≤ (J.distortion : ℝ) * (L.upper 0 - L.lower 0) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hdist
            · exact sub_nonneg.mpr (L.lower_lt_upper 0).le
      have hhol : ∀ a ∈ Ioo (L.lower 0) (L.upper 0),
          ∀ b ∈ Ioo (L.lower 1) (L.upper 1), (a, b) ∉ FL →
            DifferentiableAt ℂ fe (loomanPoint a b) := by
        intro a ha b hb hpFL
        let q : Fin 2 → ℝ := ![a, b]
        have hqL : q ∈ Box.Icc L := by
          rw [Box.Icc_def]
          exact ⟨fun i ↦ by fin_cases i <;> simp [q, ha.1.le, hb.1.le],
            fun i ↦ by fin_cases i <;> simp [q, ha.2.le, hb.2.le]⟩
        have hqI : q ∈ Box.Icc I := Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hqcoords : q 0 ∈ Icc A B₁ ∧ q 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        have hnotF : q ∉ F := by
          intro hqF
          apply hpFL
          exact ⟨⟨⟨ha.1.le, ha.2.le⟩, hb.1.le, hb.2.le⟩, hqF⟩
        have hpointH : loomanPoint a b ∈ H := by
          simpa [F, loomanCoordPoint, loomanPoint, q] using hnotF
        have hfdiff :=
          looman_differentiableAt_of_mem_holomorphicNeighborhood hpointH
        have heq : fe =ᶠ[nhds (loomanPoint a b)] f := hfe_eq_nhds
          (by
            rw [show (loomanPoint a b).re = a by unfold loomanPoint; simp]
            simpa [q] using hqcoords.1)
          (by
            rw [show (loomanPoint a b).im = b by unfold loomanPoint; simp]
            simpa [q] using hqcoords.2)
        exact hfdiff.congr_of_eventuallyEq heq
      have hmain (p : ℝ × ℝ) (hp : p ∈ FL) :
          p.1 ∈ Icc A B₁ ∧ p.2 ∈ Icc C D := by
        have hqL : toVec p ∈ Box.Icc L := by
          rw [Box.Icc_def]
          constructor
          · intro i
            fin_cases i
            · exact hp.1.1.1
            · exact hp.1.2.1
          · intro i
            fin_cases i
            · exact hp.1.1.2
            · exact hp.1.2.2
        have hqI := Box.le_iff_Icc.1 (hLJ.trans hJI) hqL
        have hcoords : toVec p 0 ∈ Icc A B₁ ∧ toVec p 1 ∈ Icc C D := by
          simpa [I, looman_rectBox_Icc] using hqI
        simpa [toVec] using hcoords
      have hpointS (p : ℝ × ℝ) (hp : p ∈ FL) : loomanPoint p.1 p.2 ∈ s := by
        have hm := hmain p hp
        apply hBs
        apply houterB p.1 p.2
        · rw [abs_le]
          dsimp [A, B₁] at hm
          constructor <;> linarith [hm.1.1, hm.1.2]
        · rw [abs_le]
          dsimp [C, D] at hm
          constructor <;> linarith [hm.2.1, hm.2.2]
      have heqpoint (p : ℝ × ℝ) (hp : p ∈ FL) :
          fe =ᶠ[nhds (loomanPoint p.1 p.2)] f := by
        have hm := hmain p hp
        apply hfe_eq_nhds
        · rw [show (loomanPoint p.1 p.2).re = p.1 by unfold loomanPoint; simp]
          exact hm.1
        · rw [show (loomanPoint p.1 p.2).im = p.2 by unfold loomanPoint; simp]
          exact hm.2
      have transfer_x (p : ℝ × ℝ) (hp : p ∈ FL) (c : ℂ → ℝ) (a : ℝ)
          (hbase₀ : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ)))) a 0) :
          HasDerivAt (fun x ↦ c (fe (loomanPoint x p.2))) a p.1 := by
        have houter : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ))))
            a (p.1 - p.1) := by
          simpa using hbase₀
        have hinner : HasDerivAt (fun x : ℝ ↦ x - p.1) 1 p.1 := by
          simpa only [id_eq] using (hasDerivAt_id p.1).sub_const p.1
        have hbase := houter.comp (h := fun x : ℝ ↦ x - p.1) p.1 hinner
        have hfline : HasDerivAt (fun x ↦ c (f (loomanPoint x p.2))) a p.1 := by
          convert hbase using 1
          · funext x
            congr 2
            unfold loomanPoint
            push_cast
            ring
          · simp
        have heqline : (fun x ↦ c (fe (loomanPoint x p.2))) =ᶠ[nhds p.1]
            fun x ↦ c (f (loomanPoint x p.2)) := by
          have htend : Tendsto (fun x : ℝ ↦ loomanPoint x p.2) (nhds p.1)
              (nhds (loomanPoint p.1 p.2)) := by
            apply Continuous.continuousAt
            unfold loomanPoint
            fun_prop
          filter_upwards [(heqpoint p hp).comp_tendsto htend] with x hx
          exact congrArg c hx
        exact hfline.congr_of_eventuallyEq heqline
      have transfer_y (p : ℝ × ℝ) (hp : p ∈ FL) (c : ℂ → ℝ) (a : ℝ)
          (hbase₀ : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I))) a 0) :
          HasDerivAt (fun y ↦ c (fe (loomanPoint p.1 y))) a p.2 := by
        have houter : HasDerivAt
            (fun t : ℝ ↦ c (f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I)))
            a (p.2 - p.2) := by
          simpa using hbase₀
        have hinner : HasDerivAt (fun y : ℝ ↦ y - p.2) 1 p.2 := by
          simpa only [id_eq] using (hasDerivAt_id p.2).sub_const p.2
        have hbase := houter.comp (h := fun y : ℝ ↦ y - p.2) p.2 hinner
        have hfline : HasDerivAt (fun y ↦ c (f (loomanPoint p.1 y))) a p.2 := by
          convert hbase using 1
          · funext y
            congr 2
            unfold loomanPoint
            push_cast
            ring
          · simp
        have heqline : (fun y ↦ c (fe (loomanPoint p.1 y))) =ᶠ[nhds p.2]
            fun y ↦ c (f (loomanPoint p.1 y)) := by
          have htend : Tendsto (fun y : ℝ ↦ loomanPoint p.1 y) (nhds p.2)
              (nhds (loomanPoint p.1 p.2)) := by
            apply Continuous.continuousAt
            unfold loomanPoint
            fun_prop
          filter_upwards [(heqpoint p hp).comp_tendsto htend] with y hy
          exact congrArg c hy
        exact hfline.congr_of_eventuallyEq heqline
      have hux_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun x ↦ (fe (loomanPoint x p.2)).re)
            (ux (loomanPoint p.1 p.2)) p.1 :=
        transfer_x p hp Complex.re (ux (loomanPoint p.1 p.2))
          (hux (loomanPoint p.1 p.2) (hpointS p hp))
      have huy_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun y ↦ (fe (loomanPoint p.1 y)).re)
            (uy (loomanPoint p.1 p.2)) p.2 :=
        transfer_y p hp Complex.re (uy (loomanPoint p.1 p.2))
          (huy (loomanPoint p.1 p.2) (hpointS p hp))
      have hvx_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun x ↦ (fe (loomanPoint x p.2)).im)
            (vx (loomanPoint p.1 p.2)) p.1 :=
        transfer_x p hp Complex.im (vx (loomanPoint p.1 p.2))
          (hvx (loomanPoint p.1 p.2) (hpointS p hp))
      have hvy_fe (p : ℝ × ℝ) (hp : p ∈ FL) :
          HasDerivAt (fun y ↦ (fe (loomanPoint p.1 y)).im)
            (vy (loomanPoint p.1 p.2)) p.2 :=
        transfer_y p hp Complex.im (vy (loomanPoint p.1 p.2))
          (hvy (loomanPoint p.1 p.2) (hpointS p hp))
      have hKpos : 0 < ρ / (n + 1) := div_pos hρ (by positivity)
      have hlipx (p : ℝ × ℝ) (hp : p ∈ FL) :
          ∀ᶠ (t : ℝ) in nhds 0,
            ‖f (loomanPoint p.1 p.2 + (t : ℂ)) -
                f (loomanPoint p.1 p.2 + (0 : ℂ))‖ ≤ (n + 1) * ‖t‖ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hKpos] with t ht
        simpa using (hbounded p hp t (by simpa [Real.dist_eq] using ht)).1
      have hlipy (p : ℝ × ℝ) (hp : p ∈ FL) :
          ∀ᶠ (t : ℝ) in nhds 0,
            ‖f (loomanPoint p.1 p.2 + (t : ℂ) * Complex.I) -
                f (loomanPoint p.1 p.2 + (0 : ℂ) * Complex.I)‖ ≤
              (n + 1) * ‖t‖ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hKpos] with t ht
        simpa using (hbounded p hp t (by simpa [Real.dist_eq] using ht)).2
      have huxK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |ux (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_re_le_of_norm_sub_le
          (hux (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipx p hp)
      have huyK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |uy (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_re_le_of_norm_sub_le
          (huy (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipy p hp)
      have hvxK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |vx (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_im_le_of_norm_sub_le
          (hvx (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipx p hp)
      have hvyK (p : ℝ × ℝ) (hp : p ∈ FL) :
          |vy (loomanPoint p.1 p.2)| ≤ (n : ℝ) + 1 :=
        looman_abs_deriv_im_le_of_norm_sub_le
          (hvy (loomanPoint p.1 p.2) (hpointS p hp)) (by positivity) (hlipy p hp)
      have hLIbounds := Box.le_iff_bounds.1 (hLJ.trans hJI)
      have hLipX (p : ℝ × ℝ) (hp : p ∈ FL) (a : ℝ)
          (ha : a ∈ Icc (L.lower 0) (L.upper 0)) :
          ‖fe (loomanPoint a p.2) - fe (loomanPoint p.1 p.2)‖ ≤
            (n + 1) * |a - p.1| := by
        have hpmain := hmain p hp
        have hamain : a ∈ Icc A B₁ := by
          constructor
          · calc
              A = I.lower 0 := by rfl
              _ ≤ L.lower 0 := hLIbounds.1 0
              _ ≤ a := ha.1
          · calc
              a ≤ L.upper 0 := ha.2
              _ ≤ I.upper 0 := hLIbounds.2 0
              _ = B₁ := by rfl
        have hsmall : ‖a - p.1‖ < ρ / (n + 1) := by
          have habs : |a - p.1| ≤ 2 * δ := by
            rw [abs_le]
            dsimp [A, B₁] at hamain hpmain
            constructor <;> linarith [hamain.1, hamain.2, hpmain.1.1, hpmain.1.2]
          simpa [Real.norm_eq_abs] using habs.trans_lt hside
        have hb := (hbounded p hp (a - p.1) hsmall).1
        have hfea : fe (loomanPoint a p.2) = f (loomanPoint a p.2) :=
          (hfe_eq_nhds
            (by
              rw [show (loomanPoint a p.2).re = a by unfold loomanPoint; simp]
              exact hamain)
            (by
              rw [show (loomanPoint a p.2).im = p.2 by unfold loomanPoint; simp]
              exact hpmain.2)).self_of_nhds
        have hfep : fe (loomanPoint p.1 p.2) = f (loomanPoint p.1 p.2) :=
          (heqpoint p hp).self_of_nhds
        rw [hfea, hfep]
        have hadd : loomanPoint p.1 p.2 + ((a - p.1 : ℝ) : ℂ) =
            loomanPoint a p.2 := by
          unfold loomanPoint
          push_cast
          ring
        simpa only [hadd, add_zero, Real.norm_eq_abs] using hb
      have hLipY (p : ℝ × ℝ) (hp : p ∈ FL) (b : ℝ)
          (hbmem : b ∈ Icc (L.lower 1) (L.upper 1)) :
          ‖fe (loomanPoint p.1 b) - fe (loomanPoint p.1 p.2)‖ ≤
            (n + 1) * |b - p.2| := by
        have hpmain := hmain p hp
        have hbmain : b ∈ Icc C D := by
          constructor
          · calc
              C = I.lower 1 := by rfl
              _ ≤ L.lower 1 := hLIbounds.1 1
              _ ≤ b := hbmem.1
          · calc
              b ≤ L.upper 1 := hbmem.2
              _ ≤ I.upper 1 := hLIbounds.2 1
              _ = D := by rfl
        have hsmall : ‖b - p.2‖ < ρ / (n + 1) := by
          have habs : |b - p.2| ≤ 2 * δ := by
            rw [abs_le]
            dsimp [C, D] at hbmain hpmain
            constructor <;> linarith [hbmain.1, hbmain.2, hpmain.2.1, hpmain.2.2]
          simpa [Real.norm_eq_abs] using habs.trans_lt hside
        have hb := (hbounded p hp (b - p.2) hsmall).2
        have hfeb : fe (loomanPoint p.1 b) = f (loomanPoint p.1 b) :=
          (hfe_eq_nhds
            (by
              rw [show (loomanPoint p.1 b).re = p.1 by unfold loomanPoint; simp]
              exact hpmain.1)
            (by
              rw [show (loomanPoint p.1 b).im = b by unfold loomanPoint; simp]
              exact hbmain)).self_of_nhds
        have hfep : fe (loomanPoint p.1 p.2) = f (loomanPoint p.1 p.2) :=
          (heqpoint p hp).self_of_nhds
        rw [hfeb, hfep]
        have hadd : loomanPoint p.1 p.2 + ((b - p.2 : ℝ) : ℂ) * Complex.I =
            loomanPoint p.1 b := by
          unfold loomanPoint
          push_cast
          ring
        simpa only [hadd, sub_self, Complex.ofReal_zero, zero_mul, add_zero,
          Real.norm_eq_abs] using hb
      have hestimate := looman_rectBoundary_norm_le
        (f := fe) (F := FL)
        (A := L.lower 0) (B := L.upper 0) (C := L.lower 1) (D := L.upper 1)
        (K := (n : ℝ) + 1) (L := dist L.lower L.upper)
        (κ := (J.distortion : ℝ))
        (ux := fun p ↦ ux (loomanPoint p.1 p.2))
        (uy := fun p ↦ uy (loomanPoint p.1 p.2))
        (vx := fun p ↦ vx (loomanPoint p.1 p.2))
        (vy := fun p ↦ vy (loomanPoint p.1 p.2))
        (L.lower_lt_upper 0) (L.lower_lt_upper 1) (by positivity) (by positivity)
        hLx hLy hLheight hLwidth hfecont hFLcompact hFLne hFLsub hhol
        hux_fe huy_fe hvx_fe hvy_fe huxK huyK hvxK hvyK
        (fun p hp ↦ hcr₁ (loomanPoint p.1 p.2) (hpointS p hp))
        (fun p hp ↦ hcr₂ (loomanPoint p.1 p.2) (hpointS p hp))
        hLipX hLipY
      have hpre : MeasurableEquiv.finTwoArrow ⁻¹' (rect \ FL) =
          Box.Icc L \ F := by
        ext q
        have hvec : toVec (q 0, q 1) = q := by
          funext i
          fin_cases i <;> rfl
        have hrect_iff : (q 0, q 1) ∈ rect ↔ q ∈ Box.Icc L := by
          rw [Box.Icc_def]
          change (q 0 ∈ Icc (L.lower 0) (L.upper 0) ∧
            q 1 ∈ Icc (L.lower 1) (L.upper 1)) ↔ _
          constructor
          · rintro ⟨h₀, h₁⟩
            exact ⟨fun i ↦ by fin_cases i <;> simp_all,
              fun i ↦ by fin_cases i <;> simp_all⟩
          · rintro ⟨hl, hu⟩
            exact ⟨⟨hl 0, hu 0⟩, hl 1, hu 1⟩
        have hbad_iff : (q 0, q 1) ∈ bad ↔ q ∈ F := by
          change toVec (q 0, q 1) ∈ F ↔ q ∈ F
          rw [hvec]
        change ((q 0, q 1) ∈ rect ∧ (q 0, q 1) ∉ FL) ↔
          q ∈ Box.Icc L ∧ q ∉ F
        rw [hrect_iff]
        simp only [FL, mem_inter_iff, not_and, hbad_iff]
        tauto
      have htargetMeas : MeasurableSet (rect \ FL) :=
        hrectcompact.isClosed.measurableSet.diff hFLcompact.isClosed.measurableSet
      have hmeasureClosed : volume (Box.Icc L \ F) =
          (volume.prod volume) (rect \ FL) := by
        have hm := (volume_preserving_finTwoArrow ℝ).measure_preimage
          htargetMeas.nullMeasurableSet
        rwa [hpre] at hm
      have hmeasureCoe : volume ((L : Set (Fin 2 → ℝ)) \ F) =
          volume (Box.Icc L \ F) := by
        apply measure_congr
        filter_upwards [Box.coe_ae_eq_Icc (I := L)] with q hq
        simp only [Set.mem_sdiff, hq]
      have hmeasureReal : (volume.prod volume).real (rect \ FL) =
          volume.real ((L : Set (Fin 2 → ℝ)) \ F) := by
        exact congrArg ENNReal.toReal (hmeasureClosed.symm.trans hmeasureCoe.symm)
      change ‖loomanBoundary fe L‖ ≤
        ((4 + 16 * (J.distortion : ℝ)) * (n + 1)) *
          volume.real ((L : Set (Fin 2 → ℝ)) \ F)
      change ‖loomanRectBoundary fe (L.lower 0) (L.upper 0)
        (L.lower 1) (L.upper 1)‖ ≤ _
      rw [← hmeasureReal]
      simpa [rect, mul_assoc] using hestimate)
    exact hg
  have hrectzero : ∀ a b c d, A < a → a < b → b < B₁ →
      C < c → c < d → d < D → loomanRectBoundary fe a b c d = 0 := by
    intro a b c d hAa hab hbB hCc hcd hdD
    let J := loomanRectBox a b c d hab hcd
    have hJI : J ≤ I := by
      rw [Box.le_iff_bounds]
      constructor
      · intro i
        fin_cases i
        · exact hAa.le
        · exact hCc.le
      · intro i
        fin_cases i
        · exact hbB.le
        · exact hdD.le
    have h := hbox J hJI
    simpa [J, looman_rectBox_boundary] using h
  let U : Set ℂ := Ioo A B₁ ×ℂ Ioo C D
  have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hfediff : DifferentiableOn ℂ fe U :=
    looman_differentiableOn_Ioo_of_rectBoundary_eq_zero hfecont hrectzero
  have hUs : U ⊆ s := by
    intro z hz
    apply hKs
    rw [Complex.mem_reProdIm] at hz ⊢
    dsimp [A, B₁, C, D] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfdiff : DifferentiableOn ℂ f U := by
    intro z hz
    have hzat : DifferentiableAt ℂ fe z :=
      (hfediff z hz).differentiableAt (hUopen.mem_nhds hz)
    rw [Complex.mem_reProdIm] at hz
    have heq : fe =ᶠ[nhds z] f := hfe_eq_nhds ⟨hz.1.1.le, hz.1.2.le⟩
      ⟨hz.2.1.le, hz.2.2.le⟩
    exact (hzat.congr_of_eventuallyEq heq.symm).differentiableWithinAt
  have hwU : (w : ℂ) ∈ U := by
    rw [Complex.mem_reProdIm]
    dsimp [A, B₁, C, D]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hwH : (w : ℂ) ∈ H := ⟨U, hUopen, hwU, hUs, hfdiff⟩
  exact w.property.2 hwH

end

end MetaMathlibExt
