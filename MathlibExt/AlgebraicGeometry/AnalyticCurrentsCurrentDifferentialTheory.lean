/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticCurrents

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Distributional differentiation of currents

The exterior derivative satisfies a bound for the chart derivative seminorms.
This bound gives `currentDifferentialTheory`: on a compact complex manifold
modelled on `Coordinates n` and carrying an `ExteriorTheory`, the differential
of a current is again a current.

Reference: J.-P. Demailly and M. Păun, *Numerical characterization of the
Kähler cone of a compact Kähler manifold*, Ann. of Math. 159 (2004),
arXiv:math/0105176v2, Theorem 0.4 (Theorem 0.5 of the published version).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticCurrentsWanted

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals AnalyticCurrents
open scoped Manifold ContDiff Topology

private theorem local_estimate (n q j : ℕ)
    (f : Coordinates n → Coordinates n [⋀^Fin q]→L[ℝ] ℝ) (z : Coordinates n)
    (hf : ContDiffAt ℝ ∞ f z) :
    ‖iteratedFDeriv ℝ j (extDeriv f) z‖ ≤
      (q + 1 : ℝ) * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
  let L := ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := q) ℝ (Coordinates n) ℝ
  change ‖iteratedFDeriv ℝ j (L ∘ fderiv ℝ f) z‖ ≤ _
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ f) z := hf.fderiv_right (by simp)
  apply (L.norm_iteratedFDeriv_comp_left hdf (by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_right
    (ContinuousAlternatingMap.norm_alternatizeUncurryFinCLM_le (n := q))
    (norm_nonneg _)

private theorem chart_domain_open (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] (a : M) :
    IsOpen (chartDomain ℝ (Coordinates n) M ⊤ a) := by
  simpa [chartDomain] using isOpen_extChartAt_target (I := 𝓘(ℝ, Coordinates n)) a

private theorem seminorm_bddAbove (n p : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] (alpha : Forms n M p) (a : M)
    (K : Set (Coordinates n)) (hK : IsCompact K)
    (hsub : K ⊆ chartDomain ℝ (Coordinates n) M ⊤ a) (m : ℕ) :
    BddAbove {r : ℝ | ∃ (j : ℕ), j ≤ m ∧ ∃ z ∈ K,
      r = ‖iteratedFDeriv ℝ j (chartForm ℝ (Coordinates n) M alpha.val a) z‖} := by
  have hc (j : ℕ) : ContinuousOn
      (fun z ↦ ‖iteratedFDeriv ℝ j (chartForm ℝ (Coordinates n) M alpha.val a) z‖) K := by
    have hdom := chart_domain_open n M a
    have h := (alpha.property a).continuousOn_iteratedFDerivWithin (m := j)
      (by simp) hdom.uniqueDiffOn
    have h' : ContinuousOn (iteratedFDeriv ℝ j
        (chartForm ℝ (Coordinates n) M alpha.val a))
        (chartDomain ℝ (Coordinates n) M ⊤ a) :=
      h.congr (fun z hz ↦ (iteratedFDerivWithin_of_isOpen j hdom hz).symm)
    exact h'.norm.mono hsub
  induction m with
  | zero =>
    have h := hK.bddAbove_image (hc 0)
    apply h.mono
    rintro r ⟨j, hj, z, hz, rfl⟩
    have hj' : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact ⟨z, hz, rfl⟩
  | succ m ih =>
    have h := bddAbove_union.mpr ⟨ih, hK.bddAbove_image (hc (m + 1))⟩
    apply h.mono
    rintro r ⟨j, hj, z, hz, rfl⟩
    by_cases hjm : j ≤ m
    · exact Or.inl ⟨j, hjm, z, hz, rfl⟩
    · have hj' : j = m + 1 := by omega
      subst j
      exact Or.inr ⟨z, hz, rfl⟩

private theorem chart_transition_derivative (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] (a b : M) (z : Coordinates n)
    (hza : z ∈ (extChartAt 𝓘(ℝ, Coordinates n) a).target)
    (hzb : (extChartAt 𝓘(ℝ, Coordinates n) a).symm z ∈
      (extChartAt 𝓘(ℝ, Coordinates n) b).source) :
    fderiv ℝ ((extChartAt 𝓘(ℝ, Coordinates n) b) ∘
      (extChartAt 𝓘(ℝ, Coordinates n) a).symm) z =
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) b) ((extChartAt 𝓘(ℝ, Coordinates n) a).symm z)).comp
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z) := by
  have ha := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Coordinates n)) (n := ∞) a).contMDiffAt
    (extChartAt_target_mem_nhds' hza)
  have hb := contMDiffAt_extChartAt' (I := 𝓘(ℝ, Coordinates n)) (n := ∞)
    (by simpa using hzb)
  have hd := mfderiv_comp z (hb.mdifferentiableAt (by simp))
    (ha.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  ext1 v
  exact congrArg (fun L ↦ L v) hd

open scoped Classical in
private theorem chart_form_transition (n q : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    (alpha : GlobalForms ℝ (Coordinates n) M q) (a b : M) (z : Coordinates n)
    (hza : z ∈ (extChartAt 𝓘(ℝ, Coordinates n) a).target)
    (hzb : (extChartAt 𝓘(ℝ, Coordinates n) a).symm z ∈
      (extChartAt 𝓘(ℝ, Coordinates n) b).source) :
    chartForm ℝ (Coordinates n) M alpha.val a =ᶠ[𝓝 z]
      fun w ↦ (chartForm ℝ (Coordinates n) M alpha.val b
        ((extChartAt 𝓘(ℝ, Coordinates n) b)
          ((extChartAt 𝓘(ℝ, Coordinates n) a).symm w))).compContinuousLinearMap
        (fderiv ℝ ((extChartAt 𝓘(ℝ, Coordinates n) b) ∘
          (extChartAt 𝓘(ℝ, Coordinates n) a).symm) w) := by
  have hn : (extChartAt 𝓘(ℝ, Coordinates n) a).symm ⁻¹'
      (extChartAt 𝓘(ℝ, Coordinates n) b).source ∈ 𝓝 z :=
    (continuousAt_extChartAt_symm'' hza).preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds hzb)
  filter_upwards [extChartAt_target_mem_nhds' hza, hn] with w hwa hwb
  have hwa' : w ∈ chartDomain ℝ (Coordinates n) M ⊤ a := by
    simpa [chartDomain] using hwa
  have hwb' : (extChartAt 𝓘(ℝ, Coordinates n) b)
      ((extChartAt 𝓘(ℝ, Coordinates n) a).symm w) ∈
      chartDomain ℝ (Coordinates n) M ⊤ b := by
    simpa [chartDomain] using (extChartAt 𝓘(ℝ, Coordinates n) b).map_source hwb
  have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓘(ℝ, Coordinates n)) hwb
  simp only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] at hinv
  have hcomp :
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) b).symm
        ((extChartAt 𝓘(ℝ, Coordinates n) b)
          ((extChartAt 𝓘(ℝ, Coordinates n) a).symm w))).comp
        (fderiv ℝ ((extChartAt 𝓘(ℝ, Coordinates n) b) ∘
          (extChartAt 𝓘(ℝ, Coordinates n) a).symm) w) =
      mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm w := by
    have hd := chart_transition_derivative n M a b w hwa hwb
    have h := congrArg (fun L : Coordinates n →L[ℝ] Coordinates n ↦
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) b).symm
        ((extChartAt 𝓘(ℝ, Coordinates n) b)
          ((extChartAt 𝓘(ℝ, Coordinates n) a).symm w))).comp L) hd
    refine h.trans ?_
    ext1 v
    exact congrArg (fun L ↦ L ((mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm w) v)) hinv
  ext1 v
  simp only [chartForm, dite_eq_left hwa', dite_eq_left hwb',
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [(extChartAt 𝓘(ℝ, Coordinates n) b).left_inv hwb]
  exact congrArg (alpha.val ⟨(extChartAt 𝓘(ℝ, Coordinates n) a).symm w, by trivial⟩)
    (congrArg (fun L : Coordinates n →L[ℝ] Coordinates n ↦ L ∘ v) hcomp.symm)

private theorem chart_derivative (n q : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M]
    (alpha : GlobalForms ℝ (Coordinates n) M q) (a : M) (z : Coordinates n)
    (hz : z ∈ chartDomain ℝ (Coordinates n) M ⊤ a) :
    chartForm ℝ (Coordinates n) M (d ℝ (Coordinates n) M q alpha).val a z =
      extDeriv (chartForm ℝ (Coordinates n) M alpha.val a) z := by
  have hza : z ∈ (extChartAt 𝓘(ℝ, Coordinates n) a).target := hz.1
  let x := (extChartAt 𝓘(ℝ, Coordinates n) a).symm z
  have hx : (extChartAt 𝓘(ℝ, Coordinates n) x x) ∈
      chartDomain ℝ (Coordinates n) M ⊤ x := by
    simp [chartDomain]
  have hxb : x ∈ (extChartAt 𝓘(ℝ, Coordinates n) x).source := mem_extChartAt_source x
  have htrans := chart_form_transition n q M alpha a x z hza hxb
  have ha := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Coordinates n)) (n := ∞) a).contMDiffAt
    (extChartAt_target_mem_nhds' hza)
  have hb := contMDiffAt_extChartAt (I := 𝓘(ℝ, Coordinates n)) (n := ∞) (x := x)
  have hf : ContDiffAt ℝ ∞ ((extChartAt 𝓘(ℝ, Coordinates n) x) ∘
      (extChartAt 𝓘(ℝ, Coordinates n) a).symm) z :=
    (hb.comp z ha).contDiffAt
  have hdom : IsOpen (chartDomain ℝ (Coordinates n) M ⊤ x) := by
    simpa [chartDomain] using isOpen_extChartAt_target (I := 𝓘(ℝ, Coordinates n)) x
  have halpha := (alpha.property x).contDiffAt (hdom.mem_nhds hx)
  have hpull := extDeriv_pullback
    (f := (extChartAt 𝓘(ℝ, Coordinates n) x) ∘ (extChartAt 𝓘(ℝ, Coordinates n) a).symm)
    (x := z) (halpha.differentiableAt (by simp)) hf (by simp)
  have he := htrans.extDeriv_eq.trans hpull
  have hdf : fderiv ℝ ((extChartAt 𝓘(ℝ, Coordinates n) x) ∘
      (extChartAt 𝓘(ℝ, Coordinates n) a).symm) z =
      mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z := by
    have h := chart_transition_derivative n M a x z hza hxb
    ext1 v
    exact (congrArg (fun L ↦ L v) h).trans
      (congrArg (fun L ↦ L ((mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z) v))
        (mfderiv_extChartAt_self (I := 𝓘(ℝ, Coordinates n)) (x := x)))
  rw [hdf] at he
  rw [he]
  simp only [chartForm, dite_eq_left hz]
  change ((extDerivWithin (chartForm ℝ (Coordinates n) M alpha.val x)
    (chartDomain ℝ (Coordinates n) M ⊤ x)
    (extChartAt 𝓘(ℝ, Coordinates n) x x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
      (extChartAt 𝓘(ℝ, Coordinates n) x) x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z) = _
  have hloc : extDerivWithin (chartForm ℝ (Coordinates n) M alpha.val x)
      (chartDomain ℝ (Coordinates n) M ⊤ x) (extChartAt 𝓘(ℝ, Coordinates n) x x) =
      extDeriv (chartForm ℝ (Coordinates n) M alpha.val x)
        (extChartAt 𝓘(ℝ, Coordinates n) x x) :=
    congrArg ContinuousAlternatingMap.alternatizeUncurryFin
      (fderivWithin_of_isOpen hdom hx)
  rw [hloc]
  ext1 v
  apply congrArg (extDeriv (chartForm ℝ (Coordinates n) M alpha.val x)
    (extChartAt 𝓘(ℝ, Coordinates n) x x))
  funext i
  exact congrArg (fun L ↦ L ((mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
    (extChartAt 𝓘(ℝ, Coordinates n) a).symm z) (v i)))
    (mfderiv_extChartAt_self (I := 𝓘(ℝ, Coordinates n)) (x := x))

private theorem seminorm_derivative (n q : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] (alpha : Forms n M q) (a : M)
    (K : Set (Coordinates n)) (hK : IsCompact K)
    (hsub : K ⊆ chartDomain ℝ (Coordinates n) M ⊤ a) (m : ℕ) :
    derivativeSeminorm n M (q + 1) a K m (d ℝ (Coordinates n) M q alpha) ≤
      (q + 1 : ℝ) * derivativeSeminorm n M q a K (m + 1) alpha := by
  classical
  by_cases h : K.Nonempty
  · obtain ⟨z₀, hz₀⟩ := h
    apply csSup_le (show {r : ℝ | ∃ (j : ℕ), j ≤ m ∧ ∃ z ∈ K,
      r = ‖iteratedFDeriv ℝ j (chartForm ℝ (Coordinates n) M
        (d ℝ (Coordinates n) M q alpha).val a) z‖}.Nonempty from
      ⟨_, 0, Nat.zero_le m, z₀, hz₀, rfl⟩)
    rintro r ⟨j, hj, z, hz, rfl⟩
    have hdom := chart_domain_open n M a
    have heq : chartForm ℝ (Coordinates n) M (d ℝ (Coordinates n) M q alpha).val a
        =ᶠ[𝓝 z] extDeriv (chartForm ℝ (Coordinates n) M alpha.val a) :=
      Filter.eventuallyEq_of_mem (hdom.mem_nhds (hsub hz))
        (fun w hw ↦ chart_derivative n q M alpha a w hw)
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    have hf := (alpha.property a).contDiffAt (hdom.mem_nhds (hsub hz))
    apply (local_estimate n q j _ z hf).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_csSup (seminorm_bddAbove n q M alpha a K hK hsub (m + 1))
      ⟨j + 1, Nat.add_le_add_right hj 1, z, hz, rfl⟩
  · have hk : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [derivativeSeminorm, hk, Real.sSup_empty]

private theorem seminorm_cast (n p q : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M]
    (h : p = q) (alpha : Forms n M p) (a : M) (K : Set (Coordinates n)) (m : ℕ) :
    derivativeSeminorm n M q a K m (castFormLinear n M h alpha) =
      derivativeSeminorm n M p a K m alpha := by
  cases h
  rfl

/-- The distributional differential of a current is again a current: the
exterior derivative is continuous for the chart seminorms. -/
public theorem currentDifferentialTheory (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] :
    CurrentDifferentialTheory n M := by
  classical
  constructor
  intro p T hp
  obtain ⟨r, a, K, m, C, hC, hK, hT⟩ := T.bounded
  let q := n * 2 - (p + 1)
  have hq : q + 1 = n * 2 - p := by dsimp [q]; omega
  refine ⟨r, a, K, m + 1, C * (q + 1), mul_nonneg hC (by positivity), hK, ?_⟩
  intro alpha
  change |(-1 : ℝ) ^ (p + 1) *
    T.functional (castFormLinear n M hq (d ℝ (Coordinates n) M q alpha))| ≤ _
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hs (i : Fin r) :
      derivativeSeminorm n M (n * 2 - p) (a i) (K i) m
        (castFormLinear n M hq (d ℝ (Coordinates n) M q alpha)) ≤
      (q + 1 : ℝ) * derivativeSeminorm n M q (a i) (K i) (m + 1) alpha := by
    rw [seminorm_cast]
    exact seminorm_derivative n q M alpha (a i) (K i) (hK i).1 (hK i).2 m
  calc
    |T.functional (castFormLinear n M hq (d ℝ (Coordinates n) M q alpha))| ≤
        C * ∑ i, derivativeSeminorm n M (n * 2 - p) (a i) (K i) m
          (castFormLinear n M hq (d ℝ (Coordinates n) M q alpha)) := hT _
    _ ≤ C * ∑ i, (q + 1 : ℝ) * derivativeSeminorm n M q (a i) (K i) (m + 1) alpha :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hs i)) hC
    _ = (C * (q + 1)) * ∑ i, derivativeSeminorm n M q (a i) (K i) (m + 1) alpha := by
      rw [← Finset.mul_sum, mul_assoc]

end WantedExt.AlgebraicGeometry.AnalyticCurrentsWanted
