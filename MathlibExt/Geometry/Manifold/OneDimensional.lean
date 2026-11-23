/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import MathlibExt.Geometry.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

section LocalDiffeomorphConstructors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- Constructor for a `PartialDiffeomorph` from inverse data on open sets. -/
private theorem odm_exists_partialDiffeomorph_of_invOn
    (f : M → N) (f' : N → M) (U : Set M) (V : Set N)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : Set.MapsTo f U V) (hf' : Set.MapsTo f' V U)
    (h : Set.InvOn f' f U V)
    (hfD : ContMDiffOn I J n f U) (hf'D : ContMDiffOn J I n f' V) :
    ∃ Φ : PartialDiffeomorph I J M N n, Φ.source = U ∧ Φ.target = V ∧
      (⇑Φ : M → N) = f ∧ Set.EqOn ⇑Φ.symm f' V := by
  refine ⟨PartialDiffeomorph.mk
    { toFun := f, invFun := f', source := U, target := V,
      map_source' := hf, map_target' := hf', left_inv' := h.1, right_inv' := h.2 }
    hU hV hfD hf'D, rfl, rfl, rfl, ?_⟩
  intro y _
  rfl

/-- A map with a smooth two-sided inverse on open sets is a local diffeomorphism. -/
private theorem odm_isLocalDiffeomorphAt_of_invOn
    (f : M → N) (f' : N → M) (U : Set M) (V : Set N)
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : Set.MapsTo f U V) (hf' : Set.MapsTo f' V U)
    (h : Set.InvOn f' f U V)
    (hfD : ContMDiffOn I J n f U) (hf'D : ContMDiffOn J I n f' V)
    (x : M) (hx : x ∈ U) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Φ, hsrc, _, hfu, _⟩ :=
    odm_exists_partialDiffeomorph_of_invOn f f' U V hU hV hf hf' h hfD hf'D
  have hx' : x ∈ Φ.source := by rw [hsrc]; exact hx
  rw [← hfu]
  exact PartialDiffeomorph.isLocalDiffeomorphAt I J n Φ hx'

/-- Local diffeomorphism is preserved under changing the map near the point.
Proved via the double local inverse: the local inverse of the local inverse is a
smooth twin of the original map, so the new map inherits smooth inverse data. -/
private theorem odm_isLocalDiffeomorphAt_congr_of_eventuallyEq
    {f f₂ : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (h : f₂ =ᶠ[nhds x] f) :
    IsLocalDiffeomorphAt I J n f₂ x := by
  set g : N → M := ⇑hf.localInverse with hgdef
  have hg : IsLocalDiffeomorphAt J I n g (f x) := hf.localInverse_isLocalDiffeomorphAt
  set g₂ : M → N := ⇑hg.localInverse with hg₂def
  have e1 : g ∘ f =ᶠ[nhds x] id := hf.localInverse_eventuallyEq_left
  have e2 : g₂ ∘ g =ᶠ[nhds (f x)] id := hg.localInverse_eventuallyEq_left
  have hcont : ContinuousAt f x := hf.contMDiffAt.continuousAt
  have key : g₂ =ᶠ[nhds x] f := by
    have A : g₂ ∘ (g ∘ f) =ᶠ[nhds x] g₂ ∘ id :=
      e1.mono fun z hz => congrArg g₂ hz
    have B : (g₂ ∘ g) ∘ f =ᶠ[nhds x] id ∘ f := hcont.eventually e2
    have A' : (g₂ ∘ g) ∘ f =ᶠ[nhds x] g₂ := by
      rw [← Function.comp_assoc, Function.comp_id] at A
      exact A
    have B' : (g₂ ∘ g) ∘ f =ᶠ[nhds x] f := by simpa using B
    exact A'.symm.trans B'
  have hfg : f₂ =ᶠ[nhds x] g₂ := h.trans key.symm
  have hUmem : { z | f₂ z = g₂ z } ∈ nhds x := hfg
  obtain ⟨U₀, hU₀sub, hU₀open, hU₀x⟩ := mem_nhds_iff.mp hUmem
  have hxg₂ : x ∈ hg.localInverse.source := by
    have h1 : g (f x) ∈ hg.localInverse.source := hg.localInverse_mem_source
    have h2 : g (f x) = x :=
      hf.localInverse_left_inv hf.localInverse_mem_target
    rwa [h2] at h1
  set W : Set M := U₀ ∩ hg.localInverse.source with hWdef
  have hxW : x ∈ W := ⟨hU₀x, hxg₂⟩
  have hWopen : IsOpen W := hU₀open.inter hg.localInverse.open_source
  have hWsub : W ⊆ hg.localInverse.source := Set.inter_subset_right
  have heqW : Set.EqOn f₂ g₂ W := fun z hz => hU₀sub hz.1
  have hf₂D : ContMDiffOn I J n f₂ W :=
    (hg.localInverse.contMDiffOn_toFun.mono hWsub).congr (fun z hz => heqW hz)
  set V : Set N :=
    hg.localInverse.symm.source ∩ ⇑hg.localInverse.symm ⁻¹' W with hVdef
  have hVopen : IsOpen V :=
    hg.localInverse.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      hg.localInverse.symm.open_source hWopen
  have hVsub : V ⊆ hg.localInverse.target := fun w hw => hw.1
  have hVL : Set.MapsTo f₂ W V := by
    intro z hz
    have hzT : hg.localInverse z ∈ hg.localInverse.target :=
      hg.localInverse.toPartialEquiv.map_source (hWsub hz)
    have hzeq : f₂ z = hg.localInverse z := heqW hz
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact hzT
    · change hg.localInverse.symm (f₂ z) ∈ W
      have hleft : hg.localInverse.symm (hg.localInverse z) = z :=
        hg.localInverse.toPartialEquiv.left_inv (hWsub hz)
      rw [hzeq]
      rw [hleft]
      exact hz
  have hVR : Set.MapsTo hg.localInverse.symm V W := fun w hw => hw.2
  have hInv : Set.InvOn hg.localInverse.symm f₂ W V := by
    constructor
    · intro z hz
      show hg.localInverse.symm (f₂ z) = z
      have hzeq : f₂ z = hg.localInverse z := heqW hz
      rw [hzeq]
      exact hg.localInverse.toPartialEquiv.left_inv (hWsub hz)
    · intro w hw
      have hwW : hg.localInverse.symm w ∈ W := hw.2
      calc f₂ (hg.localInverse.symm w) = hg.localInverse (hg.localInverse.symm w) :=
            heqW hwW
        _ = w := hg.localInverse.toPartialEquiv.right_inv (hVsub hw)
  have hf'D : ContMDiffOn J I n hg.localInverse.symm V :=
    hg.localInverse.symm.contMDiffOn_toFun.mono (fun w hw => hw.1)
  exact odm_isLocalDiffeomorphAt_of_invOn f₂ hg.localInverse.symm W V hWopen hVopen
    hVL hVR hInv hf₂D hf'D x hxW

end LocalDiffeomorphConstructors

section IntervalParametrisation

/-- Every nonempty open connected subset of `ℝ` is the range of a smooth map with
everywhere positive derivative. -/
private theorem odm_exists_contDiff_deriv_pos_range_eq
    (D : Set ℝ) (hDopen : IsOpen D) (hDconn : D.OrdConnected) (hDne : D.Nonempty) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t, 0 < deriv φ t) ∧ Set.range φ = D := by
  have hpre : IsPreconnected D := hDconn.isPreconnected
  have hex_lt : ∀ a : ℝ, a ∈ D → ∃ q ∈ D, q < a := by
    intro a ha
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds ha)
    refine ⟨a - ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (a - ε / 2) - a = -(ε / 2) := by ring
    rw [he, norm_neg, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  have hex_gt : ∀ b : ℝ, b ∈ D → ∃ q ∈ D, b < q := by
    intro b hb
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds hb)
    refine ⟨b + ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have he : (b + ε / 2) - b = ε / 2 := by ring
    rw [he, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  set a : ℝ := sInf D with ha
  set b : ℝ := sSup D with hb
  rcases hpre.mem_intervals with h | h | h | h | h | h | h | h | h | h
  · -- D = Icc: left endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a ≤ b :=
      (Set.mem_Icc.mp hx).1.trans (Set.mem_Icc.mp hx).2
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Icc.mpr ⟨le_rfl, hab⟩
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Icc.mp hqD).1 (not_le.mpr hqa)
  · -- D = Ico: left endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      (Set.mem_Ico.mp hx).1.trans_lt (Set.mem_Ico.mp hx).2
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Ico.mpr ⟨le_rfl, hab⟩
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Ico.mp hqD).1 (not_le.mpr hqa)
  · -- D = Ioc: right endpoint contradicts openness.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      (Set.mem_Ioc.mp hx).1.trans_le (Set.mem_Ioc.mp hx).2
    have hbD : b ∈ D := by
      rw [h]
      exact Set.mem_Ioc.mpr ⟨hab, le_rfl⟩
    obtain ⟨q, hqD, hqb⟩ := hex_gt _ hbD
    rw [h] at hqD
    exact absurd (Set.mem_Ioc.mp hqD).2 (not_le.mpr hqb)
  · -- D = Ioo: arctan parametrisation.
    rw [← ha, ← hb] at h
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    have hab : a < b :=
      lt_trans (Set.mem_Ioo.mp hx).1 (Set.mem_Ioo.mp hx).2
    set k : ℝ := (b - a) / Real.pi with hk
    have hkpos : 0 < k := by
      rw [hk]
      exact div_pos (by linarith) Real.pi_pos
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hk2 : k * (Real.pi / 2) = (b - a) / 2 := by
      rw [hk]
      field_simp
    refine ⟨fun t => (a + b) / 2 + k * Real.arctan t, ?_, ?_, ?_⟩
    · exact contDiff_const.add (contDiff_const.mul Real.contDiff_arctan)
    · intro t
      have hder : deriv (fun t => (a + b) / 2 + k * Real.arctan t) t
          = k * (1 / (1 + t ^ 2)) :=
        (((Real.hasDerivAt_arctan t).const_mul k).const_add _).deriv
      rw [hder]
      exact mul_pos hkpos (by positivity)
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        have hart : Real.arctan t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          rw [← Real.range_arctan]
          exact Set.mem_range_self t
        rw [Set.mem_Ioo] at hart ⊢
        have lo := mul_lt_mul_of_pos_left hart.1 hkpos
        have hi := mul_lt_mul_of_pos_left hart.2 hkpos
        constructor <;> nlinarith [hk2]
      · intro hy
        rw [Set.mem_Ioo] at hy
        have hs : (y - (a + b) / 2) / k ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          rw [Set.mem_Ioo]
          constructor
          · rw [lt_div_iff₀ hkpos]
            nlinarith [hy.1, hk2]
          · rw [div_lt_iff₀ hkpos]
            nlinarith [hy.2, hk2]
        rw [← Real.range_arctan] at hs
        obtain ⟨t, ht⟩ := hs
        refine ⟨t, ?_⟩
        have hkne : k ≠ 0 := hkpos.ne'
        change (a + b) / 2 + k * Real.arctan t = y
        rw [ht]
        field_simp
        ring
  · -- D = Ici: left endpoint contradicts openness.
    rw [← ha] at h
    have haD : a ∈ D := by
      rw [h]
      exact Set.mem_Ici.mpr le_rfl
    obtain ⟨q, hqD, hqa⟩ := hex_lt _ haD
    rw [h] at hqD
    exact absurd (Set.mem_Ici.mp hqD) (not_le.mpr hqa)
  · -- D = Ioi: exp parametrisation.
    rw [← ha] at h
    refine ⟨fun t => a + Real.exp t, contDiff_const.add Real.contDiff_exp, ?_, ?_⟩
    · intro t
      have hder : deriv (fun t => a + Real.exp t) t = Real.exp t :=
        ((Real.hasDerivAt_exp t).const_add a).deriv
      rw [hder]
      exact Real.exp_pos t
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        refine Set.mem_Ioi.mpr ?_
        change a < a + Real.exp t
        have hpos := Real.exp_pos t
        linarith
      · intro hy
        rw [Set.mem_Ioi] at hy
        have hmem : y - a ∈ Set.range Real.exp := by
          rw [Real.range_exp]
          exact Set.mem_Ioi.mpr (by linarith)
        obtain ⟨t, ht⟩ := hmem
        refine ⟨t, ?_⟩
        change a + Real.exp t = y
        rw [ht]
        ring
  · -- D = Iic: right endpoint contradicts openness.
    rw [← hb] at h
    have hbD : b ∈ D := by
      rw [h]
      exact Set.mem_Iic.mpr le_rfl
    obtain ⟨q, hqD, hqb⟩ := hex_gt _ hbD
    rw [h] at hqD
    exact absurd (Set.mem_Iic.mp hqD) (not_le.mpr hqb)
  · -- D = Iio: reflected exp parametrisation.
    rw [← hb] at h
    refine ⟨fun t => b - Real.exp (-t),
      contDiff_const.sub (Real.contDiff_exp.comp contDiff_id.neg), ?_, ?_⟩
    · intro t
      have h1 : HasDerivAt (fun t : ℝ => -t) (-1) t := (hasDerivAt_id t).neg
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * -1) t :=
        h1.exp
      have h3 := h2.const_sub b
      have hder : deriv (fun t => b - Real.exp (-t)) t = Real.exp (-t) := by
        have hderiv := h3.deriv
        simpa using hderiv
      rw [hder]
      exact Real.exp_pos _
    · rw [h]
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        refine Set.mem_Iio.mpr ?_
        change b - Real.exp (-t) < b
        have hpos := Real.exp_pos (-t)
        linarith
      · intro hy
        rw [Set.mem_Iio] at hy
        have hpos : (0 : ℝ) < b - y := by linarith
        refine ⟨-(Real.log (b - y)), ?_⟩
        have hexp : Real.exp (-(-(Real.log (b - y)))) = b - y := by
          rw [neg_neg, Real.exp_log hpos]
        change b - Real.exp (-(-(Real.log (b - y)))) = y
        rw [hexp]
        ring
  · -- D = univ: identity.
    rw [h]
    exact ⟨id, contDiff_id,
      fun t => by rw [(hasDerivAt_id t).deriv]; exact one_pos, Set.range_id⟩
  · -- D = ∅ contradicts nonemptiness.
    obtain ⟨x, hx⟩ := hDne
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)

end IntervalParametrisation

section InverseFunction1D

/-- One-dimensional inverse function theorem as a `PartialDiffeomorph`: a smooth map
with everywhere positive derivative on an open connected set is a diffeomorphism onto
its image, with explicit inverse derivative. -/
private theorem odm_exists_partialDiffeomorph_of_deriv_pos
    (J : Set ℝ) (f : ℝ → ℝ) (hJopen : IsOpen J) (hJconn : J.OrdConnected)
    (hfd : ContDiffOn ℝ ∞ f J) (hderiv : ∀ t ∈ J, 0 < deriv f t) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞, Φ.source = J ∧
      (⇑Φ : ℝ → ℝ) = f ∧ Φ.target = f '' J ∧ (Φ.target).OrdConnected ∧
      ∀ u ∈ Φ.target, HasDerivAt ⇑Φ.symm ((deriv f (Φ.symm u))⁻¹) u := by
  have hcont : ContinuousOn f J := hfd.continuousOn
  have hstrict : StrictMonoOn f J :=
    strictMonoOn_of_deriv_pos hJconn.convex hcont (by
      rw [hJopen.interior_eq]
      exact hderiv)
  have hinj : Set.InjOn f J := hstrict.injOn
  let e : PartialEquiv ℝ ℝ := hinj.toPartialEquiv f J
  have hne : ∀ t ∈ J, deriv f t ≠ 0 := fun t ht => (hderiv t ht).ne'
  have hsd : ∀ t ∈ J, HasStrictDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hfd.contDiffAt (hJopen.mem_nhds ht)).hasStrictDerivAt (by simp))
  have hmap : ∀ t ∈ J, Filter.map f (𝓝 t) = 𝓝 (f t) := by
    intro t ht
    exact HasStrictDerivAt.map_nhds_eq (hsd t ht) (hne t ht)
  have himg : ∀ V : Set ℝ, IsOpen V → IsOpen (f '' (V ∩ J)) := by
    intro V hV
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨t, ⟨htV, htJ⟩, rfl⟩
    have hmem : V ∩ J ∈ 𝓝 t :=
      Filter.inter_mem (hV.mem_nhds htV) (hJopen.mem_nhds htJ)
    exact (hmap t htJ) ▸ Filter.image_mem_map hmem
  have htgt : IsOpen (f '' J) := by
    have hU := himg Set.univ isOpen_univ
    rwa [Set.univ_inter] at hU
  have hsymm : ∀ t ∈ J, HasStrictDerivAt ⇑e.symm ((deriv f t)⁻¹) (f t) := by
    intro t ht
    exact HasStrictDerivAt.to_local_left_inverse (hsd t ht) (hne t ht)
      (Filter.eventually_of_mem (hJopen.mem_nhds ht) (fun x hx => e.left_inv hx))
  have hcont_inv : ContinuousOn ⇑e.symm (f '' J) := by
    intro u hu
    obtain ⟨t, htJ, rfl⟩ := hu
    exact ((hsymm t htJ).hasDerivAt.continuousAt).continuousWithinAt
  let o : OpenPartialHomeomorph ℝ ℝ :=
    OpenPartialHomeomorph.mk (PartialHomeomorph.mk e hcont hcont_inv) hJopen htgt
  have ho_src : o.source = J := rfl
  have ho_tgt : o.target = f '' J := rfl
  have hst : ∀ s ∈ J, o.symm (f s) = s := fun s hs => e.left_inv hs
  have hmem_src : ∀ s ∈ J, s ∈ o.source := fun s hs => hs
  have hCdAt : ∀ x ∈ o.target, ContDiffAt ℝ ∞ ⇑o.symm x := by
    intro x hx
    have hxJ : x ∈ f '' J := hx
    obtain ⟨t, htJ, rfl⟩ := hxJ
    have hsymm_eq : o.symm (f t) = t := hst t htJ
    have hmem_t : f t ∈ o.target := by
      have hmem : f t ∈ f '' J := Set.mem_image_of_mem f htJ
      exact hmem
    have hmemJ : o.symm (f t) ∈ J := by
      rw [hsymm_eq]
      exact htJ
    have hf₀' : HasDerivAt ⇑o (deriv f (o.symm (f t))) (o.symm (f t)) :=
      (hsd _ hmemJ).hasDerivAt
    have hfC : ContDiffAt ℝ ∞ ⇑o (o.symm (f t)) :=
      hfd.contDiffAt (hJopen.mem_nhds hmemJ)
    have h₀ : deriv f (o.symm (f t)) ≠ 0 := by
      rw [hsymm_eq]
      exact hne t htJ
    exact o.contDiffAt_symm_deriv h₀ hmem_t hf₀' hfC
  have hsymmD : ContDiffOn ℝ ∞ ⇑e.symm e.target := by
    intro x hx
    have hxJ : x ∈ o.target := hx
    have hCd : ContDiffAt ℝ ∞ ⇑e.symm x := hCdAt x hxJ
    exact (contDiffWithinAt_univ.mpr hCd).mono (Set.subset_univ _)
  have hfDtoFun : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ⇑e e.source :=
    contMDiffOn_iff_contDiffOn.mpr (by exact hfd)
  have hfDinvFun : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ⇑e.symm e.target :=
    contMDiffOn_iff_contDiffOn.mpr hsymmD
  have hpre : IsPreconnected (f '' J) := hJconn.isPreconnected.image f hcont
  have hord : (f '' J).OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  have hsymm_deriv : ∀ u ∈ e.target,
      HasDerivAt ⇑e.symm ((deriv f (⇑e.symm u))⁻¹) u := by
    intro u hu
    have huJ : u ∈ f '' J := hu
    obtain ⟨t, htJ, rfl⟩ := huJ
    have h1 : ⇑e.symm (f t) = t := e.left_inv htJ
    rw [h1]
    exact (hsymm t htJ).hasDerivAt
  refine ⟨PartialDiffeomorph.mk e hJopen htgt hfDtoFun hfDinvFun,
    rfl, rfl, rfl, hord, ?_⟩
  intro u hu
  exact hsymm_deriv u hu

end InverseFunction1D

section SpeedSetup

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

/-- The smooth Riemannian metric on `M`, from `riemannianMetricExistence`. -/
private theorem om_riemannianMetric [T2Space M] [SecondCountableTopology M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x)) :=
  MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted.riemannianMetricExistence

/-- Squared speed of a curve `γ : ℝ → M` at `t`, measured with the metric `g`.
If `γ` is not differentiable at `t`, `mfderiv` is `0`, so the speed is `0`. -/
private def omCurveSpeedSq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))

/-- The constant-velocity section `s ↦ (s, 1)` into `ModelProd ℝ ℝ`, with the
`ModelProd` codomain so that smoothness statements resolve the `chartedSpaceSelf`
instance (matching `tangentBundleModelSpaceHomeomorph`). -/
private def omPairFn : ℝ → ModelProd ℝ ℝ := fun s => (s, (1 : ℝ))

/-- `γ` has unit speed on `U`: it is smooth and its squared speed is `1`. -/
private def omIsUnitSpeedOn
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ U ∧ ∀ t ∈ U, omCurveSpeedSq g γ t = 1

/-- The squared speed of a smooth curve is smooth. -/
private theorem om_contDiffOn_curveSpeedSq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ U) :
    ContDiffOn ℝ ∞ (fun t => omCurveSpeedSq g γ t) U := by
  let hRiem : Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓡 1) x) :=
    ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x) :=
    ⟨g.inner, g.contMDiff, fun x v w => rfl⟩
  have hagree : ∀ (x : M) (v w : TangentSpace (𝓡 1) x),
      inner ℝ v w = g.inner x v w := fun x v w => rfl
  have htm := ContMDiffOn.contMDiffOn_tangentMapWithin hγ (m := ∞) (by simp)
    hU.uniqueMDiffOn
  have h1id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s) := contMDiff_id
  have h1c : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ => (1 : ℝ)) := contMDiff_const
  have hpair : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞ omPairFn := by
    unfold omPairFn
    convert ContMDiff.prodMk h1id h1c using 2
    · rfl
    · rfl
    · exact chartedSpaceSelf_prod.symm
  have hsymmP : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ).tangent ∞
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
        ℝ × ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm
  have hfac : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm ∘ omPairFn)
      U :=
    (ContMDiff.contMDiffOn (ContMDiff.comp hsymmP hpair))
  have hproj : ∀ s : ℝ, Bundle.TotalSpace.proj
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (s, (1 : ℝ))) = s :=
    fun s => rfl
  have hpt : ∀ s : ℝ, (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (s, (1 : ℝ))
      = (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := fun s => rfl
  have hmaps : Set.MapsTo
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm ∘ omPairFn)
      U (Bundle.TotalSpace.proj ⁻¹' U) := by
    intro s hs
    simp only [Set.mem_preimage, Function.comp_apply, omPairFn]
    rw [hproj]
    exact hs
  have hW := ContMDiffOn.comp htm hfac hmaps
  have hsec : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1).tangent ∞
      (fun t : ℝ => ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
        TangentBundle (𝓡 1) M)) U := by
    apply ContMDiffOn.congr hW
    intro t ht
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
        TangentBundle (𝓡 1) M)
      = tangentMapWithin 𝓘(ℝ, ℝ) (𝓡 1) γ U
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, (1 : ℝ)))
    rw [hpt]
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ) : TangentSpace (𝓡 1) (γ t)) :
        TangentBundle (𝓡 1) M)
      = (⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 1) γ U t (1 : ℝ)⟩ :
        TangentBundle (𝓡 1) M)
    rw [mfderivWithin_of_isOpen hU ht]
  have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))) U :=
    ContMDiffOn.inner_bundle hsec hsec
  have hdiff : ContDiffOn ℝ ∞
      (fun t : ℝ => inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))) U :=
    contMDiffOn_iff_contDiffOn.mp hinner
  apply ContDiffOn.congr hdiff
  intro t _
  show omCurveSpeedSq g γ t = _
  unfold omCurveSpeedSq
  exact (hagree _ _ _).symm

/-- Speed under reparametrisation: the speed of `γ = β ∘ k` is `(k′)²` times the
speed of `β`. -/
private theorem om_curveSpeedSq_eq_of_eventuallyEq_comp
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (β : ℝ → M) (k : ℝ → ℝ) (t : ℝ)
    (hk : DifferentiableAt ℝ k t)
    (hβ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) β (k t))
    {γ : ℝ → M} (hγ : γ =ᶠ[nhds t] β ∘ k) :
    omCurveSpeedSq g γ t = (deriv k t) ^ 2 * omCurveSpeedSq g β (k t) := by
  have hk' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t :=
    DifferentiableAt.mdifferentiableAt hk
  have hβk : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t :=
    MDifferentiableAt.comp t hβ hk'
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ t :=
    MDifferentiableAt.congr_of_eventuallyEq hβk hγ
  have H : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t)) :=
    HasMFDerivAt.comp t (MDifferentiableAt.hasMFDerivAt hβ)
      (MDifferentiableAt.hasMFDerivAt hk')
  have Hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1) γ t
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t)) :=
    HasMFDerivAt.congr_of_eventuallyEq_abuse H hγ
  have hmeq : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t :=
    (HasMFDerivAt.mfderiv Hγ).trans (HasMFDerivAt.mfderiv H).symm
  have hpt : γ t = β (k t) := Filter.EventuallyEq.eq_of_nhds hγ
  have hk1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t (1 : ℝ) = deriv k t :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t =>
        D (1 : ℝ)) mfderiv_eq_fderiv)
      (Eq.trans (show (fderiv ℝ k t) (1 : ℝ) = (1 : ℝ) • deriv k t from
        fderiv_eq_smul_deriv _) (one_smul _ _))
  have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (β ∘ k) t (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k t (1 : ℝ)) :=
    mfderiv_comp_apply t hβ hk' ((1 : ℝ))
  have hmf1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (deriv k t) :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] EuclideanSpace ℝ (Fin 1) =>
        D (1 : ℝ)) hmeq)
      (Eq.trans hcomp
        (congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) hk1))
  have hsc : (deriv k t : ℝ) = (deriv k t) • (1 : ℝ) := by
    rw [smul_eq_mul, mul_one]
  have hmf1c : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ)
      = mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)) :=
    hmf1.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) hsc)
  change g.inner (γ t) _ _ = _
  rw [hpt]
  have eA : g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      = g.inner (β (k t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ))) :=
    congrArg (fun v => g.inner (β (k t)) v v) hmf1c
  have m1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ))
      = (deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ) :=
    map_smul (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t)) (deriv k t) (1 : ℝ)
  have eB : g.inner (β (k t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) ((deriv k t) • (1 : ℝ)))
      = g.inner (β (k t))
        ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
        ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    congrArg (fun v => g.inner (β (k t)) v v) m1
  have e_i1 : (g.inner (β (k t)))
        ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      = (deriv k t) • ((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    map_smul (g.inner (β (k t))) (deriv k t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
  have e_ii : g.inner (β (k t))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      = ((deriv k t) • ((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
        ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    congrArg (fun w : TangentSpace (𝓡 1) (β (k t)) →L[ℝ] ℝ =>
      w ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) e_i1
  have e_iii : ((deriv k t) • ((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
        ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      = (deriv k t) • ((((deriv k t) • ((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    map_smul (((deriv k t) • ((g.inner (β (k t)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))) (deriv k t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
  have e_iv : ((((deriv k t) • ((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))
      = (deriv k t) • ((((g.inner (β (k t)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    rfl
  have m2 : g.inner (β (k t))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      ((deriv k t) • mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
      = (deriv k t) • ((deriv k t) •
        g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))) :=
    e_ii.trans (e_iii.trans (congrArg ((deriv k t) • ·) e_iv))
  have s1 : (deriv k t) • ((deriv k t) •
      g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)))
      = (deriv k t) ^ 2 *
        g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) := by
    simp only [smul_eq_mul, pow_two]
    ring
  have eC : g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
      = (deriv k t) ^ 2 *
        g.inner (β (k t)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) β (k t) (1 : ℝ)) :=
    eA.trans (eB.trans (m2.trans s1))
  unfold omCurveSpeedSq
  exact eC

/-- A partial diffeomorphism from `ℝ` has nonzero velocity, hence positive speed. -/
private theorem om_curveSpeedSq_pos_of_partialDiffeomorph
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞) {s : ℝ} (hs : s ∈ Φ.source) :
    0 < omCurveSpeedSq g Φ s := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΦ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s := Φ.mdifferentiableAt hn hs
  have hΦs : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) :=
    Φ.symm.mdifferentiableAt hn (Φ.map_source hs)
  apply g.pos
  intro h0
  have hev : (fun y => Φ.symm (Φ y)) =ᶠ[nhds s] id :=
    Filter.eventually_of_mem (Φ.open_source.mem_nhds hs)
      (fun y hy => Φ.toPartialEquiv.left_inv hy)
  have e1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s
      = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id s :=
    HasMFDerivAt.mfderiv (HasMFDerivAt.congr_of_eventuallyEq_abuse
      (MDifferentiableAt.hasMFDerivAt mdifferentiableAt_id) hev)
  have e2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ)
      = mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s (1 : ℝ)) :=
    mfderiv_comp_apply s hΦs hΦ ((1 : ℝ))
  have e3 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) ⇑Φ s (1 : ℝ))
      = mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) 0 :=
    congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s)) h0
  have e4 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s) 0 = (0 : ℝ) :=
    map_zero (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) ⇑Φ.symm (Φ s))
  have e5 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id s (1 : ℝ) = (1 : ℝ) :=
    Eq.trans
      (congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s =>
        D (1 : ℝ)) mfderiv_id)
      rfl
  have e6 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ) = (0 : ℝ) :=
    e2.trans (e3.trans e4)
  have e7 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⇑Φ.symm ∘ ⇑Φ) s (1 : ℝ) = (1 : ℝ) :=
    congrArg (fun D : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s =>
      D (1 : ℝ)) e1 |>.trans e5
  have e8 : (1 : ℝ) = (0 : ℝ) := e7.symm.trans e6
  exact one_ne_zero e8

end SpeedSetup

section ArcLengthIntegral

/-- Arc-length integral of a positive smooth density on an open connected set
containing `0` is smooth, with the expected derivative. -/
private theorem om_arclength_contDiffOn
    (I : Set ℝ) (σ : ℝ → ℝ) (hIopen : IsOpen I) (hIconn : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I)
    (hσ : ContDiffOn ℝ ∞ σ I) (hpos : ∀ s ∈ I, 0 < σ s) :
    ContDiffOn ℝ ∞
      (fun s => intervalIntegral (fun u => Real.sqrt (σ u)) 0 s MeasureTheory.volume) I ∧
      (∀ s ∈ I, HasDerivAt
        (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)
        (Real.sqrt (σ s)) s) := by
  have hsqrt : ContDiffOn ℝ ∞ (fun s => Real.sqrt (σ s)) I :=
    hσ.sqrt (fun s hs => ne_of_gt (hpos s hs))
  have hcont : ContinuousOn (fun s => Real.sqrt (σ s)) I := hsqrt.continuousOn
  have hsub : ∀ s ∈ I, Set.uIcc (0 : ℝ) s ⊆ I :=
    fun s hs => hIconn.uIcc_subset h0 hs
  have hder : ∀ s ∈ I, HasDerivAt
      (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)
      (Real.sqrt (σ s)) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hcont.mono (hsub s hs)).intervalIntegrable
    · exact ContinuousAt.stronglyMeasurableAtFilter hIopen
        (fun x hx => hcont.continuousAt (hIopen.mem_nhds hx)) s hs
    · exact hcont.continuousAt (hIopen.mem_nhds hs)
  have hdiff : DifferentiableOn ℝ
      (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume) I :=
    fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
  have hderiv_smooth : ContDiffOn ℝ ∞
      (deriv (fun t => intervalIntegral (fun u => Real.sqrt (σ u)) 0 t MeasureTheory.volume)) I :=
    hsqrt.congr (fun s hs => (hder s hs).deriv)
  exact ⟨(contDiffOn_infty_iff_deriv_of_isOpen hIopen).mpr ⟨hdiff, hderiv_smooth⟩, hder⟩

end ArcLengthIntegral

section UnitSpeedCharts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

/-- The linear identification `ℝ ≃L[ℝ] E1`. -/
private def omLinEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm

/-- Chart inverse through `x`: a diffeomorphism from an open interval onto a
neighbourhood of `x`, with positive smooth speed. -/
private theorem om_chartInverse
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (x : M) :
    ∃ β0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
      β0.source.OrdConnected ∧ (0 : ℝ) ∈ β0.source ∧ β0 0 = x ∧
        (∀ s ∈ β0.source, 0 < omCurveSpeedSq g β0 s) ∧
        ContDiffOn ℝ ∞ (fun s => omCurveSpeedSq g β0 s) β0.source := by
  set e := omLinEquiv with he
  set ch := chartAt (EuclideanSpace ℝ (Fin 1)) x with hch
  set x' := ch x with hx'
  have hx'src : x ∈ ch.source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 1)) x
  have hx'tgt : x' ∈ ch.target :=
    mem_chart_target (EuclideanSpace ℝ (Fin 1)) x
  have hVopen : IsOpen ((fun s : ℝ => x' + e s) ⁻¹' ch.target) :=
    ch.open_target.preimage (continuous_const.add e.continuous)
  have hV0 : (0 : ℝ) ∈ (fun s : ℝ => x' + e s) ⁻¹' ch.target := by
    have h0e : x' + e (0 : ℝ) = x' := by simp
    simpa [h0e] using hx'tgt
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hVopen 0 hV0
  set I0 : Set ℝ := Set.Ioo (-r) r with hI0
  have hI0sub : I0 ⊆ (fun s : ℝ => x' + e s) ⁻¹' ch.target := by
    intro s hs
    rw [hI0] at hs
    have hmem : s ∈ Metric.ball (0 : ℝ) r := by
      rw [Real.ball_eq_Ioo]
      simpa using hs
    exact hball hmem
  have hI0open : IsOpen I0 := isOpen_Ioo
  have hI0conn : I0.OrdConnected :=
    isPreconnected_iff_ordConnected.mp isPreconnected_Ioo
  have hI00 : (0 : ℝ) ∈ I0 := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  set W : Set (EuclideanSpace ℝ (Fin 1)) :=
    (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) ⁻¹' I0 with hW
  have hWopen : IsOpen W :=
    hI0open.preimage (e.symm.continuous.comp (continuous_id.sub continuous_const))
  set V : Set M := ch.source ∩ ⇑ch ⁻¹' W with hV
  have hVopen : IsOpen V :=
    ch.continuousOn.isOpen_inter_preimage ch.open_source hWopen
  set f : ℝ → M := fun s => ch.symm (x' + e s) with hf
  set f' : M → ℝ := fun y => e.symm (ch y - x') with hf'
  have hleft : ∀ s ∈ I0, f' (f s) = s := by
    intro s hs
    have hmem : x' + e s ∈ ch.target := hI0sub hs
    change e.symm (ch (ch.symm (x' + e s)) - x') = s
    rw [ch.right_inv hmem]
    have hab : x' + e s - x' = e s := by abel
    rw [hab]
    simp
  have hright : ∀ y ∈ V, f (f' y) = y := by
    intro y hy
    obtain ⟨hysrc, -⟩ := hy
    change ch.symm (x' + e (e.symm (ch y - x'))) = y
    have h1 : e (e.symm (ch y - x')) = ch y - x' := by simp
    rw [h1]
    have h2 : x' + (ch y - x') = ch y := by abel
    rw [h2]
    exact ch.left_inv hysrc
  have hfmaps : Set.MapsTo f I0 V := by
    intro s hs
    constructor
    · exact ch.map_target (hI0sub hs)
    · change ch (f s) ∈ W
      have hmem : x' + e s ∈ ch.target := hI0sub hs
      have hchf : ch (f s) = x' + e s := ch.right_inv hmem
      change (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) (ch (f s)) ∈ I0
      rw [hchf]
      change e.symm (x' + e s - x') ∈ I0
      have hab : x' + e s - x' = e s := by abel
      rw [hab]
      simpa using hs
  have hf'maps : Set.MapsTo f' V I0 := by
    intro y hy
    obtain ⟨-, hyW⟩ := hy
    change e.symm (ch y - x') ∈ I0
    change (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) (ch y) ∈ I0
    exact hyW
  have haff : ContDiff ℝ ∞ (fun s : ℝ => x' + e s) :=
    contDiff_const.add e.contDiff
  have haffM : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun s : ℝ => x' + e s) I0 :=
    ((haff.contMDiff).contMDiffOn.mono (Set.subset_univ I0))
  have hfD : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ f I0 :=
    ((contMDiffOn_chart_symm (x := x) :
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ ⇑ch.symm ch.target).comp haffM
      (fun s hs => hI0sub hs))
  have hsub' : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 1) => e.symm (v - x')) :=
    e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have houter : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (⇑e.symm ∘ fun v : EuclideanSpace ℝ (Fin 1) => v - x') Set.univ :=
    (hsub'.contMDiff).contMDiffOn
  have hf'D : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ f' V :=
    houter.comp (contMDiffOn_chart.mono Set.inter_subset_left)
      (Set.mapsTo_univ _ _)
  obtain ⟨β0, hβsrc, hβtgt, hβfun, -⟩ :=
    odm_exists_partialDiffeomorph_of_invOn f f' I0 V hI0open hVopen
      hfmaps hf'maps ⟨hleft, hright⟩ hfD hf'D
  refine ⟨β0, hβsrc.symm ▸ hI0conn, hβsrc.symm ▸ hI00, ?_, ?_, ?_⟩
  · rw [hβfun]
    change ch.symm (x' + e (0 : ℝ)) = x
    have h0e : x' + e (0 : ℝ) = x' := by simp
    rw [h0e]
    exact ch.left_inv hx'src
  · intro s hs
    exact om_curveSpeedSq_pos_of_partialDiffeomorph g β0 hs
  · exact om_contDiffOn_curveSpeedSq g ⇑β0 β0.source β0.open_source
      β0.contMDiffOn_toFun

/-- Unit-speed charts exist at every point. -/
private theorem om_exists_unitSpeedChart
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (x : M) :
    ∃ α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
      α.source.OrdConnected ∧ (0 : ℝ) ∈ α.source ∧ α 0 = x ∧
        ∀ s ∈ α.source, omCurveSpeedSq g α s = 1 := by
  obtain ⟨β0, hβconn, hβ0, hβx, hβpos, hβsmooth⟩ := om_chartInverse g x
  set τ : ℝ → ℝ := fun s =>
    intervalIntegral (fun u => Real.sqrt (omCurveSpeedSq g ⇑β0 u)) 0 s
      MeasureTheory.volume with hτ
  obtain ⟨hτsmooth, hτder⟩ := om_arclength_contDiffOn β0.source
    (fun s => omCurveSpeedSq g ⇑β0 s) β0.open_source hβconn hβ0 hβsmooth
    (fun s hs => hβpos s hs)
  have hτderiv : ∀ s ∈ β0.source, 0 < deriv τ s := by
    intro s hs
    have h1 : deriv τ s = Real.sqrt (omCurveSpeedSq g ⇑β0 s) :=
      (hτder s hs).deriv
    rw [h1]
    exact Real.sqrt_pos.mpr (hβpos s hs)
  obtain ⟨Φ, hΦsrc, hΦfun, hΦtgt, hΦconn, hΦsymm⟩ :=
    odm_exists_partialDiffeomorph_of_deriv_pos β0.source τ β0.open_source hβconn
      hτsmooth hτderiv
  have hτ0 : τ 0 = 0 := intervalIntegral.integral_same
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦfun]
    exact hτ0
  have h0tgt : (0 : ℝ) ∈ Φ.target := by
    rw [hΦtgt]
    exact ⟨0, hβ0, hτ0⟩
  set α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞ := Φ.symm.trans β0 with hα
  have hsymmsrc : Φ.symm.source = Φ.target := rfl
  have htrans : α.source = Φ.symm.source ∩ ⇑Φ.symm ⁻¹' β0.source := rfl
  have hsub : Φ.target ⊆ ⇑Φ.symm ⁻¹' β0.source := by
    intro u hu
    have h1 : Φ.symm u ∈ Φ.source := Φ.symm.toPartialEquiv.map_source hu
    rw [hΦsrc] at h1
    exact h1
  have hαsrc : α.source = Φ.target := by
    rw [htrans, hsymmsrc]
    exact Set.inter_eq_self_of_subset_left hsub
  have hsymm0 : Φ.symm (Φ 0) = 0 :=
    Φ.toPartialEquiv.left_inv (hΦsrc.symm ▸ hβ0)
  rw [hΦ0] at hsymm0
  refine ⟨α, hαsrc.symm ▸ hΦconn, hαsrc.symm ▸ h0tgt, ?_, ?_⟩
  · change β0 (Φ.symm 0) = x
    rw [hsymm0]
    exact hβx
  · intro u hu
    have hutgt : u ∈ Φ.target := hαsrc ▸ hu
    have husym : u ∈ Φ.symm.source := hsymmsrc ▸ hutgt
    have humem : u ∈ Φ.symm.source ∩ ⇑Φ.symm ⁻¹' β0.source := htrans ▸ hu
    have hmem2 : Φ.symm u ∈ β0.source := humem.2
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    have hdiff : DifferentiableAt ℝ ⇑Φ.symm u :=
      (Φ.symm.mdifferentiableAt hn husym).differentiableAt
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑β0 (Φ.symm u) :=
      β0.mdifferentiableAt hn hmem2
    have hev : ∀ s, α s = (⇑β0 ∘ ⇑Φ.symm) s := fun s => rfl
    have hspeed := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑β0 ⇑Φ.symm u
      hdiff hmdiff (Filter.Eventually.of_forall hev)
    have hderivk : deriv ⇑Φ.symm u = (deriv τ (Φ.symm u))⁻¹ :=
      (hΦsymm u hutgt).deriv
    have hτk : deriv τ (Φ.symm u) =
        Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u)) :=
      (hτder (Φ.symm u) hmem2).deriv
    have hspos : 0 < omCurveSpeedSq g ⇑β0 (Φ.symm u) := hβpos _ hmem2
    have hne : Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hspos)
    have hσsq : omCurveSpeedSq g ⇑β0 (Φ.symm u) =
        (Real.sqrt (omCurveSpeedSq g ⇑β0 (Φ.symm u))) ^ 2 :=
      (Real.sq_sqrt (le_of_lt hspos)).symm
    rw [hspeed, hσsq, hderivk, hτk, ← mul_pow, inv_mul_cancel₀ hne, one_pow]

/-- Rigidity: a unit-speed curve is affine in any unit-speed chart. -/
private theorem om_exists_affine_of_unitSpeed
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
    (hα : ∀ s ∈ α.source, omCurveSpeedSq g α s = 1)
    (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
    (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U)
    (hγt : γ t ∈ α.target) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ c : ℝ, ε * t + c = α.symm (γ t) ∧
      ∀ᶠ s in nhds t, ε * s + c ∈ α.source ∧ γ s = α (ε * s + c) := by
  have hγcont : ContinuousOn γ U := hγ.1.continuousOn
  set W : Set ℝ := U ∩ γ ⁻¹' α.target with hW
  have hWopen : IsOpen W :=
    hγcont.isOpen_inter_preimage hU α.open_target
  have htW : t ∈ W := ⟨ht, hγt⟩
  set k : ℝ → ℝ := ⇑α.symm ∘ γ with hk
  have hkmaps : Set.MapsTo γ W α.symm.source := fun s hs => hs.2
  have hkD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ k W :=
    α.symm.contMDiffOn_toFun.comp (hγ.1.mono Set.inter_subset_left) hkmaps
  have hkCd : ContDiffOn ℝ ∞ k W := contMDiffOn_iff_contDiffOn.mp hkD
  have hγeq : ∀ s ∈ W, γ s = α (k s) := fun s hs =>
    (α.toPartialEquiv.right_inv hs.2).symm
  have hmdk : ∀ s ∈ W, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k s := by
    intro s hs
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    exact (hkD.mdifferentiableOn hn).mdifferentiableAt (hWopen.mem_nhds hs)
  have hsqW : ∀ s ∈ W, (deriv k s) ^ 2 = 1 := by
    intro s hs
    have hks : DifferentiableAt ℝ k s := (hmdk s hs).differentiableAt
    have hkmem : k s ∈ α.source := α.symm.toPartialEquiv.map_source hs.2
    have hβs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑α (k s) :=
      α.mdifferentiableAt (by simp) hkmem
    have hWmem : ∀ᶠ s' in nhds s, s' ∈ W := hWopen.mem_nhds hs
    have hevW : ∀ᶠ s' in nhds s, γ s' = (⇑α ∘ k) s' :=
      hWmem.mono fun s' hs' => hγeq s' hs'
    have heq := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑α k s hks hβs hevW
    rw [hγ.2 s hs.1, hα (k s) hkmem] at heq
    simpa using heq.symm
  have hderivCd : ContDiffOn ℝ ∞ (deriv k) W :=
    hkCd.deriv_of_isOpen hWopen (by simp)
  have hderivCont : ContinuousAt (deriv k) t :=
    hderivCd.continuousOn.continuousAt (hWopen.mem_nhds htW)
  have hevEq : ∀ᶠ s in nhds t, deriv k s = deriv k t := by
    have h1' := (hderivCont.tendsto).eventually (Metric.ball_mem_nhds _ one_pos)
    have h1 : ∀ᶠ s in nhds t, dist (deriv k s) (deriv k t) < 1 := by
      simpa only [Metric.mem_ball] using h1'
    have h2 : ∀ᶠ s in nhds t, s ∈ W := hWopen.mem_nhds htW
    filter_upwards [h1, h2] with s hs1 hs2
    rcases sq_eq_one_iff.mp (hsqW s hs2) with hs1c | hs1c <;>
      rcases sq_eq_one_iff.mp (hsqW t htW) with htc | htc
    · rw [hs1c, htc]
    · rw [hs1c, htc] at hs1
      norm_num [dist_eq_norm] at hs1
    · rw [hs1c, htc] at hs1
      norm_num [dist_eq_norm] at hs1
    · rw [hs1c, htc]
  have hmemE : {s | deriv k s = deriv k t} ∈ nhds t := hevEq
  obtain ⟨δ, hδpos, hballsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hWopen.mem_nhds htW) hmemE)
  set J : Set ℝ := Set.Ioo (t - δ) (t + δ) with hJ
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  have htJ : t ∈ J := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hJsub : J ⊆ W ∩ {s | deriv k s = deriv k t} := by
    intro s hs
    have hs' : s ∈ Set.Ioo (t - δ) (t + δ) := hs
    have hmem : s ∈ Metric.ball t δ := by
      rwa [← Real.ball_eq_Ioo] at hs'
    exact hballsub hmem
  have hdiffJ : DifferentiableOn ℝ (fun s => k s - deriv k t * s) J :=
    ((hkCd.mono (hJsub.trans Set.inter_subset_left)).differentiableOn
      (by simp)).sub
      (differentiableOn_id.const_mul (deriv k t))
  have hderiv0 : J.EqOn (deriv (fun s => k s - deriv k t * s)) 0 := by
    intro s hs
    have hks : DifferentiableAt ℝ k s := (hmdk s (hJsub hs).1).differentiableAt
    have h1 : HasDerivAt (fun s => k s - deriv k t * s)
        (deriv k s - deriv k t * 1) s :=
      hks.hasDerivAt.sub ((hasDerivAt_id s).const_mul (deriv k t))
    have hder : deriv (fun s => k s - deriv k t * s) s =
        deriv k s - deriv k t * 1 := h1.deriv
    have hsJ : deriv k s = deriv k t := (hJsub hs).2
    rw [hder, hsJ, mul_one, sub_self]
    rfl
  obtain ⟨c, hc⟩ := hJopen.exists_is_const_of_deriv_eq_zero hJpre hdiffJ hderiv0
  have hkc : ∀ x ∈ J, k x = deriv k t * x + c := by
    intro x hx
    have hxc : k x - deriv k t * x = c := hc x hx
    linarith
  have hkt : k t = deriv k t * t + c := hkc t htJ
  refine ⟨deriv k t, sq_eq_one_iff.mp (hsqW t htW), c, hkt.symm, ?_⟩
  have hJnhds : J ∈ nhds t := hJopen.mem_nhds htJ
  filter_upwards [hJnhds] with s hs
  have hsmem : k s ∈ α.source := α.symm.toPartialEquiv.map_source ((hJsub hs).1).2
  constructor
  · rw [(hkc s hs).symm]
    exact hsmem
  · rw [(hkc s hs).symm]
    exact hγeq s (hJsub hs).1

/-- Local normal form of a unit-speed curve: near `t` it equals a unit-speed
chart composed with an affine map, on an open set where it is injective. -/
private theorem om_unitSpeed_localData
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
    (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
    ∃ α : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞,
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ D : Set ℝ, IsOpen D ∧ t ∈ D ∧
      (∀ s ∈ D, ε * s + c ∈ α.source ∧ γ s = α (ε * s + c)) ∧
      Set.InjOn γ D := by
  obtain ⟨α, -, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ t)
  have hγt : γ t ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
  obtain ⟨ε, hε, c, -, hev⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed U γ hU hγ t ht hγt
  obtain ⟨D, hDsub, hDopen, htD⟩ := mem_nhds_iff.mp hev
  refine ⟨α, ε, c, hε, D, hDopen, htD, fun s hs => hDsub hs, ?_⟩
  intro s₁ hs₁ s₂ hs₂ h12
  have h1 := (hDsub hs₁).1
  have h2 := (hDsub hs₂).1
  have h3 := (hDsub hs₁).2
  have h4 := (hDsub hs₂).2
  have hne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hsc : ε * s₁ + c = ε * s₂ + c :=
    α.toPartialEquiv.injOn h1 h2 (h3.symm.trans (h12.trans h4))
  have hmul : ε * s₁ = ε * s₂ := by linarith
  exact mul_left_cancel₀ hne hmul

/-- The affine map `s ↦ ε * s + c` with `ε = ±1` is a global partial
diffeomorphism of `ℝ`. -/
private theorem om_affine_partialDiffeo (ε c : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (⇑Φ : ℝ → ℝ) = (fun s => ε * s + c) ∧ Φ.source = Set.univ := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have haffD : ContDiff ℝ ∞ (fun s : ℝ => ε * s + c) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  have hinvD : ContDiff ℝ ∞ (fun y : ℝ => ε * (y - c)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  obtain ⟨Φ, hsrc, -, hfun, -⟩ := odm_exists_partialDiffeomorph_of_invOn
    (fun s : ℝ => ε * s + c) (fun y : ℝ => ε * (y - c))
    Set.univ Set.univ isOpen_univ isOpen_univ
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    ⟨fun s _ => by
      change ε * (ε * s + c - c) = s
      have h : ε * (ε * s + c - c) = (ε * ε) * s := by ring
      rw [h, hε2, one_mul],
    fun y _ => by
      change ε * (ε * (y - c)) + c = y
      have h : ε * (ε * (y - c)) + c = (ε * ε) * (y - c) + c := by ring
      rw [h, hε2, one_mul, sub_add_cancel]⟩
    (haffD.contMDiff.contMDiffOn) (hinvD.contMDiff.contMDiffOn)
  exact ⟨Φ, hfun, hsrc⟩

/-- A unit-speed curve is a local diffeomorphism at every point of its domain. -/
private theorem om_isLocalDiffeomorphAt_of_unitSpeed
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
    (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, -⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨Φaff, hΦaff, hΦaffsrc⟩ := om_affine_partialDiffeo ε c hε
  have hmem : Φaff t ∈ α.source := hΦaff.symm ▸ (hDprop t htD).1
  have hFmem : t ∈ (Φaff.trans α).source := by
    have h : (Φaff.trans α).source = Φaff.source ∩ ⇑Φaff ⁻¹' α.source := rfl
    rw [h]
    exact ⟨hΦaffsrc.symm ▸ Set.mem_univ t, hmem⟩
  have hF : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑(Φaff.trans α) t :=
    PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ _ hFmem
  have hevF : γ =ᶠ[nhds t] ⇑(Φaff.trans α) := by
    have hDmem : ∀ᶠ s in nhds t, s ∈ D := hDopen.mem_nhds htD
    refine hDmem.mono fun s hs => ?_
    have h2 := (hDprop s hs).2
    change γ s = (Φaff.trans α) s
    change γ s = α (Φaff s)
    rw [hΦaff]
    change γ s = α (ε * s + c)
    exact h2
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hF hevF

/-- A unit-speed curve is locally injective. -/
private theorem om_exists_injOn_of_unitSpeed
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
    (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ Set.InjOn γ (Set.Ioo (t - δ) (t + δ)) := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, hInj⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨δ, hδpos, hballsub⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds htD)
  refine ⟨δ, hδpos, ?_⟩
  apply hInj.mono
  intro s hs
  have hs' : s ∈ Set.Ioo (t - δ) (t + δ) := hs
  have hmem : s ∈ Metric.ball t δ := by
    rwa [← Real.ball_eq_Ioo] at hs'
  exact hballsub hmem

/-- The image of a neighbourhood under a unit-speed curve is a neighbourhood. -/
private theorem om_image_mem_nhds_of_unitSpeed
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (U : Set ℝ) (γ : ℝ → M) (hU : IsOpen U)
    (hγ : omIsUnitSpeedOn g γ U) (t : ℝ) (ht : t ∈ U)
    (W : Set ℝ) (hW : W ∈ nhds t) :
    γ '' W ∈ nhds (γ t) := by
  obtain ⟨α, ε, c, hε, D, hDopen, htD, hDprop, -⟩ :=
    om_unitSpeed_localData g U γ hU hγ t ht
  obtain ⟨Φaff, hΦaff, hΦaffsrc⟩ := om_affine_partialDiffeo ε c hε
  have htW : t ∈ W := mem_of_mem_nhds hW
  have htI : t ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  set E : Set ℝ := D ∩ interior W with hE
  have hEopen : IsOpen E := hDopen.inter isOpen_interior
  have htE : t ∈ E := ⟨htD, htI⟩
  have hsub1 : (fun s => ε * s + c) '' E ⊆ α.source := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact (hDprop s hs.1).1
  have haffE : IsOpen ((fun s => ε * s + c) '' E) := by
    have himg : (fun s => ε * s + c) '' E = Φaff '' E := by rw [hΦaff]
    rw [himg]
    exact Φaff.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      hEopen (fun y _ => by
        change y ∈ Φaff.source
        rw [hΦaffsrc]
        exact Set.mem_univ y)
  have hαimg : IsOpen (⇑α '' ((fun s => ε * s + c) '' E)) :=
    α.toOpenPartialHomeomorph.isOpen_image_of_subset_source haffE hsub1
  have himgEq : γ '' E = ⇑α '' ((fun s => ε * s + c) '' E) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ε * s + c, ⟨s, hs, rfl⟩, (hDprop s hs.1).2.symm⟩
    · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, ⟨hs.1, hs.2⟩, (by simpa using (hDprop s hs.1).2)⟩
  have hmem : γ '' E ∈ nhds (γ t) := himgEq.symm ▸
    hαimg.mem_nhds ⟨ε * t + c, ⟨t, htE, rfl⟩, (hDprop t htD).2.symm⟩
  have hEW : E ⊆ W :=
    (Set.inter_subset_right (s := D) (t := interior W)).trans interior_subset
  exact Filter.mem_of_superset hmem
    (fun y hy => by obtain ⟨s, hs, rfl⟩ := hy; exact ⟨s, hEW hs, rfl⟩)

end UnitSpeedCharts

section IdentityTheorem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

/-- Identity theorem: two unit-speed curves on a preconnected open set that agree
near one point agree everywhere. -/
private theorem om_eqOn_of_unitSpeed_of_eventuallyEq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (I : Set ℝ) (hIopen : IsOpen I) (hIpre : IsPreconnected I)
    (γ1 γ2 : ℝ → M) (h1 : omIsUnitSpeedOn g γ1 I) (h2 : omIsUnitSpeedOn g γ2 I)
    (t0 : ℝ) (ht0 : t0 ∈ I) (h0 : γ1 =ᶠ[nhds t0] γ2) :
    Set.EqOn γ1 γ2 I := by
  set u : Set ℝ := {t | γ1 =ᶠ[nhds t] γ2} with hu
  have huopen : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact eventually_eventuallyEq_nhds.mpr ht
  have hIu : (I ∩ u).Nonempty := ⟨t0, ht0, h0⟩
  have hsub : I ⊆ u := by
    apply hIpre.subset_of_closure_inter_subset huopen hIu
    intro t ht
    obtain ⟨htcl, htI⟩ := ht
    have hImem : I ∈ nhds t := hIopen.mem_nhds htI
    have hcont1 : ContinuousAt γ1 t := h1.1.continuousOn.continuousAt hImem
    have hcont2 : ContinuousAt γ2 t := h2.1.continuousOn.continuousAt hImem
    have hfreq : ∃ᶠ s in nhds t, γ1 s = γ2 s :=
      (mem_closure_iff_frequently.mp htcl).mono fun s hs => hs.self_of_nhds
    have hteq : γ1 t = γ2 t :=
      tendsto_nhds_unique_of_frequently_eq hcont1 hcont2 hfreq
    obtain ⟨α, -, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ1 t)
    have hγt1 : γ1 t ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
    have hγt2 : γ2 t ∈ α.target := hteq ▸ hγt1
    obtain ⟨ε1, -, c1, -, hev1⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed I γ1 hIopen h1 t htI hγt1
    obtain ⟨ε2, -, c2, -, hev2⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed I γ2 hIopen h2 t htI hγt2
    have hev : ∀ᶠ s in nhds t,
        (ε1 * s + c1 ∈ α.source ∧ γ1 s = α (ε1 * s + c1)) ∧
        (ε2 * s + c2 ∈ α.source ∧ γ2 s = α (ε2 * s + c2)) :=
      hev1.and hev2
    obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp hev
    have hmem7 : Metric.ball t (δ / 2) ∈ nhds t :=
      Metric.ball_mem_nhds t (by linarith)
    have hfreqU : ∃ᶠ s in nhds t, s ∈ u := mem_closure_iff_frequently.mp htcl
    obtain ⟨s, hsu, hsball⟩ := (hfreqU.and_eventually hmem7).exists
    obtain ⟨F, hFsub, hFopen, hsF⟩ := mem_nhds_iff.mp hsu
    set E : Set ℝ := Metric.ball s (δ / 2) ∩ F with hE
    have hEopen : IsOpen E := Metric.isOpen_ball.inter hFopen
    have hsE : s ∈ E := ⟨Metric.mem_ball_self (by linarith), hsF⟩
    have hEball : E ⊆ Metric.ball t δ := by
      intro y hy
      have h1d : dist y s < δ / 2 := Metric.mem_ball.mp hy.1
      have h2d : dist s t < δ / 2 := hsball
      refine Metric.mem_ball.mpr ?_
      calc dist y t ≤ dist y s + dist s t := dist_triangle y s t
        _ < δ := by linarith
    have hEprop : ∀ y ∈ E, ε1 * y + c1 ∈ α.source ∧ ε2 * y + c2 ∈ α.source ∧
        α (ε1 * y + c1) = α (ε2 * y + c2) := by
      intro y hy
      have hyt := hball (hEball hy)
      have hFy : γ1 y = γ2 y := hFsub hy.2
      refine ⟨(hyt.1).1, (hyt.2).1, ?_⟩
      calc α (ε1 * y + c1) = γ1 y := ((hyt.1).2).symm
        _ = γ2 y := hFy
        _ = α (ε2 * y + c2) := (hyt.2).2
    have haff : ∀ y ∈ E, ε1 * y + c1 = ε2 * y + c2 := by
      intro y hy
      obtain ⟨hm1, hm2, heq⟩ := hEprop y hy
      exact α.toPartialEquiv.injOn hm1 hm2 heq
    obtain ⟨r, hrpos, hrball⟩ := Metric.mem_nhds_iff.mp (hEopen.mem_nhds hsE)
    have hs2E : s + r / 2 ∈ E := by
      apply hrball
      rw [Metric.mem_ball, dist_eq_norm]
      have hrw : (s + r / 2) - s = r / 2 := by ring
      rw [hrw, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hne12 : s ≠ s + r / 2 := by
      intro h
      have h0' : (r / 2 : ℝ) = 0 := by linarith
      linarith
    have e1 := haff s hsE
    have e2 := haff (s + r / 2) hs2E
    have hkey : (ε1 - ε2) * (s - (s + r / 2)) = 0 := by
      have h1' : ε1 * s - ε2 * s = c2 - c1 := by linarith
      have h2' : ε1 * (s + r / 2) - ε2 * (s + r / 2) = c2 - c1 := by linarith
      have hrr : (ε1 - ε2) * (s - (s + r / 2)) =
          (ε1 * s - ε2 * s) - (ε1 * (s + r / 2) - ε2 * (s + r / 2)) := by ring
      rw [hrr, h1', h2', sub_self]
    have hε : ε1 = ε2 := by
      rcases mul_eq_zero.mp hkey with h | h
      · linarith
      · exact absurd (sub_eq_zero.mp h) hne12
    have hc : c1 = c2 := by
      have hcc := haff s hsE
      rw [hε] at hcc
      linarith
    change γ1 =ᶠ[nhds t] γ2
    filter_upwards [Metric.ball_mem_nhds t hδpos] with y hy
    have hyt := hball hy
    calc γ1 y = α (ε1 * y + c1) := (hyt.1).2
      _ = α (ε2 * y + c2) := by rw [hε, hc]
      _ = γ2 y := ((hyt.2).2).symm
  intro t ht
  exact (hsub ht).self_of_nhds

end IdentityTheorem

section MaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

/-- An admissible pair: an open connected neighbourhood of `0` carrying a
unit-speed curve that agrees with the base chart near `0`. -/
private def omAdmissible
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞) (J : Set ℝ) (δ : ℝ → M) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ omIsUnitSpeedOn g δ J ∧ δ =ᶠ[nhds 0] ⇑α0

/-- Maximal unit-speed curve through a base chart: the union of all admissible
curves, which absorbs every admissible curve. -/
private theorem om_exists_maximal_unitSpeed
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
    (hα0src : α0.source.OrdConnected) (hα00 : (0 : ℝ) ∈ α0.source)
    (hα0speed : ∀ s ∈ α0.source, omCurveSpeedSq g α0 s = 1) :
    ∃ D γ, omAdmissible g α0 D γ ∧
      ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J := by
  set S : Set (Set ℝ) := {J | ∃ δ, omAdmissible g α0 J δ}
  set D : Set ℝ := ⋃₀ S
  have hex : ∀ t : ℝ, ∃ J δ, (t ∈ D → omAdmissible g α0 J δ ∧ t ∈ J) := by
    intro t
    by_cases ht : t ∈ D
    · obtain ⟨J, hJ, htJ⟩ := ht
      obtain ⟨δ, hδ⟩ := hJ
      exact ⟨J, δ, fun _ => ⟨hδ, htJ⟩⟩
    · exact ⟨∅, fun _ => α0 0, fun h => absurd h ht⟩
  choose J0 δ0 hJ0 using hex
  set γ : ℝ → M := fun t => δ0 t t
  have hDsub : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D := by
    intro J δ hJδ t htJ
    exact Set.mem_sUnion.mpr ⟨J, ⟨δ, hJδ⟩, htJ⟩
  have hcons : ∀ J δ J' δ', omAdmissible g α0 J δ → omAdmissible g α0 J' δ' →
      Set.EqOn δ δ' (J ∩ J') := by
    intro J δ J' δ' h h'
    have hJJopen : IsOpen (J ∩ J') := h.1.inter h'.1
    have hJJconn := h.2.1.inter h'.2.1
    have hJJpre : IsPreconnected (J ∩ J') := hJJconn.isPreconnected
    have h0JJ : (0 : ℝ) ∈ J ∩ J' := ⟨h.2.2.1, h'.2.2.1⟩
    have hev : δ =ᶠ[nhds 0] δ' := h.2.2.2.2.trans h'.2.2.2.2.symm
    have hu : omIsUnitSpeedOn g δ (J ∩ J') :=
      ⟨h.2.2.2.1.1.mono Set.inter_subset_left, fun t ht => h.2.2.2.1.2 t ht.1⟩
    have hu' : omIsUnitSpeedOn g δ' (J ∩ J') :=
      ⟨h'.2.2.2.1.1.mono Set.inter_subset_right, fun t ht => h'.2.2.2.1.2 t ht.2⟩
    exact om_eqOn_of_unitSpeed_of_eventuallyEq g (J ∩ J') hJJopen hJJpre δ δ'
      hu hu' 0 h0JJ hev
  have hγeq : ∀ J δ, omAdmissible g α0 J δ → Set.EqOn δ γ J := by
    intro J δ hJδ t htJ
    have htD : t ∈ D := hDsub J δ hJδ htJ
    have hmem : t ∈ J ∩ J0 t := ⟨htJ, (hJ0 t htD).2⟩
    have h1 : δ t = δ0 t t := hcons J δ (J0 t) (δ0 t) hJδ (hJ0 t htD).1 hmem
    change δ t = δ0 t t
    exact h1
  have hα0adm : omAdmissible g α0 α0.source ⇑α0 :=
    ⟨α0.open_source, hα0src, hα00, ⟨α0.contMDiffOn_toFun, hα0speed⟩,
      Filter.EventuallyEq.refl _ _⟩
  have h0D : (0 : ℝ) ∈ D := hDsub _ _ hα0adm hα00
  have hDopen : IsOpen D := by
    apply isOpen_sUnion
    intro J hJ
    obtain ⟨δ, hδ⟩ := hJ
    exact hδ.1
  have hDpre : IsPreconnected D := by
    apply isPreconnected_sUnion 0 S _ _
    · intro s hs
      obtain ⟨δ, hδ⟩ := hs
      exact hδ.2.2.1
    · intro s hs
      obtain ⟨δ, hδ⟩ := hs
      exact hδ.2.1.isPreconnected
  have hDconn : D.OrdConnected := isPreconnected_iff_ordConnected.mp hDpre
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ D := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro t htD
    have hadm := (hJ0 t htD).1
    have htJt := (hJ0 t htD).2
    refine ⟨J0 t, hadm.1, htJt, ?_⟩
    exact (ContMDiffOn.congr hadm.2.2.2.1.1
      (fun s hs => (hγeq _ _ hadm hs).symm)).mono Set.inter_subset_right
  have hγspeed : ∀ t ∈ D, omCurveSpeedSq g γ t = 1 := by
    intro t htD
    have hadm := (hJ0 t htD).1
    have htJt := (hJ0 t htD).2
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) (δ0 t) t :=
      (hadm.2.2.2.1.1.mdifferentiableOn (by simp)).mdifferentiableAt
        (hadm.1.mem_nhds htJt)
    have hev : γ =ᶠ[nhds t] (δ0 t) ∘ id :=
      Filter.eventuallyEq_of_mem (hadm.1.mem_nhds htJt)
        (fun s hs => (hγeq _ _ hadm hs).symm)
    have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g (δ0 t) id t
      differentiableAt_id hmd hev
    have h1 : omCurveSpeedSq g (δ0 t) (id t) = 1 := hadm.2.2.2.1.2 t htJt
    rw [hcomp, h1, (hasDerivAt_id t).deriv, one_pow, mul_one]
  have hγev : γ =ᶠ[nhds 0] ⇑α0 :=
    Filter.eventuallyEq_of_mem (α0.open_source.mem_nhds hα00)
      (fun s hs => (hγeq _ _ hα0adm hs).symm)
  have hγadm : omAdmissible g α0 D γ :=
    ⟨hDopen, hDconn, h0D, ⟨hγsmooth, hγspeed⟩, hγev⟩
  exact ⟨D, γ, hγadm, fun J δ h => ⟨hDsub J δ h, hγeq J δ h⟩⟩

end MaximalCurve

section AbsorbMaximal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

/-- Extension form of maximality: a unit-speed curve on an open connected set that
agrees with the maximal curve near one common point is absorbed by it. -/
private theorem om_maximal_unitSpeed_absorb
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
    (D : Set ℝ) (γ : ℝ → M)
    (hDadm : omAdmissible g α0 D γ)
    (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J)
    (J : Set ℝ) (δ : ℝ → M)
    (hJopen : IsOpen J) (hJconn : J.OrdConnected)
    (hδ : omIsUnitSpeedOn g δ J)
    (t : ℝ) (ht : t ∈ D ∩ J) (hev : δ =ᶠ[nhds t] γ) :
    J ⊆ D ∧ Set.EqOn δ γ J := by
  classical
  obtain ⟨hDopen, hDconn, h0D, hγunit, hγev⟩ := hDadm
  have hDJopen : IsOpen (D ∩ J) := hDopen.inter hJopen
  have hDJconn := hDconn.inter hJconn
  have hDJpre : IsPreconnected (D ∩ J) := hDJconn.isPreconnected
  have hδDJ : omIsUnitSpeedOn g δ (D ∩ J) :=
    ⟨hδ.1.mono Set.inter_subset_right, fun s hs => hδ.2 s hs.2⟩
  have hγDJ : omIsUnitSpeedOn g γ (D ∩ J) :=
    ⟨hγunit.1.mono Set.inter_subset_left, fun s hs => hγunit.2 s hs.1⟩
  have hEqDJ : Set.EqOn δ γ (D ∩ J) :=
    om_eqOn_of_unitSpeed_of_eventuallyEq g (D ∩ J) hDJopen hDJpre δ γ
      hδDJ hγDJ t ht hev
  set J' : Set ℝ := D ∪ J
  set γ' : ℝ → M := fun s => if s ∈ D then γ s else δ s
  have hJ'open : IsOpen J' := hDopen.union hJopen
  have hJ'conn : J'.OrdConnected :=
    isPreconnected_iff_ordConnected.mp
      (IsPreconnected.union t ht.1 ht.2 hDconn.isPreconnected
        hJconn.isPreconnected)
  have h0J' : (0 : ℝ) ∈ J' := Or.inl h0D
  have hγ'eq : ∀ s, γ' s = (if s ∈ D then γ s else δ s) := fun s => rfl
  have hγ'D : Set.EqOn γ γ' D := fun s hs => by
    rw [hγ'eq s, ite_eq_left hs]
  have hγ'J : Set.EqOn δ γ' J := fun s hs => by
    by_cases hsD : s ∈ D
    · rw [hγ'eq s, ite_eq_left hsD]
      exact hEqDJ ⟨hsD, hs⟩
    · rw [hγ'eq s, ite_eq_right hsD]
  have hspeed_of : ∀ (U : Set ℝ) (β : ℝ → M), IsOpen U → omIsUnitSpeedOn g β U →
      Set.EqOn β γ' U → ∀ s ∈ U, omCurveSpeedSq g γ' s = 1 := by
    intro U β hUopen hβ hEq s hs
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) β s :=
      (hβ.1.mdifferentiableOn (by simp)).mdifferentiableAt (hUopen.mem_nhds hs)
    have hevS : γ' =ᶠ[nhds s] β ∘ id :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) (fun q hq => (hEq hq).symm)
    have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g β id s
      differentiableAt_id hmd hevS
    have h1 : omCurveSpeedSq g β (id s) = 1 := hβ.2 s hs
    rw [hcomp, h1, (hasDerivAt_id s).deriv, one_pow, mul_one]
  have hγ'smooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ' J' := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro s hs
    by_cases hsD : s ∈ D
    · refine ⟨D, hDopen, hsD, ?_⟩
      exact (ContMDiffOn.congr hγunit.1
        (fun q hq => (hγ'D hq).symm)).mono Set.inter_subset_right
    · have hsU : s ∈ D ∪ J := hs
      have hsJ : s ∈ J := (Set.mem_or_mem_of_mem_union hsU).resolve_left hsD
      refine ⟨J, hJopen, hsJ, ?_⟩
      exact (ContMDiffOn.congr hδ.1
        (fun q hq => (hγ'J hq).symm)).mono Set.inter_subset_right
  have hγ'speed : ∀ s ∈ J', omCurveSpeedSq g γ' s = 1 := by
    intro s hs
    by_cases hsD : s ∈ D
    · exact hspeed_of D γ hDopen hγunit hγ'D s hsD
    · have hsU : s ∈ D ∪ J := hs
      have hsJ : s ∈ J := (Set.mem_or_mem_of_mem_union hsU).resolve_left hsD
      exact hspeed_of J δ hJopen hδ hγ'J s hsJ
  have hγ'ev : γ' =ᶠ[nhds 0] ⇑α0 := by
    have h1 : γ' =ᶠ[nhds 0] γ :=
      Filter.eventuallyEq_of_mem (hDopen.mem_nhds h0D)
        (fun s hs => (hγ'D hs).symm)
    exact h1.trans hγev
  have hJ'adm : omAdmissible g α0 J' γ' :=
    ⟨hJ'open, hJ'conn, h0J', ⟨hγ'smooth, hγ'speed⟩, hγ'ev⟩
  have hsub := (hmax J' γ' hJ'adm).1
  have hJsub : J ⊆ D := Set.subset_union_right.trans hsub
  refine ⟨hJsub, fun s hs => ?_⟩
  exact hEqDJ ⟨hJsub hs, hs⟩

end AbsorbMaximal

section OntoMaximal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M] [ConnectedSpace M]

/-- The maximal unit-speed curve is onto. -/
private theorem om_maximal_unitSpeed_image_eq_univ
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
    (D : Set ℝ) (γ : ℝ → M)
    (hDadm : omAdmissible g α0 D γ)
    (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J) :
    γ '' D = Set.univ := by
  obtain ⟨hDopen, hDconnA, h0D, hγunit, hγevA⟩ := hDadm
  have hSopen : IsOpen (γ '' D) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨t, htD, rfl⟩
    exact om_image_mem_nhds_of_unitSpeed g D γ hDopen hγunit t htD D
      (hDopen.mem_nhds htD)
  have hSclosed : IsClosed (γ '' D) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨α, hαconn, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g y
    have hytgt : y ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
    have hfreqS : ∃ᶠ z in nhds y, z ∈ γ '' D := mem_closure_iff_frequently.mp hy
    have hmemT : α.target ∈ nhds y := α.open_target.mem_nhds hytgt
    obtain ⟨z, hzS, hzT⟩ := (hfreqS.and_eventually hmemT).exists
    obtain ⟨t1, ht1D, rfl⟩ := hzS
    obtain ⟨ε, hε, c, -, hev⟩ :=
      om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t1 ht1D hzT
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    set L : Set ℝ := {s | ε * s + c ∈ α.source}
    have hLopen : IsOpen L :=
      α.open_source.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hLimg : L = (fun u => ε * (u - c)) '' α.source := by
      ext s
      constructor
      · intro hs
        refine ⟨ε * s + c, hs, ?_⟩
        change ε * ((ε * s + c) - c) = s
        have hrr : ε * ((ε * s + c) - c) = (ε * ε) * s := by ring
        rw [hrr, hε2, one_mul]
      · rintro ⟨u, hu, rfl⟩
        change ε * (ε * (u - c)) + c ∈ α.source
        have hrr : ε * (ε * (u - c)) + c = u := by
          have h : ε * (ε * (u - c)) + c = (ε * ε) * (u - c) + c := by ring
          rw [h, hε2, one_mul, sub_add_cancel]
        rw [hrr]
        exact hu
    have hLconn : L.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hLimg ▸
        (hαconn.isPreconnected.image _
          (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn))
    set δ : ℝ → M := ⇑α ∘ (fun s => ε * s + c)
    have haffM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => ε * s + c) L :=
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn
    have hδsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ δ L :=
      α.contMDiffOn_toFun.comp haffM (fun s hs => hs)
    have hδspeed : ∀ s ∈ L, omCurveSpeedSq g δ s = 1 := by
      intro s hs
      have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) ⇑α (ε * s + c) :=
        α.mdifferentiableAt (by simp) hs
      have hk : DifferentiableAt ℝ (fun s => ε * s + c) s :=
        ((differentiableAt_const ε).mul differentiableAt_id).add (differentiableAt_const c)
      have hevS : δ =ᶠ[nhds s] ⇑α ∘ (fun s => ε * s + c) :=
        Filter.EventuallyEq.refl _ _
      have hcomp := om_curveSpeedSq_eq_of_eventuallyEq_comp g ⇑α _ s hk hmd hevS
      have h1 : omCurveSpeedSq g ⇑α (ε * s + c) = 1 := hαspeed _ hs
      have hder : deriv (fun s => ε * s + c) s = ε := by
        have h := (((hasDerivAt_id s).const_mul ε).add_const c).deriv
        rw [mul_one] at h
        exact h
      rw [hcomp, hder, h1, pow_two, hε2, mul_one]
    have ht1L : t1 ∈ L := (hev.self_of_nhds).1
    have hev1 : δ =ᶠ[nhds t1] γ := hev.mono fun s hs => (hs.2).symm
    have hprobe : omAdmissible g α0 D γ := ⟨hDopen, hDconnA, h0D, hγunit, hγevA⟩
    obtain ⟨hLsub, hEq⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax L δ
      hLopen hLconn ⟨hδsmooth, hδspeed⟩ t1 ⟨ht1D, ht1L⟩ hev1
    set sstar : ℝ := -ε * c
    have hsstar : ε * sstar + c = 0 := by
      change ε * (-ε * c) + c = 0
      have h : ε * (-ε * c) + c = (1 - ε * ε) * c := by ring
      rw [h, hε2, sub_self, zero_mul]
    have hsstarL : sstar ∈ L := by
      change ε * sstar + c ∈ α.source
      rw [hsstar]
      exact hα0mem
    have hmem : γ sstar = y := by
      have e1 : δ sstar = γ sstar := hEq hsstarL
      have e2 : δ sstar = α (ε * sstar + c) := rfl
      rw [← e1, e2, hsstar]
      exact hα0
    exact ⟨sstar, hLsub hsstarL, hmem⟩
  exact IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨γ 0, 0, h0D, rfl⟩

end OntoMaximal

section PeriodicCoincidence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M] [T2Space M]

/-- A coincidence forces a period and `D = ℝ`: if the maximal curve visits the
same point twice, the domain is everything and the curve is periodic. -/
private theorem om_maximal_unitSpeed_periodic_of_eq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞)
    (D : Set ℝ) (γ : ℝ → M)
    (hDadm : omAdmissible g α0 D γ)
    (hmax : ∀ J δ, omAdmissible g α0 J δ → J ⊆ D ∧ Set.EqOn δ γ J)
    (t1 t2 : ℝ) (ht1 : t1 ∈ D) (ht2 : t2 ∈ D) (hlt : t1 < t2)
    (heq : γ t1 = γ t2) :
    D = Set.univ ∧ ∀ s : ℝ, γ (s + (t2 - t1)) = γ s := by
  obtain ⟨hDopen, hDconn, h0D, hγunit, hγev⟩ := hDadm
  have hprobe : omAdmissible g α0 D γ := ⟨hDopen, hDconn, h0D, hγunit, hγev⟩
  set T : ℝ := t2 - t1 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  obtain ⟨α, hαconn, hα0mem, hα0, hαspeed⟩ := om_exists_unitSpeedChart g (γ t1)
  have hγt1 : γ t1 ∈ α.target := hα0 ▸ α.toPartialEquiv.map_source hα0mem
  have hγt2 : γ t2 ∈ α.target := heq ▸ hγt1
  obtain ⟨ε1, hε1, c1, hcen1, hev1⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t1 ht1 hγt1
  obtain ⟨ε2, hε2, c2, hcen2, hev2⟩ :=
    om_exists_affine_of_unitSpeed g α hαspeed D γ hDopen hγunit t2 ht2 hγt2
  have hcenter : ε1 * t1 + c1 = ε2 * t2 + c2 := by
    rw [hcen1, hcen2, heq]
  -- Shifted curves `γ ∘ (slope * · + shift)` on the preimage domain are unit-speed.
  have hshift : ∀ (e d : ℝ), e * e = 1 → ∀ (U : Set ℝ) (δk : ℝ → M),
      IsOpen U → U = (fun s => e * s + d) ⁻¹' D →
      δk = γ ∘ (fun s => e * s + d) → omIsUnitSpeedOn g δk U := by
    intro e d he2 U δk hUopen hUeq hδkeq
    have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => e * s + d) U :=
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn
    have hmaps : Set.MapsTo (fun s => e * s + d) U D := by
      intro s hs
      have hs' : s ∈ (fun s => e * s + d) ⁻¹' D := by rwa [← hUeq]
      exact hs'
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ (γ ∘ (fun s => e * s + d)) U :=
      hγunit.1.comp hinner hmaps
    constructor
    · rwa [hδkeq]
    · intro s hs
      have hsD : e * s + d ∈ D := by
        have hs' : s ∈ (fun s => e * s + d) ⁻¹' D := by rwa [← hUeq]
        exact hs'
      have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ (e * s + d) :=
        (hγunit.1.mdifferentiableOn (by simp)).mdifferentiableAt (hDopen.mem_nhds hsD)
      have hk : DifferentiableAt ℝ (fun s => e * s + d) s :=
        ((differentiableAt_const e).mul differentiableAt_id).add (differentiableAt_const d)
      have hevS : δk =ᶠ[nhds s] γ ∘ (fun s => e * s + d) := by
        rw [hδkeq]
      have hcomp2 := om_curveSpeedSq_eq_of_eventuallyEq_comp g γ _ s hk hmd hevS
      have h1 : omCurveSpeedSq g γ ((fun s => e * s + d) s) = 1 := hγunit.2 _ hsD
      have hder : deriv (fun s => e * s + d) s = e := by
        have h := (((hasDerivAt_id s).const_mul e).add_const d).deriv
        rw [mul_one] at h
        exact h
      rw [hcomp2, hder, h1, pow_two, he2, mul_one]
  rcases eq_or_ne ε1 ε2 with hεeq | hεne
  · -- Translation case: the orientations agree, so `T` is a period.
    rw [hεeq] at hcenter
    set Jp : Set ℝ := (fun s => 1 * s + T) ⁻¹' D
    set Jm : Set ℝ := (fun s => 1 * s + -T) ⁻¹' D
    set dp : ℝ → M := γ ∘ (fun s => 1 * s + T)
    set dm : ℝ → M := γ ∘ (fun s => 1 * s + -T)
    have hJpopen : IsOpen Jp :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hJmopen : IsOpen Jm :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hJpimg : Jp = (fun u => 1 * u - T) '' D := by
      ext s
      constructor
      · intro hs
        change 1 * s + T ∈ D at hs
        refine ⟨1 * s + T, hs, ?_⟩
        change 1 * (1 * s + T) - T = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change 1 * ((fun u => 1 * u - T) u) + T ∈ D
        have hrr : (1:ℝ) * (1 * u - T) + T = u := by ring
        rw [hrr]
        exact hu
    have hJmimg : Jm = (fun u => 1 * u + T) '' D := by
      ext s
      constructor
      · intro hs
        change 1 * s + -T ∈ D at hs
        refine ⟨1 * s + -T, hs, ?_⟩
        change 1 * (1 * s + -T) + T = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change 1 * ((fun u => 1 * u + T) u) + -T ∈ D
        have hrr : (1:ℝ) * (1 * u + T) + -T = u := by ring
        rw [hrr]
        exact hu
    have hJpconn : Jp.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hJpimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.sub continuous_const).continuousOn))
    have hJmconn : Jm.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hJmimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.add continuous_const).continuousOn))
    have hδpunit : omIsUnitSpeedOn g dp Jp := hshift 1 T (mul_one 1) Jp dp hJpopen rfl rfl
    have hδmunit : omIsUnitSpeedOn g dm Jm := hshift 1 (-T) (mul_one 1) Jm dm hJmopen rfl rfl
    have h1t : (1:ℝ) * t1 + T = t2 := by rw [hTdef]; ring
    have h1tm : (1:ℝ) * t2 + -T = t1 := by rw [hTdef]; ring
    have htendp : Filter.Tendsto (fun s => 1 * s + T) (nhds t1) (nhds (1 * t1 + T)) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    have htendm : Filter.Tendsto (fun s => 1 * s + -T) (nhds t2) (nhds (1 * t2 + -T)) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    rw [h1t] at htendp
    rw [h1tm] at htendm
    have haffid : ∀ s, ε2 * (1 * s + T) + c2 = ε2 * s + c1 := by
      intro s
      linear_combination -hcenter + ε2 * hTdef
    have haffidm : ∀ s, ε2 * (1 * s + -T) + c1 = ε2 * s + c2 := by
      intro s
      linear_combination hcenter - ε2 * hTdef
    have hptp : ∀ s, (ε1 * s + c1 ∈ α.source ∧ γ s = α (ε1 * s + c1)) →
        (ε2 * (1 * s + T) + c2 ∈ α.source ∧
          γ (1 * s + T) = α (ε2 * (1 * s + T) + c2)) →
        dp s = γ s := by
      intro s h1 h2
      have e : ε2 * (1 * s + T) + c2 = ε1 * s + c1 := by
        rw [hεeq]; exact haffid s
      calc dp s = γ (1 * s + T) := rfl
        _ = α (ε2 * (1 * s + T) + c2) := h2.2
        _ = α (ε1 * s + c1) := by rw [e]
        _ = γ s := (h1.2).symm
    have hptm : ∀ s, (ε2 * s + c2 ∈ α.source ∧ γ s = α (ε2 * s + c2)) →
        (ε1 * (1 * s + -T) + c1 ∈ α.source ∧
          γ (1 * s + -T) = α (ε1 * (1 * s + -T) + c1)) →
        dm s = γ s := by
      intro s h2 h1
      have e : ε1 * (1 * s + -T) + c1 = ε2 * s + c2 := by
        rw [hεeq]; exact haffidm s
      calc dm s = γ (1 * s + -T) := rfl
        _ = α (ε1 * (1 * s + -T) + c1) := h1.2
        _ = α (ε2 * s + c2) := by rw [e]
        _ = γ s := (h2.2).symm
    have ht1Jp : t1 ∈ Jp := by
      change (1:ℝ) * t1 + T ∈ D
      rw [h1t]
      exact ht2
    have ht2Jm : t2 ∈ Jm := by
      change (1:ℝ) * t2 + -T ∈ D
      rw [h1tm]
      exact ht1
    have hevJp : dp =ᶠ[nhds t1] γ :=
      (hev1.and (htendp.eventually hev2)).mono fun s hs => hptp s hs.1 hs.2
    have hevJm : dm =ᶠ[nhds t2] γ :=
      (hev2.and (htendm.eventually hev1)).mono fun s hs => hptm s hs.1 hs.2
    obtain ⟨hJpsub, hEqp⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Jp dp
      hJpopen hJpconn hδpunit t1 ⟨ht1, ht1Jp⟩ hevJp
    obtain ⟨hJmsub, -⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Jm dm
      hJmopen hJmconn hδmunit t2 ⟨ht2, ht2Jm⟩ hevJm
    have hmem_add : ∀ s ∈ D, s + T ∈ D := by
      intro s hs
      apply hJmsub
      change 1 * (s + T) + -T ∈ D
      have hrr : (1:ℝ) * (s + T) + -T = s := by ring
      rw [hrr]
      exact hs
    have hmem_sub : ∀ s ∈ D, s - T ∈ D := by
      intro s hs
      apply hJpsub
      change 1 * (s - T) + T ∈ D
      have hrr : (1:ℝ) * (s - T) + T = s := by ring
      rw [hrr]
      exact hs
    have hN : ∀ n : ℕ, t1 + (n : ℝ) * T ∈ D := by
      intro n
      induction n with
      | zero =>
        have h0 : t1 + ((0 : ℕ) : ℝ) * T = t1 := by simp
        rw [h0]
        exact ht1
      | succ k ih =>
        have hkk : t1 + ((k + 1 : ℕ) : ℝ) * T = (t1 + (k : ℝ) * T) + T := by
          push_cast
          ring
        rw [hkk]
        exact hmem_add _ ih
    have hNm : ∀ n : ℕ, t1 - (n : ℝ) * T ∈ D := by
      intro n
      induction n with
      | zero =>
        have h0 : t1 - ((0 : ℕ) : ℝ) * T = t1 := by simp
        rw [h0]
        exact ht1
      | succ k ih =>
        have hkk : t1 - ((k + 1 : ℕ) : ℝ) * T = (t1 - (k : ℝ) * T) - T := by
          push_cast
          ring
        rw [hkk]
        exact hmem_sub _ ih
    have hDuniv : D = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro s
      obtain ⟨n, hn⟩ := exists_nat_gt ((s - t1) / T)
      obtain ⟨m', hm'⟩ := exists_nat_gt ((t1 - s) / T)
      have hn' : s < t1 + (n : ℝ) * T := by
        have h2 : s - t1 < (n : ℝ) * T := by
          rwa [div_lt_iff₀ hTpos] at hn
        linarith
      have hm'' : t1 - (m' : ℝ) * T < s := by
        have h2 : t1 - s < (m' : ℝ) * T := by
          rwa [div_lt_iff₀ hTpos] at hm'
        linarith
      exact hDconn.uIcc_subset (hNm m') (hN n)
        (Set.mem_uIcc_of_le (le_of_lt hm'') (le_of_lt hn'))
    have hJpuniv : Jp = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro s
      change (1:ℝ) * s + T ∈ D
      rw [hDuniv]
      exact Set.mem_univ _
    have hper1 : ∀ s, γ (1 * s + T) = γ s := by
      intro s
      have hsJ : s ∈ Jp := by rw [hJpuniv]; exact Set.mem_univ s
      exact hEqp hsJ
    refine ⟨hDuniv, fun s => ?_⟩
    calc γ (s + T) = γ (1 * s + T) := by rw [one_mul]
      _ = γ s := hper1 s
  · -- Reflection case: symmetry about the midpoint contradicts local injectivity.
    have hneg : ε1 = -ε2 := by
      rcases hε1 with rfl | rfl <;> rcases hε2 with rfl | rfl
      · exact absurd rfl hεne
      · norm_num
      · norm_num
      · exact absurd rfl hεne
    set Lr : Set ℝ := (fun s => -1 * s + (t1 + t2)) ⁻¹' D
    set δr : ℝ → M := γ ∘ (fun s => -1 * s + (t1 + t2))
    have hLropen : IsOpen Lr :=
      hDopen.preimage ((continuous_const.mul continuous_id).add continuous_const)
    have hLrimg : Lr = (fun u => -1 * u + (t1 + t2)) '' D := by
      ext s
      constructor
      · intro hs
        change -1 * s + (t1 + t2) ∈ D at hs
        refine ⟨-1 * s + (t1 + t2), hs, ?_⟩
        change -1 * (-1 * s + (t1 + t2)) + (t1 + t2) = s
        ring
      · rintro ⟨u, hu, rfl⟩
        change -1 * ((fun u => -1 * u + (t1 + t2)) u) + (t1 + t2) ∈ D
        have hrr : (-1:ℝ) * (-1 * u + (t1 + t2)) + (t1 + t2) = u := by ring
        rw [hrr]
        exact hu
    have hLrconn : Lr.OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hLrimg ▸
        (hDconn.isPreconnected.image _
          (continuous_const.mul continuous_id |>.add continuous_const).continuousOn))
    have hneg11 : (-1:ℝ) * -1 = 1 := by rw [neg_mul_neg, mul_one]
    have hδrunit : omIsUnitSpeedOn g δr Lr :=
      hshift (-1) (t1 + t2) hneg11 Lr δr hLropen rfl rfl
    have h1tr : (-1:ℝ) * t1 + (t1 + t2) = t2 := by ring
    have htendr : Filter.Tendsto (fun s => -1 * s + (t1 + t2)) (nhds t1)
        (nhds (-1 * t1 + (t1 + t2))) :=
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto
    rw [h1tr] at htendr
    have ht1m : t1 + t2 - t1 = t2 := by ring
    have haffidr : ∀ s, ε2 * (-1 * s + (t1 + t2)) + c2 = ε1 * s + c1 := by
      intro s
      linear_combination -hcenter + (t1 - s) * hneg
    have hptr : ∀ s, (ε1 * s + c1 ∈ α.source ∧ γ s = α (ε1 * s + c1)) →
        (ε2 * (-1 * s + (t1 + t2)) + c2 ∈ α.source ∧
          γ (-1 * s + (t1 + t2)) = α (ε2 * (-1 * s + (t1 + t2)) + c2)) →
        δr s = γ s := by
      intro s h1 h2
      have e : ε2 * (-1 * s + (t1 + t2)) + c2 = ε1 * s + c1 := haffidr s
      calc δr s = γ (-1 * s + (t1 + t2)) := rfl
        _ = α (ε2 * (-1 * s + (t1 + t2)) + c2) := h2.2
        _ = α (ε1 * s + c1) := by rw [e]
        _ = γ s := (h1.2).symm
    have ht1Lr : t1 ∈ Lr := by
      change (-1:ℝ) * t1 + (t1 + t2) ∈ D
      rw [h1tr]
      exact ht2
    have hevr : δr =ᶠ[nhds t1] γ :=
      (hev1.and (htendr.eventually hev2)).mono fun s hs => hptr s hs.1 hs.2
    obtain ⟨-, hEqr⟩ := om_maximal_unitSpeed_absorb g α0 D γ hprobe hmax Lr δr
      hLropen hLrconn hδrunit t1 ⟨ht1, ht1Lr⟩ hevr
    set m : ℝ := (t1 + t2) / 2 with hmdef
    have hmuIcc : m ∈ Set.uIcc t1 t2 :=
      Set.mem_uIcc_of_le (by rw [hmdef]; linarith) (by rw [hmdef]; linarith)
    have hmD : m ∈ D := hDconn.uIcc_subset ht1 ht2 hmuIcc
    obtain ⟨ρ, hρpos, hρball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds hmD)
    have hsym : ∀ w : ℝ, 0 < w → w < ρ → γ (m + w) = γ (m - w) := by
      intro w hw0 hwρ
      have hm1 : m + w ∈ D := by
        apply hρball
        rw [Metric.mem_ball, dist_eq_norm]
        have hrr : (m + w) - m = w := by ring
        rw [hrr, Real.norm_eq_abs, abs_of_pos hw0]
        exact hwρ
      have hm2 : m - w ∈ D := by
        apply hρball
        rw [Metric.mem_ball, dist_eq_norm]
        have hrr : (m - w) - m = -w := by ring
        rw [hrr, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
      have hargw : t1 + t2 - (m + w) = m - w := by rw [hmdef]; ring
      have hLrw : m + w ∈ Lr := by
        change -1 * (m + w) + (t1 + t2) ∈ D
        rw [show (-1:ℝ) * (m + w) + (t1 + t2) = m - w from by ring]
        exact hm2
      have e : δr (m + w) = γ (m + w) := hEqr hLrw
      have e2 : δr (m + w) = γ (m - w) := by
        change γ (-1 * (m + w) + (t1 + t2)) = γ (m - w)
        rw [show (-1:ℝ) * (m + w) + (t1 + t2) = m - w from by ring]
      calc γ (m + w) = δr (m + w) := e.symm
        _ = γ (m - w) := e2
    obtain ⟨δ₀, hδ₀pos, hInj⟩ :=
      om_exists_injOn_of_unitSpeed g D γ hDopen hγunit m hmD
    set h : ℝ := min (δ₀ / 2) (ρ / 2) with hhdef
    have hhpos : 0 < h := lt_min (by linarith) (by linarith)
    have hδ : h < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hhρ : h < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hhm1 : m + h ∈ Set.Ioo (m - δ₀) (m + δ₀) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hhm2 : m - h ∈ Set.Ioo (m - δ₀) (m + δ₀) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    exfalso
    have hcontra := hInj hhm1 hhm2 (hsym h hhpos hhρ)
    have h0 : h = 0 := by linarith
    linarith

end PeriodicCoincidence

section MinimalPeriod

variable {M : Type*}

/-- The period set of a locally injective curve with the coincidence property is
generated by a minimal positive period. -/
private theorem om_exists_minimal_period
    (γ : ℝ → M) (δ : ℝ) (hδ : 0 < δ)
    (hinj : Set.InjOn γ (Set.Ioo (-δ) δ))
    (T : ℝ) (hT : T ≠ 0) (hperT : ∀ s, γ (s + T) = γ s)
    (hcoin : ∀ s t : ℝ, s ≠ t → γ s = γ t → ∀ u, γ (u + (t - s)) = γ u) :
    ∃ T0 : ℝ, 0 < T0 ∧ (∀ s, γ (s + T0) = γ s) ∧
      ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T0 := by
  have hadd : ∀ a b : ℝ, (∀ u, γ (u + a) = γ u) → (∀ u, γ (u + b) = γ u) →
      ∀ u, γ (u + (a + b)) = γ u := by
    intro a b ha hb u
    have h : u + (a + b) = (u + a) + b := by ring
    rw [h, hb, ha]
  have hneg : ∀ a : ℝ, (∀ u, γ (u + a) = γ u) → ∀ u, γ (u + -a) = γ u := by
    intro a ha u
    have h : u + -a + a = u := by ring
    have h2 := ha (u + -a)
    rw [h] at h2
    exact h2.symm
  set P : AddSubgroup ℝ :=
    { carrier := {T | ∀ u, γ (u + T) = γ u},
      add_mem' := fun {a b} ha hb => hadd a b ha hb,
      zero_mem' := fun u => by simp,
      neg_mem' := fun {a} ha => hneg a ha }
  have hTmem : T ∈ P := hperT
  have hdisc : ∀ x ∈ (P : Set ℝ), x ∈ Set.Ioo (-δ) δ → x = 0 := by
    intro x hxP hxI
    have hxP' : ∀ u, γ (u + x) = γ u := hxP
    have hx0 : γ x = γ 0 := by
      have h := hxP' 0
      rwa [zero_add] at h
    have hxI0 : (0:ℝ) ∈ Set.Ioo (-δ) δ :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    exact hinj hxI hxI0 hx0
  have hndense : ¬ Dense (P : Set ℝ) := by
    intro hd
    obtain ⟨x, hxP, hxI⟩ := hd.exists_between (show (0:ℝ) < δ from hδ)
    obtain ⟨hx0', -⟩ := Set.mem_Ioo.mp hxI
    have hxI' : x ∈ Set.Ioo (-δ) δ := by
      obtain ⟨hx0'', hxδ⟩ := Set.mem_Ioo.mp hxI
      exact Set.mem_Ioo.mpr ⟨by linarith, hxδ⟩
    have hx0 := hdisc x hxP hxI'
    linarith
  obtain ⟨a, ha'⟩ := P.isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (P.dense_or_isCyclic.resolve_left hndense)
  have ha : P = AddSubgroup.closure {a} :=
    ha'.symm.trans (AddSubgroup.zmultiples_eq_closure a)
  have ha0 : a ≠ 0 := by
    intro h0
    have hTmem' : T ∈ AddSubgroup.closure ({a} : Set ℝ) := by
      rwa [← ha]
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hTmem'
    rw [h0, smul_zero] at hn
    exact hT hn.symm
  set T0 : ℝ := |a| with hT0def
  have hT0pos : 0 < T0 := abs_pos.mpr ha0
  have haP : a ∈ P := by
    rw [ha]
    exact AddSubgroup.mem_closure_singleton_self a
  have hper_a : ∀ s, γ (s + a) = γ s := haP
  have hper_neg : ∀ s, γ (s + -a) = γ s := P.neg_mem haP
  have hper0 : ∀ s, γ (s + T0) = γ s := by
    rcases lt_or_gt_of_ne ha0 with ha' | ha'
    · have hT0a : T0 = -a := abs_of_neg ha'
      intro s
      rw [hT0a]
      exact hper_neg s
    · have hT0a : T0 = a := abs_of_nonneg (le_of_lt ha')
      intro s
      rw [hT0a]
      exact hper_a s
  have hiff : ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T0 := by
    intro s t
    constructor
    · intro hst
      by_cases hst' : s = t
      · refine ⟨0, ?_⟩
        rw [hst']
        simp
      · have hmem : t - s ∈ P := hcoin s t hst' hst
        have hmem' : t - s ∈ AddSubgroup.closure ({a} : Set ℝ) := by
          rwa [← ha]
        obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hmem'
        rcases lt_or_gt_of_ne ha0 with ha' | ha'
        · refine ⟨-n, ?_⟩
          have hT0a : T0 = -a := abs_of_neg ha'
          have hnn : (((-n : ℤ)) : ℝ) * -a = (n : ℝ) * a := by
            push_cast
            ring
          rw [hT0a, hnn, ← hn]
          exact zsmul_eq_mul _ _
        · refine ⟨n, ?_⟩
          have hT0a : T0 = a := abs_of_nonneg (le_of_lt ha')
          rw [hT0a, ← hn]
          exact zsmul_eq_mul _ _
    · intro hnt
      obtain ⟨n, hn⟩ := hnt
      have hper : Function.Periodic γ T0 := hper0
      have hstep := (hper.int_mul n) s
      have ht : t = s + (n : ℝ) * T0 := by linarith
      rw [ht]
      exact hstep.symm
  exact ⟨T0, hT0pos, hper0, hiff⟩

end MinimalPeriod

section CircleExpLocalDiffeo

/-- `Circle.exp` is a local diffeomorphism. Near each `θ₀`, with `w := Circle.exp θ₀`,
the map `θ ↦ Circle.exp θ` on `Ioo (θ₀ - π) (θ₀ + π)` has the smooth local inverse
`z ↦ θ₀ + arg (z * w⁻¹)` on the preimage of the slit plane; smoothness of the
inverse goes through the complex logarithm. -/
private theorem om_isLocalDiffeomorph_circleExp :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp := by
  intro θ₀
  have := finrank_real_complex_fact'
  set w : Circle := Circle.exp θ₀ with hw
  set f₁ : Circle → ℂ := fun z => ((z * w⁻¹ : Circle) : ℂ) with hf₁
  set U : Set ℝ := Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) with hU
  set V : Set Circle := f₁ ⁻¹' Complex.slitPlane with hV
  set L : Circle → ℝ := fun z => θ₀ + Complex.arg (f₁ z) with hL
  have hUopen : IsOpen U := isOpen_Ioo
  have hU0 : θ₀ ∈ U := Set.mem_Ioo.mpr
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmulW : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z * w⁻¹) :=
    contMDiff_mul_right
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  have hinner : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ f₁ := hcoe.comp hmulW
  have hf₁cont : Continuous f₁ := hinner.continuous
  have hVopen : IsOpen V := Complex.isOpen_slitPlane.preimage hf₁cont
  have hED : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp U :=
    (contMDiff_circleExp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp).contMDiffOn.mono
      (Set.subset_univ _)
  have hexpsub : ∀ θ : ℝ, Circle.exp θ * w⁻¹ = Circle.exp (θ - θ₀) := by
    intro θ
    rw [hw, ← div_eq_mul_inv, ← Circle.exp_sub]
  have hsubmem : ∀ θ ∈ U, θ - θ₀ ∈ Set.Ioo (-Real.pi) Real.pi := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) := hθ
    have hθII := Set.mem_Ioo.mp hθI
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hce : ∀ θ ∈ U, f₁ (Circle.exp θ) = ((Circle.exp (θ - θ₀) : Circle) : ℂ) := by
    intro θ hθ
    change ((Circle.exp θ * w⁻¹ : Circle) : ℂ) = _
    rw [hexpsub θ]
  have hargC : ∀ θ ∈ U, Complex.arg (((Circle.exp (θ - θ₀) : Circle)) : ℂ)
      = θ - θ₀ := by
    intro θ hθ
    have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
    exact Circle.arg_exp hmemI.1 (le_of_lt hmemI.2)
  have hMapsE : Set.MapsTo ⇑Circle.exp U V := by
    intro θ hθ
    have hzmem : f₁ (Circle.exp θ) ∈ Complex.slitPlane := by
      rw [hce θ hθ, Complex.mem_slitPlane_iff_arg]
      have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
      rw [hargC θ hθ]
      exact ⟨ne_of_lt hmemI.2, Circle.coe_ne_zero _⟩
    exact hzmem
  have hLeft : ∀ θ ∈ U, L (Circle.exp θ) = θ := by
    intro θ hθ
    have hmemI := Set.mem_Ioo.mp (hsubmem θ hθ)
    have h1 : L (Circle.exp θ) = θ₀ + (θ - θ₀) := by
      change θ₀ + Complex.arg (f₁ (Circle.exp θ)) = _
      rw [hce θ hθ, Circle.arg_exp hmemI.1 (le_of_lt hmemI.2)]
    rw [h1]
    ring
  have hRight : ∀ z ∈ V, Circle.exp (L z) = z := by
    intro z hz
    have h1 : L z = θ₀ + Complex.arg (((z * w⁻¹ : Circle)) : ℂ) := rfl
    rw [h1, Circle.exp_add, ← hw, Circle.exp_arg]
    change w * (z * w⁻¹) = z
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hMapsL : Set.MapsTo L V U := by
    intro z hz
    have hzmem : f₁ z ∈ Complex.slitPlane := hz
    have hne : Complex.arg (f₁ z) ≠ Real.pi :=
      (Complex.mem_slitPlane_iff_arg.mp hzmem).1
    have hlt : Complex.arg (f₁ z) < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi _) with h | h
      · exact h
      · exact absurd h hne
    have hgt : -Real.pi < Complex.arg (f₁ z) := Complex.neg_pi_lt_arg _
    have hmem : L z ∈ Set.Ioo (θ₀ - Real.pi) (θ₀ + Real.pi) := by
      rw [Set.mem_Ioo]
      change θ₀ - Real.pi < θ₀ + Complex.arg (f₁ z) ∧
        θ₀ + Complex.arg (f₁ z) < θ₀ + Real.pi
      constructor <;> linarith
    exact hmem
  have houter : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun c : ℂ => θ₀ + Complex.arg c) Complex.slitPlane := by
    have hlog : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
        (fun c : ℂ => θ₀ + (Complex.log c).im) Complex.slitPlane := by
      rw [contMDiffOn_iff_contDiffOn]
      intro c hc
      have h1 : ContDiffAt ℂ ∞ Complex.log c := Complex.contDiffAt_log hc
      have h2 : ContDiffAt ℝ ∞ Complex.log c := h1.restrict_scalars (𝕜 := ℝ)
      have h3' : ContDiffAt ℝ ∞ (fun c : ℂ => (Complex.log c).im) c :=
        (Complex.imCLM.contDiff.contDiffAt).comp c h2
      have h4 : ContDiffAt ℝ ∞ (fun c : ℂ => θ₀ + (Complex.log c).im) c :=
        contDiffAt_const.add h3'
      exact h4.contDiffWithinAt
    refine hlog.congr (fun c hc => ?_)
    show θ₀ + Complex.arg c = θ₀ + (Complex.log c).im
    rw [Complex.log_im]
  have hLD : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ L V := by
    have hinnerV : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℂ) ∞ f₁ V :=
      hinner.contMDiffOn.mono (Set.subset_univ _)
    have hcomp := houter.comp hinnerV (fun z hz => hz)
    exact hcomp.congr (fun z hz => rfl)
  exact odm_isLocalDiffeomorphAt_of_invOn ⇑Circle.exp L U V hUopen hVopen
    hMapsE hMapsL ⟨hLeft, hRight⟩ hED hLD θ₀ hU0

end CircleExpLocalDiffeo

section PeriodicCase

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]

/-- Periodic case: a surjective curve that is a local diffeomorphism everywhere and
whose coincidence set is exactly the lattice `T₀·ℤ` descends to a diffeomorphism
from `Circle`, via `z ↦ γ ((T₀/(2π)) * arg z)`. -/
private theorem om_nonempty_diffeomorph_circle_of_periodic
    (γ : ℝ → M) (hsurj : Function.Surjective γ)
    (hld : ∀ t : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t)
    (T₀ : ℝ) (hT₀ : 0 < T₀)
    (hiff : ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, t - s = n * T₀) :
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ M) := by
  have hT₀ne : T₀ ≠ 0 := ne_of_gt hT₀
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hperInt : ∀ (s : ℝ) (m : ℤ), γ (s + m * T₀) = γ s := by
    intro s m
    exact ((hiff s (s + m * T₀)).mpr ⟨m, by ring⟩).symm
  set c : ℝ := T₀ / (2 * Real.pi) with hc
  set G : Circle → M := fun z => γ (c * Complex.arg (z : ℂ)) with hG
  have hcc : (2 * Real.pi / T₀) * (T₀ / (2 * Real.pi)) = 1 := by
    rw [div_mul_div_comm, mul_comm T₀,
      div_self (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hT₀ne)]
  have hGexp : ∀ θ : ℝ, G (Circle.exp θ) = γ (c * θ) := by
    intro θ
    have harg : Circle.exp (Complex.arg ((Circle.exp θ : Circle) : ℂ))
        = Circle.exp θ :=
      Circle.exp_arg _
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp harg
    have hscale : c * Complex.arg ((Circle.exp θ : Circle) : ℂ)
        = c * θ + m * T₀ := by
      rw [hm, mul_add]
      congr 1
      rw [hc, mul_left_comm, div_mul_cancel₀ _ h2pi]
    have hGθ : G (Circle.exp θ)
        = γ (c * Complex.arg ((Circle.exp θ : Circle) : ℂ)) := rfl
    rw [hGθ, hscale]
    exact hperInt _ m
  have hGsurj : Function.Surjective G := by
    intro y
    obtain ⟨t, rfl⟩ := hsurj y
    refine ⟨Circle.exp (2 * Real.pi * t / T₀), ?_⟩
    rw [hGexp]
    have e : c * (2 * Real.pi * t / T₀) = t := by
      rw [hc]
      field_simp
    rw [e]
  have hGinj : Function.Injective G := by
    intro z₁ z₂ h
    have hγ : γ (c * Complex.arg (z₁ : ℂ)) = γ (c * Complex.arg (z₂ : ℂ)) := h
    obtain ⟨n, hn⟩ := (hiff _ _).mp hγ
    have hdiff : Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)
        = ↑n * (2 * Real.pi) := by
      have e : c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)) = ↑n * T₀ := by
        rw [mul_sub]
        exact hn
      have hT : (2 * Real.pi / T₀) * (c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)))
          = (2 * Real.pi / T₀) * (↑n * T₀) := congrArg _ e
      have hL : (2 * Real.pi / T₀) * (c * (Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ)))
          = Complex.arg (z₂ : ℂ) - Complex.arg (z₁ : ℂ) := by
        rw [hc, ← mul_assoc, hcc, one_mul]
      have hR : (2 * Real.pi / T₀) * (↑n * T₀) = ↑n * (2 * Real.pi) := by
        rw [mul_left_comm, div_mul_cancel₀ _ hT₀ne]
      rw [hL, hR] at hT
      exact hT
    have e1 : Circle.exp (Complex.arg (z₁ : ℂ)) = z₁ := Circle.exp_arg z₁
    have e2 : Circle.exp (Complex.arg (z₂ : ℂ)) = z₂ := Circle.exp_arg z₂
    have harg2 : Complex.arg (z₂ : ℂ)
        = Complex.arg (z₁ : ℂ) + ↑n * (2 * Real.pi) := by linarith [hdiff]
    rw [← e1, ← e2, harg2, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hGl : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ G := by
    intro z
    have hθ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Circle.exp
        (Complex.arg (z : ℂ)) :=
      om_isLocalDiffeomorph_circleExp _
    set ψ : Circle → ℝ := ⇑hθ.localInverse with hψ
    have hψl : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ ψ
        (⇑Circle.exp (Complex.arg (z : ℂ))) :=
      hθ.localInverse_isLocalDiffeomorphAt
    have hze : ⇑Circle.exp (Complex.arg (z : ℂ)) = z := Circle.exp_arg z
    rw [hze] at hψl
    set sc : ℝ → ℝ := fun t => c * t with hsc
    set iv : ℝ → ℝ := fun s => (2 * Real.pi / T₀) * s with hiv
    have hscD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ sc Set.univ :=
      (contDiff_const.mul contDiff_id).contMDiff.contMDiffOn
    have hivD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ iv Set.univ :=
      (contDiff_const.mul contDiff_id).contMDiff.contMDiffOn
    have hleft : ∀ x ∈ (Set.univ : Set ℝ), iv (sc x) = x := by
      intro x _
      change (2 * Real.pi / T₀) * (c * x) = x
      rw [← mul_assoc, hc, hcc, one_mul]
    have hright : ∀ y ∈ (Set.univ : Set ℝ), sc (iv y) = y := by
      intro y _
      change c * ((2 * Real.pi / T₀) * y) = y
      rw [← mul_assoc]
      have hcc₂ : c * (2 * Real.pi / T₀) = 1 := by
        rw [hc, div_mul_div_comm, mul_comm T₀,
          div_self (mul_ne_zero h2pi hT₀ne)]
      rw [hcc₂, one_mul]
    have hsc_ld : ∀ t' : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ sc t' := by
      intro t'
      exact odm_isLocalDiffeomorphAt_of_invOn sc iv Set.univ Set.univ
        isOpen_univ isOpen_univ (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
        ⟨hleft, hright⟩ hscD hivD t' (Set.mem_univ _)
    have hγsc : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ (sc (ψ z)) := hld _
    have hmid : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (sc ∘ ψ) z :=
      IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) hψl (hsc_ld _)
    have hcomp : IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ ((γ ∘ sc) ∘ ψ) z :=
      IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := M) hmid hγsc
    have hGeq : G =ᶠ[nhds z] ((γ ∘ sc) ∘ ψ) := by
      have hbase := hθ.localInverse_eventuallyEq_right
      rw [hze] at hbase
      filter_upwards [hbase] with z' hz'
      change G z' = γ (sc (ψ z'))
      have e1 : G z' = G (⇑Circle.exp (ψ z')) := by
        congr 1
        exact hz'.symm
      rw [e1, hGexp]
    exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hGeq
  exact ⟨hGl.diffeomorphOfBijective ⟨hGinj, hGsurj⟩⟩

end PeriodicCase

section BoundaryInterior

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M]

/-- The inclusion of the open half of `H` into `E1`, as an open partial homeomorphism.
Its target is the interior of the range of `𝓡∂ 1`. -/
private def omb_interiorModelHomeomorph :
    OpenPartialHomeomorph (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1)) :=
  OpenPartialHomeomorph.mk
    (PartialHomeomorph.mk
      { toFun := Subtype.val
        invFun := (𝓡∂ 1).symm
        source := {y | 0 < (y.val) 0}
        target := {y | 0 < y 0}
        map_source' := fun _ hy => hy
        map_target' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          change 0 < (((𝓡∂ 1).symm y).val) 0
          rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hy')]
          exact hy'
        left_inv' := by
          intro y _
          exact ModelWithCorners.left_inv (𝓡∂ 1) y
        right_inv' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          have hle : 0 ≤ y.ofLp 0 := le_of_lt hy'
          have hmem : y ∈ Set.range (𝓡∂ 1) := by
            rw [range_modelWithCornersEuclideanHalfSpace]
            exact hle
          have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
          simpa using h }
      (continuous_subtype_val.continuousOn)
      ((ModelWithCorners.continuous_symm (𝓡∂ 1)).continuousOn))
    ((PiLp.continuous_apply 2 _ 0 |>.comp continuous_subtype_val).isOpen_preimage _
      isOpen_Ioi)
    ((PiLp.continuous_apply 2 _ 0).isOpen_preimage _ isOpen_Ioi)

/-- The interior of `M` as an open subset. -/
private def ombInterior : TopologicalSpace.Opens M :=
  ⟨(𝓡∂ 1).interior M, (𝓡∂ 1).isOpen_interior (by simp : (∞ : ℕ∞ω) ≠ 0)⟩

private theorem omb_mem_ombInterior_iff (x : M) :
    x ∈ ombInterior M ↔ (𝓡∂ 1).IsInteriorPoint x :=
  Iff.rfl

/-- The interior carries `E1` charts: the `H` chart followed by `ι`. -/
private instance ombChartedSpaceInterior :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) ↥(ombInterior M) where
  atlas := Set.range fun x : ↥(ombInterior M) =>
    (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph
  chartAt x := (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph
  mem_chart_source := by
    intro x
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_chart_source _ x, ?_⟩
    have hx : (𝓡∂ 1).IsInteriorPoint (x.val) := x.2
    have hnhds := range_mem_nhds_isInteriorPoint hx
    have hmem : (𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) x) x) ∈
        interior (Set.range (𝓡∂ 1)) := by
      rw [mem_interior_iff_mem_nhds]
      exact hnhds
    rw [interior_range_modelWithCornersEuclideanHalfSpace 1] at hmem
    have hpos : 0 < (((chartAt (EuclideanHalfSpace 1) x) x).val).ofLp 0 := hmem
    exact hpos
  chart_mem_atlas := fun x => Set.mem_range_self x

private theorem omb_chartAt_ombInterior (x : ↥(ombInterior M)) :
    chartAt (EuclideanSpace ℝ (Fin 1)) x =
      (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph :=
  rfl

/-- Every `E1` atlas member is a translated `H` chart. -/
private theorem omb_atlas_mem_obtain
    (e : OpenPartialHomeomorph ↥(ombInterior M) (EuclideanSpace ℝ (Fin 1)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 1)) ↥(ombInterior M)) :
    ∃ x : ↥(ombInterior M),
      (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph = e :=
  he

/-- The transition between translated charts equals the `𝓡∂ 1` extended
coordinate change. -/
private theorem omb_trans_eq_extendCoordChange (x x' : ↥(ombInterior M)) :
    Set.EqOn
      ⇑(((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans omb_interiorModelHomeomorph))
      ⇑((𝓡∂ 1).extendCoordChange (chartAt (EuclideanHalfSpace 1) x)
        (chartAt (EuclideanHalfSpace 1) x'))
      ((((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans
          omb_interiorModelHomeomorph)).source) := by
  intro y _
  rfl

/-- The interior is a boundaryless `E1` manifold. -/
private instance ombIsManifoldInterior :
    IsManifold (𝓡 1) ∞ ↥(ombInterior M) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := omb_atlas_mem_obtain M e he
  obtain ⟨x', rfl⟩ := omb_atlas_mem_obtain M e' he'
  have hAmax : (chartAt (EuclideanHalfSpace 1) x) ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ ↥(ombInterior M) :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas _ x)
  have hA'max : (chartAt (EuclideanHalfSpace 1) x') ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ ↥(ombInterior M) :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas _ x')
  have hE := ModelWithCorners.contDiffOn_extendCoordChange hAmax hA'max
  have hfun := omb_trans_eq_extendCoordChange M x x'
  have hsub : ((((chartAt (EuclideanHalfSpace 1) x).trans
      omb_interiorModelHomeomorph).symm ≫ₕ
      ((chartAt (EuclideanHalfSpace 1) x').trans
        omb_interiorModelHomeomorph)).source) ⊆
      (((𝓡∂ 1).extendCoordChange (chartAt (EuclideanHalfSpace 1) x)
        (chartAt (EuclideanHalfSpace 1) x')).source) := by
    intro y hy
    rw [ModelWithCorners.extendCoordChange_source]
    rw [OpenPartialHomeomorph.trans_source] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [OpenPartialHomeomorph.symm_source] at hy1
    have himg : y ∈ ((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph) ''
        (((chartAt (EuclideanHalfSpace 1) x).trans
          omb_interiorModelHomeomorph).source) := by
      rw [OpenPartialHomeomorph.image_source_eq_target]
      exact hy1
    obtain ⟨z, hz, hzy⟩ := himg
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzA, hzι⟩ := hz
    have hzy' : omb_interiorModelHomeomorph
        ((chartAt (EuclideanHalfSpace 1) x) z) = y := hzy
    have hyι : y ∈ omb_interiorModelHomeomorph.target := by
      rw [← hzy']
      exact omb_interiorModelHomeomorph.map_source hzι
    have hyinv : omb_interiorModelHomeomorph.symm y =
        (chartAt (EuclideanHalfSpace 1) x) z := by
      rw [← hzy']
      exact omb_interiorModelHomeomorph.left_inv hzι
    have hsymsrc : omb_interiorModelHomeomorph.symm y ∈
        ((chartAt (EuclideanHalfSpace 1) x).symm ≫ₕ
          (chartAt (EuclideanHalfSpace 1) x')).source := by
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.symm_source, hyinv]
        exact (chartAt (EuclideanHalfSpace 1) x).map_source hzA
      · have hmem2 : ((chartAt (EuclideanHalfSpace 1) x).trans
            omb_interiorModelHomeomorph).symm y ∈
            ((chartAt (EuclideanHalfSpace 1) x').trans
              omb_interiorModelHomeomorph).source := hy2
        rw [OpenPartialHomeomorph.trans_source] at hmem2
        obtain ⟨hmem2A, -⟩ := hmem2
        have e2 : ((chartAt (EuclideanHalfSpace 1) x).trans
            omb_interiorModelHomeomorph).symm y = z := by
          change (chartAt (EuclideanHalfSpace 1) x).symm
            (omb_interiorModelHomeomorph.symm y) = z
          rw [hyinv]
          exact (chartAt (EuclideanHalfSpace 1) x).left_inv hzA
        rw [e2] at hmem2A
        have e3 : (chartAt (EuclideanHalfSpace 1) x).symm
            (omb_interiorModelHomeomorph.symm y) = z := by
          rw [hyinv]
          exact (chartAt (EuclideanHalfSpace 1) x).left_inv hzA
        rw [Set.mem_preimage, e3]
        exact hmem2A
    refine ⟨omb_interiorModelHomeomorph.symm y, hsymsrc, ?_⟩
    calc (𝓡∂ 1) (omb_interiorModelHomeomorph.symm y)
        = omb_interiorModelHomeomorph (omb_interiorModelHomeomorph.symm y) :=
          rfl
      _ = y := omb_interiorModelHomeomorph.right_inv hyι
  have hT : ContDiffOn ℝ ∞
      ⇑(((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans omb_interiorModelHomeomorph))
      ((((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans
          omb_interiorModelHomeomorph)).source) :=
    (hE.mono hsub).congr hfun
  refine ContDiffOn.congr_mono hT (fun z _ => ?_) (fun z hz => hz.1)
  rfl

/-- Retraction from `M` onto the interior subtype, defaulting to `x₀` outside. -/
private def ombRetract (x₀ : ↥(ombInterior M)) : M → ↥(ombInterior M) := by
  classical
  exact fun y => if h : y ∈ ombInterior M then ⟨y, h⟩ else x₀

private theorem ombRetract_of_mem (x₀ : ↥(ombInterior M)) (y : M)
    (h : y ∈ ombInterior M) : ombRetract M x₀ y = ⟨y, h⟩ := by
  unfold ombRetract
  split
  · rfl
  · next h' => exact (h' h).elim

/-- `Subtype.val` from the interior is smooth on every `E1` chart domain. -/
private theorem omb_contMDiffOn_val_of_mem_chartAt (x : ↥(ombInterior M)) :
    ContMDiffOn (𝓡 1) (𝓡∂ 1) ∞ (Subtype.val : ↥(ombInterior M) → M)
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source) := by
  have he : (chartAt (EuclideanSpace ℝ (Fin 1)) x) ∈
      IsManifold.maximalAtlas (𝓡 1) ∞ ↥(ombInterior M) :=
    IsManifold.chart_mem_maximalAtlas x
  have he' : (chartAt (EuclideanHalfSpace 1) (x.val)) ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (x.val)
  have h2s : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M)
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source)
      ((chartAt (EuclideanHalfSpace 1) (x.val)).source) := by
    intro w hw
    rw [omb_chartAt_ombInterior, OpenPartialHomeomorph.trans_source] at hw
    obtain ⟨hwA, -⟩ := hw
    rwa [TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] at hwA
  rw [contMDiffOn_iff_of_mem_maximalAtlas he he' (fun x hx => hx) h2s]
  refine ⟨continuous_subtype_val.continuousOn, ?_⟩
  have hEq : Set.EqOn (((chartAt (EuclideanHalfSpace 1) (x.val)).extend (𝓡∂ 1)) ∘
      (Subtype.val : ↥(ombInterior M) → M) ∘
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).symm) id
      (((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)) ''
        ((chartAt (EuclideanSpace ℝ (Fin 1)) x).source)) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hleft : ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).symm
        (((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)) w) = w :=
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x).extend (𝓡 1)).left_inv (by
        rwa [OpenPartialHomeomorph.extend_source])
    simp only [Function.comp_apply, hleft]
    rfl
  exact contDiffOn_id.congr hEq

/-- `Subtype.val` from the interior is smooth everywhere. -/
private theorem omb_contMDiffOn_val :
    ContMDiffOn (𝓡 1) (𝓡∂ 1) ∞ (Subtype.val : ↥(ombInterior M) → M)
      Set.univ := by
  intro x _
  have hW := omb_contMDiffOn_val_of_mem_chartAt M x
  have hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) x).source :=
    mem_chart_source _ x
  have hxnhds : (chartAt (EuclideanSpace ℝ (Fin 1)) x).source ∈ nhds x :=
    (chartAt (EuclideanSpace ℝ (Fin 1)) x).open_source.mem_nhds hx
  exact (hW.contMDiffAt hxnhds).contMDiffWithinAt

/-- Points of an `H` chart domain lying in the interior have positive coordinate. -/
private theorem omb_coord_pos_of_mem_source (y₀ y : M)
    (hy : y ∈ (chartAt (EuclideanHalfSpace 1) y₀).source)
    (hint : (𝓡∂ 1).IsInteriorPoint y) :
    0 < (((chartAt (EuclideanHalfSpace 1) y₀) y).val).ofLp 0 := by
  have h1 := (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := ∞)
    (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas _ y₀) hy).mp hint
  have h2 := OpenPartialHomeomorph.interior_extend_target_subset_interior_range
    (f := chartAt (EuclideanHalfSpace 1) y₀) (I := (𝓡∂ 1)) h1
  rw [interior_range_modelWithCornersEuclideanHalfSpace 1] at h2
  have h3 : 0 < ((𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) y₀) y)).ofLp 0 := h2
  have h4 : (𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) y₀) y) =
      (((chartAt (EuclideanHalfSpace 1) y₀) y).val :
        EuclideanSpace ℝ (Fin 1)) := rfl
  rw [h4] at h3
  exact h3

/-- An `H` chart on the interior subtype, applied to a coerced point. -/
private theorem omb_opens_chartAt_apply (u w : ↥(ombInterior M)) :
    (chartAt (EuclideanHalfSpace 1) u) w =
      (chartAt (EuclideanHalfSpace 1) (u.val)) (w.val) :=
  rfl

/-- The retract is smooth on each `H` chart domain intersected with the interior. -/
private theorem omb_contMDiffOn_retract_of_mem (x₀ : ↥(ombInterior M)) (y : M)
    (hy : y ∈ (ombInterior M : Set M)) :
    ContMDiffOn (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀)
      ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M)) := by
  have hyO : y ∈ ombInterior M := SetLike.mem_coe.mp hy
  have he : (chartAt (EuclideanHalfSpace 1) y) ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ M :=
    IsManifold.chart_mem_maximalAtlas y
  have he' : (chartAt (EuclideanSpace ℝ (Fin 1)) (⟨y, hyO⟩ : ↥(ombInterior M))) ∈
      IsManifold.maximalAtlas (𝓡 1) ∞ ↥(ombInterior M) :=
    IsManifold.chart_mem_maximalAtlas _
  have h2s : Set.MapsTo (ombRetract M x₀)
      ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M))
      ((chartAt (EuclideanSpace ℝ (Fin 1)) (⟨y, hyO⟩ : ↥(ombInterior M))).source) := by
    intro w hw
    obtain ⟨hwA, hwS⟩ := hw
    have hwO : w ∈ ombInterior M := SetLike.mem_coe.mp hwS
    rw [ombRetract_of_mem M x₀ w hwO, omb_chartAt_ombInterior,
      OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage]
      exact hwA
    · rw [Set.mem_preimage, omb_opens_chartAt_apply]
      have hpos := omb_coord_pos_of_mem_source M y w hwA hwO
      exact hpos
  rw [contMDiffOn_iff_of_mem_maximalAtlas' he he' Set.inter_subset_left h2s]
  have hEq : Set.EqOn (((chartAt (EuclideanSpace ℝ (Fin 1))
      (⟨y, hyO⟩ : ↥(ombInterior M))).extend (𝓡 1)) ∘ (ombRetract M x₀) ∘
      ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).symm) id
      (((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)) ''
        ((chartAt (EuclideanHalfSpace 1) y).source ∩ ↑(ombInterior M))) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hwA, hwS⟩ := hw
    have hwO : w ∈ ombInterior M := SetLike.mem_coe.mp hwS
    have hleft : ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).symm
        (((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)) w) = w :=
      ((chartAt (EuclideanHalfSpace 1) y).extend (𝓡∂ 1)).left_inv (by
        rwa [OpenPartialHomeomorph.extend_source])
    simp only [Function.comp_apply, hleft, ombRetract_of_mem M x₀ w hwO]
    rfl
  exact contDiffOn_id.congr hEq

/-- The retract is smooth on the interior. -/
private theorem omb_contMDiffOn_retract (x₀ : ↥(ombInterior M)) :
    ContMDiffOn (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀) ↑(ombInterior M) := by
  intro y hy
  have hW := omb_contMDiffOn_retract_of_mem M x₀ y hy
  have hymem : y ∈ (chartAt (EuclideanHalfSpace 1) y).source ∩
      ↑(ombInterior M) :=
    ⟨mem_chart_source _ y, hy⟩
  have hynnhds : (chartAt (EuclideanHalfSpace 1) y).source ∩
      ↑(ombInterior M) ∈ nhds y :=
    Filter.inter_mem ((chartAt (EuclideanHalfSpace 1) y).open_source.mem_nhds
      (mem_chart_source _ y)) ((ombInterior M).2.mem_nhds
        (SetLike.mem_coe.mp hy))
  exact (hW.contMDiffAt hynnhds).contMDiffWithinAt

/-- `Subtype.val` from the interior extends to a partial diffeomorphism. -/
private theorem omb_exists_partialDiffeomorph_val (x₀ : ↥(ombInterior M)) :
    ∃ Φ : PartialDiffeomorph (𝓡 1) (𝓡∂ 1) ↥(ombInterior M) M ∞,
      Φ.source = Set.univ ∧ Φ.target = ↑(ombInterior M) ∧
        (⇑Φ : ↥(ombInterior M) → M) = Subtype.val ∧
        Set.EqOn ⇑Φ.symm (ombRetract M x₀) ↑(ombInterior M) := by
  have hf : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M) Set.univ
      ↑(ombInterior M) := fun x _ => x.2
  have hf' : Set.MapsTo (ombRetract M x₀) ↑(ombInterior M) Set.univ :=
    Set.mapsTo_univ _ _
  have hInv : Set.InvOn (ombRetract M x₀)
      (Subtype.val : ↥(ombInterior M) → M) Set.univ ↑(ombInterior M) := by
    refine ⟨?_, ?_⟩
    · intro x _
      rw [ombRetract_of_mem M x₀ _ x.2]
    · intro y hy
      have hyO : y ∈ ombInterior M := SetLike.mem_coe.mp hy
      rw [ombRetract_of_mem M x₀ y hyO]
  exact odm_exists_partialDiffeomorph_of_invOn _ _ _ _ isOpen_univ
    (ombInterior M).2 hf hf' hInv (omb_contMDiffOn_val M)
    (omb_contMDiffOn_retract M x₀)

/-- `Subtype.val` from the interior is a local diffeomorphism. -/
private theorem omb_isLocalDiffeomorph_val (x₀ : ↥(ombInterior M)) :
    IsLocalDiffeomorph (𝓡 1) (𝓡∂ 1) ∞
      (Subtype.val : ↥(ombInterior M) → M) := by
  obtain ⟨Φ, hsrc, -, hfun, -⟩ := omb_exists_partialDiffeomorph_val M x₀
  intro x
  have hx : x ∈ Φ.source := by rw [hsrc]; exact Set.mem_univ x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 1) (𝓡∂ 1) ∞ Φ hx
  rw [hfun] at h
  exact h

/-- The retract is a local diffeomorphism at every interior point. -/
private theorem omb_isLocalDiffeomorphAt_retract (x₀ : ↥(ombInterior M))
    (y : M) (hy : y ∈ (ombInterior M : Set M)) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀) y := by
  have hf : Set.MapsTo (ombRetract M x₀) ↑(ombInterior M) Set.univ :=
    Set.mapsTo_univ _ _
  have hf' : Set.MapsTo (Subtype.val : ↥(ombInterior M) → M) Set.univ
      ↑(ombInterior M) := fun x _ => x.2
  have hInv : Set.InvOn (Subtype.val : ↥(ombInterior M) → M)
      (ombRetract M x₀) ↑(ombInterior M) Set.univ := by
    refine ⟨?_, ?_⟩
    · intro z hz
      have hzO : z ∈ ombInterior M := SetLike.mem_coe.mp hz
      rw [ombRetract_of_mem M x₀ z hzO]
    · intro x _
      rw [ombRetract_of_mem M x₀ _ x.2]
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ (ombInterior M).2 isOpen_univ
    hf hf' hInv (omb_contMDiffOn_retract M x₀) (omb_contMDiffOn_val M) y hy

/-- The half-chart curve at a boundary point: the chart inverse applied to the
ray `t ↦ t` in the model. -/
private def ombHalfCurve (p : M) : ℝ → M :=
  fun t => (chartAt (EuclideanHalfSpace 1) p).symm ((𝓡∂ 1).symm (omLinEquiv t))

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- At a boundary point, the chart sends `p` to the corner `0`. -/
private theorem omb_chartAt_boundary_val (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ((((chartAt (EuclideanHalfSpace 1) p) p).val :
      EuclideanSpace ℝ (Fin 1))) = 0 := by
  have h := ModelWithCorners.isBoundaryPoint_iff.mp hp
  rw [frontier_range_modelWithCornersEuclideanHalfSpace 1] at h
  have h' : 0 = (extChartAt (𝓡∂ 1) p p).ofLp 0 := h
  have heq : extChartAt (𝓡∂ 1) p p =
      ((((chartAt (EuclideanHalfSpace 1) p) p).val :
        EuclideanSpace ℝ (Fin 1))) := rfl
  rw [heq] at h'
  have hcoord : ((((chartAt (EuclideanHalfSpace 1) p) p).val :
      EuclideanSpace ℝ (Fin 1))).ofLp 0 = 0 := h'.symm
  apply PiLp.ext
  intro i
  fin_cases i
  simpa using hcoord

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The model ray at `0` hits the chart value of `p`. -/
private theorem omb_symm_ray_zero (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    (𝓡∂ 1).symm (omLinEquiv 0) = (chartAt (EuclideanHalfSpace 1) p) p := by
  have hvec := omb_chartAt_boundary_val M p hp
  rw [map_zero]
  have hsym0 : (𝓡∂ 1).symm (0 : EuclideanSpace ℝ (Fin 1)) =
      (⟨0, le_refl _⟩ : EuclideanHalfSpace 1) :=
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_refl _)
  rw [hsym0]
  apply Subtype.ext
  rw [hvec]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve starts at `p`. -/
private theorem omb_halfCurve_zero (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : ombHalfCurve M p 0 = p := by
  simp only [ombHalfCurve]
  rw [omb_symm_ray_zero M p hp]
  exact (chartAt (EuclideanHalfSpace 1) p).left_inv (mem_chart_source _ p)

/-- Good radius bundle for the half-chart curve at `p`. -/
private def ombGoodRadius (p : M) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    ∀ t : ℝ, |t| < ε → (𝓡∂ 1).symm (omLinEquiv t) ∈
      (chartAt (EuclideanHalfSpace 1) p).target

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Radius on which the model ray stays in the chart target. -/
private theorem omb_exists_halfCurve_radius (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ∃ ε, ombGoodRadius M p ε := by
  have hmem : (𝓡∂ 1).symm (omLinEquiv 0) ∈
      (chartAt (EuclideanHalfSpace 1) p).target := by
    rw [omb_symm_ray_zero M p hp]
    exact mem_chart_target _ p
  have hcont : Continuous (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) :=
    (ModelWithCorners.continuous_symm (𝓡∂ 1)).comp omLinEquiv.continuous
  have hopen : IsOpen ((fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) ⁻¹'
      (chartAt (EuclideanHalfSpace 1) p).target) :=
    (chartAt (EuclideanHalfSpace 1) p).open_target.preimage hcont
  obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  refine ⟨min δ (1 / 2), lt_min hδpos (by norm_num), min_le_right _ _, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
  simpa using hle

/-- The single coordinate of `omLinEquiv t` is `t`. -/
private theorem ombLinEquiv_coord (t : ℝ) : (omLinEquiv t).ofLp 0 = t := rfl

/-- For `t ≥ 0`, the model ray lands on the coercion. -/
private theorem omb_symm_ray_val_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    (((𝓡∂ 1).symm (omLinEquiv t)).val : EuclideanSpace ℝ (Fin 1)) =
      omLinEquiv t := by
  have hle : 0 ≤ (omLinEquiv t).ofLp 0 := by
    rw [ombLinEquiv_coord t]
    exact ht
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hle]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve is continuous on the symmetric interval. -/
private theorem omb_halfCurve_continuousOn (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    ContinuousOn (ombHalfCurve M p) (Set.Ioo (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) :=
    (ModelWithCorners.continuous_symm (𝓡∂ 1)).comp omLinEquiv.continuous
  have hmaps : Set.MapsTo (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t))
      (Set.Ioo (-ε) ε) (chartAt (EuclideanHalfSpace 1) p).target := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    have habs : |t| < ε := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact hε.2.2 t habs
  exact (chartAt (EuclideanHalfSpace 1) p).continuousOn_symm.comp
    hcont.continuousOn hmaps

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve tends to `p` from the right. -/
private theorem omb_halfCurve_tendsto (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    Filter.Tendsto (ombHalfCurve M p) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε :=
    ⟨by linarith [hε.1], hε.1⟩
  have hcat : ContinuousAt (ombHalfCurve M p) 0 :=
    (omb_halfCurve_continuousOn M p ε hε).continuousAt
      (isOpen_Ioo.mem_nhds hmem0)
  have htend : Filter.Tendsto (ombHalfCurve M p) (nhds 0)
      (nhds (ombHalfCurve M p 0)) := hcat
  rw [omb_halfCurve_zero M p hp] at htend
  exact htend.mono_left nhdsWithin_le_nhds

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Vectors in `E1` are determined by their single coordinate. -/
private theorem omb_E1_ext {v w : EuclideanSpace ℝ (Fin 1)}
    (h : v.ofLp 0 = w.ofLp 0) : v = w := by
  apply PiLp.ext
  intro i
  fin_cases i
  simpa using h

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Image of the half-chart curve on an initial interval. -/
private theorem omb_halfCurve_image_Ico (p : M) (ε δ : ℝ)
    (hε : ombGoodRadius M p ε) (hδε : δ ≤ ε) :
    (ombHalfCurve M p) '' Set.Ico 0 δ =
      (chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | (y.val).ofLp 0 < δ} := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, htδ⟩, rfl⟩
    have htabs : |t| < ε := by
      rw [abs_of_nonneg ht0]
      exact lt_of_lt_of_le htδ hδε
    have hT := hε.2.2 t htabs
    have hsrc : (chartAt (EuclideanHalfSpace 1) p).symm
        ((𝓡∂ 1).symm (omLinEquiv t)) ∈
        (chartAt (EuclideanHalfSpace 1) p).source :=
      (chartAt (EuclideanHalfSpace 1) p).map_target hT
    refine ⟨hsrc, ?_⟩
    have hchart : (chartAt (EuclideanHalfSpace 1) p)
        ((chartAt (EuclideanHalfSpace 1) p).symm
          ((𝓡∂ 1).symm (omLinEquiv t))) =
        (𝓡∂ 1).symm (omLinEquiv t) :=
      (chartAt (EuclideanHalfSpace 1) p).right_inv hT
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ombHalfCurve]
    rw [hchart, omb_symm_ray_val_of_nonneg t ht0, ombLinEquiv_coord]
    exact htδ
  · rintro ⟨hxsrc, hxmem⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
    set t : ℝ := (((chartAt (EuclideanHalfSpace 1) p) x).val).ofLp 0 with ht
    have ht0 : 0 ≤ t := ((chartAt (EuclideanHalfSpace 1) p) x).property
    have htδ : t < δ := hxmem
    have htabs : |t| < ε := by
      rw [abs_of_nonneg ht0]
      exact lt_of_lt_of_le htδ hδε
    have hT := hε.2.2 t htabs
    have htIco : t ∈ Set.Ico 0 δ := ⟨ht0, htδ⟩
    refine ⟨t, htIco, ?_⟩
    simp only [ombHalfCurve]
    have hval : (((𝓡∂ 1).symm (omLinEquiv t)).val :
        EuclideanSpace ℝ (Fin 1)) =
        (((chartAt (EuclideanHalfSpace 1) p) x).val :
        EuclideanSpace ℝ (Fin 1)) := by
      rw [omb_symm_ray_val_of_nonneg t ht0]
      apply omb_E1_ext
      rw [ombLinEquiv_coord]
    have hH : (𝓡∂ 1).symm (omLinEquiv t) =
        (chartAt (EuclideanHalfSpace 1) p) x :=
      EuclideanHalfSpace.ext _ _ hval
    rw [hH]
    exact (chartAt (EuclideanHalfSpace 1) p).left_inv hxsrc

/-- Positive parameters land in the interior. -/
private theorem omb_halfCurve_mem_interior (p : M) (ε t : ℝ)
    (hε : ombGoodRadius M p ε) (ht : t ∈ Set.Ioo 0 ε) :
    ombHalfCurve M p t ∈ ombInterior M := by
  rw [omb_mem_ombInterior_iff]
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  set e := chartAt (EuclideanHalfSpace 1) p with he
  have hsrc : ombHalfCurve M p t ∈ e.source := by
    simp only [ombHalfCurve]
    exact e.map_target hT
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := ∞)
    (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas _ p) hsrc]
  have hext : e.extend (𝓡∂ 1) (ombHalfCurve M p t) = omLinEquiv t := by
    simp only [ombHalfCurve, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply]
    rw [e.right_inv hT]
    have hmem : omLinEquiv t ∈ Set.range (𝓡∂ 1) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ (omLinEquiv t).ofLp 0
      rw [ombLinEquiv_coord]
      exact ht.1.le
    have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
    simpa using h
  rw [hext, OpenPartialHomeomorph.extend_target]
  have hopen : IsOpen ((𝓡∂ 1).symm ⁻¹' e.target) :=
    e.open_target.preimage (ModelWithCorners.continuous_symm (𝓡∂ 1))
  rw [interior_inter, hopen.interior_eq,
    interior_range_modelWithCornersEuclideanHalfSpace 1]
  refine ⟨?_, ?_⟩
  · exact hT
  · change 0 < (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1

/-- A boundary point is not in the interior. -/
private theorem omb_boundary_not_mem_interior (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : p ∉ ombInterior M := by
  rw [omb_mem_ombInterior_iff]
  have h := (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint p).mp hp
  exact h

/-- Model identity: the ray meets the left Icc chart. -/
private theorem omb_symm_leftChart (z : Set.Icc (0 : ℝ) 1) :
    (𝓡∂ 1).symm (omLinEquiv z.val) = IccLeftChart 0 1 z := by
  have hnonneg : 0 ≤ (z.val : ℝ) := z.property.1
  apply EuclideanHalfSpace.ext
  rw [omb_symm_ray_val_of_nonneg _ hnonneg]
  apply omb_E1_ext
  rw [ombLinEquiv_coord, IccLeftChart_apply]
  simp

/-- Model identity: the ray meets the right Icc chart. -/
private theorem omb_symm_rightChart (z : Set.Icc (0 : ℝ) 1) :
    (𝓡∂ 1).symm (omLinEquiv (1 - z.val)) = IccRightChart 0 1 z := by
  have hnonneg : 0 ≤ (1 - z.val : ℝ) := by
    have hle : z.val ≤ 1 := z.property.2
    linarith
  apply EuclideanHalfSpace.ext
  rw [omb_symm_ray_val_of_nonneg _ hnonneg]
  apply omb_E1_ext
  rw [ombLinEquiv_coord, IccRightChart_apply]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve meets the left Icc chart. -/
private theorem omb_halfCurve_leftChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p z.val =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccLeftChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_leftChart]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The reflected half-chart curve meets the right Icc chart. -/
private theorem omb_halfCurve_rightChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p (1 - z.val) =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccRightChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_rightChart]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The target box for the half-chart inverse is open. -/
private theorem omb_halfCurve_V_open (p : M) (ε : ℝ) :
    IsOpen ((chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  apply (chartAt (EuclideanHalfSpace 1) p).isOpen_inter_preimage
  have hcont : Continuous (fun y : EuclideanHalfSpace 1 => (y.val) 0) :=
    (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
  have : {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε} =
      (fun y : EuclideanHalfSpace 1 => (y.val) 0) ⁻¹' Set.Ioo 0 ε := rfl
  rw [this]
  exact isOpen_Ioo.preimage hcont

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The inverse of the half-chart curve reads off the model coordinate. -/
private def ombHalfCurveInv (p : M) : M → ℝ :=
  fun y => omLinEquiv.symm ((𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) p) y))

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve maps the open interval into the target box. -/
private theorem omb_halfCurve_maps_fwd (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    Set.MapsTo (ombHalfCurve M p) (Set.Ioo 0 ε)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  have hsrc : ombHalfCurve M p t ∈ (chartAt (EuclideanHalfSpace 1) p).source := by
    simp only [ombHalfCurve]
    exact (chartAt (EuclideanHalfSpace 1) p).map_target hT
  refine ⟨hsrc, ?_⟩
  have hchart : (chartAt (EuclideanHalfSpace 1) p) (ombHalfCurve M p t) =
      (𝓡∂ 1).symm (omLinEquiv t) := by
    simp only [ombHalfCurve]
    exact (chartAt (EuclideanHalfSpace 1) p).right_inv hT
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hchart, omb_symm_ray_val_of_nonneg t ht.1.le, ombLinEquiv_coord]
  exact ht

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The coordinate map is a left inverse on the open interval. -/
private theorem omb_halfCurve_left_inv (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    ombHalfCurveInv M p (ombHalfCurve M p t) = t := by
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  simp only [ombHalfCurveInv, ombHalfCurve,
    (chartAt (EuclideanHalfSpace 1) p).right_inv hT]
  have hmem : omLinEquiv t ∈ Set.range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1.le
  have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
  have h2 : (𝓡∂ 1) ((𝓡∂ 1).symm (omLinEquiv t)) = omLinEquiv t := h
  rw [h2]
  exact omLinEquiv.symm_apply_apply t

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve is a right inverse on the target box. -/
private theorem omb_halfCurve_right_inv (p : M) (ε : ℝ)
    (y : M) (hy : y ∈ (chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :
    ombHalfCurve M p (ombHalfCurveInv M p y) = y := by
  obtain ⟨hxsrc, hxmem⟩ := hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
  have hcoord0 : 0 < ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 :=
    hxmem.1
  have hcoordε : ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 < ε :=
    hxmem.2
  set s : ℝ := ombHalfCurveInv M p y with hs
  have hval : omLinEquiv s =
      (((chartAt (EuclideanHalfSpace 1) p) y).val :
        EuclideanSpace ℝ (Fin 1)) := by
    rw [hs]
    simp only [ombHalfCurveInv]
    exact ContinuousLinearEquiv.apply_symm_apply omLinEquiv _
  have hspos : 0 ≤ s := by
    have : s = (omLinEquiv s).ofLp 0 := (ombLinEquiv_coord s).symm
    rw [this, hval]
    exact hcoord0.le
  have hH : (𝓡∂ 1).symm (omLinEquiv s) =
      (chartAt (EuclideanHalfSpace 1) p) y := by
    apply EuclideanHalfSpace.ext
    rw [omb_symm_ray_val_of_nonneg s hspos, hval]
  simp only [ombHalfCurve, hH]
  exact (chartAt (EuclideanHalfSpace 1) p).left_inv hxsrc

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The coordinate map lands in the open interval. -/
private theorem omb_halfCurveInv_maps (p : M) (ε : ℝ) :
    Set.MapsTo (ombHalfCurveInv M p)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε})
      (Set.Ioo 0 ε) := by
  intro y hy
  obtain ⟨-, hxmem⟩ := hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
  have hval : omLinEquiv (ombHalfCurveInv M p y) =
      (((chartAt (EuclideanHalfSpace 1) p) y).val :
        EuclideanSpace ℝ (Fin 1)) := by
    simp only [ombHalfCurveInv]
    exact ContinuousLinearEquiv.apply_symm_apply omLinEquiv _
  have hcoord : ombHalfCurveInv M p y =
      ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp 0) hval
    simpa [ombLinEquiv_coord] using h
  rw [Set.mem_Ioo, hcoord]
  exact hxmem

/-- The half-chart curve is smooth on the open interval. -/
private theorem omb_halfCurve_contMDiffOn (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) (Set.Ioo 0 ε) := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ omLinEquiv :=
    contMDiff_iff_contDiff.mpr omLinEquiv.contDiff
  have h1On : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      omLinEquiv (Set.Ioo 0 ε) := h1.contMDiffOn
  have hmaps1 : Set.Ioo 0 ε ⊆ omLinEquiv ⁻¹' Set.range (𝓡∂ 1) := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    rw [Set.mem_preimage, range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1.le
  have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ 1) ∞
      (𝓡∂ 1).symm (Set.range (𝓡∂ 1)) :=
    (𝓡∂ 1).contMDiffOn_symm
  have h12 : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞
      ((𝓡∂ 1).symm ∘ omLinEquiv) (Set.Ioo 0 ε) := h2.comp h1On hmaps1
  have hmaps2 : Set.Ioo 0 ε ⊆ ((𝓡∂ 1).symm ∘ omLinEquiv) ⁻¹'
      (chartAt (EuclideanHalfSpace 1) p).target := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    simp only [Set.mem_preimage, Function.comp_apply]
    apply hε.2.2
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have h3 : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
      (chartAt (EuclideanHalfSpace 1) p).symm
      (chartAt (EuclideanHalfSpace 1) p).target :=
    contMDiffOn_chart_symm
  have hfin : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞
      ((chartAt (EuclideanHalfSpace 1) p).symm ∘
        ((𝓡∂ 1).symm ∘ omLinEquiv)) (Set.Ioo 0 ε) := h3.comp h12 hmaps2
  have heq : ombHalfCurve M p =
      (chartAt (EuclideanHalfSpace 1) p).symm ∘
        ((𝓡∂ 1).symm ∘ omLinEquiv) := rfl
  rw [heq]
  exact hfin

/-- The coordinate map is smooth on the target box. -/
private theorem omb_halfCurveInv_contMDiffOn (p : M) (ε : ℝ) :
    ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (ombHalfCurveInv M p)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  have he : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
      (chartAt (EuclideanHalfSpace 1) p)
      (chartAt (EuclideanHalfSpace 1) p).source :=
    contMDiffOn_chart
  have heV : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
      (chartAt (EuclideanHalfSpace 1) p)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    he.mono Set.inter_subset_left
  have hI : ContMDiff (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ (𝓡∂ 1) :=
    (𝓡∂ 1).contMDiff
  have hIe : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p))
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    hI.contMDiffOn.comp heV Set.subset_preimage_univ
  have hL : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℝ) ∞
      omLinEquiv.symm :=
    contMDiff_iff_contDiff.mpr omLinEquiv.symm.contDiff
  have hfin : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (omLinEquiv.symm ∘ ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p)))
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :=
    hL.contMDiffOn.comp hIe Set.subset_preimage_univ
  have heq : ombHalfCurveInv M p =
      omLinEquiv.symm ∘ ((𝓡∂ 1) ∘ (chartAt (EuclideanHalfSpace 1) p)) := rfl
  rw [heq]
  exact hfin

/-- The half-chart curve is a local diffeomorphism on the open interval. -/
private theorem omb_isLocalDiffeomorphAt_halfCurve (p : M) (ε t : ℝ)
    (hε : ombGoodRadius M p ε) (ht : t ∈ Set.Ioo 0 ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) t := by
  have hInv : Set.InvOn (ombHalfCurveInv M p) (ombHalfCurve M p)
      (Set.Ioo 0 ε)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      exact omb_halfCurve_left_inv M p ε hε s hs
    · intro y hy
      exact omb_halfCurve_right_inv M p ε y hy
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ isOpen_Ioo
    (omb_halfCurve_V_open M p ε) (omb_halfCurve_maps_fwd M p ε hε)
    (omb_halfCurveInv_maps M p ε) hInv
    (omb_halfCurve_contMDiffOn M p ε hε)
    (omb_halfCurveInv_contMDiffOn M p ε) t ht

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart image on an initial interval is open. -/
private theorem omb_halfCurve_image_open (p : M) (ε δ : ℝ)
    (hε : ombGoodRadius M p ε) (hδε : δ ≤ ε) :
    IsOpen ((ombHalfCurve M p) '' Set.Ico 0 δ) := by
  rw [omb_halfCurve_image_Ico M p ε δ hε hδε]
  apply (chartAt (EuclideanHalfSpace 1) p).isOpen_inter_preimage
  have hcont : Continuous
      (fun y : EuclideanHalfSpace 1 => ((y.val).ofLp 0 : ℝ)) :=
    ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
  have : {y : EuclideanHalfSpace 1 | (y.val).ofLp 0 < δ} =
      (fun y : EuclideanHalfSpace 1 => ((y.val).ofLp 0 : ℝ)) ⁻¹' Set.Iio δ :=
    rfl
  rw [this]
  exact isOpen_Iio.preimage hcont

/-- The interior is nonempty. -/
private theorem omb_nonempty_ombInterior [ConnectedSpace M] :
    (ombInterior M : Set M).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x with h | h
  · exact ⟨x, (omb_mem_ombInterior_iff M x).mpr h⟩
  · obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M x h
    refine ⟨ombHalfCurve M x (ε / 2), ?_⟩
    have hmem : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := by
      rw [Set.mem_Ioo]
      constructor <;> linarith [hε.1]
    have h := omb_halfCurve_mem_interior M x ε (ε / 2) hε hmem
    exact SetLike.mem_coe.mp h

/-- The interior is dense. -/
private theorem omb_closure_ombInterior [ConnectedSpace M] :
    closure (ombInterior M : Set M) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x with h | h
  · exact subset_closure (SetLike.mem_coe.mp ((omb_mem_ombInterior_iff M x).mpr h))
  · obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M x h
    apply mem_closure_of_tendsto
      (omb_halfCurve_tendsto M x h ε hε)
    filter_upwards [Ioo_mem_nhdsGT hε.1] with t ht
    have hmem : t ∈ Set.Ioo (0 : ℝ) ε := ht
    have h := omb_halfCurve_mem_interior M x ε t hε hmem
    exact SetLike.mem_coe.mp h

/-- Each boundary tail lies on one side of a disjoint cover of the interior. -/
private theorem omb_tail_side [ConnectedSpace M]
    (u v : Set M) (hu : IsOpen u) (hv : IsOpen v)
    (hcover : (ombInterior M : Set M) ⊆ u ∪ v)
    (hdisj : (ombInterior M : Set M) ∩ (u ∩ v) = ∅)
    (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ∃ ε, ombGoodRadius M p ε ∧
      ((ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u ∨
        (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ v) := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M p hp
  refine ⟨ε, hε, ?_⟩
  have hsub : Set.Ioo (0 : ℝ) ε ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo (by linarith [hε.1]) le_rfl
  have hpre : IsPreconnected ((ombHalfCurve M p) '' Set.Ioo 0 ε) :=
    isPreconnected_Ioo.image _
      ((omb_halfCurve_continuousOn M p ε hε).mono hsub)
  have hTS : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ (ombInterior M : Set M) := by
    rintro y ⟨t, ht, rfl⟩
    exact SetLike.mem_coe.mp (omb_halfCurve_mem_interior M p ε t hε ht)
  have hTuv : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u ∪ v :=
    hTS.trans hcover
  have hTdisj : (ombHalfCurve M p) '' Set.Ioo 0 ε ∩ (u ∩ v) = ∅ := by
    have hsub2 : (ombHalfCurve M p) '' Set.Ioo 0 ε ∩ (u ∩ v) ⊆
        (ombInterior M : Set M) ∩ (u ∩ v) :=
      Set.inter_subset_inter hTS le_rfl
    rw [hdisj] at hsub2
    exact Set.subset_empty_iff.mp hsub2
  exact (isPreconnected_iff_subset_of_disjoint.mp hpre) u v hu hv hTuv hTdisj

/-- A cap meets the interior only along its tail. -/
private theorem omb_cap_inter_subset (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) (ε δ : ℝ)
    (hδε : δ ≤ ε) (u : Set M)
    (htail : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u) :
    ((ombHalfCurve M p) '' Set.Ico 0 δ) ∩ (ombInterior M : Set M) ⊆ u := by
  rintro x ⟨⟨t, ⟨ht0, htδ⟩, rfl⟩, hxS⟩
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · subst h0
    rw [omb_halfCurve_zero M p hp] at hxS
    exact absurd (SetLike.mem_coe.mpr hxS)
      (omb_boundary_not_mem_interior M p hp)
  · apply htail
    refine ⟨t, ?_, rfl⟩
    rw [Set.mem_Ioo]
    exact ⟨hpos, lt_of_lt_of_le htδ hδε⟩

/-- Cap union on one side of a cover of the interior. -/
private def ombSideCap (u : Set M) : Set M :=
  u ∪ ⋃ (p : M) (_ : (𝓡∂ 1).IsBoundaryPoint p) (ε : ℝ)
    (_ : ombGoodRadius M p ε)
    (_ : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u),
    (ombHalfCurve M p) '' Set.Ico 0 ε

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Each cap in the union is open. -/
private theorem omb_sideCap_open (u : Set M) (hu : IsOpen u) :
    IsOpen (ombSideCap M u) := by
  unfold ombSideCap
  apply hu.union
  apply isOpen_iUnion; intro p
  apply isOpen_iUnion; intro _
  apply isOpen_iUnion; intro ε
  apply isOpen_iUnion; intro hε
  apply isOpen_iUnion; intro _
  exact omb_halfCurve_image_open M p ε ε hε le_rfl

/-- Points of the interior in a side cap lie in the side. -/
private theorem omb_mem_of_sideCap_inter (u : Set M)
    (x : M) (hxS : x ∈ (ombInterior M : Set M)) (hx : x ∈ ombSideCap M u) :
    x ∈ u := by
  unfold ombSideCap at hx
  rcases hx with h | h
  · exact h
  · simp only [Set.mem_iUnion] at h
    obtain ⟨p, hp, ε, hε, htail, hcap⟩ := h
    exact omb_cap_inter_subset M p hp ε ε le_rfl u htail ⟨hcap, hxS⟩

/-- The interior is preconnected. -/
private theorem omb_isPreconnected_ombInterior [ConnectedSpace M] :
    IsPreconnected (ombInterior M : Set M) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcover hdisj
  have hU'open : IsOpen (ombSideCap M u) := omb_sideCap_open M u hu
  have hV'open : IsOpen (ombSideCap M v) := omb_sideCap_open M v hv
  have hSU : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M u → x ∈ u :=
    fun x hxS hx => omb_mem_of_sideCap_inter M u x hxS hx
  have hSV : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M v → x ∈ v :=
    fun x hxS hx => omb_mem_of_sideCap_inter M v x hxS hx
  have hdisj' : ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxU, hxV⟩, hxS⟩
    have hxu := hSU x hxS hxU
    have hxv := hSV x hxS hxV
    have hmem : x ∈ (ombInterior M : Set M) ∩ (u ∩ v) := ⟨hxS, hxu, hxv⟩
    rw [hdisj] at hmem
    exact Set.notMem_empty x hmem
  have hUV : ombSideCap M u ∩ ombSideCap M v = ∅ := by
    by_contra hne
    have hne' : (ombSideCap M u ∩ ombSideCap M v).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hdense : Dense (ombInterior M : Set M) :=
      dense_iff_closure_eq.mpr (omb_closure_ombInterior M)
    obtain ⟨y, hyUV, hyS⟩ :=
      (dense_iff_inter_open.mp hdense) _ (hU'open.inter hV'open) hne'
    have hmem : y ∈ ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) :=
      ⟨hyUV, hyS⟩
    rw [hdisj'] at hmem
    exact Set.notMem_empty y hmem
  have hcoverM : (Set.univ : Set M) ⊆ ombSideCap M u ∪ ombSideCap M v := by
    intro x _
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x
      with h | h
    · have hxS : x ∈ (ombInterior M : Set M) :=
        SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M x).mpr h)
      rcases hcover hxS with hxu | hxv
      · exact Or.inl (Or.inl hxu)
      · exact Or.inr (Or.inl hxv)
    · obtain ⟨ε, hε, hside⟩ := omb_tail_side M u v hu hv hcover hdisj x h
      rcases hside with htail | htail
      · refine Or.inl (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
      · refine Or.inr (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
  have hUVdisj : (Set.univ : Set M) ∩ (ombSideCap M u ∩ ombSideCap M v) = ∅ := by
    rw [Set.univ_inter]
    exact hUV
  rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ)
    _ _ hU'open hV'open hcoverM hUVdisj with hU | hV
  · exact Or.inl (fun x hxS => hSU x hxS (hU (Set.mem_univ x)))
  · exact Or.inr (fun x hxS => hSV x hxS (hV (Set.mem_univ x)))

/-- The interior is connected. -/
private instance omb_connectedSpace_ombInterior [ConnectedSpace M] :
    ConnectedSpace ↥(ombInterior M) :=
  isConnected_iff_connectedSpace.mp
    ⟨omb_nonempty_ombInterior M, omb_isPreconnected_ombInterior M⟩

end BoundaryInterior

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

@[expose] public section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

open MathlibExt.Geometry.Manifold.OneDimensionalClassification

/--
**Classification of connected $1$-manifolds without boundary.** Every connected, Hausdorff,
second-countable smooth $1$-manifold $M$ without boundary is diffeomorphic either to the circle
$S^1$ or to the real line $\mathbb{R}$.

Proves `Wanted` entry `connected_boundaryless_one_manifold_classification`.

Source: Classification of connected boundaryless
1-manifolds; Milnor (1965); Hirsch; Lean states dichotomy specialization for `𝓡 1`.
-/
theorem connected_boundaryless_one_manifold_classification
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (𝓡 1) ∞ M]
    [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ (EuclideanSpace ℝ (Fin 1))) := by
  classical
  obtain ⟨g⟩ := om_riemannianMetric (M := M)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨α₀, hα₀src, hα₀₀, _, hα₀speed⟩ := om_exists_unitSpeedChart g x₀
  obtain ⟨D, γ, hDadm, hmax⟩ :=
    om_exists_maximal_unitSpeed g α₀ hα₀src hα₀₀ hα₀speed
  have hDadmC := hDadm
  obtain ⟨hDopen, hDconn, h0D, hγunit, _⟩ := hDadmC
  have himg : γ '' D = Set.univ :=
    om_maximal_unitSpeed_image_eq_univ g α₀ D γ hDadm hmax
  by_cases hInj : Set.InjOn γ D
  · -- Injective case: `M` is diffeomorphic to `E1`, via `γ ∘ φ`.
    obtain ⟨φ, hφsmooth, hφderiv, hφrange⟩ :=
      odm_exists_contDiff_deriv_pos_range_eq D hDopen hDconn ⟨0, h0D⟩
    have hφD : ContDiffOn ℝ ∞ φ Set.univ := hφsmooth.contDiffOn
    have hderivU : ∀ t ∈ (Set.univ : Set ℝ), 0 < deriv φ t :=
      fun t _ => hφderiv t
    obtain ⟨Φ, hΦsrc, hΦfun, _, _, _⟩ :=
      odm_exists_partialDiffeomorph_of_deriv_pos Set.univ φ isOpen_univ
        (isPreconnected_iff_ordConnected.mp isPreconnected_univ) hφD hderivU
    have hFld : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ (γ ∘ φ) := by
      intro t
      have hmem : φ t ∈ D := hφrange ▸ Set.mem_range_self t
      have hγt := om_isLocalDiffeomorphAt_of_unitSpeed g D γ hDopen hγunit
        (φ t) hmem
      have hφt : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ t := by
        have hmemS : t ∈ Φ.source := by
          rw [hΦsrc]
          exact Set.mem_univ t
        have h := PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          Φ hmemS
        rwa [hΦfun] at h
      exact IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := M) hφt hγt
    have hφinj : Function.Injective φ := by
      have hstrict : StrictMonoOn φ Set.univ :=
        strictMonoOn_of_deriv_pos convex_univ hφD.continuousOn (by
          rw [isOpen_univ.interior_eq]
          exact hderivU)
      intro a b hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (ne_of_lt (hstrict (Set.mem_univ _) (Set.mem_univ _) h))
      · exact h
      · exact absurd hab (ne_of_gt (hstrict (Set.mem_univ _) (Set.mem_univ _) h))
    have hFinj : Function.Injective (γ ∘ φ) := by
      intro a b hab
      have haD : φ a ∈ D := hφrange ▸ Set.mem_range_self a
      have hbD : φ b ∈ D := hφrange ▸ Set.mem_range_self b
      exact hφinj (hInj haD hbD hab)
    have hFsurj : Function.Surjective (γ ∘ φ) := by
      intro y
      have hy : y ∈ γ '' D := himg.symm ▸ Set.mem_univ y
      obtain ⟨t, htD, rfl⟩ := hy
      obtain ⟨s, rfl⟩ := hφrange.symm ▸ htD
      exact ⟨s, rfl⟩
    exact Or.inr ⟨(hFld.diffeomorphOfBijective ⟨hFinj, hFsurj⟩).symm.trans
      omLinEquiv.toDiffeomorph⟩
  · -- Non-injective case: the maximal curve is periodic, so `M ≃ Circle`.
    have hpair : ∃ t₁ t₂ : ℝ, t₁ ∈ D ∧ t₂ ∈ D ∧ t₁ < t₂ ∧ γ t₁ = γ t₂ := by
      by_contra hcon
      have hInj' : Set.InjOn γ D := by
        intro a haD b hbD hab
        rcases lt_trichotomy a b with h | h | h
        · exact (hcon ⟨a, b, haD, hbD, h, hab⟩).elim
        · exact h
        · exact (hcon ⟨b, a, hbD, haD, h, hab.symm⟩).elim
      exact hInj hInj'
    obtain ⟨t₁, t₂, ht₁, ht₂, hlt, heq⟩ := hpair
    obtain ⟨hDuniv, hper⟩ :=
      om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax t₁ t₂ ht₁ ht₂
        hlt heq
    have hTne : t₂ - t₁ ≠ 0 := ne_of_gt (by linarith)
    obtain ⟨δ, hδpos, hδinj⟩ :=
      om_exists_injOn_of_unitSpeed g D γ hDopen hγunit 0 h0D
    have hδinj' : Set.InjOn γ (Set.Ioo (-δ) δ) := by
      have e : Set.Ioo ((0 : ℝ) - δ) (0 + δ) = Set.Ioo (-δ) δ := by
        rw [zero_sub, zero_add]
      rwa [e] at hδinj
    have hcoin : ∀ s t : ℝ, s ≠ t → γ s = γ t → ∀ u, γ (u + (t - s)) = γ u := by
      intro s t hst heq' u
      rcases lt_or_gt_of_ne hst with h | h
      · have hsD : s ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ s
        have htD : t ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ t
        exact (om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax s t
          hsD htD h heq').2 u
      · have hsD : s ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ s
        have htD : t ∈ D := by
          rw [hDuniv]
          exact Set.mem_univ t
        have h2 := (om_maximal_unitSpeed_periodic_of_eq g α₀ D γ hDadm hmax t s
          htD hsD h heq'.symm).2
        have e2 := h2 (u + (t - s))
        have e3 : u + (t - s) + (s - t) = u := by ring
        rw [e3] at e2
        exact e2.symm
    obtain ⟨T₀, hT₀pos, _, hiff⟩ :=
      om_exists_minimal_period γ δ hδpos hδinj' (t₂ - t₁) hTne hper hcoin
    have hsurj : Function.Surjective γ := by
      intro y
      have hy : y ∈ γ '' D := himg.symm ▸ Set.mem_univ y
      obtain ⟨t, _, ht⟩ := hy
      exact ⟨t, ht⟩
    have hld : ∀ t : ℝ, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ t := by
      intro t
      have htD : t ∈ D := by
        rw [hDuniv]
        exact Set.mem_univ t
      exact om_isLocalDiffeomorphAt_of_unitSpeed g D γ hDopen hγunit t htD
    obtain ⟨hC⟩ := om_nonempty_diffeomorph_circle_of_periodic γ hsurj hld T₀
      hT₀pos hiff
    exact Or.inl ⟨hC.symm⟩

/-- The black box applied to the interior subtype. -/
private theorem omb_blackbox_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) ∨
      Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡 1⟯ (EuclideanSpace ℝ (Fin 1))) :=
  connected_boundaryless_one_manifold_classification ↥(ombInterior M)

/-- Empty boundary: `M` is diffeomorphic to `Circle`. -/
private theorem omb_circle_of_boundary_empty (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : ModelWithCorners.boundary (I := 𝓡∂ 1) M = ∅) :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) := by
  have hS : ((ombInterior M : TopologicalSpace.Opens M) : Set M) = Set.univ := by
    have h := ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 1) (M := M)
    rw [hB, Set.union_empty] at h
    exact h
  obtain ⟨xw, hxw⟩ := omb_nonempty_ombInterior M
  let x₀ : ↥(ombInterior M) := ⟨xw, hxw⟩
  have hbij : Function.Bijective (Subtype.val : ↥(ombInterior M) → M) := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    show y ∈ ombInterior M
    have hy : y ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [hS]
      exact Set.mem_univ y
    exact hy
  have hld := omb_isLocalDiffeomorph_val M x₀
  have hD : Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M) :=
    ⟨hld.diffeomorphOfBijective hbij⟩
  obtain ⟨D⟩ := hD
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · exact ⟨D.symm.trans Φ⟩
  · have DE : M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ EuclideanSpace ℝ (Fin 1) := D.symm.trans Φ
    have hC := Homeomorph.compactSpace DE.toHomeomorph
    exact absurd (@isCompact_univ _ _ hC) (noncompact_univ _)

/-- Nonempty boundary: the interior is diffeomorphic to `ℝ`. -/
private theorem omb_exists_diffeomorph_real_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    Nonempty (ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) := by
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · have hC := Homeomorph.compactSpace Φ.toHomeomorph.symm
    have hcpt : IsCompact ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      isCompact_iff_compactSpace.mpr hC
    have hclopen : IsClopen ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      ⟨hcpt.isClosed, (ombInterior M).2⟩
    have huniv := hclopen.eq_univ (omb_nonempty_ombInterior M)
    obtain ⟨p, hp⟩ := hB
    have hpS : p ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [huniv]
      exact Set.mem_univ p
    have hmem := (omb_mem_ombInterior_iff M p).mp hpS
    have hbp : (𝓡∂ 1).IsBoundaryPoint p := hp
    exact ((𝓡∂ 1).isBoundaryPoint_iff_not_isInteriorPoint p).mp hbp hmem |>.elim
  · exact ⟨omLinEquiv.toDiffeomorph.trans Φ.symm⟩

/-- The end map: `Ψ.symm` of the retracted half-curve. -/
private def ombTheta (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) : ℝ → ℝ :=
  fun t => Ψ.symm (ombRetract M x₀ (ombHalfCurve M p t))

/-- On the tail, `Ψ (θ t)` recovers the half-curve. -/
private theorem omb_theta_apply (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    ((Ψ (ombTheta M Ψ x₀ p t) : ↥(ombInterior M)) : M)
      = ombHalfCurve M p t := by
  have hmemO : ombHalfCurve M p t ∈ ombInterior M :=
    omb_halfCurve_mem_interior M p ε t hε ht
  have e : ombTheta M Ψ x₀ p t
      = Ψ.symm (ombRetract M x₀ (ombHalfCurve M p t)) := rfl
  rw [e, Ψ.apply_symm_apply, ombRetract_of_mem M x₀ _ hmemO]

/-- The end map is a local diffeomorphism on the tail. -/
private theorem omb_isLocalDiffeomorphAt_theta (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (ombTheta M Ψ x₀ p) t := by
  have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) t :=
    omb_isLocalDiffeomorphAt_halfCurve M p ε t hε ht
  have hmem : ombHalfCurve M p t ∈ (ombInterior M : Set M) :=
    SetLike.mem_coe.mp (omb_halfCurve_mem_interior M p ε t hε ht)
  have h2 : IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀)
      (ombHalfCurve M p t) :=
    omb_isLocalDiffeomorphAt_retract M x₀ _ hmem
  have h3 : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (⇑Ψ.symm)
      (ombRetract M x₀ (ombHalfCurve M p t)) :=
    Ψ.symm.isLocalDiffeomorph _
  have h12 := IsLocalDiffeomorphAt.comp (K := (𝓡 1)) (P := ↥(ombInterior M)) h1 h2
  have h := IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) h12 h3
  have e : (⇑Ψ.symm ∘ ombRetract M x₀ ∘ ombHalfCurve M p)
      = ombTheta M Ψ x₀ p := rfl
  rw [e] at h
  exact h

/-- The end map is smooth on the tail interval. -/
private theorem omb_theta_contDiffOn (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    ContDiffOn ℝ ∞ (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
  intro t ht
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  exact h.contMDiffAt.contDiffAt.contDiffWithinAt

/-- The derivative of the end map never vanishes on the tail. -/
private theorem omb_theta_deriv_ne (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    deriv (ombTheta M Ψ x₀ p) t ≠ 0 := by
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  have hinv := h.isInvertible_mfderiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  have heq : (fderiv ℝ (ombTheta M Ψ x₀ p) t)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ombTheta M Ψ x₀ p) t) :=
    mfderiv_eq_fderiv.symm
  have hinv2 : (fderiv ℝ (ombTheta M Ψ x₀ p) t).IsInvertible := heq ▸ hinv
  obtain ⟨A, hA⟩ := hinv2
  have h1 : (fderiv ℝ (ombTheta M Ψ x₀ p) t) 1 ≠ 0 := by
    rw [← hA]
    have hA1 : A (1 : ℝ) ≠ A 0 := by
      intro hcon
      exact one_ne_zero (A.injective hcon)
    rwa [map_zero] at hA1
  rwa [fderiv_apply_one_eq_deriv] at h1

/-- The derivative of the end map has constant sign on the tail. -/
private theorem omb_theta_deriv_sign (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    (∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) ∨
      (∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) := by
  have hne : ∀ t ∈ Set.Ioo (0 : ℝ) ε, deriv (ombTheta M Ψ x₀ p) t ≠ 0 :=
    fun t ht => omb_theta_deriv_ne M Ψ x₀ p ε hε t ht
  have hcont : ContinuousOn (deriv (ombTheta M Ψ x₀ p)) (Set.Ioo 0 ε) :=
    (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn_deriv_of_isOpen isOpen_Ioo
      (by simp : (1 : ℕ∞ω) ≤ ∞)
  by_cases h : ∃ t ∈ Set.Ioo (0 : ℝ) ε, 0 < deriv (ombTheta M Ψ x₀ p) t
  · left
    obtain ⟨a, ha, hapos⟩ := h
    intro t ht
    rcases lt_trichotomy (deriv (ombTheta M Ψ x₀ p) t) 0 with hneg | hzero | hpos
    · exfalso
      obtain ⟨c, hc, hczero⟩ := isPreconnected_Ioo.intermediate_value₂ ht ha
        hcont continuousOn_const (le_of_lt hneg) (le_of_lt hapos)
      exact hne c hc hczero
    · exact absurd hzero (hne t ht)
    · exact hpos
  · right
    push Not at h
    intro t ht
    rcases lt_or_gt_of_ne (hne t ht) with hneg | hpos
    · exact hneg
    · have hle := h t ht
      linarith

/-- A two-sided bound on a tail interval is impossible. -/
private theorem omb_theta_bounded_false (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (δ : ℝ) (hδpos : 0 < δ) (hδε : δ ≤ ε) (lo hi : ℝ)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) δ, ombTheta M Ψ x₀ p t ∈ Set.Icc lo hi) :
    False := by
  set K : Set M := (fun u : ℝ => ((Ψ u : ↥(ombInterior M)) : M)) ''
    Set.Icc lo hi with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    apply IsCompact.image isCompact_Icc
    exact continuous_subtype_val.comp Ψ.continuous
  have hKclosed : IsClosed K := hKc.isClosed
  have hpclosure : p ∈ closure ((ombHalfCurve M p) '' Set.Ioo 0 δ) := by
    apply mem_closure_of_tendsto (omb_halfCurve_tendsto M p hp ε hε)
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht
    exact ⟨t, ht, rfl⟩
  have hsub : (ombHalfCurve M p) '' Set.Ioo 0 δ ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    have hθt := hb t ht
    rw [hKdef]
    exact ⟨ombTheta M Ψ x₀ p t, hθt,
      omb_theta_apply M Ψ x₀ p ε hε t htε⟩
  have hpK : p ∈ K := closure_minimal hsub hKclosed hpclosure
  obtain ⟨u, _, hpu⟩ := hpK
  have hpS : p ∈ (ombInterior M : Set M) := by
    rw [← hpu]
    exact (Ψ u).2
  have hnot : p ∉ ombInterior M := omb_boundary_not_mem_interior M p hp
  exact hnot (SetLike.mem_coe.mpr hpS)

/-- Increasing end map tends to `atBot`. -/
private theorem omb_theta_tendsto_atBot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hpos : ∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot := by
  have hmono : StrictMonoOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hpos
  rw [Filter.tendsto_atBot]
  intro B
  obtain ⟨t₀, ht₀, hlt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, ombTheta M Ψ x₀ p t < B := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε B
      (ombTheta M Ψ x₀ p (ε / 2))
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨hcon t htε, ?_⟩
    exact le_of_lt (hmono htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans (hmono htε ht₀ ht.2) hlt)

/-- Decreasing end map tends to `atTop`. -/
private theorem omb_theta_tendsto_atTop (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hneg : ∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  have hanti : StrictAntiOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hneg
  rw [Filter.tendsto_atTop]
  intro B
  obtain ⟨t₀, ht₀, hgt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, B < ombTheta M Ψ x₀ p t := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε
      (ombTheta M Ψ x₀ p (ε / 2)) B
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨?_, hcon t htε⟩
    exact le_of_lt (hanti htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans hgt (hanti htε ht₀ ht.2))

/-- The composite `val ∘ Ψ`, landing in the interior. -/
private def ombValPsi (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) : ℝ → M :=
  fun u => ((Ψ u : ↥(ombInterior M)) : M)

/-- The composite is injective. -/
private theorem omb_valPsi_injective (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) :
    Function.Injective (ombValPsi M Ψ) := by
  have h : Function.Injective (Subtype.val ∘ ⇑Ψ) :=
    Subtype.val_injective.comp Ψ.toEquiv.injective
  have e : (Subtype.val ∘ ⇑Ψ) = ombValPsi M Ψ := rfl
  rw [e] at h
  exact h

/-- Every interior point is a value of the composite. -/
private theorem omb_mem_interior_eq_valPsi (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) (m : M)
    (hm : m ∈ (ombInterior M : Set M)) :
    ∃ u₀, ombValPsi M Ψ u₀ = m := by
  refine ⟨Ψ.symm ⟨m, hm⟩, ?_⟩
  change ((Ψ (Ψ.symm ⟨m, hm⟩) : ↥(ombInterior M)) : M) = m
  rw [Ψ.apply_symm_apply]

/-- An `𝓝[>] 0`-eventually statement holds on some `Ioo 0 δ`. -/
private theorem omb_eventually_nhdsGT_Ioo {P : ℝ → Prop}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ δ > 0, ∀ t ∈ Set.Ioo 0 δ, P t := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨δ, hδpos, hδ⟩ := h
  refine ⟨δ, hδpos, ?_⟩
  intro t ht
  rw [Set.mem_Ioo] at ht
  refine hδ t ?_ ht.1
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hδpos, ht.1, ht.2]

/-- A left end absorbs far-left values into any of its neighbourhoods. -/
private theorem omb_absorb_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x : M) (hx : (𝓡∂ 1).IsBoundaryPoint x)
    (ε : ℝ) (hε : ombGoodRadius M x ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atBot)
    (N : Set M) (hN : N ∈ 𝓝 x) :
    ∃ R, ∀ u < R, ombValPsi M Ψ u ∈ N := by
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo
    ((omb_halfCurve_tendsto M x hx ε hε).eventually hN)
  have hminpos : 0 < min δ ε := lt_min hδpos hε.1
  have hminε : min δ ε ≤ ε := min_le_right _ _
  have hminδ : min δ ε ≤ δ := min_le_left _ _
  have ht₀ε : min δ ε / 2 ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨by linarith, by linarith⟩
  refine ⟨ombTheta M Ψ x₀ x (min δ ε / 2), ?_⟩
  intro u hu
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ombTheta M Ψ x₀ x t < u :=
    hlim.eventually (Filter.eventually_lt_atBot u)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (min δ ε / 2) :=
    Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < min δ ε / 2)
  obtain ⟨t₁, ht₁lt, ht₁mem⟩ := (hev1.and hev2).exists
  have ht₁ε : t₁ ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨ht₁mem.1, lt_trans ht₁mem.2 (by linarith)⟩
  have hcont : ContinuousOn (ombTheta M Ψ x₀ x)
      (Set.Icc t₁ (min δ ε / 2)) :=
    (omb_theta_contDiffOn M Ψ x₀ x ε hε).continuousOn.mono (by
      intro t ht
      rw [Set.mem_Icc] at ht
      rw [Set.mem_Ioo]
      exact ⟨lt_of_lt_of_le ht₁mem.1 ht.1,
        lt_of_le_of_lt ht.2 (by linarith [hminpos, hminε])⟩)
  have hivt := intermediate_value_Icc (le_of_lt ht₁mem.2) hcont
  have hmem : u ∈ Set.Icc (ombTheta M Ψ x₀ x t₁)
      (ombTheta M Ψ x₀ x (min δ ε / 2)) :=
    ⟨le_of_lt ht₁lt, le_of_lt hu⟩
  obtain ⟨t, htIcc, htθ⟩ := hivt hmem
  have htδ : t ∈ Set.Ioo (0 : ℝ) (min δ ε) := by
    rw [Set.mem_Icc] at htIcc
    refine ⟨lt_of_lt_of_le ht₁mem.1 htIcc.1, ?_⟩
    calc t ≤ min δ ε / 2 := htIcc.2
      _ < min δ ε := by linarith [hminpos]
  have htN : ombHalfCurve M x t ∈ N := by
    apply hδ t
    rw [Set.mem_Ioo]
    exact ⟨htδ.1, lt_of_lt_of_le htδ.2 hminδ⟩
  have htu : t ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨htδ.1, lt_of_lt_of_le htδ.2 hminε⟩
  have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
    have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
      omb_theta_apply M Ψ x₀ x ε hε t htu
    rw [← htθ]
    exact h1
  rw [heq]
  exact htN

/-- A right end absorbs far-right values into any of its neighbourhoods. -/
private theorem omb_absorb_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x : M) (hx : (𝓡∂ 1).IsBoundaryPoint x)
    (ε : ℝ) (hε : ombGoodRadius M x ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atTop)
    (N : Set M) (hN : N ∈ 𝓝 x) :
    ∃ R, ∀ u > R, ombValPsi M Ψ u ∈ N := by
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo
    ((omb_halfCurve_tendsto M x hx ε hε).eventually hN)
  have hminpos : 0 < min δ ε := lt_min hδpos hε.1
  have hminε : min δ ε ≤ ε := min_le_right _ _
  have hminδ : min δ ε ≤ δ := min_le_left _ _
  have hcontIoo := (omb_theta_contDiffOn M Ψ x₀ x ε hε).continuousOn
  have hsubIoo : ∀ t ∈ Set.Ioo (0 : ℝ) (min δ ε),
      ombHalfCurve M x t ∈ N := by
    intro t ht
    apply hδ t
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hminδ⟩
  refine ⟨ombTheta M Ψ x₀ x (min δ ε / 2), ?_⟩
  intro u hu
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u < ombTheta M Ψ x₀ x t :=
    hlim.eventually (Filter.eventually_gt_atTop u)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (min δ ε) :=
    Ioo_mem_nhdsGT hminpos
  obtain ⟨t₁, ht₁gt, ht₁mem⟩ := (hev1.and hev2).exists
  have hmemIcc : u ∈ Set.Icc (ombTheta M Ψ x₀ x (min δ ε / 2))
      (ombTheta M Ψ x₀ x t₁) :=
    ⟨le_of_lt hu, le_of_lt ht₁gt⟩
  rcases le_total (min δ ε / 2) t₁ with hle | hle
  · obtain ⟨t, htIcc, htθ⟩ := intermediate_value_Icc hle
      (hcontIoo.mono (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le (by linarith [hminpos]) ht.1,
          lt_of_le_of_lt ht.2 (lt_of_lt_of_le ht₁mem.2 hminε)⟩)) hmemIcc
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) htIcc.1
    have htmin : t < min δ ε := lt_of_le_of_lt htIcc.2 ht₁mem.2
    have htN : ombHalfCurve M x t ∈ N := hsubIoo t ⟨ht0, htmin⟩
    have htu : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht0, lt_of_lt_of_le htmin hminε⟩
    have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
      have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
        omb_theta_apply M Ψ x₀ x ε hε t htu
      rw [← htθ]
      exact h1
    rw [heq]
    exact htN
  · obtain ⟨t, htIcc, htθ⟩ := intermediate_value_Icc' hle
      (hcontIoo.mono (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le ht₁mem.1 ht.1,
          lt_of_le_of_lt ht.2 (by linarith [hminpos, hminε])⟩)) hmemIcc
    have ht0 : 0 < t := lt_of_lt_of_le ht₁mem.1 htIcc.1
    have htmin : t < min δ ε := by
      calc t ≤ min δ ε / 2 := htIcc.2
        _ < min δ ε := by linarith [hminpos]
    have htN : ombHalfCurve M x t ∈ N := hsubIoo t ⟨ht0, htmin⟩
    have htu : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht0, lt_of_lt_of_le htmin hminε⟩
    have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
      have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
        omb_theta_apply M Ψ x₀ x ε hε t htu
      rw [← htθ]
      exact h1
    rw [heq]
    exact htN

/-- Every boundary point is a left end or a right end. -/
private theorem omb_theta_tendsto (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot ∨
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M p hp
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exact Or.inl (omb_theta_tendsto_atBot M Ψ x₀ p hp ε hε hpos)
  · exact Or.inr (omb_theta_tendsto_atTop M Ψ x₀ p hp ε hε hneg)

/-- No end tends to both infinities. -/
private theorem omb_end_not_both (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (hBot : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot)
    (hTop : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop) :
    False :=
  hBot.not_tendsto Filter.disjoint_atBot_atTop hTop

/-- Two left ends coincide. -/
private theorem omb_end_unique_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x y : M)
    (hx : (𝓡∂ 1).IsBoundaryPoint x) (hy : (𝓡∂ 1).IsBoundaryPoint y)
    (hlimx : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atBot)
    (hlimy : Filter.Tendsto (ombTheta M Ψ x₀ y) (𝓝[>] 0) Filter.atBot) :
    x = y := by
  by_contra hne
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hdisj⟩ := t2_separation hne
  obtain ⟨εx, hεx⟩ := omb_exists_halfCurve_radius M x hx
  obtain ⟨εy, hεy⟩ := omb_exists_halfCurve_radius M y hy
  obtain ⟨R₁, hR₁⟩ :=
    omb_absorb_left M Ψ x₀ x hx εx hεx hlimx U (hUopen.mem_nhds hxU)
  obtain ⟨R₂, hR₂⟩ :=
    omb_absorb_left M Ψ x₀ y hy εy hεy hlimy V (hVopen.mem_nhds hyV)
  have hu1 : min R₁ R₂ - 1 < R₁ := by
    calc min R₁ R₂ - 1 < min R₁ R₂ := by linarith
      _ ≤ R₁ := min_le_left _ _
  have hu2 : min R₁ R₂ - 1 < R₂ := by
    calc min R₁ R₂ - 1 < min R₁ R₂ := by linarith
      _ ≤ R₂ := min_le_right _ _
  have huU := hR₁ _ hu1
  have huV := hR₂ _ hu2
  exact (Set.disjoint_left.mp hdisj) huU huV

/-- `val ∘ Ψ` is an open embedding of `ℝ` into `M`. -/
private theorem omb_valPsi_openEmbedding (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) :
    Topology.IsOpenEmbedding (ombValPsi M Ψ) := by
  have hS : IsOpen (ombInterior M : Set M) := (ombInterior M).2
  have e : ombValPsi M Ψ = Subtype.val ∘ ⇑Ψ := rfl
  rw [e]
  exact hS.isOpenEmbedding_subtypeVal.comp Ψ.toHomeomorph.isOpenEmbedding

/-- A cluster point of the `atBot` tail is not in the interior. -/
private theorem omb_mapClusterPt_atBot_not_mem (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (m : M) (hm : MapClusterPt m Filter.atBot (ombValPsi M Ψ))
    (hmS : m ∈ (ombInterior M : Set M)) : False := by
  obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
  have hopen : IsOpen ((ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1)) :=
    (omb_valPsi_openEmbedding M Ψ).isOpenMap _ isOpen_Ioo
  have hmem : m ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) := by
    rw [← hu₀]
    exact ⟨u₀, ⟨by linarith, by linarith⟩, rfl⟩
  have hfreq : ∃ᶠ u in Filter.atBot,
      ombValPsi M Ψ u ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) :=
    mapClusterPt_iff_frequently.mp hm _ (hopen.mem_nhds hmem)
  have hev : ∀ᶠ u in Filter.atBot, u < u₀ - 1 :=
    Filter.eventually_lt_atBot (u₀ - 1)
  obtain ⟨u, huN, huLt⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨v, hvIoo, hvu⟩ := huN
  have hvu' : v = u := omb_valPsi_injective M Ψ hvu
  rw [hvu'] at hvIoo
  linarith [hvIoo.1, huLt]

/-- A cluster point of the `atTop` tail is not in the interior. -/
private theorem omb_mapClusterPt_atTop_not_mem (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (m : M) (hm : MapClusterPt m Filter.atTop (ombValPsi M Ψ))
    (hmS : m ∈ (ombInterior M : Set M)) : False := by
  obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
  have hopen : IsOpen ((ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1)) :=
    (omb_valPsi_openEmbedding M Ψ).isOpenMap _ isOpen_Ioo
  have hmem : m ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) := by
    rw [← hu₀]
    exact ⟨u₀, ⟨by linarith, by linarith⟩, rfl⟩
  have hfreq : ∃ᶠ u in Filter.atTop,
      ombValPsi M Ψ u ∈ (ombValPsi M Ψ) '' Set.Ioo (u₀ - 1) (u₀ + 1) :=
    mapClusterPt_iff_frequently.mp hm _ (hopen.mem_nhds hmem)
  have hev : ∀ᶠ u in Filter.atTop, u₀ + 1 < u :=
    Filter.eventually_gt_atTop (u₀ + 1)
  obtain ⟨u, huN, huGt⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨v, hvIoo, hvu⟩ := huN
  have hvu' : v = u := omb_valPsi_injective M Ψ hvu
  rw [hvu'] at hvIoo
  linarith [hvIoo.2, huGt]

/-- A cluster point of the `atBot` tail is not a right end. -/
private theorem omb_mapClusterPt_atBot_not_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (m : M) (hmB : (𝓡∂ 1).IsBoundaryPoint m)
    (hm : MapClusterPt m Filter.atBot (ombValPsi M Ψ))
    (hTop : Filter.Tendsto (ombTheta M Ψ x₀ m) (𝓝[>] 0) Filter.atTop) :
    False := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M m hmB
  rcases omb_theta_deriv_sign M Ψ x₀ m ε hε with hpos | hneg
  · exact omb_end_not_both M Ψ x₀ m
      (omb_theta_tendsto_atBot M Ψ x₀ m hmB ε hε hpos) hTop
  · set δ := ε / 2 with hδdef
    have hδpos : 0 < δ := by linarith [hε.1]
    have hδε : δ ≤ ε := by linarith [hε.1]
    have hNopen : IsOpen ((ombHalfCurve M m) '' Set.Ico 0 δ) :=
      omb_halfCurve_image_open M m ε δ hε hδε
    have hNm : m ∈ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      refine ⟨0, ⟨le_refl _, hδpos⟩, ?_⟩
      exact omb_halfCurve_zero M m hmB
    have hfreq : ∃ᶠ u in Filter.atBot,
        ombValPsi M Ψ u ∈ (ombHalfCurve M m) '' Set.Ico 0 δ :=
      mapClusterPt_iff_frequently.mp hm _ (hNopen.mem_nhds hNm)
    have hanti : StrictAntiOn (ombTheta M Ψ x₀ m) (Set.Ioo 0 ε) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioo 0 ε)
        (omb_theta_contDiffOn M Ψ x₀ m ε hε).continuousOn
      rw [interior_Ioo]
      exact hneg
    have hbound : ∀ᶠ u in Filter.atBot,
        ombValPsi M Ψ u ∉ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      filter_upwards [Filter.eventually_le_atBot (ombTheta M Ψ x₀ m δ)]
        with u hu hNu
      obtain ⟨t, htIco, htu⟩ := hNu
      have ht0 : 0 < t := by
        rcases eq_or_lt_of_le htIco.1 with h0 | hpos
        · exfalso
          have htm : ombHalfCurve M m t = m := by
            rw [← h0]
            exact omb_halfCurve_zero M m hmB
          have hfm : m ∈ (ombInterior M : Set M) := by
            rw [← htm, htu]
            exact (Ψ u).2
          exact omb_boundary_not_mem_interior M m hmB (SetLike.mem_coe.mp hfm)
        · exact hpos
      have htIoo : t ∈ Set.Ioo (0 : ℝ) ε :=
        ⟨ht0, lt_of_lt_of_le htIco.2 hδε⟩
      have hδIoo : δ ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
      have hlt : ombTheta M Ψ x₀ m δ < ombTheta M Ψ x₀ m t :=
        hanti htIoo hδIoo htIco.2
      have htu2 : ombValPsi M Ψ (ombTheta M Ψ x₀ m t) = ombHalfCurve M m t :=
        omb_theta_apply M Ψ x₀ m ε hε t htIoo
      have huv : u = ombTheta M Ψ x₀ m t :=
        omb_valPsi_injective M Ψ (htu.symm.trans htu2.symm)
      linarith
    obtain ⟨u, hu1, hu2⟩ := (hfreq.and_eventually hbound).exists
    exact hu2 hu1

/-- A cluster point of the `atTop` tail is not a left end. -/
private theorem omb_mapClusterPt_atTop_not_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (m : M) (hmB : (𝓡∂ 1).IsBoundaryPoint m)
    (hm : MapClusterPt m Filter.atTop (ombValPsi M Ψ))
    (hBot : Filter.Tendsto (ombTheta M Ψ x₀ m) (𝓝[>] 0) Filter.atBot) :
    False := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M m hmB
  rcases omb_theta_deriv_sign M Ψ x₀ m ε hε with hpos | hneg
  · set δ := ε / 2 with hδdef
    have hδpos : 0 < δ := by linarith [hε.1]
    have hδε : δ ≤ ε := by linarith [hε.1]
    have hNopen : IsOpen ((ombHalfCurve M m) '' Set.Ico 0 δ) :=
      omb_halfCurve_image_open M m ε δ hε hδε
    have hNm : m ∈ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      refine ⟨0, ⟨le_refl _, hδpos⟩, ?_⟩
      exact omb_halfCurve_zero M m hmB
    have hfreq : ∃ᶠ u in Filter.atTop,
        ombValPsi M Ψ u ∈ (ombHalfCurve M m) '' Set.Ico 0 δ :=
      mapClusterPt_iff_frequently.mp hm _ (hNopen.mem_nhds hNm)
    have hmono : StrictMonoOn (ombTheta M Ψ x₀ m) (Set.Ioo 0 ε) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
        (omb_theta_contDiffOn M Ψ x₀ m ε hε).continuousOn
      rw [interior_Ioo]
      exact hpos
    have hbound : ∀ᶠ u in Filter.atTop,
        ombValPsi M Ψ u ∉ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      filter_upwards [Filter.eventually_ge_atTop (ombTheta M Ψ x₀ m δ)]
        with u hu hNu
      obtain ⟨t, htIco, htu⟩ := hNu
      have ht0 : 0 < t := by
        rcases eq_or_lt_of_le htIco.1 with h0 | hpos
        · exfalso
          have htm : ombHalfCurve M m t = m := by
            rw [← h0]
            exact omb_halfCurve_zero M m hmB
          have hfm : m ∈ (ombInterior M : Set M) := by
            rw [← htm, htu]
            exact (Ψ u).2
          exact omb_boundary_not_mem_interior M m hmB (SetLike.mem_coe.mp hfm)
        · exact hpos
      have htIoo : t ∈ Set.Ioo (0 : ℝ) ε :=
        ⟨ht0, lt_of_lt_of_le htIco.2 hδε⟩
      have hδIoo : δ ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
      have hlt : ombTheta M Ψ x₀ m t < ombTheta M Ψ x₀ m δ :=
        hmono htIoo hδIoo htIco.2
      have htu2 : ombValPsi M Ψ (ombTheta M Ψ x₀ m t) = ombHalfCurve M m t :=
        omb_theta_apply M Ψ x₀ m ε hε t htIoo
      have huv : u = ombTheta M Ψ x₀ m t :=
        omb_valPsi_injective M Ψ (htu.symm.trans htu2.symm)
      linarith
    obtain ⟨u, hu1, hu2⟩ := (hfreq.and_eventually hbound).exists
    exact hu2 hu1
  · exact omb_end_not_both M Ψ x₀ m hBot
      (omb_theta_tendsto_atTop M Ψ x₀ m hmB ε hε hneg)

/-- One-sided blend of `θ` into the line `α + β·t`, via `smoothTransition`. -/
private def ombBlend (θ : ℝ → ℝ) (α β a : ℝ) : ℝ → ℝ :=
  fun t => (1 - Real.smoothTransition ((t - a) / a)) * θ t +
    Real.smoothTransition ((t - a) / a) * (α + β * t)

/-- The blend equals `θ` below `a`. -/
private theorem ombBlend_eq_theta_of_le (θ : ℝ → ℝ) (α β a : ℝ) (ha : 0 < a)
    (t : ℝ) (ht : t ≤ a) : ombBlend θ α β a t = θ t := by
  have hs : (t - a) / a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha)
  simp only [ombBlend, Real.smoothTransition.zero_of_nonpos hs]
  ring

/-- The blend equals the line above `2 * a`. -/
private theorem ombBlend_eq_line_of_ge (θ : ℝ → ℝ) (α β a : ℝ) (ha : 0 < a)
    (t : ℝ) (ht : 2 * a ≤ t) : ombBlend θ α β a t = α + β * t := by
  have hs : 1 ≤ (t - a) / a := by
    rw [le_div_iff₀ ha]
    linarith
  simp only [ombBlend, Real.smoothTransition.one_of_one_le hs]
  ring

/-- The blend is smooth on `(0, ∞)`. -/
private theorem ombBlend_contDiffOn (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
    (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b)) :
    ContDiffOn ℝ ∞ (ombBlend θ α β a) (Set.Ioi 0) := by
  have hℓC : ContDiff ℝ ∞ (fun s : ℝ => α + β * s) := by fun_prop
  have hsC : ContDiff ℝ ∞ (fun s : ℝ => (s - a) / a) := by fun_prop
  intro t ht
  rw [Set.mem_Ioi] at ht
  rcases lt_or_ge t b with htb | htb
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht, htb⟩
    have hLam : ContDiffAt ℝ ∞
        (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t :=
      Real.smoothTransition.contDiffAt.comp t (hsC.contDiffAt)
    have hθt : ContDiffAt ℝ ∞ θ t := hθ.contDiffAt (isOpen_Ioo.mem_nhds htIoo)
    have hℓt : ContDiffAt ℝ ∞ (fun s : ℝ => α + β * s) t := hℓC.contDiffAt
    have hcombo : ContDiffAt ℝ ∞ (fun s : ℝ =>
        (1 - Real.smoothTransition ((s - a) / a)) * θ s +
        Real.smoothTransition ((s - a) / a) * (α + β * s)) t :=
      ((contDiffAt_const.sub hLam).mul hθt).add (hLam.mul hℓt)
    exact hcombo.contDiffWithinAt
  · have h2a : 2 * a < t := lt_of_lt_of_le hab htb
    have hev : ombBlend θ α β a =ᶠ[𝓝 t] (fun s : ℝ => α + β * s) := by
      filter_upwards [Ioi_mem_nhds h2a] with s hs
      exact ombBlend_eq_line_of_ge θ α β a ha s (le_of_lt hs)
    exact (hℓC.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt

/-- The transition map has nonnegative derivative. -/
private theorem ombBlend_lam_deriv_nonneg (a t : ℝ) (ha : 0 < a) :
    0 ≤ deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t := by
  have hS : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t - a) / a)) ((t - a) / a) :=
    Real.smoothTransition.contDiffAt.differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0) |>.hasDerivAt
  have hs : HasDerivAt (fun s : ℝ => (s - a) / a) (1 / a) t := by
    have h := ((HasDerivAt.sub (hasDerivAt_id t) (hasDerivAt_const t a)).div_const a)
    simpa using h
  have hcomp := hS.comp t hs
  have ed : deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t =
      deriv Real.smoothTransition ((t - a) / a) * (1 / a) := hcomp.deriv
  rw [ed]
  exact mul_nonneg (Monotone.deriv_nonneg Real.smoothTransition.monotone)
    (le_of_lt (one_div_pos.mpr ha))

/-- The transition map is locally constant below `a`. -/
private theorem ombBlend_lam_deriv_zero_of_lt (a t : ℝ) (ha : 0 < a)
    (ht : t < a) :
    deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t = 0 := by
  have hev : (fun s : ℝ => Real.smoothTransition ((s - a) / a)) =ᶠ[𝓝 t]
      (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    have hle : (s - a) / a ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [Set.mem_Iio.mp hs])
        (le_of_lt ha)
    exact Real.smoothTransition.zero_of_nonpos hle
  rw [hev.deriv_eq]
  exact deriv_const _ _

/-- The transition map is locally constant above `2 * a`. -/
private theorem ombBlend_lam_deriv_zero_of_gt (a t : ℝ) (ha : 0 < a)
    (ht : 2 * a < t) :
    deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t = 0 := by
  have hev : (fun s : ℝ => Real.smoothTransition ((s - a) / a)) =ᶠ[𝓝 t]
      (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hge : 1 ≤ (s - a) / a := by
      rw [le_div_iff₀ ha]
      linarith [Set.mem_Ioi.mp hs]
    exact Real.smoothTransition.one_of_one_le hge
  rw [hev.deriv_eq]
  exact deriv_const _ _

/-- The derivative of the affine line is its slope. -/
private theorem ombBlend_affine_deriv (α β t : ℝ) :
    deriv (fun s : ℝ => α + β * s) t = β := by
  simp

/-- The blend has positive derivative on `(0, ∞)`. -/
private theorem ombBlend_deriv_pos (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
    (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b))
    (hpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ t) (hβ : 0 < β)
    (hle : θ (2 * a) ≤ α + β * a) (t : ℝ) (ht : 0 < t) :
    0 < deriv (ombBlend θ α β a) t := by
  by_cases htb : t < b
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) b := ⟨ht, htb⟩
    have hθt : ContDiffAt ℝ ∞ θ t := hθ.contDiffAt (isOpen_Ioo.mem_nhds htIoo)
    have hθd : HasDerivAt θ (deriv θ t) t :=
      (hθt.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
    have hsC : ContDiff ℝ ∞ (fun s : ℝ => (s - a) / a) := by fun_prop
    have hlamC : ContDiffAt ℝ ∞
        (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t :=
      Real.smoothTransition.contDiffAt.comp t (hsC.contDiffAt)
    have hlamd : HasDerivAt (fun s : ℝ => Real.smoothTransition ((s - a) / a))
        (deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t) t :=
      (hlamC.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
    have hℓC : ContDiff ℝ ∞ (fun s : ℝ => α + β * s) := by fun_prop
    have hld : HasDerivAt (fun s : ℝ => α + β * s)
        (deriv (fun s : ℝ => α + β * s) t) t :=
      ((hℓC.differentiable (by simp : (∞ : ℕ∞ω) ≠ 0)).differentiableAt).hasDerivAt
    rw [ombBlend_affine_deriv α β t] at hld
    set S := Real.smoothTransition ((t - a) / a) with hSdef
    set S' := deriv (fun s : ℝ => Real.smoothTransition ((s - a) / a)) t
      with hS'def
    have h1 : HasDerivAt (fun s : ℝ => 1 - Real.smoothTransition ((s - a) / a))
        (0 - S') t :=
      HasDerivAt.sub (hasDerivAt_const t 1) hlamd
    have h2 : HasDerivAt
        (fun s : ℝ => (1 - Real.smoothTransition ((s - a) / a)) * θ s)
        ((0 - S') * θ t + (1 - S) * deriv θ t) t :=
      HasDerivAt.mul h1 hθd
    have h3 : HasDerivAt
        (fun s : ℝ => Real.smoothTransition ((s - a) / a) * (α + β * s))
        (S' * (α + β * t) + S * β) t :=
      HasDerivAt.mul hlamd hld
    have hψ : HasDerivAt (ombBlend θ α β a)
        (((0 - S') * θ t + (1 - S) * deriv θ t) +
          (S' * (α + β * t) + S * β)) t :=
      HasDerivAt.add h2 h3
    have eψ : deriv (ombBlend θ α β a) t =
        (((0 - S') * θ t + (1 - S) * deriv θ t) +
          (S' * (α + β * t) + S * β)) := hψ.deriv
    have hSnn : 0 ≤ S := Real.smoothTransition.nonneg _
    have hS1 : S ≤ 1 := Real.smoothTransition.le_one _
    have hθ' : 0 < deriv θ t := hpos t htIoo
    have hm : 0 < min (deriv θ t) β := lt_min hθ' hβ
    have c1 : (1 - S) * min (deriv θ t) β ≤ (1 - S) * deriv θ t :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have c2 : S * min (deriv θ t) β ≤ S * β :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hSnn
    have hring : (1 - S) * min (deriv θ t) β + S * min (deriv θ t) β =
        min (deriv θ t) β := by ring
    have hlast : 0 ≤ S' * ((α + β * t) - θ t) := by
      rcases lt_or_ge t a with hta | hta
      · have e0 : S' = 0 := ombBlend_lam_deriv_zero_of_lt a t ha hta
        simp [e0]
      · rcases le_or_gt t (2 * a) with ht2 | ht2
        · have hgap : θ t ≤ α + β * t := by
            have hmonoθ : StrictMonoOn θ (Set.Ioo 0 b) :=
              strictMonoOn_of_deriv_pos (convex_Ioo 0 b) hθ.continuousOn
                (by rw [interior_Ioo]; exact hpos)
            have h2aIoo : 2 * a ∈ Set.Ioo (0 : ℝ) b := ⟨by linarith, hab⟩
            have hθle : θ t ≤ θ (2 * a) :=
              hmonoθ.monotoneOn htIoo h2aIoo ht2
            have hline : α + β * a ≤ α + β * t := by
              have hmul : β * a ≤ β * t :=
                mul_le_mul_of_nonneg_left hta (le_of_lt hβ)
              linarith
            exact le_trans hθle (le_trans hle hline)
          exact mul_nonneg (ombBlend_lam_deriv_nonneg a t ha)
            (sub_nonneg.mpr hgap)
        · have e0 : S' = 0 := ombBlend_lam_deriv_zero_of_gt a t ha ht2
          simp [e0]
    have hring2 : (((0 - S') * θ t + (1 - S) * deriv θ t) +
          (S' * (α + β * t) + S * β)) =
        ((1 - S) * deriv θ t + S * β) + S' * ((α + β * t) - θ t) := by ring
    rw [eψ, hring2]
    linarith
  · have htle : b ≤ t := le_of_not_gt htb
    have h2a : 2 * a < t := lt_of_lt_of_le hab htle
    have hev : ombBlend θ α β a =ᶠ[𝓝 t] (fun s : ℝ => α + β * s) := by
      filter_upwards [Ioi_mem_nhds h2a] with s hs
      exact ombBlend_eq_line_of_ge θ α β a ha s (le_of_lt hs)
    rw [hev.deriv_eq, ombBlend_affine_deriv]
    exact hβ

/-- One-sided blend of an increasing function into a line. -/
private theorem omb_exists_blend_line (θ : ℝ → ℝ) (α β a b : ℝ) (ha : 0 < a)
    (hab : 2 * a < b) (hθ : ContDiffOn ℝ ∞ θ (Set.Ioo 0 b))
    (hpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ t) (hβ : 0 < β)
    (hle : θ (2 * a) ≤ α + β * a) :
    ∃ ψ : ℝ → ℝ, ContDiffOn ℝ ∞ ψ (Set.Ioi 0) ∧
      (∀ t > 0, 0 < deriv ψ t) ∧
      Set.EqOn ψ θ (Set.Ioc 0 a) ∧
      (∀ t ≥ 2 * a, ψ t = α + β * t) := by
  refine ⟨ombBlend θ α β a, ombBlend_contDiffOn θ α β a b ha hab hθ, ?_, ?_, ?_⟩
  · intro t ht
    exact ombBlend_deriv_pos θ α β a b ha hab hθ hpos hβ hle t ht
  · intro t ht
    rw [Set.mem_Ioc] at ht
    exact ombBlend_eq_theta_of_le θ α β a ha t ht.2
  · intro t ht
    exact ombBlend_eq_line_of_ge θ α β a ha t ht

/-- Setup for interpolation: choice of `a`, slope, and the two one-sided blends. -/
private theorem omb_interp_setup (θ₁ θ₂ : ℝ → ℝ) (b : ℝ) (hb0 : 0 < b)
    (hb12 : b ≤ 1 / 2)
    (hθ₁ : ContDiffOn ℝ ∞ θ₁ (Set.Ioo 0 b))
    (hθ₂ : ContDiffOn ℝ ∞ θ₂ (Set.Ioo 0 b))
    (hpos₁ : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ₁ t)
    (hneg₂ : ∀ t ∈ Set.Ioo 0 b, deriv θ₂ t < 0)
    (hlim₁ : Filter.Tendsto θ₁ (𝓝[>] 0) Filter.atBot)
    (hlim₂ : Filter.Tendsto θ₂ (𝓝[>] 0) Filter.atTop) :
    ∃ a β : ℝ, ∃ ψ₁ ψ₂ : ℝ → ℝ, 0 < a ∧ a < b ∧ a < 1 / 4 ∧ 0 < β ∧
      ContDiffOn ℝ ∞ ψ₁ (Set.Ioi 0) ∧ ContDiffOn ℝ ∞ ψ₂ (Set.Ioi 0) ∧
      (∀ t > 0, 0 < deriv ψ₁ t) ∧ (∀ t > 0, 0 < deriv ψ₂ t) ∧
      Set.EqOn ψ₁ θ₁ (Set.Ioo 0 a) ∧ Set.EqOn ψ₂ (-θ₂) (Set.Ioo 0 a) ∧
      (∀ t ≥ 2 * a, ψ₁ t = (θ₁ (2 * a) - β * a) + β * t) ∧
      (∀ s ≥ 2 * a, ψ₂ s = (-θ₁ (2 * a) - β * (1 - a)) + β * s) := by
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), θ₁ t < 0 :=
    hlim₁.eventually (Filter.eventually_lt_atBot 0)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < θ₂ t :=
    hlim₂.eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo (hev1.and hev2)
  set a := min δ b / 4 with hadef
  have hminpos : 0 < min δ b := lt_min hδpos hb0
  have ha : 0 < a := by linarith
  have hminδ : min δ b ≤ δ := min_le_left _ _
  have hminb : min δ b ≤ b := min_le_right _ _
  have hab : a < b := by linarith
  have ha14 : a < 1 / 4 := by linarith
  have h2aδ : 2 * a < δ := by linarith
  have h2ab : 2 * a < b := by linarith
  have h2amem : 2 * a ∈ Set.Ioo (0 : ℝ) δ := ⟨by linarith, h2aδ⟩
  have hθ₁2 : θ₁ (2 * a) < 0 := (hδ (2 * a) h2amem).1
  have hθ₂2 : 0 < θ₂ (2 * a) := (hδ (2 * a) h2amem).2
  set β := (θ₂ (2 * a) - θ₁ (2 * a)) / (1 - 2 * a) with hβdef
  have hβpos : 0 < 1 - 2 * a := by linarith
  have hβ : 0 < β := div_pos (by linarith) hβpos
  have hβcancel : β * (1 - 2 * a) = θ₂ (2 * a) - θ₁ (2 * a) :=
    div_mul_cancel₀ _ (by linarith)
  have hle₁ : θ₁ (2 * a) ≤ (θ₁ (2 * a) - β * a) + β * a := by linarith
  have hring₂ : -β * (1 - a) + β * a = -(β * (1 - 2 * a)) := by ring
  have hle₂ : (-θ₂) (2 * a) ≤ (-θ₁ (2 * a) - β * (1 - a)) + β * a := by
    have hpi : (-θ₂) (2 * a) = -θ₂ (2 * a) := rfl
    rw [hpi]
    linarith [hβcancel, hring₂]
  have hnegθ₂ : ContDiffOn ℝ ∞ (-θ₂) (Set.Ioo 0 b) := hθ₂.neg
  have hnegpos : ∀ t ∈ Set.Ioo 0 b, 0 < deriv (-θ₂) t := by
    intro t ht
    rw [deriv.neg]
    linarith [hneg₂ t ht]
  obtain ⟨ψ₁, hψ₁D, hψ₁pos, hψ₁eq, hψ₁line⟩ :=
    omb_exists_blend_line θ₁ (θ₁ (2 * a) - β * a) β a b ha h2ab hθ₁ hpos₁
      hβ hle₁
  obtain ⟨ψ₂, hψ₂D, hψ₂pos, hψ₂eq, hψ₂line⟩ :=
    omb_exists_blend_line (-θ₂) (-θ₁ (2 * a) - β * (1 - a)) β a b ha h2ab
      hnegθ₂ hnegpos hβ hle₂
  refine ⟨a, β, ψ₁, ψ₂, ha, hab, ha14, hβ, hψ₁D, hψ₂D, hψ₁pos, hψ₂pos, ?_, ?_,
    hψ₁line, hψ₂line⟩
  · intro s hs
    exact hψ₁eq (Set.Ioo_subset_Ioc_self hs)
  · intro s hs
    exact hψ₂eq (Set.Ioo_subset_Ioc_self hs)

/-- Smooth increasing bijection `(0, 1) → ℝ` with prescribed ends. -/
private theorem omb_exists_interpolation (θ₁ θ₂ : ℝ → ℝ) (b : ℝ) (hb0 : 0 < b)
    (hb12 : b ≤ 1 / 2)
    (hθ₁ : ContDiffOn ℝ ∞ θ₁ (Set.Ioo 0 b))
    (hθ₂ : ContDiffOn ℝ ∞ θ₂ (Set.Ioo 0 b))
    (hpos₁ : ∀ t ∈ Set.Ioo 0 b, 0 < deriv θ₁ t)
    (hneg₂ : ∀ t ∈ Set.Ioo 0 b, deriv θ₂ t < 0)
    (hlim₁ : Filter.Tendsto θ₁ (𝓝[>] 0) Filter.atBot)
    (hlim₂ : Filter.Tendsto θ₂ (𝓝[>] 0) Filter.atTop) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ ∃ φ : ℝ → ℝ,
      ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) ∧
      (∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t) ∧
      φ '' Set.Ioo 0 1 = Set.univ ∧
      Set.EqOn φ θ₁ (Set.Ioo 0 a) ∧
      Set.EqOn φ (fun t => θ₂ (1 - t)) (Set.Ioo (1 - a) 1) := by
  obtain ⟨a, β, ψ₁, ψ₂, ha, hab, ha14, hβ, hψ₁D, hψ₂D, hψ₁pos, hψ₂pos,
    eψ₁θ, eψ₂θ, hψ₁line, hψ₂line⟩ :=
    omb_interp_setup θ₁ θ₂ b hb0 hb12 hθ₁ hθ₂ hpos₁ hneg₂ hlim₁ hlim₂
  have h2a1 : 2 * a < 1 - 2 * a := by linarith
  have hhalf1 : 2 * a < 1 / 2 := by linarith
  have hhalf2 : (1 : ℝ) / 2 < 1 - 2 * a := by linarith
  have hagree : ∀ t ∈ Set.Icc (2 * a) (1 - 2 * a), -ψ₂ (1 - t) = ψ₁ t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have h1t : 2 * a ≤ 1 - t := by linarith [ht.2]
    rw [hψ₁line t ht.1, hψ₂line (1 - t) h1t]
    ring
  set φ : ℝ → ℝ := fun t => if t ≤ 1 / 2 then ψ₁ t else -ψ₂ (1 - t)
    with hφdef
  have eleft : ∀ s ∈ Set.Ioo (0 : ℝ) a, φ s = θ₁ s := by
    intro s hs
    have hs' : s < a := (Set.mem_Ioo.mp hs).2
    have hle : s ≤ 1 / 2 := by linarith [hs', ha14]
    change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = θ₁ s
    rw [ite_eq_left hle]
    exact eψ₁θ hs
  have eright : ∀ s ∈ Set.Ioo (1 - a) 1, φ s = θ₂ (1 - s) := by
    intro s hs
    have hs' := Set.mem_Ioo.mp hs
    have hle : ¬ s ≤ 1 / 2 := by linarith [hs'.1, ha14]
    change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = θ₂ (1 - s)
    rw [ite_eq_right hle]
    have h1s : (1 - s) ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
    have h2 := eψ₂θ h1s
    simpa using congrArg (fun x => -x) h2
  have hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    rcases lt_or_ge t (1 - 2 * a) with h1 | h1
    · have htmem : t ∈ Set.Ioo (0 : ℝ) (1 - 2 * a) := ⟨ht.1, h1⟩
      have hev : φ =ᶠ[𝓝 t] ψ₁ := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_left hle]
        · have hs2a : 2 * a < s := by linarith
          have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            exact ⟨le_of_lt hs2a, le_of_lt hs.2⟩
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_right hle]
          exact hagree s hsIcc
      have hψ₁at : ContDiffAt ℝ ∞ ψ₁ t :=
        hψ₁D.contDiffAt (isOpen_Ioi.mem_nhds ht.1)
      exact (hψ₁at.congr_of_eventuallyEq hev).contDiffWithinAt
    · have ht2a : 2 * a < t := lt_of_lt_of_le h2a1 h1
      have htmem : t ∈ Set.Ioo (2 * a) 1 := ⟨ht2a, ht.2⟩
      have hev : φ =ᶠ[𝓝 t] (fun s => -ψ₂ (1 - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            refine ⟨le_of_lt hs.1, ?_⟩
            linarith [hle, hhalf2]
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_left hle]
          exact (hagree s hsIcc).symm
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_right hle]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hψ₂at : ContDiffAt ℝ ∞ ψ₂ (1 - t) :=
        hψ₂D.contDiffAt (isOpen_Ioi.mem_nhds h1t)
      have hsub : ContDiffAt ℝ ∞ (fun s : ℝ => 1 - s) t :=
        contDiffAt_const.sub contDiffAt_id
      have hcomp : ContDiffAt ℝ ∞ (fun s => -ψ₂ (1 - s)) t :=
        (hψ₂at.comp t hsub).neg
      exact (hcomp.congr_of_eventuallyEq hev).contDiffWithinAt
  have hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    rcases lt_or_ge t (1 - 2 * a) with h1 | h1
    · have htmem : t ∈ Set.Ioo (0 : ℝ) (1 - 2 * a) := ⟨ht.1, h1⟩
      have hev : φ =ᶠ[𝓝 t] ψ₁ := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_left hle]
        · have hs2a : 2 * a < s := by linarith
          have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            exact ⟨le_of_lt hs2a, le_of_lt hs.2⟩
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = ψ₁ s
          rw [ite_eq_right hle]
          exact hagree s hsIcc
      rw [hev.deriv_eq]
      exact hψ₁pos t ht.1
    · have ht2a : 2 * a < t := lt_of_lt_of_le h2a1 h1
      have htmem : t ∈ Set.Ioo (2 * a) 1 := ⟨ht2a, ht.2⟩
      have hev : φ =ᶠ[𝓝 t] (fun s => -ψ₂ (1 - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
        rw [Set.mem_Ioo] at hs
        by_cases hle : s ≤ 1 / 2
        · have hsIcc : s ∈ Set.Icc (2 * a) (1 - 2 * a) := by
            rw [Set.mem_Icc]
            refine ⟨le_of_lt hs.1, ?_⟩
            linarith [hle, hhalf2]
          change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_left hle]
          exact (hagree s hsIcc).symm
        · change (if s ≤ 1 / 2 then ψ₁ s else -ψ₂ (1 - s)) = -ψ₂ (1 - s)
          rw [ite_eq_right hle]
      rw [hev.deriv_eq]
      have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
      have hψ₂d : HasDerivAt ψ₂ (deriv ψ₂ (1 - t)) (1 - t) :=
        ((hψ₂D.contDiffAt (isOpen_Ioi.mem_nhds h1t)).differentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
      have hsubd : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        have h := HasDerivAt.sub (hasDerivAt_const t 1) (hasDerivAt_id t)
        have efun : ((fun _ : ℝ => 1) - id) = (fun s : ℝ => 1 - s) := by
          funext s
          rfl
        have eval : (0 : ℝ) - 1 = -1 := by ring
        rw [efun, eval] at h
        exact h
      have hcompd := HasDerivAt.comp t hψ₂d hsubd
      have hnegd := HasDerivAt.neg hcompd
      have e2 : deriv (fun s : ℝ => -ψ₂ (1 - s)) t = deriv ψ₂ (1 - t) := by
        have e := hnegd.deriv
        have efun : (-(ψ₂ ∘ (fun s : ℝ => 1 - s))) =
            (fun s : ℝ => -ψ₂ (1 - s)) := by
          funext s
          rfl
        have eval : -(deriv ψ₂ (1 - t) * -1) = deriv ψ₂ (1 - t) := by ring
        rw [efun, eval] at e
        exact e
      rw [e2]
      exact hψ₂pos (1 - t) h1t
  have hφsurj : φ '' Set.Ioo 0 1 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    have hevLt : ∀ᶠ s in 𝓝[>] (0 : ℝ), θ₁ s < y :=
      hlim₁.eventually (Filter.eventually_lt_atBot y)
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := omb_eventually_nhdsGT_Ioo hevLt
    set s₁ := min δ₁ a / 2 with hs₁def
    have hm₁ : (0 : ℝ) < min δ₁ a := lt_min hδ₁pos ha
    have hs₁a : s₁ ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs₁def, hm₁], by linarith [hs₁def, min_le_right δ₁ a]⟩
    have hs₁δ : s₁ ∈ Set.Ioo (0 : ℝ) δ₁ :=
      ⟨by linarith [hs₁def, hm₁], by linarith [hs₁def, min_le_left δ₁ a]⟩
    have hφs₁ : φ s₁ < y := by
      rw [eleft s₁ hs₁a]
      exact hδ₁ s₁ hs₁δ
    have hevGt : ∀ᶠ s in 𝓝[>] (0 : ℝ), y < θ₂ s :=
      hlim₂.eventually (Filter.eventually_gt_atTop y)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := omb_eventually_nhdsGT_Ioo hevGt
    set s₂' := min δ₂ a / 2 with hs₂def
    have hm₂ : (0 : ℝ) < min δ₂ a := lt_min hδ₂pos ha
    have hs₂'a : s₂' ∈ Set.Ioo (0 : ℝ) a :=
      ⟨by linarith [hs₂def, hm₂], by linarith [hs₂def, min_le_right δ₂ a]⟩
    have hs₂'δ : s₂' ∈ Set.Ioo (0 : ℝ) δ₂ :=
      ⟨by linarith [hs₂def, hm₂], by linarith [hs₂def, min_le_left δ₂ a]⟩
    set s₂ := 1 - s₂' with hs₂def
    have hs₂ : s₂ ∈ Set.Ioo (1 - a) 1 :=
      ⟨by linarith [hs₂'a.2], by linarith [hs₂'a.1]⟩
    have hφs₂ : y < φ s₂ := by
      have e : φ s₂ = θ₂ (1 - s₂) := eright s₂ hs₂
      have e1s : (1 : ℝ) - s₂ = s₂' := by linarith
      rw [e, e1s]
      exact hδ₂ s₂' hs₂'δ
    have hs₁₂ : s₁ < s₂ := by linarith [hs₁a.2, hs₂.1, ha14]
    have hmem : y ∈ Set.Icc (φ s₁) (φ s₂) := ⟨le_of_lt hφs₁, le_of_lt hφs₂⟩
    have hcont : ContinuousOn φ (Set.Icc s₁ s₂) :=
      hφD.continuousOn.mono (by
        intro x hx
        rw [Set.mem_Icc] at hx
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hs₁a.1 hx.1, lt_of_le_of_lt hx.2 hs₂.2⟩)
    obtain ⟨s, hsIcc, hsφ⟩ :=
      intermediate_value_Icc (le_of_lt hs₁₂) hcont hmem
    refine ⟨s, ?_, hsφ⟩
    rw [Set.mem_Icc] at hsIcc
    rw [Set.mem_Ioo]
    exact ⟨lt_of_lt_of_le hs₁a.1 hsIcc.1, lt_of_le_of_lt hsIcc.2 hs₂.2⟩
  exact ⟨a, ha, hab, φ, hφD, hφderiv, hφsurj, eleft, eright⟩

/-- A chart-to-chart map between manifolds with the same model is a local
diffeomorphism. -/
private theorem omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    (e : OpenPartialHomeomorph X H) (he : e ∈ IsManifold.maximalAtlas I n X)
    (e' : OpenPartialHomeomorph Y H) (he' : e' ∈ IsManifold.maximalAtlas I n Y)
    (x : X) (hx : x ∈ e.source) (hmem : e x ∈ e'.target) :
    IsLocalDiffeomorphAt I I n (e'.symm ∘ e) x := by
  have hU : IsOpen (e.source ∩ e ⁻¹' e'.target) :=
    e.isOpen_inter_preimage e'.open_target
  have hV : IsOpen (e'.source ∩ e' ⁻¹' e.target) :=
    e'.isOpen_inter_preimage e.open_target
  have hf : Set.MapsTo (e'.symm ∘ e) (e.source ∩ e ⁻¹' e'.target)
      (e'.source ∩ e' ⁻¹' e.target) := by
    intro z hz
    obtain ⟨hzsrc, hztgt⟩ := hz
    rw [Set.mem_inter_iff]
    refine ⟨e'.map_target hztgt, ?_⟩
    rw [Set.mem_preimage, Function.comp_apply, e'.right_inv hztgt]
    exact e.map_source hzsrc
  have hf' : Set.MapsTo (e.symm ∘ e') (e'.source ∩ e' ⁻¹' e.target)
      (e.source ∩ e ⁻¹' e'.target) := by
    intro w hw
    obtain ⟨hwsrc, hwtgt⟩ := hw
    rw [Set.mem_inter_iff]
    refine ⟨e.map_target hwtgt, ?_⟩
    rw [Set.mem_preimage, Function.comp_apply, e.right_inv hwtgt]
    exact e'.map_source hwsrc
  have hleft : Set.LeftInvOn (e.symm ∘ e') (e'.symm ∘ e)
      (e.source ∩ e ⁻¹' e'.target) := by
    intro z hz
    obtain ⟨hzsrc, hztgt⟩ := hz
    simp only [Function.comp_apply, e'.right_inv hztgt, e.left_inv hzsrc]
  have hright : Set.RightInvOn (e.symm ∘ e') (e'.symm ∘ e)
      (e'.source ∩ e' ⁻¹' e.target) := by
    intro w hw
    obtain ⟨hwsrc, hwtgt⟩ := hw
    simp only [Function.comp_apply, e.right_inv hwtgt, e'.left_inv hwsrc]
  have h1U : ContMDiffOn I I n e (e.source ∩ e ⁻¹' e'.target) :=
    (contMDiffOn_of_mem_maximalAtlas he).mono Set.inter_subset_left
  have hfD : ContMDiffOn I I n (e'.symm ∘ e)
      (e.source ∩ e ⁻¹' e'.target) := by
    have h2 := contMDiffOn_symm_of_mem_maximalAtlas he'
    refine h2.comp h1U (by intro z hz; exact hz.2)
  have h1V : ContMDiffOn I I n e' (e'.source ∩ e' ⁻¹' e.target) :=
    (contMDiffOn_of_mem_maximalAtlas he').mono Set.inter_subset_left
  have hf'D : ContMDiffOn I I n (e.symm ∘ e')
      (e'.source ∩ e' ⁻¹' e.target) := by
    have h2 := contMDiffOn_symm_of_mem_maximalAtlas he
    refine h2.comp h1V (by intro w hw; exact hw.2)
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ hU hV hf hf' ⟨hleft, hright⟩
    hfD hf'D x ⟨hx, hmem⟩

/-- The left Icc chart is in the maximal atlas. -/
private theorem omb_IccLeftChart_mem_maximalAtlas :
    IccLeftChart (0 : ℝ) 1 ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ (Set.Icc (0 : ℝ) 1) := by
  have hbot : (⊥ : Set.Icc (0 : ℝ) 1).val < 1 := by
    rw [Set.Icc.coe_bot]
    norm_num
  have e : chartAt (EuclideanHalfSpace 1) (⊥ : Set.Icc (0 : ℝ) 1) =
      IccLeftChart 0 1 :=
    Icc_chartedSpaceChartAt_of_le_top hbot
  rw [← e]
  exact IsManifold.chart_mem_maximalAtlas _

/-- The right Icc chart is in the maximal atlas. -/
private theorem omb_IccRightChart_mem_maximalAtlas :
    IccRightChart (0 : ℝ) 1 ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ (Set.Icc (0 : ℝ) 1) := by
  have htop : (1 : ℝ) ≤ (⊤ : Set.Icc (0 : ℝ) 1).val := by
    rw [Set.Icc.coe_top]
  have e : chartAt (EuclideanHalfSpace 1) (⊤ : Set.Icc (0 : ℝ) 1) =
      IccRightChart 0 1 :=
    Icc_chartedSpaceChartAt_of_top_le htop
  rw [← e]
  exact IsManifold.chart_mem_maximalAtlas _

/-- The inclusion of the open interval of `Icc 0 1` is a local diffeomorphism. -/
private theorem omb_isLocalDiffeomorphAt_Icc_val (z : Set.Icc (0 : ℝ) 1)
    (h0 : 0 < z.val) (h1 : z.val < 1) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val z := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hU : IsOpen {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    have e : {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} =
        Subtype.val ⁻¹' Set.Ioo (0 : ℝ) 1 := rfl
    rw [e]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hV : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hf : Set.MapsTo Subtype.val
      {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    exact hz
  have hf' : Set.MapsTo (Set.projIcc 0 1 h01) (Set.Ioo (0 : ℝ) 1)
      {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    intro u hu
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have e : (Set.projIcc 0 1 h01 u).val = u :=
      congrArg Subtype.val (Set.projIcc_of_mem h01 hmem)
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hu.1
    · rw [e]
      exact hu.2
  have hleft : Set.LeftInvOn (Set.projIcc 0 1 h01) Subtype.val
      {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} := by
    intro z hz
    have hmem : z.val ∈ Set.Icc (0 : ℝ) 1 := z.2
    have e : Set.projIcc 0 1 h01 z.val = ⟨z.val, hmem⟩ :=
      Set.projIcc_of_mem h01 hmem
    rw [e]
  have hright : Set.RightInvOn (Set.projIcc 0 1 h01) Subtype.val
      (Set.Ioo (0 : ℝ) 1) := by
    intro u hu
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    exact congrArg Subtype.val (Set.projIcc_of_mem h01 hmem)
  have hval : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) := contMDiff_subtypeVal_Icc
  have hfD : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val
      {z : Set.Icc (0 : ℝ) 1 | 0 < z.val ∧ z.val < 1} :=
    (contMDiffOn_univ.mpr hval).mono (Set.subset_univ _)
  have hproj : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc 0 1 h01)
      (Set.Icc (0 : ℝ) 1) := contMDiffOn_projIcc
  have hf'D : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc 0 1 h01)
      (Set.Ioo (0 : ℝ) 1) :=
    hproj.mono Set.Ioo_subset_Icc_self
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ hU hV hf hf' ⟨hleft, hright⟩
    hfD hf'D z ⟨h0, h1⟩

/-- Two right ends coincide. -/
private theorem omb_end_unique_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x y : M)
    (hx : (𝓡∂ 1).IsBoundaryPoint x) (hy : (𝓡∂ 1).IsBoundaryPoint y)
    (hlimx : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atTop)
    (hlimy : Filter.Tendsto (ombTheta M Ψ x₀ y) (𝓝[>] 0) Filter.atTop) :
    x = y := by
  by_contra hne
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hdisj⟩ := t2_separation hne
  obtain ⟨εx, hεx⟩ := omb_exists_halfCurve_radius M x hx
  obtain ⟨εy, hεy⟩ := omb_exists_halfCurve_radius M y hy
  obtain ⟨R₁, hR₁⟩ :=
    omb_absorb_right M Ψ x₀ x hx εx hεx hlimx U (hUopen.mem_nhds hxU)
  obtain ⟨R₂, hR₂⟩ :=
    omb_absorb_right M Ψ x₀ y hy εy hεy hlimy V (hVopen.mem_nhds hyV)
  have hu1 : max R₁ R₂ + 1 > R₁ := by
    calc R₁ ≤ max R₁ R₂ := le_max_left _ _
      _ < max R₁ R₂ + 1 := by linarith
  have hu2 : max R₁ R₂ + 1 > R₂ := by
    calc R₂ ≤ max R₁ R₂ := le_max_right _ _
      _ < max R₁ R₂ + 1 := by linarith
  have huU := hR₁ _ hu1
  have huV := hR₂ _ hu2
  exact (Set.disjoint_left.mp hdisj) huU huV

/-- There is a left end: a cluster point of the `atBot` tail. -/
private theorem omb_exists_left_end (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ q : M, (𝓡∂ 1).IsBoundaryPoint q ∧
      Filter.Tendsto (ombTheta M Ψ x₀ q) (𝓝[>] 0) Filter.atBot := by
  have hleBot : Filter.map (ombValPsi M Ψ) Filter.atBot ≤ Filter.principal (Set.univ : Set M) := by
    simp
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_mapClusterPt hleBot
  have hmB : (𝓡∂ 1).IsBoundaryPoint m := by
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) m
      with hI | hB
    · exfalso
      exact omb_mapClusterPt_atBot_not_mem M Ψ m hm
        (SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M m).mpr hI))
    · exact hB
  rcases omb_theta_tendsto M Ψ x₀ m hmB with hL | hR
  · exact ⟨m, hmB, hL⟩
  · exfalso
    exact omb_mapClusterPt_atBot_not_right M Ψ x₀ m hmB hm hR

/-- There is a right end: a cluster point of the `atTop` tail. -/
private theorem omb_exists_right_end (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ p : M, (𝓡∂ 1).IsBoundaryPoint p ∧
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  have hleTop : Filter.map (ombValPsi M Ψ) Filter.atTop ≤ Filter.principal (Set.univ : Set M) := by
    simp
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_mapClusterPt hleTop
  have hmB : (𝓡∂ 1).IsBoundaryPoint m := by
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) m
      with hI | hB
    · exfalso
      exact omb_mapClusterPt_atTop_not_mem M Ψ m hm
        (SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M m).mpr hI))
    · exact hB
  rcases omb_theta_tendsto M Ψ x₀ m hmB with hL | hR
  · exfalso
    exact omb_mapClusterPt_atTop_not_left M Ψ x₀ m hmB hm hL
  · exact ⟨m, hmB, hR⟩

/-- The boundary is exactly one left end and one right end. -/
private theorem omb_boundary_eq_pair (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ q p : M, q ≠ p ∧ ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} ∧
      Filter.Tendsto (ombTheta M Ψ x₀ q) (𝓝[>] 0) Filter.atBot ∧
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  obtain ⟨q, hqb, hqlim⟩ := omb_exists_left_end M Ψ x₀
  obtain ⟨p, hpb, hplim⟩ := omb_exists_right_end M Ψ x₀
  have hne : q ≠ p := by
    intro hcon
    rw [hcon] at hqlim
    exact omb_end_not_both M Ψ x₀ p hqlim hplim
  refine ⟨q, p, hne, ?_, hqlim, hplim⟩
  ext z
  constructor
  · intro hz
    have hzb : (𝓡∂ 1).IsBoundaryPoint z := hz
    rcases omb_theta_tendsto M Ψ x₀ z hzb with hL | hR
    · left
      exact omb_end_unique_left M Ψ x₀ z q hzb hqb hL hqlim
    · right
      exact omb_end_unique_right M Ψ x₀ z p hzb hpb hR hplim
  · intro hz
    rcases Set.mem_insert_iff.mp hz with h | h
    · rw [h]
      exact hqb
    · rw [Set.mem_singleton_iff.mp h]
      exact hpb

/-- Sign extraction: a left end has positive derivative on the tail. -/
private theorem omb_theta_sign_of_atBot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot) :
    ∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t := by
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exact hpos
  · exfalso
    exact omb_end_not_both M Ψ x₀ p hlim
      (omb_theta_tendsto_atTop M Ψ x₀ p hp ε hε hneg)

/-- Sign extraction: a right end has negative derivative on the tail. -/
private theorem omb_theta_sign_of_atTop (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop) :
    ∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0 := by
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exfalso
    exact omb_end_not_both M Ψ x₀ p
      (omb_theta_tendsto_atBot M Ψ x₀ p hp ε hε hpos) hlim
  · exact hneg

/-- Gluing setup: ends, radii, and the interpolating reparametrisation. -/
private theorem omb_glue_setup (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    ∃ (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) (x₀ : ↥(ombInterior M))
      (q p : M) (εq εp a : ℝ) (φ : ℝ → ℝ),
      (𝓡∂ 1).IsBoundaryPoint q ∧ (𝓡∂ 1).IsBoundaryPoint p ∧ q ≠ p ∧
      ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} ∧
      ombGoodRadius M q εq ∧ ombGoodRadius M p εp ∧
      0 < a ∧ a < 1 / 2 ∧ a ≤ εq ∧ a ≤ εp ∧
      ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) ∧
      (∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t) ∧ φ '' Set.Ioo 0 1 = Set.univ ∧
      Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a) ∧
      Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1) := by
  obtain ⟨Ψ⟩ := omb_exists_diffeomorph_real_interior M hB
  obtain ⟨xw, hxw⟩ := omb_nonempty_ombInterior M
  refine ⟨Ψ, ⟨xw, hxw⟩, ?_⟩
  obtain ⟨q, p, hne, hbp_eq, hqlim, hplim⟩ := omb_boundary_eq_pair M Ψ ⟨xw, hxw⟩
  have hqb : (𝓡∂ 1).IsBoundaryPoint q := by
    change q ∈ ModelWithCorners.boundary (I := 𝓡∂ 1) M
    rw [hbp_eq]
    exact Set.mem_insert q {p}
  have hpb : (𝓡∂ 1).IsBoundaryPoint p := by
    change p ∈ ModelWithCorners.boundary (I := 𝓡∂ 1) M
    rw [hbp_eq]
    exact Set.mem_insert_of_mem q rfl
  obtain ⟨εq, hεq⟩ := omb_exists_halfCurve_radius M q hqb
  obtain ⟨εp, hεp⟩ := omb_exists_halfCurve_radius M p hpb
  have hposq := omb_theta_sign_of_atBot M Ψ ⟨xw, hxw⟩ q hqb εq hεq hqlim
  have hnegp := omb_theta_sign_of_atTop M Ψ ⟨xw, hxw⟩ p hpb εp hεp hplim
  have hb0 : 0 < min (min εq εp) (1 / 2) :=
    lt_min (lt_min hεq.1 hεp.1) (by norm_num)
  have hb12 : min (min εq εp) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hbεq : min (min εq εp) (1 / 2) ≤ εq :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hbεp : min (min εq εp) (1 / 2) ≤ εp :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hθq : ContDiffOn ℝ ∞ (ombTheta M Ψ ⟨xw, hxw⟩ q)
      (Set.Ioo 0 (min (min εq εp) (1 / 2))) :=
    (omb_theta_contDiffOn M Ψ ⟨xw, hxw⟩ q εq hεq).mono
      (Set.Ioo_subset_Ioo le_rfl hbεq)
  have hθp : ContDiffOn ℝ ∞ (ombTheta M Ψ ⟨xw, hxw⟩ p)
      (Set.Ioo 0 (min (min εq εp) (1 / 2))) :=
    (omb_theta_contDiffOn M Ψ ⟨xw, hxw⟩ p εp hεp).mono
      (Set.Ioo_subset_Ioo le_rfl hbεp)
  have hposq' : ∀ t ∈ Set.Ioo 0 (min (min εq εp) (1 / 2)),
      0 < deriv (ombTheta M Ψ ⟨xw, hxw⟩ q) t :=
    fun t ht => hposq t (Set.Ioo_subset_Ioo le_rfl hbεq ht)
  have hnegp' : ∀ t ∈ Set.Ioo 0 (min (min εq εp) (1 / 2)),
      deriv (ombTheta M Ψ ⟨xw, hxw⟩ p) t < 0 :=
    fun t ht => hnegp t (Set.Ioo_subset_Ioo le_rfl hbεp ht)
  obtain ⟨a, ha, hab, φ, hφD, hφderiv, hφsurj, eleft, eright⟩ :=
    omb_exists_interpolation (ombTheta M Ψ ⟨xw, hxw⟩ q)
      (ombTheta M Ψ ⟨xw, hxw⟩ p) _ hb0 hb12 hθq hθp hposq' hnegp' hqlim hplim
  have hbp_eq : ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} := by
    ext z
    constructor
    · intro hz
      have hzb : (𝓡∂ 1).IsBoundaryPoint z := hz
      rcases omb_theta_tendsto M Ψ ⟨xw, hxw⟩ z hzb with hL | hR
      · left
        exact omb_end_unique_left M Ψ ⟨xw, hxw⟩ z q hzb hqb hL hqlim
      · right
        exact omb_end_unique_right M Ψ ⟨xw, hxw⟩ z p hzb hpb hR hplim
    · intro hz
      rcases Set.mem_insert_iff.mp hz with h | h
      · rw [h]
        exact hqb
      · rw [Set.mem_singleton_iff.mp h]
        exact hpb
  refine ⟨q, p, εq, εp, a, φ, hqb, hpb, hne, hbp_eq, hεq, hεp, ha, ?_, ?_, ?_,
    hφD, hφderiv, hφsurj, eleft, eright⟩
  · exact lt_of_lt_of_le hab hb12
  · exact le_trans (le_of_lt hab) hbεq
  · exact le_trans (le_of_lt hab) hbεp

/-- The gluing map `Set.Icc 0 1 → M`: left half-curve, right half-curve, middle. -/
private def ombGlueF (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ) : Set.Icc (0 : ℝ) 1 → M := by
  classical
  exact fun z =>
    if z.val < a then ombHalfCurve M q z.val
    else if 1 - a < z.val then ombHalfCurve M p (1 - z.val)
    else ombValPsi M Ψ (φ z.val)

/-- The gluing map on the left piece. -/
private theorem ombGlueF_of_lt (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1) (h : z.val < a) :
    ombGlueF M Ψ q p a φ z = ombHalfCurve M q z.val := by
  classical
  unfold ombGlueF
  rw [ite_eq_left h]

/-- The gluing map on the right piece. -/
private theorem ombGlueF_of_gt (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1)
    (h1 : ¬ z.val < a) (h2 : 1 - a < z.val) :
    ombGlueF M Ψ q p a φ z = ombHalfCurve M p (1 - z.val) := by
  classical
  unfold ombGlueF
  rw [ite_eq_right h1, ite_eq_left h2]

/-- The gluing map on the middle piece. -/
private theorem ombGlueF_of_mid (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ) (z : Set.Icc (0 : ℝ) 1)
    (h1 : ¬ z.val < a) (h2 : ¬ 1 - a < z.val) :
    ombGlueF M Ψ q p a φ z = ombValPsi M Ψ (φ z.val) := by
  classical
  unfold ombGlueF
  rw [ite_eq_right h1, ite_eq_right h2]

/-- The gluing map is a local diffeomorphism on the left piece. -/
private theorem ombGlueF_local_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq : ℝ) (hεq : ombGoodRadius M q εq)
    (haεq : a ≤ εq) (ha12 : a < 1 / 2)
    (z : Set.Icc (0 : ℝ) 1) (hz : z.val < a) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  have hz1 : z.val < 1 := lt_trans hz (lt_trans ha12 (by norm_num))
  have hsrc : z ∈ (IccLeftChart 0 1).source := by
    change z.val < 1
    exact hz1
  have htgt : IccLeftChart 0 1 z ∈ (chartAt (EuclideanHalfSpace 1) q).target := by
    rw [← omb_symm_leftChart z]
    apply hεq.2.2
    have h0 : 0 ≤ z.val := z.property.1
    rw [abs_of_nonneg h0]
    exact lt_of_lt_of_le hz haεq
  have hchart := omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
    (IccLeftChart 0 1) omb_IccLeftChart_mem_maximalAtlas
    (chartAt (EuclideanHalfSpace 1) q)
    (IsManifold.chart_mem_maximalAtlas q) z hsrc htgt
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | w.val < a} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | w.val < a} = Subtype.val ⁻¹' Set.Iio a :=
      rfl
    rw [e]
    exact isOpen_Iio.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      ((chartAt (EuclideanHalfSpace 1) q).symm ∘ IccLeftChart 0 1) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (ombGlueF_of_lt M Ψ q p a φ w hw).trans
      (omb_halfCurve_leftChart M q w)
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hchart hev

/-- The gluing map is a local diffeomorphism on the right piece. -/
private theorem ombGlueF_local_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εp : ℝ) (hεp : ombGoodRadius M p εp)
    (haεp : a ≤ εp) (ha12 : a < 1 / 2)
    (z : Set.Icc (0 : ℝ) 1) (hright : 1 - a < z.val) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  have h0z : 0 < z.val := lt_trans (by linarith : (0 : ℝ) < 1 - a) hright
  have hsrc : z ∈ (IccRightChart 0 1).source := by
    change 0 < z.val
    exact h0z
  have htgt : IccRightChart 0 1 z ∈ (chartAt (EuclideanHalfSpace 1) p).target := by
    rw [← omb_symm_rightChart z]
    apply hεp.2.2
    have hle : 0 ≤ 1 - z.val := by linarith [z.property.2]
    rw [abs_of_nonneg hle]
    calc 1 - z.val < a := by linarith
      _ ≤ εp := haεp
  have hchart := omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
    (IccRightChart 0 1) omb_IccRightChart_mem_maximalAtlas
    (chartAt (EuclideanHalfSpace 1) p)
    (IsManifold.chart_mem_maximalAtlas p) z hsrc htgt
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | 1 - a < w.val} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | 1 - a < w.val} =
        Subtype.val ⁻¹' Set.Ioi (1 - a) := rfl
    rw [e]
    exact isOpen_Ioi.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      ((chartAt (EuclideanHalfSpace 1) p).symm ∘ IccRightChart 0 1) := by
    filter_upwards [hU.mem_nhds hright] with w hw
    have hwleft : ¬ w.val < a := by
      have : 1 - a < w.val := hw
      linarith [ha12]
    exact (ombGlueF_of_gt M Ψ q p a φ w hwleft hw).trans
      (omb_halfCurve_rightChart M p w)
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hchart hev

/-- On the open interval, the gluing map is the middle composite. -/
private theorem ombGlueF_eq_mid (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    ombGlueF M Ψ q p a φ z = ombValPsi M Ψ (φ z.val) := by
  by_cases hleft : z.val < a
  · rw [ombGlueF_of_lt M Ψ q p a φ z hleft]
    have hmem : z.val ∈ Set.Ioo (0 : ℝ) a := ⟨h0, hleft⟩
    have eφ : φ z.val = ombTheta M Ψ x₀ q z.val := eleft hmem
    rw [eφ]
    have hε : z.val ∈ Set.Ioo (0 : ℝ) εq := ⟨h0, lt_of_lt_of_le hleft haεq⟩
    exact (omb_theta_apply M Ψ x₀ q εq hεq z.val hε).symm
  · by_cases hright : 1 - a < z.val
    · rw [ombGlueF_of_gt M Ψ q p a φ z hleft hright]
      have hmem : z.val ∈ Set.Ioo (1 - a) 1 := ⟨hright, h1⟩
      have eφ : φ z.val = ombTheta M Ψ x₀ p (1 - z.val) := eright hmem
      rw [eφ]
      have h1w : (1 - z.val) ∈ Set.Ioo (0 : ℝ) εp :=
        ⟨by linarith, lt_of_lt_of_le (by linarith) haεp⟩
      exact (omb_theta_apply M Ψ x₀ p εp hεp (1 - z.val) h1w).symm
    · exact ombGlueF_of_mid M Ψ q p a φ z hleft hright

/-- The gluing map is a local diffeomorphism on the middle piece. -/
private theorem ombGlueF_local_mid (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  obtain ⟨Φ, hΦsrc, hΦfun, -, -, -⟩ :=
    odm_exists_partialDiffeomorph_of_deriv_pos (Set.Ioo 0 1) φ isOpen_Ioo
      (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) hφD hφderiv
  have h1φ : IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val z :=
    omb_isLocalDiffeomorphAt_Icc_val z h0 h1
  have hmem : z.val ∈ Φ.source := by
    rw [hΦsrc]
    exact ⟨h0, h1⟩
  have h2φ0 := PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Φ hmem
  rw [hΦfun] at h2φ0
  have h3φ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Ψ (φ z.val) :=
    Ψ.isLocalDiffeomorph _
  have h4φ : IsLocalDiffeomorphAt (𝓡 1) (𝓡∂ 1) ∞ Subtype.val (Ψ (φ z.val)) :=
    omb_isLocalDiffeomorph_val M x₀ _
  have h12 := IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) h1φ h2φ0
  have h123 := IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := ↥(ombInterior M)) h12 h3φ
  have hcomp := IsLocalDiffeomorphAt.comp (K := (𝓡∂ 1)) (P := M) h123 h4φ
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | 0 < w.val ∧ w.val < 1} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | 0 < w.val ∧ w.val < 1} =
        Subtype.val ⁻¹' Set.Ioo (0 : ℝ) 1 := rfl
    rw [e]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      (Subtype.val ∘ ⇑Ψ ∘ φ ∘ Subtype.val) := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with w hw
    exact ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright
      w hw.1 hw.2
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hev

/-- The gluing map is a local diffeomorphism everywhere. -/
private theorem ombGlueF_isLocalDiffeomorph (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) := by
  intro z
  by_cases hleft : z.val < a
  · exact ombGlueF_local_left M Ψ q p a φ εq hεq haεq ha12 z hleft
  · by_cases hright : 1 - a < z.val
    · exact ombGlueF_local_right M Ψ q p a φ εp hεp haεp ha12 z hright
    · have h0 : 0 < z.val := lt_of_lt_of_le ha0 (le_of_not_gt hleft)
      have h1 : z.val < 1 :=
        lt_of_le_of_lt (le_of_not_gt hright) (by linarith)
      exact ombGlueF_local_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp hφD
        hφderiv eleft eright z h0 h1

/-- The gluing map sends `⊥` to the left end. -/
private theorem ombGlueF_bot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (hqb : (𝓡∂ 1).IsBoundaryPoint q) :
    ombGlueF M Ψ q p a φ ⊥ = q := by
  have h0a : (⊥ : Set.Icc (0 : ℝ) 1).val < a := by
    rw [Set.Icc.coe_bot]
    exact ha0
  rw [ombGlueF_of_lt M Ψ q p a φ ⊥ h0a, Set.Icc.coe_bot]
  exact omb_halfCurve_zero M q hqb

/-- The gluing map sends `⊤` to the right end. -/
private theorem ombGlueF_top (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (hpb : (𝓡∂ 1).IsBoundaryPoint p) :
    ombGlueF M Ψ q p a φ ⊤ = p := by
  have hna : ¬ (⊤ : Set.Icc (0 : ℝ) 1).val < a := by
    rw [Set.Icc.coe_top]
    have hle : a ≤ 1 := by linarith
    exact not_lt.mpr hle
  have hgt : 1 - a < (⊤ : Set.Icc (0 : ℝ) 1).val := by
    rw [Set.Icc.coe_top]
    linarith
  rw [ombGlueF_of_gt M Ψ q p a φ ⊤ hna hgt, Set.Icc.coe_top]
  have e0 : (1 : ℝ) - (1 : ℝ) = 0 := by norm_num
  rw [e0]
  exact omb_halfCurve_zero M p hpb

/-- The gluing map sends a point of value `0` to the left end. -/
private theorem ombGlueF_of_val_zero (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (hqb : (𝓡∂ 1).IsBoundaryPoint q)
    (z : Set.Icc (0 : ℝ) 1) (hz0 : z.val = 0) :
    ombGlueF M Ψ q p a φ z = q := by
  have h0a : z.val < a := by
    rw [hz0]
    exact ha0
  rw [ombGlueF_of_lt M Ψ q p a φ z h0a, hz0]
  exact omb_halfCurve_zero M q hqb

/-- The gluing map sends a point of value `1` to the right end. -/
private theorem ombGlueF_of_val_one (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (z : Set.Icc (0 : ℝ) 1) (hz1 : z.val = 1) :
    ombGlueF M Ψ q p a φ z = p := by
  have hna : ¬ z.val < a := by
    rw [hz1]
    have hle : a ≤ 1 := by linarith
    exact not_lt.mpr hle
  have hgt : 1 - a < z.val := by
    rw [hz1]
    linarith
  rw [ombGlueF_of_gt M Ψ q p a φ z hna hgt]
  have e0 : (1 : ℝ) - z.val = 0 := by
    rw [hz1]
    norm_num
  rw [e0]
  exact omb_halfCurve_zero M p hpb

/-- Interior points of `Icc` land in the interior of `M`. -/
private theorem ombGlueF_mem_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    ombGlueF M Ψ q p a φ z ∈ (ombInterior M : Set M) := by
  rw [ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright z h0
    h1]
  exact (Ψ (φ z.val)).2

/-- The gluing map is injective on interior points of `Icc`. -/
private theorem ombGlueF_interior_inj (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z₁ z₂ : Set.Icc (0 : ℝ) 1)
    (h10 : 0 < z₁.val) (h11 : z₁.val < 1) (h20 : 0 < z₂.val) (h21 : z₂.val < 1)
    (h12 : ombGlueF M Ψ q p a φ z₁ = ombGlueF M Ψ q p a φ z₂) :
    z₁ = z₂ := by
  have hmono : StrictMonoOn φ (Set.Ioo 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) hφD.continuousOn
    rw [interior_Ioo]
    exact hφderiv
  have e1 := ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft
    eright z₁ h10 h11
  have e2 := ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft
    eright z₂ h20 h21
  rw [e1, e2] at h12
  have hcomp : Function.Injective (Subtype.val ∘ ⇑Ψ) :=
    Subtype.val_injective.comp Ψ.toEquiv.injective
  have e : (Subtype.val ∘ ⇑Ψ) = ombValPsi M Ψ := rfl
  rw [e] at hcomp
  have hφ : φ z₁.val = φ z₂.val := hcomp h12
  have hval : z₁.val = z₂.val := hmono.injOn ⟨h10, h11⟩ ⟨h20, h21⟩ hφ
  exact Subtype.ext hval

/-- The gluing map is injective. -/
private theorem ombGlueF_injective (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (hne : q ≠ p)
    (hqb : (𝓡∂ 1).IsBoundaryPoint q) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    Function.Injective (ombGlueF M Ψ q p a φ) := by
  have hqS : q ∉ (ombInterior M : Set M) := omb_boundary_not_mem_interior M q hqb
  have hpS : p ∉ (ombInterior M : Set M) := omb_boundary_not_mem_interior M p hpb
  have hpos_of_ne_zero : ∀ z : Set.Icc (0 : ℝ) 1, z.val ≠ 0 → 0 < z.val := by
    intro z hz
    exact lt_of_le_of_ne' z.property.1 hz
  intro z₁ z₂ h12
  by_cases hz1bot : z₁.val = 0
  · have e1 : z₁ = ⊥ :=
      Subtype.ext (by rw [Set.Icc.coe_bot]; exact hz1bot)
    have e2 : z₂ = ⊥ := by
      by_cases hz2bot : z₂.val = 0
      · exact Subtype.ext (by rw [Set.Icc.coe_bot]; exact hz2bot)
      · exfalso
        have hpos := hpos_of_ne_zero z₂ hz2bot
        have hFq : ombGlueF M Ψ q p a φ z₂ = q := by
          rw [← h12, e1]
          exact ombGlueF_bot M Ψ q p a φ ha0 hqb
        by_cases hz2top : z₂.val = 1
        · have hFp : ombGlueF M Ψ q p a φ z₂ = p :=
            ombGlueF_of_val_one M Ψ q p a φ ha0 ha12 hpb z₂ hz2top
          exact hne (hFq.symm.trans hFp)
        · have hlt : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          have hS := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₂ hpos hlt
          rw [hFq] at hS
          exact hqS hS
    exact e1.trans e2.symm
  · by_cases hz1top : z₁.val = 1
    · have e1 : z₁ = ⊤ :=
        Subtype.ext (by rw [Set.Icc.coe_top]; exact hz1top)
      have hFp2 : ombGlueF M Ψ q p a φ z₂ = p := by
        rw [← h12, e1]
        exact ombGlueF_top M Ψ q p a φ ha0 ha12 hpb
      by_cases hz2bot : z₂.val = 0
      · exfalso
        have hFq : ombGlueF M Ψ q p a φ z₂ = q :=
          ombGlueF_of_val_zero M Ψ q p a φ ha0 hqb z₂ hz2bot
        exact hne (hFq.symm.trans hFp2)
      · have hpos := hpos_of_ne_zero z₂ hz2bot
        by_cases hz2top : z₂.val = 1
        · exact e1.trans
              (Subtype.ext (by rw [Set.Icc.coe_top]; exact hz2top)).symm
        · exfalso
          have hlt : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          have hS := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₂ hpos hlt
          rw [hFp2] at hS
          exact hpS hS
    · have h10 : 0 < z₁.val := hpos_of_ne_zero z₁ hz1bot
      have h11 : z₁.val < 1 := lt_of_le_of_ne z₁.property.2 hz1top
      by_cases hz2bot : z₂.val = 0
      · exfalso
        have hS1 := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
          haεp eleft eright z₁ h10 h11
        rw [h12] at hS1
        have hFq : ombGlueF M Ψ q p a φ z₂ = q :=
          ombGlueF_of_val_zero M Ψ q p a φ ha0 hqb z₂ hz2bot
        rw [hFq] at hS1
        exact hqS hS1
      · have hpos := hpos_of_ne_zero z₂ hz2bot
        by_cases hz2top : z₂.val = 1
        · exfalso
          have hS1 := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₁ h10 h11
          rw [h12] at hS1
          have hFp : ombGlueF M Ψ q p a φ z₂ = p :=
            ombGlueF_of_val_one M Ψ q p a φ ha0 ha12 hpb z₂ hz2top
          rw [hFp] at hS1
          exact hpS hS1
        · have h21 : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          exact ombGlueF_interior_inj M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp
            hφD hφderiv eleft eright z₁ z₂ h10 h11 hpos h21 h12

/-- The gluing map is surjective. -/
private theorem ombGlueF_surjective (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (ha0 : 0 < a) (ha12 : a < 1 / 2)
    (hqb : (𝓡∂ 1).IsBoundaryPoint q) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (hbp_eq : ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p})
    (hφsurj : φ '' Set.Ioo 0 1 = Set.univ)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    Function.Surjective (ombGlueF M Ψ q p a φ) := by
  intro m
  have hunion : m ∈ (↑(ombInterior M) : Set M) ∪ {q, p} := by
    have h := ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 1) (M := M)
    rw [hbp_eq] at h
    change m ∈ (𝓡∂ 1).interior M ∪ {q, p}
    rw [h]
    exact Set.mem_univ m
  rcases hunion with hmS | hmqp
  · obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
    have hmem : u₀ ∈ φ '' Set.Ioo 0 1 := by
      rw [hφsurj]
      exact Set.mem_univ u₀
    obtain ⟨t, ht, htu⟩ := hmem
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    refine ⟨⟨t, htIcc⟩, ?_⟩
    have h0 : (0 : ℝ) < (⟨t, htIcc⟩ : Set.Icc (0 : ℝ) 1).val := ht.1
    have h1 : (⟨t, htIcc⟩ : Set.Icc (0 : ℝ) 1).val < 1 := ht.2
    rw [ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright _
      h0 h1]
    rw [htu]
    exact hu₀
  · rcases Set.mem_insert_iff.mp hmqp with h | h
    · rw [h]
      exact ⟨⊥, ombGlueF_bot M Ψ q p a φ ha0 hqb⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨⊤, ombGlueF_top M Ψ q p a φ ha0 ha12 hpb⟩

/-- Boundary case: `M` is diffeomorphic to `Set.Icc 0 1`. -/
private theorem omb_diffeomorph_Icc_of_boundary_nonempty (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨Ψ, x₀, q, p, εq, εp, a, φ, hqb, hpb, hne, hbp_eq, hεq, hεp, ha0,
    ha12, haεq, haεp, hφD, hφderiv, hφsurj, eleft, eright⟩ := omb_glue_setup M hB
  have hld := ombGlueF_isLocalDiffeomorph M Ψ x₀ q p a φ εq εp hεq hεp ha0
    ha12 haεq haεp hφD hφderiv eleft eright
  have hinj := ombGlueF_injective M Ψ x₀ q p a φ εq εp hεq hεp hne hqb hpb ha0
    ha12 haεq haεp hφD hφderiv eleft eright
  have hsurj := ombGlueF_surjective M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp ha0
    ha12 hqb hpb hbp_eq hφsurj eleft eright
  exact ⟨(hld.diffeomorphOfBijective ⟨hinj, hsurj⟩).symm⟩

/--
**Classification of compact connected $1$-manifolds with boundary.** Every compact, connected,
Hausdorff, second-countable smooth $1$-manifold $M$ with (possibly empty) boundary is
diffeomorphic either to the circle $S^1$ or to the closed interval $[0, 1]$.

Proves `Wanted` entry `compact_connected_one_manifold_with_boundary_classification`.

Source: Classification of 1-manifolds with
boundary; Hirsch, Differential Topology; J. Lee, Introduction to Smooth Manifolds, 2nd ed.,
collar theorem; Lean states compact connected `𝓡∂ 1` with closed interval specialization.
-/
theorem compact_connected_one_manifold_with_boundary_classification
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ (Set.Icc (0 : ℝ) 1)) := by
  rcases Set.eq_empty_or_nonempty (ModelWithCorners.boundary (I := 𝓡∂ 1) M) with
    hB | hB
  · exact Or.inl (omb_circle_of_boundary_empty M hB)
  · obtain ⟨D⟩ := omb_diffeomorph_Icc_of_boundary_nonempty M hB
    exact Or.inr ⟨D⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
