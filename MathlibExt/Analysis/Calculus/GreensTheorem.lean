/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof

/-!
# Green's theorem for a simple piecewise C¹ boundary

The boundary may belong to the region, and the tangent may vanish at subdivision points.
To avoid assuming a global separation theorem, first retain an exterior weight in the line
integral. At a transverse slice the left side is interior; the jump records whether the other
side is exterior. Almost every slice is regular, and one-dimensional change of variables counts
the crossings with multiplicity. Applying the resulting weighted identity to exact differentials
shows that the weight does not change across the exceptional times. Positive area then forces
the weight to be one.

For the classical theorem with a rectifiable Jordan boundary (not just coordinate-simple
regions), see [Green's theorem: proof for rectifiable Jordan curves]
(https://en.wikipedia.org/wiki/Green%27s_theorem#Proof_for_rectifiable_Jordan_curves).
-/

namespace MetaMathlibExt

open Set Filter MeasureTheory
open scoped Topology

/-- The image of the critical set of a real-valued real function is null, even when the
function is differentiable only on an open set and the critical set need not be closed. -/
private theorem volume_image_critical_eq_zero {V : Set ℝ} (hV : IsOpen V) {g : ℝ → ℝ}
    (hg : DifferentiableOn ℝ g V) : volume (g '' {t ∈ V | deriv g t = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
  · intro t ht
    have hd := ((hg t ht.1).differentiableAt (hV.mem_nhds ht.1)).hasDerivAt
    rw [ht.2] at hd
    simpa only [ContinuousLinearMap.toSpanSingleton_zero] using
      hd.hasFDerivAt.hasFDerivWithinAt (s := {t ∈ V | deriv g t = 0})
  · intro t ht
    simp

/-- The part of a simple closed trace near any non-endpoint time comes from an arbitrarily
small open interval of times around that time. -/
private theorem exists_open_trace_subset {a b t : ℝ} {γ : ℝ → ℝ × ℝ} {T : Set ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (ht : t ∈ Ioo a b) (hT : IsOpen T) (htT : t ∈ T) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ γ t ∈ V ∧ V ∩ γ '' Icc a b ⊆ γ '' (Icc a b ∩ T) := by
  have hc : IsCompact (Icc a b \ T) := isCompact_Icc.diff hT
  have hclosed := (hc.image_of_continuousOn (hγcont.mono sdiff_subset)).isClosed
  have hnot : γ t ∉ γ '' (Icc a b \ T) := by
    rintro ⟨u, hu, hEq⟩
    have ht' : t ∈ Ico a b := ⟨ht.1.le, ht.2⟩
    rcases lt_or_eq_of_le hu.1.2 with hub | rfl
    · exact hu.2 (hγinj ⟨hu.1.1, hub⟩ ht' hEq ▸ htT)
    · have hEq' : γ a = γ t := hγclosed.trans hEq
      have hat := hγinj ⟨le_rfl, ht.1.trans ht.2⟩ ht' hEq'
      exact ht.1.ne' hat.symm
  refine ⟨_, hclosed.isOpen_compl, hnot, ?_⟩
  rintro p ⟨hp, t', ht', rfl⟩
  exact ⟨t', ⟨ht', by
    by_contra h
    exact hp ⟨t', ⟨ht', h⟩, rfl⟩⟩, rfl⟩

/-- A regular fiber that misses the exceptional times is compact and discrete, hence finite. -/
private theorem finite_regular_fiber {a b z : ℝ} {g : ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hgc : ContinuousOn g (Icc a b)) (hg : ContDiffOn ℝ 1 g V)
    (hreg : ∀ t ∈ Icc a b, g t = z → t ∈ V ∧ deriv g t ≠ 0) :
    ({t ∈ Icc a b | g t = z} : Set ℝ).Finite := by
  let K : Set ℝ := {t ∈ Icc a b | g t = z}
  have hclosed : IsClosed K := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hc : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed fun _ ht => ht.1
  have hd : ContinuousOn (deriv g) V := hg.continuousOn_deriv_of_isOpen hV le_rfl
  have hisol : ∀ t ∈ K, ∀ᶠ v in 𝓝 t, v ∈ K → v = t := by
    intro t ht
    obtain ⟨htV, hne⟩ := hreg t ht.1 ht.2
    have hc' := (hd t htV).continuousAt (hV.mem_nhds htV)
    have hv : ∀ᶠ v in 𝓝 t, v ∈ V := hV.mem_nhds htV
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hev : ∀ᶠ v in 𝓝 t, v ∈ V ∩ {v | deriv g v < 0} :=
        hv.and (hc'.eventually_lt continuousAt_const hneg)
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
      have hsub' : Metric.ball t ε ⊆ V := hsub.trans inter_subset_left
      have hmono := strictAntiOn_of_deriv_neg (convex_ball t ε)
        (hg.continuousOn.mono hsub') (fun x hx => (hsub (interior_subset hx)).2)
      filter_upwards [Metric.ball_mem_nhds t hε] with v hv' hvK
      exact hmono.injOn hv' (Metric.mem_ball_self hε) (hvK.2.trans ht.2.symm)
    · have hev : ∀ᶠ v in 𝓝 t, v ∈ V ∩ {v | 0 < deriv g v} :=
        hv.and (continuousAt_const.eventually_lt hc' hpos)
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
      have hsub' : Metric.ball t ε ⊆ V := hsub.trans inter_subset_left
      have hmono := strictMonoOn_of_deriv_pos (convex_ball t ε)
        (hg.continuousOn.mono hsub') (fun x hx => (hsub (interior_subset hx)).2)
      filter_upwards [Metric.ball_mem_nhds t hε] with v hv' hvK
      exact hmono.injOn hv' (Metric.mem_ball_self hε) (hvK.2.trans ht.2.symm)
  refine hc.finite (isDiscrete_iff_discreteTopology.mpr
    (discreteTopology_iff_isOpen_singleton.mpr fun t => isOpen_iff_mem_nhds.mpr ?_))
  intro v hv
  rw [mem_singleton_iff.mp hv]
  exact (mem_nhds_subtype K t _).mpr ⟨_, hisol t t.property,
    fun x hx => mem_singleton_iff.mpr (Subtype.ext (hx x.property))⟩

/-- A regular point with nonvertical tangent has a neighborhood in which the frontier is
exactly a single graph. The derivative is the ratio of the two tangent coordinates. -/
private theorem exists_frontier_graph {a b t : ℝ} {γ : ℝ → ℝ × ℝ} {D : Set (ℝ × ℝ)}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (htcd : ContDiffAt ℝ 1 γ t) (h₁ : (deriv γ t).1 ≠ 0) :
    ∃ (r δ : ℝ) (f : ℝ → ℝ), 0 < r ∧ 0 < δ ∧
      let I := Metric.ball (γ t).1 r
      let J := Metric.ball (γ t).2 δ
      ContinuousOn f I ∧ MapsTo f I J ∧ f (γ t).1 = (γ t).2 ∧
        HasDerivAt f ((deriv γ t).2 * (deriv γ t).1⁻¹) (γ t).1 ∧
        ∀ x ∈ I, ∀ y ∈ J, (x, y) ∈ frontier D ↔ y = f x := by
  let g : ℝ → ℝ := fun u => (γ u).1
  let k : ℝ → ℝ := fun u => (γ u).2
  have hγd := (htcd.differentiableAt one_ne_zero).hasDerivAt
  have hgd : HasDerivAt g (deriv γ t).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hγd
  have hkd : HasDerivAt k (deriv γ t).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hγd
  have hs := htcd.fst.hasStrictDerivAt hgd one_ne_zero
  have H := hs.hasStrictFDerivAt_equiv h₁
  let e := H.toOpenPartialHomeomorph g
  have hte : t ∈ e.source := H.mem_toOpenPartialHomeomorph_source
  have hgte : g t ∈ e.target := H.image_mem_toOpenPartialHomeomorph_target
  have hinv : e.symm (g t) = t := e.left_inv hte
  obtain ⟨V, hVo, hγtV, hV⟩ :=
    exists_open_trace_subset hγcont hγclosed hγinj ht e.open_source hte
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hγtV)
  let f : ℝ → ℝ := k ∘ e.symm
  have hfval : f (g t) = k t := congrArg k hinv
  have hfd : HasDerivAt f ((deriv γ t).2 * (deriv γ t).1⁻¹) (g t) := by
    have he' : HasDerivAt e.symm ((deriv γ t).1⁻¹) (g t) := (hs.to_localInverse h₁).hasDerivAt
    have hkd' : HasDerivAt k (deriv γ t).2 (e.symm (g t)) := by simpa only [hinv] using hkd
    exact hkd'.comp (g t) he'
  have hci : ContinuousAt e.symm (g t) := e.continuousAt_symm hgte
  have hN : ∀ᶠ x in 𝓝 (g t), x ∈ e.target ∧ e.symm x ∈ Ioo a b ∧ f x ∈ Metric.ball (k t) δ := by
    have hNt : ∀ᶠ x in 𝓝 (g t), x ∈ e.target := e.open_target.mem_nhds hgte
    have hNab : ∀ᶠ x in 𝓝 (g t), e.symm x ∈ Ioo a b :=
      hci (by simpa only [hinv] using Ioo_mem_nhds ht.1 ht.2)
    have hNf : ∀ᶠ x in 𝓝 (g t), f x ∈ Metric.ball (k t) δ :=
      hfd.continuousAt (by rw [hfval]; exact Metric.ball_mem_nhds _ hδ)
    exact hNt.and (hNab.and hNf)
  obtain ⟨r₀, hr₀, hrN⟩ := Metric.mem_nhds_iff.mp hN
  let r := min r₀ δ
  have hr : 0 < r := lt_min hr₀ hδ
  have hsub₀ : Metric.ball (g t) r ⊆ Metric.ball (g t) r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hrect : Metric.ball (g t) r ×ˢ Metric.ball (k t) δ ⊆ V := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hδV
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨Metric.ball_subset_ball (min_le_right _ _) hx, hy⟩
  refine ⟨r, δ, f, hr, hδ, ?_, fun x hx => (hrN (hsub₀ hx)).2.2, hfval, hfd, ?_⟩
  · apply hγcont.snd.comp (e.symm.continuousOn.mono fun x hx => (hrN (hsub₀ hx)).1)
    exact fun x hx => Ioo_subset_Icc_self (hrN (hsub₀ hx)).2.1
  · intro x hx y hy
    change (x, y) ∈ frontier D ↔ y = k (e.symm x)
    rw [← hγtrace]
    constructor
    · intro hp
      obtain ⟨u, ⟨_, hue⟩, hup⟩ := hV ⟨hrect ⟨hx, hy⟩, hp⟩
      have hux : g u = x := congrArg Prod.fst hup
      have huy : k u = y := congrArg Prod.snd hup
      rw [← hux, show e.symm (g u) = u from e.left_inv hue, huy]
    · intro hp
      have hmem := hrN (hsub₀ hx)
      exact ⟨e.symm x, Ioo_subset_Icc_self hmem.2.1,
        Prod.ext (e.right_inv hmem.1) hp.symm⟩

/-- The open part of a rectangle above a continuous graph is preconnected. -/
private theorem isPreconnected_above_graph {I : Set ℝ} {f : ℝ → ℝ} {d : ℝ}
    (hI : IsPreconnected I) (hf : ContinuousOn f I) (hfd : ∀ x ∈ I, f x < d) :
    IsPreconnected {p : ℝ × ℝ | p.1 ∈ I ∧ f p.1 < p.2 ∧ p.2 < d} := by
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, f p.1 + p.2 * (d - f p.1))
  have hF : ContinuousOn F (I ×ˢ Ioo 0 1) := by
    have hf' : ContinuousOn (f ∘ Prod.fst) (I ×ˢ (Ioo 0 1 : Set ℝ)) :=
      hf.comp continuous_fst.continuousOn fun _ hp => hp.1
    exact continuous_fst.continuousOn.prodMk
      (hf'.add (continuous_snd.continuousOn.mul (continuousOn_const.sub hf')))
  convert (hI.prod isPreconnected_Ioo).image F hF using 1
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · rintro ⟨hx, hxy, hyd⟩
    refine ⟨(x, (y - f x) / (d - f x)), ⟨hx, ?_, ?_⟩, Prod.ext rfl ?_⟩
    · exact div_pos (sub_pos.mpr hxy) (sub_pos.mpr (hfd x hx))
    · rw [div_lt_one (sub_pos.mpr (hfd x hx))]
      linarith
    · change f x + (y - f x) / (d - f x) * (d - f x) = y
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (hfd x hx).ne')]
      ring
  · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, heq⟩
    rw [← heq]
    refine ⟨hx, ?_, ?_⟩
    · change f x < f x + s * (d - f x)
      linarith [mul_pos hs.1 (sub_pos.mpr (hfd x hx))]
    · change f x + s * (d - f x) < d
      linarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr (hfd x hx))]

/-- The open part of a rectangle below a continuous graph is preconnected. -/
private theorem isPreconnected_below_graph {I : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hI : IsPreconnected I) (hf : ContinuousOn f I) (hcf : ∀ x ∈ I, c < f x) :
    IsPreconnected {p : ℝ × ℝ | p.1 ∈ I ∧ c < p.2 ∧ p.2 < f p.1} := by
  have h := isPreconnected_above_graph (f := fun x => -f x) (d := -c) hI hf.neg
    (fun x hx => neg_lt_neg (hcf x hx))
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, -p.2)
  have hF : Continuous F := continuous_fst.prodMk continuous_snd.neg
  convert h.image F hF.continuousOn using 1
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro hp
    exact ⟨(x, -y), ⟨hp.1, neg_lt_neg hp.2.2, neg_lt_neg hp.2.1⟩, Prod.ext rfl (neg_neg y)⟩
  · rintro ⟨⟨x, u⟩, ⟨hx, hu, huc⟩, heq⟩
    rw [← heq]
    change x ∈ I ∧ c < -u ∧ -u < f x
    exact ⟨hx, by linarith, by linarith⟩

/-- A preconnected set disjoint from the frontier is entirely inside or entirely outside. -/
private theorem subset_interior_or_exterior {D V : Set (ℝ × ℝ)}
    (hV : IsPreconnected V) (hdis : Disjoint V (frontier D)) :
    V ⊆ interior D ∨ V ⊆ interior Dᶜ := by
  apply hV.subset_or_subset isOpen_interior isOpen_interior
    (Set.disjoint_left.mpr fun p hp hq => (interior_subset hq : p ∉ D) (interior_subset hp))
  rw [← compl_frontier_eq_union_interior]
  exact fun _ hp hpf => disjoint_left.mp hdis hp hpf

/-- A function vanishing at zero with positive derivative there is positive just to the right. -/
private theorem eventually_pos_of_hasDerivAt_zero {u : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt u d 0) (hdpos : 0 < d) (hzero : u 0 = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < u ε := by
  have hs : Tendsto (slope u 0) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
    hd.tendsto_slope.mono_left (nhdsWithin_mono _ (fun _ h => mem_compl_singleton_iff.mpr h.ne'))
  filter_upwards [hs (Ioi_mem_nhds hdpos), self_mem_nhdsWithin] with ε hε hεpos
  have hsl : 0 < u ε / ε := by simpa [slope_def_field, hzero] using hε
  exact (div_pos_iff_of_pos_right hεpos).mp hsl

/-- The signed graph height of a left-normal displacement is positive for all sufficiently
small positive displacements. Multiplying by the horizontal velocity accounts for its sign. -/
private theorem eventually_left_normal_in_graph_side {x y vx vy : ℝ} {f : ℝ → ℝ}
    (hf : HasDerivAt f (vy * vx⁻¹) x) (hval : f x = y) (hvx : vx ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < vx * ((y + ε * vx) - f (x - ε * vy)) := by
  have hx : HasDerivAt (fun ε : ℝ => x - ε * vy) (-vy) 0 := by
    simpa only [one_mul, id_eq] using (((hasDerivAt_id (0 : ℝ)).mul_const vy).const_sub x)
  have hy : HasDerivAt (fun ε : ℝ => y + ε * vx) vx 0 := by
    simpa only [one_mul, id_eq] using (((hasDerivAt_id (0 : ℝ)).mul_const vx).const_add y)
  have hf₀ : HasDerivAt f (vy * vx⁻¹) (x - 0 * vy) := by simpa using hf
  have hd := (hy.sub (hf₀.comp 0 hx)).const_mul vx
  apply eventually_pos_of_hasDerivAt_zero hd
  · have hid : vx * (vx - vy * vx⁻¹ * -vy) = vx ^ 2 + vy ^ 2 := by
      field_simp
      ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hvx) (sq_nonneg _)
  · simp [hval]

/-- In a nonvertical chart, each strict side lies in the interior or exterior. The side
selected by the horizontal velocity is necessarily interior; no assumption is made about
whether the graph itself belongs to `D`. -/
private theorem frontier_graph_side_status {D : Set (ℝ × ℝ)} {x₀ y₀ vx vy r δ : ℝ}
    {f : ℝ → ℝ} (hr : 0 < r) (hδ : 0 < δ) (hvx : vx ≠ 0)
    (hf : ContinuousOn f (Metric.ball x₀ r))
    (hfrange : MapsTo f (Metric.ball x₀ r) (Metric.ball y₀ δ))
    (hf₀ : f x₀ = y₀) (hfd : HasDerivAt f (vy * vx⁻¹) x₀)
    (hgraph : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball y₀ δ,
      (x, y) ∈ frontier D ↔ y = f x)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η → (x₀ - ε * vy, y₀ + ε * vx) ∈ D) :
    let A := {p : ℝ × ℝ | p.1 ∈ Metric.ball x₀ r ∧ f p.1 < p.2 ∧ p.2 < y₀ + δ}
    let B := {p : ℝ × ℝ | p.1 ∈ Metric.ball x₀ r ∧ y₀ - δ < p.2 ∧ p.2 < f p.1}
    (A ⊆ interior D ∨ A ⊆ interior Dᶜ) ∧ (B ⊆ interior D ∨ B ⊆ interior Dᶜ) ∧
      (0 < vx → A ⊆ interior D) ∧ (vx < 0 → B ⊆ interior D) := by
  intro A B
  have hi : IsPreconnected (Metric.ball x₀ r) := (convex_ball x₀ r).isPreconnected
  have hAf : ∀ x ∈ Metric.ball x₀ r, f x < y₀ + δ := by
    intro x hx
    have hh := hfrange hx
    rw [Real.ball_eq_Ioo] at hh
    exact hh.2
  have hBf : ∀ x ∈ Metric.ball x₀ r, y₀ - δ < f x := by
    intro x hx
    have hh := hfrange hx
    rw [Real.ball_eq_Ioo] at hh
    exact hh.1
  have hA : A ⊆ interior D ∨ A ⊆ interior Dᶜ := by
    apply subset_interior_or_exterior (isPreconnected_above_graph hi hf hAf)
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hxy, hyd⟩ hF
    have hym : y ∈ Metric.ball y₀ δ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨(hBf x hx).trans hxy, hyd⟩
    exact hxy.ne' ((hgraph x hx y hym).mp hF)
  have hB : B ⊆ interior D ∨ B ⊆ interior Dᶜ := by
    apply subset_interior_or_exterior (isPreconnected_below_graph hi hf hBf)
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hcy, hyx⟩ hF
    have hym : y ∈ Metric.ball y₀ δ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨hcy, hyx.trans (hAf x hx)⟩
    exact hyx.ne ((hgraph x hx y hym).mp hF)
  obtain ⟨η, hη, hleft⟩ := hleft
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < η :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hη)
  have hx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x₀ - ε * vy ∈ Metric.ball x₀ r := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : Continuous (fun ε : ℝ => x₀ - ε * vy) := continuous_const.sub
      (continuous_id.mul continuous_const)
    exact hc.continuousAt (by simpa using Metric.ball_mem_nhds x₀ hr)
  have hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), y₀ + ε * vx ∈ Metric.ball y₀ δ := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : Continuous (fun ε : ℝ => y₀ + ε * vx) := continuous_const.add
      (continuous_id.mul continuous_const)
    exact hc.continuousAt (by simpa using Metric.ball_mem_nhds y₀ hδ)
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < η ∧
      x₀ - ε * vy ∈ Metric.ball x₀ r ∧ y₀ + ε * vx ∈ Metric.ball y₀ δ ∧
        0 < vx * ((y₀ + ε * vx) - f (x₀ - ε * vy)) :=
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε from self_mem_nhdsWithin).and
      (hsmall.and (hx.and (hy.and (eventually_left_normal_in_graph_side hfd hf₀ hvx))))
  obtain ⟨ε, hε₀, hεη, hεx, hεy, hεsign⟩ := hε.exists
  have hmem := hleft ε hε₀ hεη
  rw [Real.ball_eq_Ioo] at hεy
  refine ⟨hA, hB, ?_, ?_⟩
  · intro hv
    refine hA.resolve_right fun he => ?_
    have hp : (x₀ - ε * vy, y₀ + ε * vx) ∈ A :=
      ⟨hεx, sub_pos.mp ((mul_pos_iff_of_pos_left hv).mp hεsign), hεy.2⟩
    exact (interior_subset (he hp) : (x₀ - ε * vy, y₀ + ε * vx) ∉ D) hmem
  · intro hv
    refine hB.resolve_right fun he => ?_
    have hp : (x₀ - ε * vy, y₀ + ε * vx) ∈ B :=
      ⟨hεx, hεy.1, sub_neg.mp (neg_of_mul_pos_right hεsign hv.le)⟩
    exact (interior_subset (he hp) : (x₀ - ε * vy, y₀ + ε * vx) ∉ D) hmem

/-- A finite sum of steps is locally constant away from its breakpoints. -/
private theorem eventually_eq_jump_sum {S : Finset ℝ} {x : ℝ} (hx : x ∉ S) (J : ℝ → ℝ) :
    (fun y => ∑ c ∈ S, if c ≤ y then J c else 0) =ᶠ[𝓝 x]
      fun _ => ∑ c ∈ S, if c ≤ x then J c else 0 := by
  have h : ∀ c ∈ S, ∀ᶠ y in 𝓝 x, (if c ≤ y then J c else 0) =
      (if c ≤ x then J c else 0) := by
    intro c hc
    have hne : c ≠ x := fun he => hx (he ▸ hc)
    rcases lt_or_gt_of_ne hne with hcx | hxc
    · have hh : ∀ᶠ y in 𝓝 x, c < y := Ioi_mem_nhds hcx
      filter_upwards [hh] with y hy using by simp [hcx.le, hy.le]
    · have hh : ∀ᶠ y in 𝓝 x, y < c := Iio_mem_nhds hxc
      filter_upwards [hh] with y hy using by simp [hxc.not_ge, hy.not_ge]
  filter_upwards [eventually_all_finset S |>.mpr h] with y hy using Finset.sum_congr rfl hy

/-- Integrate a derivative off finitely many crossings by subtracting the jumps. Values of
`u` at the crossing points are immaterial. -/
private theorem integral_add_jumps {a b : ℝ} {u v L R : ℝ → ℝ} (hab : a ≤ b) (S : Finset ℝ)
    (hS : (↑S : Set ℝ) ⊆ Ioo a b)
    (hc : ContinuousOn u (Icc a b \ ↑S))
    (hd : ∀ x ∈ Ioo a b \ ↑S, HasDerivAt u (v x) x) (hi : IntervalIntegrable v volume a b)
    (hL : ∀ c ∈ S, Tendsto u (𝓝[<] c) (𝓝 (L c)))
    (hR : ∀ c ∈ S, Tendsto u (𝓝[>] c) (𝓝 (R c))) :
    (∫ x in a..b, v x) + ∑ c ∈ S, (R c - L c) = u b - u a := by
  classical
  let jump : ℝ → ℝ := fun c => R c - L c
  let H : ℝ → ℝ := fun x => ∑ c ∈ S, if c ≤ x then jump c else 0
  let F : ℝ → ℝ := fun x => (if x ∈ S then R x else u x) - H x
  have hFoff (x : ℝ) (hx : x ∉ S) : F =ᶠ[𝓝 x] fun y => u y - H x := by
    have hn : ∀ᶠ y in 𝓝 x, y ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [hn, eventually_eq_jump_sum hx jump] with y hy hH
    simp only [F, ite_eq_right hy, H, hH]
  have hcont : ContinuousOn F (Icc a b) := by
    intro x hx
    by_cases hm : x ∈ S
    · let K : ℝ → ℝ := fun y => ∑ c ∈ S.erase x, if c ≤ y then jump c else 0
      have hK : K =ᶠ[𝓝 x] fun _ => K x := eventually_eq_jump_sum (S.notMem_erase x) jump
      have hH (y : ℝ) : H y = K y + (if x ≤ y then jump x else 0) :=
        (Finset.sum_erase_add _ _ hm).symm
      have hne : ∀ᶠ y in 𝓝 x, y ∉ S.erase x :=
        (S.erase x).finite_toSet.isClosed.isOpen_compl.mem_nhds (S.notMem_erase x)
      have hval : F x = L x - K x := by
        simp only [F, ite_eq_left hm, hH, ite_eq_left (le_refl x), jump]
        ring
      apply ContinuousAt.continuousWithinAt
      rw [continuousAt_iff_continuous_left'_right']
      constructor
      · change Tendsto F (𝓝[<] x) (𝓝 (F x))
        rw [hval]
        apply ((hL x hm).sub_const (K x)).congr'
        filter_upwards [hK.filter_mono nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_eventually_nhds hne,
          (show ∀ᶠ y in 𝓝[<] x, y < x from self_mem_nhdsWithin)] with y hy hyne hyx
        have hys : y ∉ S := fun hy' => hyne (Finset.mem_erase.mpr ⟨hyx.ne, hy'⟩)
        simp only [F, ite_eq_right hys, hH, hy, ite_eq_right hyx.not_ge, add_zero]
      · change Tendsto F (𝓝[>] x) (𝓝 (F x))
        have hfx : F x = R x - (K x + jump x) := by simp [F, hm, hH]
        rw [hfx]
        apply ((hR x hm).sub_const (K x + jump x)).congr'
        filter_upwards [hK.filter_mono nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_eventually_nhds hne,
          (show ∀ᶠ y in 𝓝[>] x, x < y from self_mem_nhdsWithin)] with y hy hyne hyx
        have hys : y ∉ S := fun hy' => hyne (Finset.mem_erase.mpr ⟨hyx.ne', hy'⟩)
        simp only [F, ite_eq_right hys, hH, hy, ite_eq_left hyx.le]
    · have hn : ∀ᶠ y in 𝓝 x, y ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hm
      have hnh : Icc a b \ (↑S : Set ℝ) ∈ 𝓝[Icc a b] x :=
        inter_mem self_mem_nhdsWithin (eventually_nhdsWithin_of_eventually_nhds hn)
      have cu : ContinuousWithinAt (fun y => u y - H x) (Icc a b) x :=
        ((hc x ⟨hx, hm⟩).mono_of_mem_nhdsWithin hnh).sub continuousWithinAt_const
      exact cu.congr_of_eventuallyEq ((hFoff x hm).filter_mono nhdsWithin_le_nhds)
        (hFoff x hm).self_of_nhds
  have hderiv : ∀ x ∈ Ioo a b \ (↑S : Set ℝ), HasDerivAt F (v x) x := by
    intro x hx
    exact ((hd x hx).sub_const (H x)).congr_of_eventuallyEq (hFoff x hx.2)
  have ha : a ∉ S := fun h => (hS h).1.false
  have hb : b ∉ S := fun h => (hS h).2.false
  have hHa : H a = 0 := by
    apply Finset.sum_eq_zero
    intro c hc'
    rw [ite_eq_right (hS hc').1.not_ge]
  have hHb : H b = ∑ c ∈ S, jump c := by
    exact Finset.sum_congr rfl fun c hc' => ite_eq_left (hS hc').2.le
  rw [integral_eq_of_hasDerivAt_off_countable_of_le F v hab S.finite_toSet.countable
    hcont hderiv hi]
  simp only [F, ite_eq_right ha, ite_eq_right hb, hHa, hHb, sub_zero, jump]
  ring

/-- The noncritical part of a locally C¹ real map has a countable Borel partition into
injective sets. -/
private theorem exists_injective_partition {V : Set ℝ} {g : ℝ → ℝ}
    (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V) :
    ∃ A : ℕ → Set ℝ,
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, InjOn g (A n)) ∧
        Pairwise (fun i j => Disjoint (A i) (A j)) ∧
        (⋃ n, A n) = {x ∈ V | deriv g x ≠ 0} := by
  classical
  let W : Set ℝ := {x ∈ V | deriv g x ≠ 0}
  by_cases hW : W.Nonempty
  · have : Nonempty W := hW.to_subtype
    have hd : ContinuousOn (deriv g) V := hg.continuousOn_deriv_of_isOpen hV le_rfl
    have hr (x : W) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (x : ℝ) ε ⊆ W ∧
        InjOn g (Metric.ball (x : ℝ) ε) := by
      have hxV : (x : ℝ) ∈ V := x.property.1
      have hxne : deriv g (x : ℝ) ≠ 0 := x.property.2
      have hc := (hd x hxV).continuousAt (hV.mem_nhds hxV)
      have hn : ∀ᶠ y in 𝓝 (x : ℝ), y ∈ V := hV.mem_nhds hxV
      rcases lt_or_gt_of_ne hxne with hneg | hpos
      · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
          (hn.and (hc.eventually_lt continuousAt_const hneg))
        refine ⟨ε, hε, fun y hy => ⟨(hball hy).1, (hball hy).2.ne⟩, ?_⟩
        exact (strictAntiOn_of_deriv_neg (convex_ball _ _)
          (hg.continuousOn.mono fun _ hy => (hball hy).1)
          (fun y hy => (hball (interior_subset hy)).2)).injOn
      · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
          (hn.and (continuousAt_const.eventually_lt hc hpos))
        refine ⟨ε, hε, fun y hy => ⟨(hball hy).1, (hball hy).2.ne'⟩, ?_⟩
        exact (strictMonoOn_of_deriv_pos (convex_ball _ _)
          (hg.continuousOn.mono fun _ hy => (hball hy).1)
          (fun y hy => (hball (interior_subset hy)).2)).injOn
    choose ε hε hsub hinj using hr
    let B (x : W) := Metric.ball (x : ℝ) (ε x)
    have hcover : W ⊆ ⋃ x : W, B x := fun x hx =>
      mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hε ⟨x, hx⟩))
    obtain ⟨c, hc⟩ := (HereditarilyLindelofSpace.isLindelof W).indexed_countable_subcover B
      (fun _ => Metric.isOpen_ball) hcover
    let C : ℕ → Set ℝ := B ∘ c
    refine ⟨disjointed C, MeasurableSet.disjointed (fun _ => Metric.isOpen_ball.measurableSet),
      fun n => (hinj (c n)).mono (disjointed_subset _ _), disjoint_disjointed _, ?_⟩
    rw [iUnion_disjointed]
    exact (iUnion_subset fun n => hsub (c n)).antisymm hc
  · refine ⟨fun _ => ∅, by simp, by simp, fun _ _ _ => by simp, ?_⟩
    change (⋃ _ : ℕ, (∅ : Set ℝ)) = W
    rw [iUnion_empty, not_nonempty_iff_eq_empty.mp hW]

/-- One-dimensional coarea over the noncritical set, with multiplicity retained. This is a
countable sum of the injective change-of-variable formula, not an assumption that the whole
path can be written as finitely many monotone graphs. -/
private theorem integral_abs_deriv_eq_integral_fiber_sum {V : Set ℝ} {g w : ℝ → ℝ}
    (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V)
    (hi : IntegrableOn (fun t => |deriv g t| • w t) {t ∈ V | deriv g t ≠ 0}) :
    (∫ t in {t ∈ V | deriv g t ≠ 0}, |deriv g t| • w t) =
      ∫ z, ∑' t : {t : ℝ // (t ∈ V ∧ deriv g t ≠ 0) ∧ g t = z}, w (t : ℝ) := by
  classical
  let W : Set ℝ := {t ∈ V | deriv g t ≠ 0}
  obtain ⟨A, hA, hAinj, hAdis, hAu⟩ := exists_injective_partition hV hg
  change (⋃ n, A n) = W at hAu
  change IntegrableOn (fun t => |deriv g t| • w t) W at hi
  change (∫ t in W, |deriv g t| • w t) = _
  have hsub (n : ℕ) : A n ⊆ W := fun t ht => hAu ▸ mem_iUnion_of_mem n ht
  have hd (n : ℕ) : ∀ t ∈ A n, HasDerivWithinAt g (deriv g t) (A n) t := by
    intro t ht
    have htV := (hsub n ht).1
    exact ((hg.differentiableOn one_ne_zero t htV).differentiableAt
      (hV.mem_nhds htV)).hasDerivAt.hasDerivWithinAt
  let G (n : ℕ) (z : ℝ) : ℝ := w (Function.invFunOn g (A n) z)
  let F (n : ℕ) : ℝ → ℝ := (g '' A n).indicator (G n)
  have hmeas (n : ℕ) : MeasurableSet (g '' A n) := (hA n).image_of_continuousOn_injOn
    (hg.continuousOn.mono fun _ ht => (hsub n ht).1) (hAinj n)
  have hcomp (n : ℕ) (t : ℝ) (ht : t ∈ A n) : G n (g t) = w t :=
    congrArg w (hAinj n |>.leftInvOn_invFunOn ht)
  have hfi (n : ℕ) : Integrable (F n) volume := by
    apply (integrable_indicator_iff (hmeas n)).mpr
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul (hA n) (hd n) (hAinj n) _).mpr
    apply (hi.mono_set (hsub n)).congr_fun _ (hA n)
    intro t ht
    exact congrArg (fun x => |deriv g t| • x) (hcomp n t ht).symm
  have hterm (n : ℕ) : (∫ z, F n z) = ∫ t in A n, |deriv g t| • w t := by
    rw [integral_indicator (hmeas n), integral_image_eq_integral_abs_deriv_smul
      (hA n) (hd n) (hAinj n)]
    exact setIntegral_congr_fun (hA n) fun t ht =>
      congrArg (fun x => |deriv g t| • x) (hcomp n t ht)
  have hnorm (n : ℕ) : (∫ z, ‖F n z‖) = ∫ t in A n, ‖|deriv g t| • w t‖ := by
    have hEq (z : ℝ) : ‖F n z‖ = (g '' A n).indicator (fun y => ‖G n y‖) z := by
      by_cases h : z ∈ g '' A n <;> simp [F, h]
    simp_rw [hEq, integral_indicator (hmeas n)]
    rw [integral_image_eq_integral_abs_deriv_smul (hA n) (hd n) (hAinj n)]
    apply setIntegral_congr_fun (hA n)
    intro t ht
    simp only [hcomp n t ht, Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_abs]
  have hsum : Summable fun n => ∫ z, ‖F n z‖ := by
    simp_rw [hnorm]
    exact (hasSum_integral_iUnion hA hAdis (hAu.symm ▸ hi.norm)).summable
  have hfiber (z : ℝ) : (∑' n, F n z) =
      ∑' t : {t : ℝ // t ∈ W ∧ g t = z}, w (t : ℝ) := by
    let B : Set ℕ := {n | z ∈ g '' A n}
    let φ (n : B) : {t : ℝ // t ∈ W ∧ g t = z} :=
      ⟨Function.invFunOn g (A n) z, hsub n (Function.invFunOn_mem n.property),
        (Function.invFunOn_pos n.property).2⟩
    have hφ : Function.Bijective φ := by
      constructor
      · intro n m hnm
        apply Subtype.ext
        by_contra hne
        have h₁ : (φ n : ℝ) ∈ A n := Function.invFunOn_mem n.property
        have h₂ : (φ n : ℝ) ∈ A m := hnm ▸ Function.invFunOn_mem m.property
        exact Set.disjoint_left.mp (hAdis hne) h₁ h₂
      · intro t
        have htA : (t : ℝ) ∈ ⋃ n, A n := by
          rw [hAu]
          exact t.property.1
        obtain ⟨n, hn⟩ := mem_iUnion.mp htA
        have hz : z ∈ g '' A n := ⟨t, hn, t.property.2⟩
        refine ⟨⟨n, hz⟩, Subtype.ext ?_⟩
        change Function.invFunOn g (A n) z = (t : ℝ)
        calc
          _ = Function.invFunOn g (A n) (g t) :=
            congrArg (Function.invFunOn g (A n)) t.property.2.symm
          _ = _ := (hAinj n).leftInvOn_invFunOn hn
    let e := Equiv.ofBijective φ hφ
    calc
      (∑' n, F n z) = ∑' n : B, G n z := by
        rw [tsum_subtype B (fun n => G n z)]
        apply tsum_congr
        intro n
        by_cases hn : z ∈ g '' A n
        · have hb : n ∈ B := hn
          simp only [F, indicator_of_mem hn, indicator_of_mem hb]
        · have hb : n ∉ B := hn
          simp only [F, indicator_of_notMem hn, indicator_of_notMem hb]
      _ = ∑' t : {t : ℝ // t ∈ W ∧ g t = z}, w (t : ℝ) :=
        e.tsum_eq fun t => w (t : ℝ)
  rw [← hAu, integral_iUnion hA hAdis (hAu.symm ▸ hi), ← funext hterm,
    integral_tsum_of_summable_integral_norm hfi hsum]
  exact integral_congr_ae (Eventually.of_forall hfiber)

/-- Each time off the finite subdivision set lies between consecutive subdivision points. -/
private theorem exists_consecutive_bounds {a b t : ℝ} {S : Finset ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (ht : t ∈ Ioo a b) :
    ∃ u ∈ S, ∃ v ∈ S, t ∈ Ioo u v ∧ Ioo u v ∩ (↑S : Set ℝ) ⊆ {t} := by
  classical
  let Sl := S.filter (· < t)
  let Sr := S.filter (t < ·)
  have hl : Sl.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, ht.1⟩⟩
  have hr : Sr.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, ht.2⟩⟩
  let u := Sl.max' hl
  let v := Sr.min' hr
  have hul : u ∈ Sl := Sl.max'_mem hl
  have hvr : v ∈ Sr := Sr.min'_mem hr
  have hu := Finset.mem_filter.mp hul
  have hv := Finset.mem_filter.mp hvr
  refine ⟨u, hu.1, v, hv.1, ⟨hu.2, hv.2⟩, ?_⟩
  intro x hx
  rcases lt_trichotomy x t with hlt | heq | hgt
  · exact (hx.1.1.not_ge (Sl.le_max' x (Finset.mem_filter.mpr ⟨hx.2, hlt⟩))).elim
  · exact heq
  · exact (hx.1.2.not_ge (Sr.min'_le x (Finset.mem_filter.mpr ⟨hx.2, hgt⟩))).elim

/-- A continuous weight times the derivative of a piecewise C¹ real function is integrable
on the full closed parameter interval, also when using the absolute derivative. -/
private theorem integrableOn_mul_deriv_of_piecewise {a b : ℝ} {S : Finset ℝ} {f g : ℝ → ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hS : (↑S : Set ℝ) ⊆ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ∀ u v, u ∈ S → v ∈ S → u < v → Ioo u v ∩ (↑S : Set ℝ) = ∅ →
      ContDiffOn ℝ 1 g (Icc u v)) :
    IntegrableOn (fun t => f t * deriv g t) (Icc a b) := by
  classical
  let P : Set (ℝ × ℝ) := {q | q.1 ∈ S ∧ q.2 ∈ S ∧ q.1 < q.2 ∧
    Ioo q.1 q.2 ∩ (↑S : Set ℝ) = ∅}
  have hP : P.Finite := (S.finite_toSet.prod S.finite_toSet).subset fun _ hx => ⟨hx.1, hx.2.1⟩
  have hc : Ioo a b \ ↑S ⊆ ⋃ q ∈ P, Ioo q.1 q.2 := by
    intro t ht
    obtain ⟨u, hu, v, hv, htuv, hs⟩ := exists_consecutive_bounds ha hb ht.1
    have hgap : Ioo u v ∩ (↑S : Set ℝ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have : x = t := hs hx
      exact ht.2 (this ▸ hx.2)
    exact mem_iUnion₂.mpr ⟨(u, v), ⟨hu, hv, htuv.1.trans htuv.2, hgap⟩, htuv⟩
  have hi : IntegrableOn (fun t => f t * deriv g t) (⋃ q ∈ P, Ioo q.1 q.2) := by
    apply (integrableOn_finite_biUnion hP).mpr
    intro q hq
    have hqq : q.1 < q.2 := hq.2.2.1
    have hsub : Icc q.1 q.2 ⊆ Icc a b :=
      Icc_subset_Icc (hS hq.1).1 (hS hq.2.1).2
    have hcd := hg q.1 q.2 hq.1 hq.2.1 hqq hq.2.2.2
    have hci : ContinuousOn (fun t => f t * derivWithin g (Icc q.1 q.2) t) (Icc q.1 q.2) :=
      (hf.mono hsub).mul (hcd.continuousOn_derivWithin (uniqueDiffOn_Icc hqq) le_rfl)
    have h := (hci.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioo_subset_Icc_self
    exact h.congr_fun (fun t ht => by
      change f t * derivWithin g (Icc q.1 q.2) t = f t * deriv g t
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]) measurableSet_Ioo
  have hset : (Icc a b : Set ℝ) =ᵐ[volume] (Ioo a b \ ↑S : Set ℝ) := by
    have hs : ∀ᵐ x : ℝ, x ∉ (↑S : Set ℝ) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using S.finite_toSet.measure_zero (volume : Measure ℝ)
    filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b), hs] with x hx hxs
    change x ∈ Icc a b ↔ x ∈ Ioo a b ∧ x ∉ S
    exact ⟨fun h => ⟨hx.mpr h, hxs⟩, fun h => hx.mp h.1⟩
  exact (hi.mono_set hc).congr_set_ae hset

/-- Almost every projection level avoids both the finite exceptional set and critical values. -/
private theorem ae_forall_mem_regular_fiber {a b : ℝ} {S : Finset ℝ} {g : ℝ → ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hg : ContDiffOn ℝ 1 g (Ioo a b \ ↑S)) :
    ∀ᵐ z : ℝ, ∀ t ∈ Icc a b, g t = z → t ∈ Ioo a b \ (↑S : Set ℝ) ∧ deriv g t ≠ 0 := by
  let V := Ioo a b \ (↑S : Set ℝ)
  have hV : IsOpen V := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  let C := g '' {t ∈ V | deriv g t = 0}
  let E := g '' (↑S : Set ℝ)
  have hC : (volume : Measure ℝ) C = 0 :=
    volume_image_critical_eq_zero hV (hg.differentiableOn one_ne_zero)
  have hE : (volume : Measure ℝ) E = 0 := (S.finite_toSet.image g).measure_zero volume
  have hnull : ∀ᵐ z : ℝ, z ∉ C ∪ E := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using measure_union_null hC hE
  filter_upwards [hnull] with z hz t ht htz
  have hts : t ∉ S := fun h => hz (Or.inr ⟨t, h, htz⟩)
  have htV : t ∈ V := ⟨⟨lt_of_le_of_ne ht.1 (fun e => hts (e ▸ ha)),
    lt_of_le_of_ne ht.2 (fun e => hts (e.symm ▸ hb))⟩, hts⟩
  exact ⟨htV, fun hn => hz (Or.inl ⟨t, ⟨htV, hn⟩, htz⟩)⟩

/-- Whether a graph point borders the open exterior is determined by the two strict sides
in its rectangle. This does not make any assertion about membership of the graph in `D`. -/
private theorem graph_exterior_closure_iff {D : Set (ℝ × ℝ)} {I : Set ℝ} {c d : ℝ}
    {f : ℝ → ℝ} (hI : IsOpen I) (hf : MapsTo f I (Ioo c d))
    (hgraph : ∀ x ∈ I, ∀ y ∈ Ioo c d, (x, y) ∈ frontier D ↔ y = f x)
    (hA : {p : ℝ × ℝ | p.1 ∈ I ∧ f p.1 < p.2 ∧ p.2 < d} ⊆ interior D ∨
      {p : ℝ × ℝ | p.1 ∈ I ∧ f p.1 < p.2 ∧ p.2 < d} ⊆ interior Dᶜ)
    (hB : {p : ℝ × ℝ | p.1 ∈ I ∧ c < p.2 ∧ p.2 < f p.1} ⊆ interior D ∨
      {p : ℝ × ℝ | p.1 ∈ I ∧ c < p.2 ∧ p.2 < f p.1} ⊆ interior Dᶜ)
    {x : ℝ} (hx : x ∈ I) :
    (x, f x) ∈ closure (interior Dᶜ) ↔
      {p : ℝ × ℝ | p.1 ∈ I ∧ f p.1 < p.2 ∧ p.2 < d} ⊆ interior Dᶜ ∨
      {p : ℝ × ℝ | p.1 ∈ I ∧ c < p.2 ∧ p.2 < f p.1} ⊆ interior Dᶜ := by
  have hfx : f x ∈ Ioo c d := hf hx
  constructor
  · intro h
    rcases hA with hA | hA
    · rcases hB with hB | hB
      · exfalso
        obtain ⟨p, hp, hext⟩ := (mem_closure_iff.mp h) (I ×ˢ Ioo c d)
          (hI.prod isOpen_Ioo) ⟨hx, hfx⟩
        rcases lt_trichotomy p.2 (f p.1) with hlt | heq | hgt
        · exact (interior_subset hext : p ∉ D) (interior_subset (hB ⟨hp.1, hp.2.1, hlt⟩))
        · have hpt : (p.1, p.2) ∈ frontier D := (hgraph p.1 hp.1 p.2 hp.2).mpr heq
          exact disjoint_left.mp disjoint_interior_frontier hext ((frontier_compl D).symm ▸ hpt)
        · exact (interior_subset hext : p ∉ D) (interior_subset (hA ⟨hp.1, hgt, hp.2.2⟩))
      · exact Or.inr hB
    · exact Or.inl hA
  · intro h
    have hc : Continuous (fun y : ℝ => (x, y)) := continuous_const.prodMk continuous_id
    rcases h with h | h
    · have hN : ∀ᶠ y in 𝓝[>] (f x), (x, y) ∈ interior Dᶜ := by
        filter_upwards [Ioo_mem_nhdsGT hfx.2] with y hy
        exact h ⟨hx, hy.1, hy.2⟩
      exact mem_closure_of_tendsto (hc.continuousAt.mono_left nhdsWithin_le_nhds) hN
    · have hN : ∀ᶠ y in 𝓝[<] (f x), (x, y) ∈ interior Dᶜ := by
        filter_upwards [Ioo_mem_nhdsLT hfx.1] with y hy
        exact h ⟨hx, hy.1, hy.2⟩
      exact mem_closure_of_tendsto (hc.continuousAt.mono_left nhdsWithin_le_nhds) hN

/-- In a nonvertical chart the exterior flag is locally constant along the parameter. -/
private theorem eventually_exterior_flag_iff {a b t : ℝ} {D : Set (ℝ × ℝ)} {γ : ℝ → ℝ × ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (hcd : ContDiffAt ℝ 1 γ t) (hd : (deriv γ t).1 ≠ 0)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    ∀ᶠ s in 𝓝 t, γ s ∈ closure (interior Dᶜ) ↔ γ t ∈ closure (interior Dᶜ) := by
  obtain ⟨r, δ, f, hr, hδ, hf, hfr, hf₀, hfd, hgraph⟩ :=
    exists_frontier_graph hγcont hγclosed hγinj hγtrace ht hcd hd
  have hleft' : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ((γ t).1 - ε * (deriv γ t).2, (γ t).2 + ε * (deriv γ t).1) ∈ D := by
    obtain ⟨η, hη, hnormal⟩ := hleft
    refine ⟨η, hη, fun ε hε hlt => ?_⟩
    have hcoord : γ t + ε • (-(deriv γ t).2, (deriv γ t).1) =
        ((γ t).1 - ε * (deriv γ t).2, (γ t).2 + ε * (deriv γ t).1) := by
      apply Prod.ext <;> simp [sub_eq_add_neg]
    exact hcoord ▸ hnormal ε hε hlt
  obtain ⟨hA, hB, _, _⟩ := frontier_graph_side_status hr hδ hd hf hfr hf₀ hfd hgraph hleft'
  let I := Metric.ball (γ t).1 r
  let J := Metric.ball (γ t).2 δ
  have hJ : J = Ioo ((γ t).2 - δ) ((γ t).2 + δ) := Real.ball_eq_Ioo _ _
  have hstat {x : ℝ} (hx : x ∈ I) := graph_exterior_closure_iff (D := D) (f := f) (I := I)
    (c := (γ t).2 - δ) (d := (γ t).2 + δ) Metric.isOpen_ball
    (hJ ▸ hfr) (hJ ▸ hgraph) hA hB hx
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ I ×ˢ J := hcd.continuousAt.eventually_mem
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hδ⟩)
  have hab : ∀ᶠ s in 𝓝 t, s ∈ Icc a b := Icc_mem_nhds ht.1 ht.2
  filter_upwards [hn, hab] with s hs hsab
  have hfront : γ s ∈ frontier D := hγtrace ▸ mem_image_of_mem γ hsab
  have hval' : (γ s).2 = f (γ s).1 := (hgraph _ hs.1 _ hs.2).mp hfront
  have hsg : γ s = ((γ s).1, f (γ s).1) := Prod.ext rfl hval'
  have htg : γ t = ((γ t).1, f (γ t).1) := Prod.ext rfl hf₀.symm
  exact hsg ▸ htg ▸ (hstat hs.1).trans (hstat (Metric.mem_ball_self hr)).symm

private noncomputable def exteriorWeight (D : Set (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  open Classical in if p ∈ closure (interior Dᶜ) then 1 else 0

private noncomputable def crossingSign (d : ℝ) : ℝ :=
  if 0 < d then 1 else -1

/-- The jump of a vertical slice at a transverse time is the signed exterior flag times
its boundary value. The value of the slice at the crossing itself is not prescribed. -/
private theorem exists_vertical_slice_jump {a b t : ℝ} {D : Set (ℝ × ℝ)}
    {γ : ℝ → ℝ × ℝ} {P : ℝ × ℝ → ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (hcd : ContDiffAt ℝ 1 γ t) (hd : (deriv γ t).1 ≠ 0)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D)
    (hP : ContinuousAt P (γ t)) :
    let u := fun y => D.indicator P ((γ t).1, y)
    ∃ l r : ℝ, Tendsto u (𝓝[<] (γ t).2) (𝓝 l) ∧ Tendsto u (𝓝[>] (γ t).2) (𝓝 r) ∧
      r - l = crossingSign (deriv γ t).1 * exteriorWeight D (γ t) * P (γ t) := by
  classical
  obtain ⟨ρ, δ, f, hρ, hδ, hf, hfr, hf₀, hfd, hgraph⟩ :=
    exists_frontier_graph hγcont hγclosed hγinj hγtrace ht hcd hd
  let x := (γ t).1
  let y := (γ t).2
  let v := (deriv γ t).1
  let A := {p : ℝ × ℝ | p.1 ∈ Metric.ball x ρ ∧ f p.1 < p.2 ∧ p.2 < y + δ}
  let B := {p : ℝ × ℝ | p.1 ∈ Metric.ball x ρ ∧ y - δ < p.2 ∧ p.2 < f p.1}
  have hleft' : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      (x - ε * (deriv γ t).2, y + ε * v) ∈ D := by
    obtain ⟨η, hη, hnormal⟩ := hleft
    refine ⟨η, hη, fun ε hε hlt => ?_⟩
    have hcoord : γ t + ε • (-(deriv γ t).2, (deriv γ t).1) =
        (x - ε * (deriv γ t).2, y + ε * v) := by
      apply Prod.ext <;> simp [x, y, v, sub_eq_add_neg]
    exact hcoord ▸ hnormal ε hε hlt
  obtain ⟨hA, hB, hpos, hneg⟩ := frontier_graph_side_status hρ hδ hd hf hfr hf₀ hfd hgraph hleft'
  have hxc : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ
  have hflag : γ t ∈ closure (interior Dᶜ) ↔ A ⊆ interior Dᶜ ∨ B ⊆ interior Dᶜ := by
    have hJ := Real.ball_eq_Ioo y δ
    have heq : (x, f x) = γ t := Prod.ext rfl hf₀
    rw [← heq]
    exact graph_exterior_closure_iff (f := f) Metric.isOpen_ball
      (hJ ▸ hfr) (hJ ▸ hgraph) hA hB hxc
  have hAbove : ∀ᶠ z in 𝓝[>] y, (x,z) ∈ A := by
    have hlt : y < y + δ := lt_add_of_pos_right _ hδ
    filter_upwards [Ioo_mem_nhdsGT hlt] with z hz
    exact ⟨hxc, hf₀ ▸ hz.1, hz.2⟩
  have hBelow : ∀ᶠ z in 𝓝[<] y, (x,z) ∈ B := by
    have hlt : y - δ < y := sub_lt_self _ hδ
    filter_upwards [Ioo_mem_nhdsLT hlt] with z hz
    exact ⟨hxc, hz.1, hf₀ ▸ hz.2⟩
  have hdis {C : Set (ℝ × ℝ)} (hne : C.Nonempty) (h₁ : C ⊆ interior D)
      (h₂ : C ⊆ interior Dᶜ) : False := by
    obtain ⟨p, hp⟩ := hne
    exact (interior_subset (h₂ hp) : p ∉ D) (interior_subset (h₁ hp))
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := hAbove.exists
    exact ⟨_, hz⟩
  have hBne : B.Nonempty := by
    obtain ⟨z, hz⟩ := hBelow.exists
    exact ⟨_, hz⟩
  have hc : Continuous (fun z : ℝ => (x,z)) := continuous_const.prodMk continuous_id
  have hPc : ContinuousAt (fun z => P (x,z)) y :=
    (show ContinuousAt P (x, y) from hP).comp hc.continuousAt
  intro u
  have hLim (J : Set ℝ) (C : Set (ℝ × ℝ)) (hE : ∀ᶠ z in 𝓝[J] y, (x,z) ∈ C) :
      (C ⊆ interior D → Tendsto u (𝓝[J] y) (𝓝 (P (γ t)))) ∧
      (C ⊆ interior Dᶜ → Tendsto u (𝓝[J] y) (𝓝 0)) := by
    constructor
    · intro h
      apply (hPc.continuousWithinAt.tendsto).congr'
      filter_upwards [hE] with z hz
      exact (indicator_of_mem (interior_subset (h hz)) P).symm
    · intro h
      apply tendsto_const_nhds.congr'
      filter_upwards [hE] with z hz
      exact (indicator_of_notMem (interior_subset (h hz)) P).symm
  obtain ⟨hAin, hAout⟩ := hLim (Ioi y) A hAbove
  obtain ⟨hBin, hBout⟩ := hLim (Iio y) B hBelow
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · have hf' : γ t ∉ closure (interior Dᶜ) := by
      intro h
      rcases hflag.mp h with h | h
      · exact hdis hAne hA h
      · exact hdis hBne hB h
    exact ⟨_, _, hBin hB, hAin hA, by
      simp only [exteriorWeight, ite_eq_right hf', mul_zero, zero_mul, sub_self]⟩
  · have hf' := hflag.mpr (Or.inr hB)
    have hv : 0 < (deriv γ t).1 := (lt_or_gt_of_ne hd).resolve_left (fun h => hdis hBne (hneg h) hB)
    exact ⟨_, _, hBout hB, hAin hA, by
      simp only [exteriorWeight, ite_eq_left hf', crossingSign, ite_eq_left hv, mul_one, one_mul,
        sub_zero]⟩
  · have hf' := hflag.mpr (Or.inl hA)
    have hv : (deriv γ t).1 < 0 := (lt_or_gt_of_ne hd).resolve_right
      (fun h => hdis hAne (hpos h) hA)
    exact ⟨_, _, hBin hB, hAout hA, by
      simp only [exteriorWeight, ite_eq_left hf', crossingSign, ite_eq_right hv.not_gt, mul_one,
        neg_one_mul, zero_sub]⟩
  · exact ((lt_or_gt_of_ne hd).elim (fun h => hdis hBne (hneg h) hB)
      (fun h => hdis hAne (hpos h) hA)).elim

/-- A vertical line has derivative `(0,1)`. -/
private theorem hasDerivAt_vertical (x y : ℝ) :
    HasDerivAt (fun z : ℝ => (x, z)) (0, 1) y := by
  simpa only [id_eq] using HasDerivAt.prodMk (hasDerivAt_const y x) (hasDerivAt_id y)

private theorem deriv_fst_curve {γ : ℝ → ℝ × ℝ} {t : ℝ}
    (hd : DifferentiableAt ℝ γ t) : deriv (fun s => (γ s).1) t = (deriv γ t).1 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv

/-- On a regular vertical slice, the integral of the partial derivative is minus the
sum of the oriented jumps. The compactness and regularity assumptions yield finitely
many crossings, without requiring a decomposition of the whole region into simple regions. -/
private theorem integral_vertical_slice {a b c d x : ℝ} {D U : Set (ℝ × ℝ)}
    {γ : ℝ → ℝ × ℝ} {P : ℝ × ℝ → ℝ} {V : Set ℝ}
    (hcd : c ≤ d) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (hbox : ∀ p ∈ closure D, p.2 ∈ Ioo c d) (hP : ContDiffOn ℝ 1 P U)
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (hV : IsOpen V) (hVsub : V ⊆ Ioo a b) (hγ : ContDiffOn ℝ 1 γ V)
    (hleft : ∀ t ∈ V, ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D)
    (hreg : ∀ t ∈ Icc a b, (γ t).1 = x → t ∈ V ∧ deriv (fun s => (γ s).1) t ≠ 0)
    (hi : Integrable (fun y => D.indicator (fun p => deriv (fun z => P (p.1, z)) p.2) (x, y))
      volume) :
    (∫ y, D.indicator (fun p => deriv (fun z => P (p.1, z)) p.2) (x,y)) =
      -(∑' t : {t : ℝ // (t ∈ V ∧ deriv (fun s => (γ s).1) t ≠ 0) ∧ (γ t).1 = x},
        crossingSign (deriv (fun s => (γ s).1) (t : ℝ)) * exteriorWeight D (γ t) * P (γ t)) := by
  classical
  let g := fun s => (γ s).1
  let k := fun s => (γ s).2
  let X : Set ℝ := {t ∈ Icc a b | g t = x}
  have hX : X.Finite := finite_regular_fiber hV hγcont.fst hγ.fst hreg
  let K := hX.toFinset
  have hK (t : ℝ) : t ∈ K ↔ t ∈ Icc a b ∧ g t = x := Set.Finite.mem_toFinset _
  let Y := K.image k
  let u := fun y => D.indicator P (x, y)
  let v := fun y => D.indicator (fun p => deriv (fun z => P (p.1, z)) p.2) (x,y)
  let w := fun t => crossingSign (deriv g t) * exteriorWeight D (γ t) * P (γ t)
  have hY (y : ℝ) : y ∈ Y ↔ (x, y) ∈ frontier D := by
    rw [← hγtrace, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, heq⟩
      obtain ⟨htI, htX⟩ := (hK _).mp ht
      exact ⟨t, htI, Prod.ext htX heq⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨t, (hK _).mpr ⟨ht, congrArg Prod.fst heq⟩, congrArg Prod.snd heq⟩
  have hYI : (↑Y : Set ℝ) ⊆ Ioo c d := fun y hy =>
    hbox (x,y) (frontier_subset_closure ((hY y).mp hy))
  have hKinj : Set.InjOn k (↑K : Set ℝ) := by
    intro t ht s hs hts
    obtain ⟨htI, htx⟩ := (hK _).mp ht
    obtain ⟨hsI, hsx⟩ := (hK _).mp hs
    have ht' := hVsub (hreg t htI htx).1
    have hs' := hVsub (hreg s hsI hsx).1
    exact hγinj ⟨htI.1, ht'.2⟩ ⟨hsI.1, hs'.2⟩ (Prod.ext (htx.trans hsx.symm) hts)
  have hjump (y : ℝ) (hy : y ∈ Y) : ∃ l r : ℝ, Tendsto u (𝓝[<] y) (𝓝 l) ∧
      Tendsto u (𝓝[>] y) (𝓝 r) ∧ ∀ t ∈ K, k t = y → r - l = w t := by
    obtain ⟨t, ht, htY⟩ := Finset.mem_image.mp hy
    obtain ⟨htI, htX⟩ := (hK _).mp ht
    obtain ⟨htV, htd⟩ := hreg t htI htX
    have hct := (hγ t htV).contDiffAt (hV.mem_nhds htV)
    have hdeq : deriv g t = (deriv γ t).1 := deriv_fst_curve (hct.differentiableAt one_ne_zero)
    have hγD : γ t ∈ frontier D := hγtrace ▸ mem_image_of_mem γ htI
    have hpcont := (hP.continuousOn _ (hDU (frontier_subset_closure hγD))).continuousAt
      (hU.mem_nhds (hDU (frontier_subset_closure hγD)))
    obtain ⟨l, r, hl, hr, heq⟩ := exists_vertical_slice_jump hγcont hγclosed hγinj hγtrace
      (hVsub htV) hct (hdeq ▸ htd) (hleft t htV) hpcont
    change Tendsto (fun y => D.indicator P (g t, y)) (𝓝[<] (k t)) (𝓝 l) at hl
    change Tendsto (fun y => D.indicator P (g t, y)) (𝓝[>] (k t)) (𝓝 r) at hr
    rw [htX, htY] at hl hr
    refine ⟨l, r, hl, hr, fun s hs hsy => ?_⟩
    have hst := hKinj hs ht (hsy.trans htY.symm)
    rw [hst]
    simpa only [w, hdeq] using heq
  choose! L R hL hR hLR using hjump
  have hloc (y : ℝ) (hy : y ∉ Y) : HasDerivAt u (v y) y := by
    have hp : (x,y) ∈ interior D ∪ interior Dᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact fun h => hy ((hY y).mpr h)
    have he : Continuous (fun z : ℝ => (x,z)) := continuous_const.prodMk continuous_id
    rcases hp with hp | hp
    · have hmem : (x,y) ∈ D := interior_subset hp
      have hd := hP.differentiableOn one_ne_zero _ (hDU (subset_closure hmem))
      have hP' := (hd.differentiableAt (hU.mem_nhds (hDU (subset_closure hmem)))).hasFDerivAt
      have hp' := hP'.comp_hasDerivAt y (hasDerivAt_vertical x y)
      have hv : v y = (fderiv ℝ P (x,y)) (0,1) := by
        change D.indicator (fun p => deriv (fun z => P (p.1, z)) p.2) (x,y) = _
        rw [indicator_of_mem hmem]
        exact hp'.deriv
      rw [hv]
      apply hp'.congr_of_eventuallyEq
      filter_upwards [he.continuousAt.eventually_mem (isOpen_interior.mem_nhds hp)] with z hz
      exact indicator_of_mem (interior_subset hz) P
    · have hmem : (x,y) ∉ D := interior_subset hp
      have hv : v y = 0 := indicator_of_notMem hmem _
      rw [hv]
      apply (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [he.continuousAt.eventually_mem (isOpen_interior.mem_nhds hp)] with z hz
      exact indicator_of_notMem (interior_subset hz) P
  have hv1 : IntervalIntegrable v volume c d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr hi.integrableOn
  have hzero (y : ℝ) (hy : y ∉ Ioo c d) : (x,y) ∉ D :=
    fun hm => hy (hbox (x,y) (subset_closure hm))
  have hends : u d - u c = 0 := by
    have hc' := hzero c (fun h => h.1.false)
    have hd' := hzero d (fun h => h.2.false)
    simp only [u, indicator_of_notMem hc', indicator_of_notMem hd', sub_self]
  have hf := integral_add_jumps hcd Y hYI
    (fun y hy => (hloc y hy.2).continuousAt.continuousWithinAt)
    (fun y hy => hloc y hy.2) hv1 hL hR
  have hsum : (∑ y ∈ Y, (R y - L y)) = ∑ t ∈ K, w t := by
    rw [Finset.sum_image (fun t ht s hs h => hKinj ht hs h)]
    exact Finset.sum_congr rfl fun t ht => hLR (k t) (Finset.mem_image_of_mem k ht) t ht rfl
  have hival : (∫ y in c..d, v y) = ∫ y, v y := by
    rw [intervalIntegral.integral_of_le hcd, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ioc c d
    · exact indicator_of_mem hy _
    · have hy' : y ∉ Ioo c d := fun h => hy (Ioo_subset_Ioc_self h)
      rw [indicator_of_notMem hy, show v y = 0 from indicator_of_notMem (hzero y hy') _]
  have hFiber : {t : ℝ | (t ∈ V ∧ deriv g t ≠ 0) ∧ g t = x} = (↑K : Set ℝ) := by
    ext t
    rw [Finset.mem_coe, hK]
    exact ⟨fun h => ⟨Ioo_subset_Icc_self (hVsub h.1.1), h.2⟩,
      fun h => ⟨hreg t h.1 h.2, h.2⟩⟩
  change (∫ y, v y) = -(∑' t : ({t : ℝ | (t ∈ V ∧ deriv g t ≠ 0) ∧ g t = x} : Set ℝ),
    w (t : ℝ))
  rw [hFiber, tsum_subtype]
  have hsum' : (∑' t, (↑K : Set ℝ).indicator w t) = ∑ t ∈ K, w t := by
    rw [tsum_eq_sum (s := K) fun t h => indicator_of_notMem h w]
    exact Finset.sum_congr rfl fun t ht => indicator_of_mem ht _
  rw [hsum', ← hsum, ← hival]
  linarith [hf.trans hends]

/-- Coordinate partial derivatives of a C¹ field are continuous on its open domain. -/
private theorem continuousOn_vertical_partial {U : Set (ℝ × ℝ)} {P : ℝ × ℝ → ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U) :
    ContinuousOn (fun p => deriv (fun y => P (p.1,y)) p.2) U := by
  apply ((hP.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
    (continuousOn_const (c := ((0,1) : ℝ × ℝ)))).congr
  intro p hp
  rcases p with ⟨x,y⟩
  have hd := (hP.differentiableOn one_ne_zero (x,y) hp).differentiableAt (hU.mem_nhds hp)
  exact (hd.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_vertical x y)).deriv

/-- The exterior weight times the parameter integrand is integrable. The weight is a
measurable indicator, not initially assumed to be one. -/
private theorem integrableOn_weighted_deriv {a b : ℝ} {D : Set (ℝ × ℝ)} {γ : ℝ → ℝ × ℝ}
    {f g : ℝ → ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hf : IntegrableOn (fun t => f t * deriv g t) (Icc a b)) :
    IntegrableOn (fun t => exteriorWeight D (γ t) * f t * deriv g t) (Icc a b) := by
  classical
  let E := Icc a b ∩ γ ⁻¹' closure (interior Dᶜ)
  have hE : IsClosed E := hγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  apply (hf.indicator hE.measurableSet).congr_fun _ measurableSet_Icc
  intro t ht
  change E.indicator (fun t => f t * deriv g t) t = exteriorWeight D (γ t) * f t * deriv g t
  by_cases h : γ t ∈ closure (interior Dᶜ)
  · simp only [indicator_of_mem (show t ∈ E from ⟨ht, h⟩), exteriorWeight, ite_eq_left h, one_mul]
  · simp only [indicator_of_notMem (show t ∉ E from fun ht' => h ht'.2), exteriorWeight,
      ite_eq_right h, zero_mul]

/-- Fubini, the finite-slice jump formula, and coarea give the vertical part of Green's formula
with the exterior flag retained as a weight. -/
private theorem weighted_vertical_green {a b : ℝ} {D U : Set (ℝ × ℝ)} {S : Finset ℝ}
    {γ : ℝ → ℝ × ℝ} {P : ℝ × ℝ → ℝ}
    (hab : a < b) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (hD : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : ContDiffOn ℝ 1 P U)
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ha : a ∈ S) (hb : b ∈ S) (hS : (↑S : Set ℝ) ⊆ Icc a b)
    (hγ : ContDiffOn ℝ 1 γ (Ioo a b \ ↑S))
    (hγpieces : ∀ u v, u ∈ S → v ∈ S → u < v → Ioo u v ∩ (↑S : Set ℝ) = ∅ →
      ContDiffOn ℝ 1 γ (Icc u v))
    (hleft : ∀ t ∈ Ioo a b \ (↑S : Set ℝ), ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (∫ p in D, deriv (fun y => P (p.1, y)) p.2) =
      -(∫ t in a..b, exteriorWeight D (γ t) * P (γ t) * deriv (fun s => (γ s).1) t) := by
  classical
  let V := Ioo a b \ (↑S : Set ℝ)
  let g := fun t => (γ t).1
  let W : Set ℝ := {t ∈ V | deriv g t ≠ 0}
  let w := fun t => crossingSign (deriv g t) * exteriorWeight D (γ t) * P (γ t)
  let q := fun p : ℝ × ℝ => deriv (fun y => P (p.1, y)) p.2
  have hV : IsOpen V := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have hVsub : V ⊆ Ioo a b := sdiff_subset
  have hpathU (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ U :=
    hDU (frontier_subset_closure (hγtrace ▸ mem_image_of_mem γ ht))
  have hI : IntegrableOn q D :=
    (((continuousOn_vertical_partial hU hP).mono hDU).integrableOn_compact
      (μ := volume) hD.isCompact_closure).mono_set subset_closure
  have hprod : Integrable (D.indicator q) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hDm).mpr hI
  have hlineInt : IntegrableOn (fun t => P (γ t) * deriv g t) (Icc a b) :=
    integrableOn_mul_deriv_of_piecewise ha hb hS
      (hP.continuousOn.comp hγcont hpathU)
      (fun u v hu hv huv hgap => (hγpieces u v hu hv huv hgap).fst)
  let l := fun t => exteriorWeight D (γ t) * P (γ t) * deriv g t
  have hl : IntegrableOn l (Icc a b) := integrableOn_weighted_deriv hγcont hlineInt
  have hsub : W ⊆ V := fun _ ht => ht.1
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun t ht => ?_
    have h₁ : ∀ᶠ s in 𝓝 t, s ∈ V := hV.mem_nhds ht.1
    have hc : ContinuousAt (deriv g) t :=
      ((hγ.fst.continuousOn_deriv_of_isOpen hV le_rfl) t ht.1).continuousAt h₁
    have h₂ : ∀ᶠ s in 𝓝 t, deriv g s ≠ 0 := hc.eventually_ne ht.2
    exact h₁.and h₂
  have hws (t : ℝ) (ht : t ∈ W) : |deriv g t| • w t = l t := by
    rcases lt_or_gt_of_ne ht.2 with hn | hp
    · simp only [smul_eq_mul, w, l, crossingSign, ite_eq_right hn.not_gt, abs_of_neg hn,
        mul_neg, neg_mul, neg_neg]
      ring
    · simp only [smul_eq_mul, w, l, crossingSign, ite_eq_left hp, abs_of_pos hp, one_mul]
      ring
  have hwInt : IntegrableOn (fun t => |deriv g t| • w t) W :=
    (hl.mono_set (hsub.trans (hVsub.trans Ioo_subset_Icc_self))).congr_fun
      (fun t ht => (hws t ht).symm) hW.measurableSet
  have hvAE : V =ᵐ[volume] (Icc a b : Set ℝ) := by
    have hs : ∀ᵐ x : ℝ, x ∉ (↑S : Set ℝ) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using S.finite_toSet.measure_zero (volume : Measure ℝ)
    filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b), hs]
      with t ht hs'
    exact ⟨fun hv => ht.mp hv.1, fun hv => ⟨ht.mpr hv, hs'⟩⟩
  have hline : (∫ t in a..b, l t) = ∫ t in W, |deriv g t| • w t := by
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_congr_set Ioc_ae_eq_Icc,
      setIntegral_congr_set hvAE.symm]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV.measurableSet hsub
      (fun t ht => show l t = 0 from by
        have hz : deriv g t = 0 := by
          by_contra hn
          exact ht.2 ⟨ht.1, hn⟩
        simp only [l, hz, mul_zero])]
    exact setIntegral_congr_fun hW.measurableSet fun t ht => (hws t ht).symm
  obtain ⟨r, hr, hball⟩ := (Metric.isBounded_closure_of_isBounded hD).subset_ball_lt 0 0
  have hbox (p : ℝ × ℝ) (hp : p ∈ closure D) : p.2 ∈ Ioo (-r) r := by
    have hlt : ‖p‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hball hp
    rw [Prod.norm_def] at hlt
    exact abs_lt.mp ((le_max_right ‖p.1‖ ‖p.2‖).trans_lt hlt)
  have hFub : (∫ p in D, q p) = ∫ x : ℝ, ∫ y : ℝ, D.indicator q (x,y) := by
    rw [← integral_indicator hDm, Measure.volume_eq_prod]
    exact integral_prod _ hprod
  have hreg := ae_forall_mem_regular_fiber ha hb hγ.fst
  change (∫ p in D, q p) = -(∫ t in a..b, l t)
  rw [hFub, hline, integral_abs_deriv_eq_integral_fiber_sum hV hγ.fst hwInt,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hreg, hprod.prod_right_ae] with x hx hxi
  exact integral_vertical_slice (by linarith : -r ≤ r) hU hDU hbox hP hγcont hγclosed hγinj
    hγtrace hV hVsub hγ hleft hx hxi

private def quarterTurn : (ℝ × ℝ) ≃ₗᵢ[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, -p.1)
  invFun p := (-p.2, p.1)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [add_comm]
  map_smul' r p := by simp
  norm_map' p := by simp [Prod.norm_def, max_comm]

private theorem quarterTurn_apply (p : ℝ × ℝ) : quarterTurn p = (p.2, -p.1) := rfl

private theorem quarterTurn_symm_apply (p : ℝ × ℝ) : quarterTurn.symm p = (-p.2, p.1) := rfl

private theorem quarterTurn_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n quarterTurn :=
  quarterTurn.toContinuousLinearEquiv.toContinuousLinearMap.contDiff

private theorem quarterTurn_symm_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n quarterTurn.symm :=
  quarterTurn.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff

private theorem deriv_quarterTurn_comp {γ : ℝ → ℝ × ℝ} {t : ℝ} (h : DifferentiableAt ℝ γ t) :
    deriv (quarterTurn ∘ γ) t = quarterTurn (deriv γ t) :=
  (quarterTurn.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t h.hasDerivAt).deriv

private theorem quarterTurn_trace {D : Set (ℝ × ℝ)} {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (h : γ '' Icc a b = frontier D) :
    (quarterTurn ∘ γ) '' Icc a b = frontier (quarterTurn '' D) := by
  calc
    _ = quarterTurn '' (γ '' Icc a b) := (Set.image_image quarterTurn γ (Icc a b)).symm
    _ = _ := by rw [h]; exact quarterTurn.toHomeomorph.image_frontier D

private theorem quarterTurn_left {D : Set (ℝ × ℝ)} {γ : ℝ → ℝ × ℝ} {t : ℝ}
    (h : DifferentiableAt ℝ γ t)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η → (quarterTurn ∘ γ) t +
      ε • (-(deriv (quarterTurn ∘ γ) t).2, (deriv (quarterTurn ∘ γ) t).1) ∈ quarterTurn '' D := by
  obtain ⟨η, hη, hn⟩ := hleft
  refine ⟨η, hη, fun ε hε he => ?_⟩
  rw [deriv_quarterTurn_comp h]
  refine ⟨_, hn ε hε he, ?_⟩
  rw [map_add, map_smul]
  congr 2
  simp [quarterTurn_apply]

private theorem mem_exterior_closure_quarterTurn {D : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    quarterTurn p ∈ closure (interior (quarterTurn '' D)ᶜ) ↔ p ∈ closure (interior Dᶜ) := by
  let e := quarterTurn.toHomeomorph
  change e p ∈ closure (interior (e '' D)ᶜ) ↔ p ∈ closure (interior Dᶜ)
  have hc : (e '' D)ᶜ = e '' Dᶜ := (e.toEquiv.image_compl D).symm
  rw [hc, ← e.image_interior, ← e.image_closure]
  exact e.injective.mem_set_image

private theorem quarterTurn_weight (D : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    exteriorWeight (quarterTurn '' D) (quarterTurn p) = exteriorWeight D p := by
  classical
  simp only [exteriorWeight, mem_exterior_closure_quarterTurn]

private theorem measurePreserving_quarterTurn :
    MeasurePreserving quarterTurn (volume : Measure (ℝ × ℝ)) volume := by
  have hn := Measure.measurePreserving_neg (volume : Measure ℝ)
  have he := (MeasurePreserving.id (volume : Measure ℝ)).prod hn
  exact he.comp (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))

private theorem hasDerivAt_horizontal (x y : ℝ) :
    HasDerivAt (fun z : ℝ => (z, y)) (1, 0) x := by
  simpa only [id_eq] using HasDerivAt.prodMk (hasDerivAt_id x) (hasDerivAt_const x y)

private theorem quarterTurn_partial {P : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : DifferentiableAt ℝ P p) :
    deriv (fun y => P (quarterTurn.symm ((quarterTurn p).1, y))) (quarterTurn p).2 =
      -(deriv (fun x => P (x,p.2)) p.1) := by
  rcases p with ⟨x,y⟩
  have hpart := h.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontal x y)
  have hneg : HasDerivAt Neg.neg (-1 : ℝ) (-x) := hasDerivAt_neg _
  have hd := hpart.comp_of_eq (-x) hneg (neg_neg x).symm
  change deriv (fun s => P (-s,y)) (-x) = -(deriv (fun s => P (s,y)) x)
  change HasDerivAt (fun s => P (-s,y)) (_ * -1) (-x) at hd
  change HasDerivAt (fun s => P (s,y)) _ x at hpart
  rw [hd.deriv, hpart.deriv, mul_neg_one]

/-- The horizontal part is the vertical formula after an orientation-preserving quarter-turn. -/
private theorem weighted_horizontal_green {a b : ℝ} {D U : Set (ℝ × ℝ)} {S : Finset ℝ}
    {γ : ℝ → ℝ × ℝ} {P : ℝ × ℝ → ℝ}
    (hab : a < b) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (hD : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : ContDiffOn ℝ 1 P U)
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ha : a ∈ S) (hb : b ∈ S) (hS : (↑S : Set ℝ) ⊆ Icc a b)
    (hγ : ContDiffOn ℝ 1 γ (Ioo a b \ ↑S))
    (hγpieces : ∀ u v, u ∈ S → v ∈ S → u < v → Ioo u v ∩ (↑S : Set ℝ) = ∅ →
      ContDiffOn ℝ 1 γ (Icc u v))
    (hleft : ∀ t ∈ Ioo a b \ (↑S : Set ℝ), ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (∫ p in D, deriv (fun x => P (x, p.2)) p.1) =
      ∫ t in a..b, exteriorWeight D (γ t) * P (γ t) * deriv (fun s => (γ s).2) t := by
  let e := quarterTurn.toHomeomorph
  let D' := quarterTurn '' D
  let U' := quarterTurn '' U
  let P' := P ∘ quarterTurn.symm
  let γ' := quarterTurn ∘ γ
  have hV : IsOpen (Ioo a b \ (↑S : Set ℝ)) := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have hU' : IsOpen U' := e.isOpenMap _ hU
  have hDU' : closure D' ⊆ U' := by
    change closure (e '' D) ⊆ e '' U
    rw [← e.image_closure]
    exact image_mono hDU
  have hD' : Bornology.IsBounded D' :=
    ((hD.isCompact_closure.image quarterTurn.continuous).isBounded).subset
      (image_mono subset_closure)
  have hemb : MeasurableEmbedding quarterTurn := e.measurableEmbedding
  have hDm' : MeasurableSet D' := hemb.measurableSet_image' hDm
  have hP' : ContDiffOn ℝ 1 P' U' := hP.comp quarterTurn_symm_contDiff.contDiffOn (by
    rintro q ⟨p, hp, rfl⟩
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hp)
  have hor : ∀ t ∈ Ioo a b \ (↑S : Set ℝ), ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ' t + ε • (-(deriv γ' t).2, (deriv γ' t).1) ∈ D' := fun t ht =>
    quarterTurn_left ((hγ.differentiableOn one_ne_zero t ht).differentiableAt (hV.mem_nhds ht))
      (hleft t ht)
  have hGreen := weighted_vertical_green (γ := γ') (P := P') hab hU' hDU' hD' hDm' hP'
    (quarterTurn.continuous.comp_continuousOn hγcont) (congrArg quarterTurn hγclosed)
    (fun _ hx _ hy he => hγinj hx hy (quarterTurn.injective he)) (quarterTurn_trace hγtrace)
    ha hb hS (quarterTurn_contDiff.comp_contDiffOn hγ)
    (fun u v hu hv huv hgap => quarterTurn_contDiff.comp_contDiffOn
      (hγpieces u v hu hv huv hgap)) hor
  change (∫ q in D', deriv (fun y => P' (q.1,y)) q.2) = _ at hGreen
  rw [← measurePreserving_quarterTurn.setIntegral_preimage_emb hemb
    (fun q => deriv (fun y => P' (q.1,y)) q.2) D'] at hGreen
  have hpre : quarterTurn ⁻¹' D' = D := preimage_image_eq _ quarterTurn.injective
  rw [hpre] at hGreen
  have harea : (∫ p in D, deriv (fun y => P' ((quarterTurn p).1,y)) (quarterTurn p).2) =
      -(∫ p in D, deriv (fun x => P (x, p.2)) p.1) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun hDm
    intro p hp
    have hpU := hDU (subset_closure hp)
    exact quarterTurn_partial ((hP.differentiableOn one_ne_zero p hpU).differentiableAt
      (hU.mem_nhds hpU))
  have hline : (fun t => exteriorWeight D' (γ' t) * P' (γ' t) *
      deriv (fun s => (γ' s).1) t) = fun t =>
      exteriorWeight D (γ t) * P (γ t) * deriv (fun s => (γ s).2) t := by
    funext t
    simp only [γ', Function.comp_apply, quarterTurn_apply, P', D']
    change exteriorWeight D' (quarterTurn (γ t)) * P (quarterTurn.symm (quarterTurn (γ t))) *
      deriv (fun s => (γ s).2) t = _
    rw [quarterTurn_weight, LinearIsometryEquiv.symm_apply_apply]
  rw [harea, hline] at hGreen
  exact neg_injective hGreen

private theorem hasDerivAt_snd_curve {γ : ℝ → ℝ × ℝ} {t : ℝ}
    (hd : DifferentiableAt ℝ γ t) :
    HasDerivAt (fun s => (γ s).2) (deriv γ t).2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt

/-- At every regular time the exterior weight is locally constant, using a quarter-turn
when the original tangent is vertical. -/
private theorem eventually_exterior_weight_eq {a b t : ℝ} {D : Set (ℝ × ℝ)} {γ : ℝ → ℝ × ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (hcd : ContDiffAt ℝ 1 γ t) (hd : deriv γ t ≠ 0)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    ∀ᶠ s in 𝓝 t, exteriorWeight D (γ s) = exteriorWeight D (γ t) := by
  classical
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ closure (interior Dᶜ) ↔ γ t ∈ closure (interior Dᶜ) := by
    by_cases hfst : (deriv γ t).1 = 0
    · have hsnd : (deriv γ t).2 ≠ 0 := fun hs => hd (Prod.ext hfst hs)
      have hd' := hcd.differentiableAt one_ne_zero
      have hn' : (deriv (quarterTurn ∘ γ) t).1 ≠ 0 := by
        rw [deriv_quarterTurn_comp hd', quarterTurn_apply]
        exact hsnd
      have h := eventually_exterior_flag_iff
        (quarterTurn.continuous.comp_continuousOn hγcont) (congrArg quarterTurn hγclosed)
        (fun _ hx _ hy he => hγinj hx hy (quarterTurn.injective he)) (quarterTurn_trace hγtrace)
        ht (quarterTurn_contDiff.contDiffAt.comp t hcd) hn' (quarterTurn_left hd' hleft)
      simpa only [Function.comp_apply, mem_exterior_closure_quarterTurn] using h
    · exact eventually_exterior_flag_iff hγcont hγclosed hγinj hγtrace ht hcd hfst hleft
  filter_upwards [hn] with s hs
  simp only [exteriorWeight, hs]

private theorem fderiv_apply_coords (A : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    A p = A (1,0) * p.1 + A (0,1) * p.2 := by
  have hp : p = p.1 • ((1,0) : ℝ × ℝ) + p.2 • ((0,1) : ℝ × ℝ) := by
    apply Prod.ext <;> simp
  calc
    A p = A (p.1 • ((1,0) : ℝ × ℝ) + p.2 • ((0,1) : ℝ × ℝ)) := congrArg A hp
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul, mul_comm]

/-- Weighted Green applied to an exact form says that its weighted line integral is zero. -/
private theorem weighted_gradient_integral_eq_zero {D : Set (ℝ × ℝ)} {a b : ℝ} {S : Finset ℝ}
    {γ : ℝ → ℝ × ℝ} (hab : a < b) (ha : a ∈ S) (hb : b ∈ S)
    (hS : (↑S : Set ℝ) ⊆ Icc a b) (hc : ContinuousOn γ (Icc a b))
    (hd : DifferentiableOn ℝ γ (Ioo a b \ ↑S))
    (hpc : ∀ u v, u ∈ S → v ∈ S → u < v → Ioo u v ∩ (↑S : Set ℝ) = ∅ →
      ContDiffOn ℝ 1 γ (Icc u v))
    (hvert : ∀ P : ℝ × ℝ → ℝ, ContDiff ℝ 1 P →
      (∫ p in D, deriv (fun y => P (p.1,y)) p.2) =
        -(∫ t in a..b, exteriorWeight D (γ t) * P (γ t) * deriv (fun s => (γ s).1) t))
    (horiz : ∀ Q : ℝ × ℝ → ℝ, ContDiff ℝ 1 Q →
      (∫ p in D, deriv (fun x => Q (x,p.2)) p.1) =
        ∫ t in a..b, exteriorWeight D (γ t) * Q (γ t) * deriv (fun s => (γ s).2) t)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    let z := fun t => exteriorWeight D (γ t) * deriv (φ ∘ γ) t
    IntervalIntegrable z volume a b ∧ (∫ t in a..b, z t) = 0 := by
  let e₁ : ℝ × ℝ := (1,0)
  let e₂ : ℝ × ℝ := (0,1)
  let P := fun p => fderiv ℝ φ p e₁
  let Q := fun p => fderiv ℝ φ p e₂
  have hdφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hP : ContDiff ℝ 1 P := hdφ.clm_apply contDiff_const
  have hQ : ContDiff ℝ 1 Q := hdφ.clm_apply contDiff_const
  have hcurl (p : ℝ × ℝ) : deriv (fun x => Q (x,p.2)) p.1 = deriv (fun y => P (p.1,y)) p.2 := by
    have hF := (hdφ.differentiable one_ne_zero p).hasFDerivAt
    have hPd := hF.clm_apply (hasFDerivAt_const e₁ p)
    have hQd := hF.clm_apply (hasFDerivAt_const e₂ p)
    have hp := (hPd.comp_hasDerivAt p.2 (hasDerivAt_vertical p.1 p.2)).deriv
    have hq := (hQd.comp_hasDerivAt p.1 (hasDerivAt_horizontal p.1 p.2)).deriv
    have hsym := hφ.contDiffAt.isSymmSndFDerivAt (x := p) (by simp)
    change deriv (fun y => P (p.1,y)) p.2 = _ at hp
    change deriv (fun x => Q (x,p.2)) p.1 = _ at hq
    rw [hp, hq]
    simpa [e₁, e₂] using hsym.eq e₁ e₂
  let l := fun t => exteriorWeight D (γ t) * P (γ t) * deriv (fun s => (γ s).1) t
  let m := fun t => exteriorWeight D (γ t) * Q (γ t) * deriv (fun s => (γ s).2) t
  have hli : IntervalIntegrable l volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr <|
      integrableOn_weighted_deriv hc (integrableOn_mul_deriv_of_piecewise ha hb hS
        (hP.continuous.comp_continuousOn hc)
        (fun u v hu hv huv hgap => (hpc u v hu hv huv hgap).fst))
  have hmi : IntervalIntegrable m volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr <|
      integrableOn_weighted_deriv hc (integrableOn_mul_deriv_of_piecewise ha hb hS
        (hQ.continuous.comp_continuousOn hc)
        (fun u v hu hv huv hgap => (hpc u v hu hv huv hgap).snd))
  let V := Ioo a b \ (↑S : Set ℝ)
  have hV : IsOpen V := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have hev : (fun t => exteriorWeight D (γ t) * deriv (φ ∘ γ) t) =ᵐ[volume.restrict (uIoc a b)]
      fun t => l t + m t := by
    rw [uIoc_of_le hab.le, ← restrict_Ioo_eq_restrict_Ioc]
    have hs : ∀ᵐ x : ℝ, x ∉ (↑S : Set ℝ) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using S.finite_toSet.measure_zero (volume : Measure ℝ)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo,
      ae_restrict_of_ae hs] with t ht hts
    have htv : t ∈ V := ⟨ht, hts⟩
    have hdγ := (hd t htv).differentiableAt (hV.mem_nhds htv)
    have hcomp := ((hφ.differentiable (by norm_num) (γ t)).hasFDerivAt.comp_hasDerivAt
      t hdγ.hasDerivAt).deriv
    change exteriorWeight D (γ t) * deriv (φ ∘ γ) t = l t + m t
    rw [hcomp, fderiv_apply_coords]
    simp only [l, m, P, Q, deriv_fst_curve hdγ, (hasDerivAt_snd_curve hdγ).deriv, e₁, e₂]
    ring
  refine ⟨(hli.add hmi).congr_ae hev.symm, ?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict hev, intervalIntegral.integral_add hli hmi]
  have hv := hvert P hP
  have hh := horiz Q hQ
  have heq : (∫ p in D, deriv (fun x => Q (x,p.2)) p.1) =
      ∫ p in D, deriv (fun y => P (p.1,y)) p.2 := by simp only [hcurl]
  rw [hh, hv] at heq
  change (∫ t in a..b, l t) + (∫ t in a..b, m t) = 0
  linarith

/-- A function that is locally constant at all points of a preconnected set is constant there. -/
private theorem eq_of_eventually_eq_const_on_preconnected {T : Set ℝ} {w : ℝ → ℝ}
    (hT : IsPreconnected T) (hw : ∀ x ∈ T, ∀ᶠ y in 𝓝 x, w y = w x)
    {x y : ℝ} (hx : x ∈ T) (hy : y ∈ T) : w y = w x := by
  let A : Set ℝ := {t | w t = w x}
  have hs : T ⊆ interior A ∪ interior Aᶜ := by
    intro t ht
    by_cases h : t ∈ A
    · exact Or.inl (mem_interior_iff_mem_nhds.mpr ((hw t ht).mono fun u hu => hu.trans h))
    · exact Or.inr (mem_interior_iff_mem_nhds.mpr ((hw t ht).mono fun u hu hu' =>
        h (hu.symm.trans hu')))
  have hd : Disjoint (interior A) (interior Aᶜ) :=
    Set.disjoint_left.mpr fun t h₁ h₂ => (interior_subset h₂ : t ∉ A) (interior_subset h₁)
  have h := (hT.subset_or_subset isOpen_interior isOpen_interior hd hs).resolve_right
    (fun h => (interior_subset (h hx) : x ∉ A) rfl)
  exact interior_subset (h hy)

private theorem exists_left_weight {a b c : ℝ} {S : Finset ℝ} {w : ℝ → ℝ}
    (hac : a < c) (hcb : c ≤ b)
    (hw : ∀ x ∈ Ioo a b \ (↑S : Set ℝ), ∀ᶠ y in 𝓝 x, w y = w x) :
    ∃ k : ℝ, ∀ᶠ t in 𝓝[<] c, w t = k := by
  classical
  have hn : (↑(S.erase c) : Set ℝ)ᶜ ∈ 𝓝 c :=
    (S.erase c).finite_toSet.isClosed.isOpen_compl.mem_nhds (S.notMem_erase c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let δ := min r (c - a)
  have hδ : 0 < δ := lt_min hr (sub_pos.mpr hac)
  let T := Ioo (c - δ) c
  have hT : T ⊆ Ioo a b \ (↑S : Set ℝ) := by
    intro t ht
    have htr : t ∈ Metric.ball c r := by
      rw [Real.ball_eq_Ioo]
      have hδr : δ ≤ r := min_le_left _ _
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨⟨?_, ht.2.trans_le hcb⟩, fun hs =>
      hball htr (Finset.mem_erase.mpr ⟨ht.2.ne, hs⟩)⟩
    have hδa : δ ≤ c - a := min_le_right _ _
    linarith [ht.1]
  let t₀ := c - δ / 2
  have ht₀ : t₀ ∈ T := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  refine ⟨w t₀, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self c hδ)] with t ht
  exact eq_of_eventually_eq_const_on_preconnected isPreconnected_Ioo
    (fun x hx => hw x (hT hx)) ht₀ ht

private theorem exists_right_weight {a b c : ℝ} {S : Finset ℝ} {w : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c < b)
    (hw : ∀ x ∈ Ioo a b \ (↑S : Set ℝ), ∀ᶠ y in 𝓝 x, w y = w x) :
    ∃ k : ℝ, ∀ᶠ t in 𝓝[>] c, w t = k := by
  classical
  have hn : (↑(S.erase c) : Set ℝ)ᶜ ∈ 𝓝 c :=
    (S.erase c).finite_toSet.isClosed.isOpen_compl.mem_nhds (S.notMem_erase c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let δ := min r (b - c)
  have hδ : 0 < δ := lt_min hr (sub_pos.mpr hcb)
  let T := Ioo c (c + δ)
  have hT : T ⊆ Ioo a b \ (↑S : Set ℝ) := by
    intro t ht
    have htr : t ∈ Metric.ball c r := by
      rw [Real.ball_eq_Ioo]
      have hδr : δ ≤ r := min_le_left _ _
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨⟨hac.trans_lt ht.1, ?_⟩, fun hs =>
      hball htr (Finset.mem_erase.mpr ⟨ht.1.ne', hs⟩)⟩
    have hδb : δ ≤ b - c := min_le_right _ _
    linarith [ht.2]
  let t₀ := c + δ / 2
  have ht₀ : t₀ ∈ T := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  refine ⟨w t₀, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right c hδ)] with t ht
  exact eq_of_eventually_eq_const_on_preconnected isPreconnected_Ioo
    (fun x hx => hw x (hT hx)) ht₀ ht

/-- A polynomial potential can assign value one to one exceptional point and zero to all
other exceptional points. -/
private theorem exists_separating_potential (E : Finset (ℝ × ℝ)) (p : ℝ × ℝ) :
    ∃ φ : ℝ × ℝ → ℝ, ContDiff ℝ 2 φ ∧ φ p = 1 ∧ ∀ q ∈ E, q ≠ p → φ q = 0 := by
  classical
  let distSq (z q : ℝ × ℝ) := (z.1 - q.1)^2 + (z.2 - q.2)^2
  let F (z : ℝ × ℝ) : ℝ := ∏ q ∈ E.erase p, distSq z q
  have hF : ContDiff ℝ 2 F := by
    apply contDiff_prod
    intro q _
    dsimp only [distSq]
    fun_prop
  have hpos : 0 < F p := by
    apply Finset.prod_pos
    intro q hq
    have hne := (Finset.mem_erase.mp hq).1
    by_cases h₁ : p.1 = q.1
    · have h₂ : p.2 ≠ q.2 := fun h => hne (Prod.ext h₁ h).symm
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁)) (sq_nonneg _)
  refine ⟨fun z => F z * (F p)⁻¹, hF.mul contDiff_const, mul_inv_cancel₀ hpos.ne', ?_⟩
  intro q hq hne
  have hz : F q = 0 := Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hq⟩) (by simp [distSq])
  change F q * (F p)⁻¹ = 0
  rw [hz, zero_mul]

/-- Exact forms force the weights on either side of each exceptional time to agree. This
uses test potentials supported in value at a single exceptional image (not an assumption
that the curve has a nonzero one-sided tangent at the exception). -/
private theorem weight_constant_off_subdivision {a b : ℝ} {S : Finset ℝ} {γ : ℝ → ℝ × ℝ}
    {w : ℝ → ℝ} (hab : a < b) (hγc : ContinuousOn γ (Icc a b))
    (hγclosed : γ a = γ b) (hγinj : InjOn γ (Ico a b))
    (hγsimple : ∀ t ∈ Ioo a b, γ t ≠ γ a)
    (ha : a ∈ S) (hb : b ∈ S) (hS : (↑S : Set ℝ) ⊆ Icc a b)
    (hw : ∀ x ∈ Ioo a b \ (↑S : Set ℝ), ∀ᶠ y in 𝓝 x, w y = w x)
    (hd : ∀ t ∈ Ioo a b \ (↑S : Set ℝ), DifferentiableAt ℝ γ t)
    (hTest : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 2 φ →
      IntervalIntegrable (fun t => w t * deriv (φ ∘ γ) t) volume a b ∧
        (∫ t in a..b, w t * deriv (φ ∘ γ) t) = 0) :
    ∀ x ∈ Ioo a b \ (↑S : Set ℝ), ∀ y ∈ Ioo a b \ (↑S : Set ℝ), w x = w y := by
  classical
  let S' := S.filter (fun t => t ∈ Ioo a b)
  have hS' (t : ℝ) : t ∈ S' ↔ t ∈ S ∧ t ∈ Ioo a b := Finset.mem_filter
  have hSl (t : ℝ) (ht : t ∈ S') : ∃ k, ∀ᶠ s in 𝓝[<] t, w s = k := by
    have ht' := ((hS' _).mp ht).2
    exact exists_left_weight (S := S) ht'.1 ht'.2.le hw
  have hSr (t : ℝ) (ht : t ∈ S') : ∃ k, ∀ᶠ s in 𝓝[>] t, w s = k := by
    have ht' := ((hS' _).mp ht).2
    exact exists_right_weight (S := S) ht'.1.le ht'.2 hw
  choose! left hl using hSl
  choose! right hr using hSr
  have hmatch (c : ℝ) (hc : c ∈ S') : left c = right c := by
    obtain ⟨φ, hφ, hcφ, hzφ⟩ := exists_separating_potential (S.image γ) (γ c)
    let F := φ ∘ γ
    let u := fun t => w t * F t
    let v := fun t => w t * deriv F t
    have hct := ((hS' _).mp hc).2
    have hz (s : ℝ) (hs : s ∈ S) (hsc : s ≠ c) : F s = 0 := by
      apply hzφ _ (Finset.mem_image_of_mem _ hs)
      intro he
      have hsi := hS hs
      rcases lt_or_eq_of_le hsi.2 with hsb | rfl
      · exact hsc (hγinj ⟨hsi.1, hsb⟩ ⟨hct.1.le, hct.2⟩ he)
      · rw [← hγclosed] at he
        exact hγsimple c hct he.symm
    have hFa : F a = 0 := hz a ha hct.1.ne
    have hFb : F b = 0 := hz b hb hct.2.ne'
    have hFc : F c = 1 := hcφ
    have hF := hφ.continuous.comp_continuousOn hγc
    have hFl (t : ℝ) (ht : t ∈ Ioc a b) : Tendsto F (𝓝[<] t) (𝓝 (F t)) := by
      refine (hF t ⟨ht.1.le, ht.2⟩).tendsto.mono_left ?_
      exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Icc_mem_nhdsLT_of_mem ht))
    have hFr (t : ℝ) (ht : t ∈ Ico a b) : Tendsto F (𝓝[>] t) (𝓝 (F t)) := by
      refine (hF t ⟨ht.1, ht.2.le⟩).tendsto.mono_left ?_
      exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Icc_mem_nhdsGT_of_mem ht))
    have hder (t : ℝ) (ht : t ∈ Ioo a b \ (↑S : Set ℝ)) : HasDerivAt u (v t) t := by
      have hfd : DifferentiableAt ℝ F t :=
        (hφ.differentiable (by norm_num) (γ t)).comp t (hd t ht)
      apply (hfd.hasDerivAt.const_mul (w t)).congr_of_eventuallyEq
      filter_upwards [hw t ht] with s hs
      exact congrArg (· * F s) hs
    have hcont : ContinuousOn u (Icc a b \ (↑S' : Set ℝ)) := by
      intro t ht
      apply ContinuousWithinAt.mono (t := Icc a b) _ sdiff_subset
      rcases lt_or_eq_of_le ht.1.1 with hat | heq
      · rcases lt_or_eq_of_le ht.1.2 with htb | heq
        · have h := hder t ⟨⟨hat, htb⟩, fun hm => ht.2 ((hS' _).mpr ⟨hm, hat, htb⟩)⟩
          exact h.continuousAt.continuousWithinAt
        · subst t
          obtain ⟨k, hk⟩ := exists_left_weight (S := S) hab le_rfl hw
          apply ContinuousWithinAt.mono (t := Iic b) _ Icc_subset_Iic_self
          rw [← continuousWithinAt_Iio_iff_Iic]
          change Tendsto u (𝓝[<] b) (𝓝 (w b * F b))
          have hv : k * F b = w b * F b := by simp [hFb]
          rw [← hv]
          apply ((hFl b ⟨hab, le_rfl⟩).const_mul k).congr'
          filter_upwards [hk] with s hs using (congrArg (· * F s) hs).symm
      · subst t
        obtain ⟨k, hk⟩ := exists_right_weight (S := S) le_rfl hab hw
        apply ContinuousWithinAt.mono (t := Ici a) _ Icc_subset_Ici_self
        rw [← continuousWithinAt_Ioi_iff_Ici]
        change Tendsto u (𝓝[>] a) (𝓝 (w a * F a))
        have hv : k * F a = w a * F a := by simp [hFa]
        rw [← hv]
        apply ((hFr a ⟨le_rfl, hab⟩).const_mul k).congr'
        filter_upwards [hk] with s hs using (congrArg (· * F s) hs).symm
    have hl' (t : ℝ) (ht : t ∈ S') : Tendsto u (𝓝[<] t) (𝓝 (left t * F t)) := by
      have ht' := ((hS' _).mp ht).2
      apply ((hFl t ⟨ht'.1, ht'.2.le⟩).const_mul (left t)).congr'
      filter_upwards [hl t ht] with s hs using (congrArg (· * F s) hs).symm
    have hr' (t : ℝ) (ht : t ∈ S') : Tendsto u (𝓝[>] t) (𝓝 (right t * F t)) := by
      have ht' := ((hS' _).mp ht).2
      apply ((hFr t ⟨ht'.1.le, ht'.2⟩).const_mul (right t)).congr'
      filter_upwards [hr t ht] with s hs using (congrArg (· * F s) hs).symm
    obtain ⟨hint, h0⟩ := hTest φ hφ
    have hsum := integral_add_jumps (u := u) (v := v) hab.le S'
      (fun s hs => ((hS' s).mp hs).2) hcont
      (fun t ht => hder t ⟨ht.1, fun h => ht.2 ((hS' t).mpr ⟨h, ht.1⟩)⟩)
      hint hl' hr'
    change (∫ t in a..b, v t) = 0 at h0
    have hs0 (s : ℝ) (hs : s ∈ S') (hsc : s ≠ c) :
        right s * F s - left s * F s = 0 := by
      rw [hz s ((hS' _).mp hs).1 hsc, mul_zero, mul_zero, sub_self]
    rw [h0, zero_add, Finset.sum_eq_single c hs0 (fun h => (h hc).elim), hFc] at hsum
    simp only [u, hFa, hFb, mul_zero, sub_self, mul_one] at hsum
    exact (sub_eq_zero.mp hsum).symm
  have horder (x : ℝ) (hx : x ∈ Ioo a b \ (↑S : Set ℝ))
      (y : ℝ) (hy : y ∈ Ioo a b \ (↑S : Set ℝ)) (hxy : x ≤ y) : w x = w y := by
    let T := S'.filter (fun t => t ∈ Ioo x y)
    have hT (t : ℝ) : t ∈ T ↔ t ∈ S' ∧ t ∈ Ioo x y := Finset.mem_filter
    have hTsub : (↑T : Set ℝ) ⊆ Ioo x y := fun t ht => ((hT t).mp ht).2
    have hreg (t : ℝ) (ht : t ∈ Icc x y \ (↑T : Set ℝ)) : t ∈ Ioo a b \ (↑S : Set ℝ) := by
      have hi : t ∈ Ioo a b := ⟨hx.1.1.trans_le ht.1.1, ht.1.2.trans_lt hy.1.2⟩
      refine ⟨hi, fun hm => ?_⟩
      rcases lt_or_eq_of_le ht.1.1 with hxt | rfl
      · rcases lt_or_eq_of_le ht.1.2 with hty | rfl
        · exact ht.2 ((hT t).mpr ⟨(hS' t).mpr ⟨hm, hi⟩, hxt, hty⟩)
        · exact hy.2 hm
      · exact hx.2 hm
    have hwd (t : ℝ) (ht : t ∈ Icc x y \ (↑T : Set ℝ)) : HasDerivAt w 0 t :=
      (hasDerivAt_const t (w t)).congr_of_eventuallyEq (hw t (hreg t ht))
    have hj := integral_add_jumps (u := w) (v := fun _ => 0) hxy T hTsub
      (fun t ht => (hwd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hwd t ⟨Ioo_subset_Icc_self ht.1, ht.2⟩)
      (continuous_const.intervalIntegrable _ _)
      (fun t ht => tendsto_const_nhds.congr' ((hl t ((hT t).mp ht).1).mono fun _ h => h.symm))
      (fun t ht => tendsto_const_nhds.congr' ((hr t ((hT t).mp ht).1).mono fun _ h => h.symm))
    have hh (t : ℝ) (ht : t ∈ T) : right t - left t = 0 :=
      sub_eq_zero.mpr (hmatch t ((hT t).mp ht).1).symm
    have hz := Finset.sum_eq_zero hh
    simp only [intervalIntegral.integral_zero, hz, zero_add] at hj
    exact (sub_eq_zero.mp hj.symm).symm
  intro x hx y hy
  rcases le_total x y with h | h
  · exact horder x hx y hy h
  · exact (horder y hy x hx h).symm

/-- A single regular left-normal chart supplies an interior point. -/
private theorem interior_nonempty_of_nonvertical {a b t : ℝ} {D : Set (ℝ × ℝ)}
    {γ : ℝ → ℝ × ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (hcd : ContDiffAt ℝ 1 γ t) (hd : (deriv γ t).1 ≠ 0)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (interior D).Nonempty := by
  obtain ⟨r, δ, f, hr, hδ, hf, hfr, hf₀, hfd, hgraph⟩ :=
    exists_frontier_graph hγcont hγclosed hγinj hγtrace ht hcd hd
  have hleft' : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ((γ t).1 - ε * (deriv γ t).2, (γ t).2 + ε * (deriv γ t).1) ∈ D := by
    obtain ⟨η, hη, hn⟩ := hleft
    refine ⟨η, hη, fun ε hε he => ?_⟩
    have hcoord : γ t + ε • (-(deriv γ t).2, (deriv γ t).1) =
        ((γ t).1 - ε * (deriv γ t).2, (γ t).2 + ε * (deriv γ t).1) := by
      apply Prod.ext <;> simp [sub_eq_add_neg]
    exact hcoord ▸ hn ε hε he
  obtain ⟨_, _, hp, hn⟩ := frontier_graph_side_status hr hδ hd hf hfr hf₀ hfd hgraph hleft'
  rcases lt_or_gt_of_ne hd with hv | hv
  · refine ⟨((γ t).1, (γ t).2 - δ / 2), hn hv ⟨Metric.mem_ball_self hr, ?_, ?_⟩⟩
    · dsimp; linarith
    · dsimp; rw [hf₀]; linarith
  · refine ⟨((γ t).1, (γ t).2 + δ / 2), hp hv ⟨Metric.mem_ball_self hr, ?_, ?_⟩⟩
    · dsimp; rw [hf₀]; linarith
    · dsimp; linarith

private theorem interior_nonempty_of_regular {a b t : ℝ} {D : Set (ℝ × ℝ)}
    {γ : ℝ → ℝ × ℝ}
    (hγcont : ContinuousOn γ (Icc a b)) (hγclosed : γ a = γ b)
    (hγinj : InjOn γ (Ico a b)) (hγtrace : γ '' Icc a b = frontier D)
    (ht : t ∈ Ioo a b) (hcd : ContDiffAt ℝ 1 γ t) (hd : deriv γ t ≠ 0)
    (hleft : ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (interior D).Nonempty := by
  by_cases hfst : (deriv γ t).1 = 0
  · have hsnd : (deriv γ t).2 ≠ 0 := fun hs => hd (Prod.ext hfst hs)
    have hd' := hcd.differentiableAt one_ne_zero
    have hn' : (deriv (quarterTurn ∘ γ) t).1 ≠ 0 := by
      rw [deriv_quarterTurn_comp hd', quarterTurn_apply]
      exact hsnd
    have h := interior_nonempty_of_nonvertical
      (quarterTurn.continuous.comp_continuousOn hγcont) (congrArg quarterTurn hγclosed)
      (fun _ hx _ hy he => hγinj hx hy (quarterTurn.injective he)) (quarterTurn_trace hγtrace)
      ht (quarterTurn_contDiff.contDiffAt.comp t hcd) hn' (quarterTurn_left hd' hleft)
    change (interior (quarterTurn.toHomeomorph '' D)).Nonempty at h
    rw [← quarterTurn.toHomeomorph.image_interior] at h
    exact h.of_image
  · exact interior_nonempty_of_nonvertical hγcont hγclosed hγinj hγtrace ht hcd hfst hleft

private theorem continuousOn_horizontal_partial {U : Set (ℝ × ℝ)} {P : ℝ × ℝ → ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U) :
    ContinuousOn (fun p => deriv (fun x => P (x,p.2)) p.1) U := by
  apply ((hP.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
    (continuousOn_const (c := ((1,0) : ℝ × ℝ)))).congr
  intro p hp
  rcases p with ⟨x,y⟩
  have hd := (hP.differentiableOn one_ne_zero (x,y) hp).differentiableAt (hU.mem_nhds hp)
  exact (hd.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontal x y)).deriv

@[expose] public section

/-- **Green's theorem.** Let $U \subseteq \mathbb{R}^2$ be open, let $D \subseteq U$ be bounded and
measurable, and let $L, M : \mathbb{R}^2 \to \mathbb{R}$ be continuously differentiable on $U$.
Let $a<b$ and let $\gamma=(\gamma_1,\gamma_2) : \mathbb{R} \to \mathbb{R}^2$ be continuous on
$[a,b]$, with $\gamma(a)=\gamma(b)$, injective on $[a,b)$, with $\gamma(t)\ne\gamma(a)$ for
$a<t<b$, with image $\gamma([a,b])$ equal to the boundary of $D$, and with $\gamma(t)\in U$ for
all $t\in[a,b]$. Suppose there is a finite set $S\subseteq[a,b]$ containing $a$ and $b$ such that
$\gamma$ is continuously differentiable on $[a,b]\setminus S$ and on $[u,v]$ for any two
consecutive points $u<v$ of $S$, and such that for every $t\in(a,b)\setminus S$ we have
$\gamma'(t)\ne0$ and, for some $\delta>0$, $\gamma(t)+\varepsilon(-\gamma_2'(t),\gamma_1'(t))\in D$
for all $0<\varepsilon<\delta$ (so $D$ lies to the left of the curve). Then
$$
\int_a^b \bigl(L(\gamma(t))\,\gamma_1'(t)+M(\gamma(t))\,\gamma_2'(t)\bigr)\,dt
=\int_D \Bigl(\frac{\partial M}{\partial x}-\frac{\partial L}{\partial y}\Bigr)\,d(x,y).
$$

Source: https://en.wikipedia.org/wiki/Green%27s_theorem (greens-theorem-s1). -/
theorem greens_theorem
    (U D : Set (ℝ × ℝ))
    (a b : ℝ)
    (γ : ℝ → ℝ × ℝ)
    (L M : ℝ × ℝ → ℝ)
    (hU : IsOpen U)
    (hDU : D ⊆ U)
    (hD_bdd : Bornology.IsBounded D)
    (hD_meas : MeasurableSet D)
    (hL : ContDiffOn ℝ 1 L U)
    (hM : ContDiffOn ℝ 1 M U)
    (hab : a < b)
    (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγclosed : γ a = γ b)
    (hγinj : Set.InjOn γ (Set.Ico a b))
    (hγsimple : ∀ t ∈ Set.Ioo a b, γ t ≠ γ a)
    (hγtrace : γ '' Set.Icc a b = frontier D)
    (hγU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγpw : ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ ↑S ⊆ Set.Icc a b ∧
      ContDiffOn ℝ 1 γ (Set.Icc a b \ ↑S) ∧
      (∀ u v : ℝ, u ∈ S → v ∈ S → u < v → Set.Ioo u v ∩ ↑S = ∅ →
        ContDiffOn ℝ 1 γ (Set.Icc u v)) ∧
      ∀ t ∈ Set.Ioo a b \ ↑S, deriv γ t ≠ 0 ∧
        ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
          γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (∫ t in a..b,
      (L (γ t) * deriv (fun t => (γ t).1) t +
        M (γ t) * deriv (fun t => (γ t).2) t)) =
    ∫ p in D,
      (deriv (fun x => M (x, p.2)) p.1 -
        deriv (fun y => L (p.1, y)) p.2) ∂volume := by
  classical
  obtain ⟨S, ha, hb, hS, hγcd, hpieces, hnormal⟩ := hγpw
  let V := Ioo a b \ (↑S : Set ℝ)
  let w := fun t => exteriorWeight D (γ t)
  have hV : IsOpen V := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have hVγ : ContDiffOn ℝ 1 γ V := hγcd.mono fun _ ht => ⟨Ioo_subset_Icc_self ht.1, ht.2⟩
  have hclU : closure D ⊆ U := by
    rw [closure_eq_self_union_frontier, ← hγtrace, union_subset_iff]
    exact ⟨hDU, by rintro _ ⟨t, ht, rfl⟩; exact hγU t ht⟩
  have hleft (t : ℝ) (ht : t ∈ V) := (hnormal t ht).2
  have hγat (t : ℝ) (ht : t ∈ V) := (hVγ t ht).contDiffAt (hV.mem_nhds ht)
  have hloc (t : ℝ) (ht : t ∈ V) : ∀ᶠ s in 𝓝 t, w s = w t :=
    eventually_exterior_weight_eq hγcont hγclosed hγinj hγtrace ht.1 (hγat t ht)
      (hnormal t ht).1 (hleft t ht)
  have hver {P : ℝ × ℝ → ℝ} (hp : ContDiffOn ℝ 1 P U) :=
    weighted_vertical_green hab hU hclU hD_bdd hD_meas hp hγcont hγclosed hγinj hγtrace
      ha hb hS hVγ hpieces hleft
  have hhor {P : ℝ × ℝ → ℝ} (hp : ContDiffOn ℝ 1 P U) :=
    weighted_horizontal_green hab hU hclU hD_bdd hD_meas hp hγcont hγclosed hγinj hγtrace
      ha hb hS hVγ hpieces hleft
  have hTest (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) :=
    weighted_gradient_integral_eq_zero hab ha hb hS hγcont (hVγ.differentiableOn one_ne_zero)
      hpieces (fun _ h => hver h.contDiffOn) (fun _ h => hhor h.contDiffOn) hφ
  have hwconst := weight_constant_off_subdivision hab hγcont hγclosed hγinj hγsimple
    ha hb hS hloc (fun t ht => (hγat t ht).differentiableAt one_ne_zero) hTest
  have hnon : V.Nonempty := by
    by_contra h
    have hsub : Ioo a b ⊆ (↑S : Set ℝ) := fun t ht => by
      by_contra hs
      exact h ⟨t, ⟨ht, hs⟩⟩
    exact (Set.Ioo_infinite hab) (S.finite_toSet.subset hsub)
  obtain ⟨t₀, ht₀⟩ := hnon
  have hpos : 0 < (volume : Measure (ℝ × ℝ)) D := by
    have hne := interior_nonempty_of_regular hγcont hγclosed hγinj hγtrace ht₀.1 (hγat t₀ ht₀)
      (hnormal t₀ ht₀).1 (hleft t₀ ht₀)
    exact (isOpen_interior.measure_pos (volume : Measure (ℝ × ℝ)) hne).trans_le
      (measure_mono interior_subset)
  have hfinite : (volume : Measure (ℝ × ℝ)) D < ⊤ :=
    (measure_mono subset_closure).trans_lt hD_bdd.isCompact_closure.measure_lt_top
  have hae : ∀ᵐ t ∂volume.restrict (uIoc a b), t ∈ V := by
    rw [uIoc_of_le hab.le, ← restrict_Ioo_eq_restrict_Ioc]
    have hs : ∀ᵐ x : ℝ, x ∉ (↑S : Set ℝ) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using S.finite_toSet.measure_zero (volume : Measure ℝ)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo,
      ae_restrict_of_ae hs] with t ht hts
    exact ⟨ht, hts⟩
  have hw₀ : w t₀ ≠ 0 := by
    intro hz
    have harea := hhor (P := Prod.fst) contDiff_fst.contDiffOn
    have hgrad (p : ℝ × ℝ) : deriv (fun x => (x,p.2).1) p.1 = 1 := (hasDerivAt_id p.1).deriv
    have heq : (fun t => w t * (γ t).1 * deriv (fun s => (γ s).2) t) =ᵐ[volume.restrict (uIoc a b)]
        fun _ => 0 := by
      filter_upwards [hae] with t ht
      have hx := (hwconst t ht t₀ ht₀).trans hz
      simp only [hx, zero_mul]
    have hneg : (∫ p in D, (1 : ℝ)) = 0 := by
      simp only [hgrad] at harea
      exact harea.trans ((intervalIntegral.integral_congr_ae_restrict heq).trans
        intervalIntegral.integral_zero)
    have hp : 0 < (∫ p in D, (1 : ℝ)) := by
      simpa [Measure.real, hD_meas] using ENNReal.toReal_pos hpos.ne' hfinite.ne
    exact hp.ne' hneg
  have hwOne : w t₀ = 1 := by
    by_cases h : γ t₀ ∈ closure (interior Dᶜ)
    · simp only [w, exteriorWeight, ite_eq_left h]
    · exfalso
      exact hw₀ (by simp only [w, exteriorWeight, ite_eq_right h])
  have hwae : ∀ᵐ t ∂volume.restrict (uIoc a b), w t = 1 := by
    filter_upwards [hae] with t ht
    exact (hwconst t ht t₀ ht₀).trans hwOne
  have hLline : (fun t => w t * L (γ t) * deriv (fun s => (γ s).1) t) =ᵐ[volume.restrict (uIoc a b)]
      fun t => L (γ t) * deriv (fun s => (γ s).1) t := by
    filter_upwards [hwae] with t ht using by rw [ht, one_mul]
  have hMline : (fun t => w t * M (γ t) * deriv (fun s => (γ s).2) t) =ᵐ[volume.restrict (uIoc a b)]
      fun t => M (γ t) * deriv (fun s => (γ s).2) t := by
    filter_upwards [hwae] with t ht using by rw [ht, one_mul]
  have hLV := (hver hL).trans (congrArg Neg.neg
    (intervalIntegral.integral_congr_ae_restrict hLline))
  have hMH := (hhor hM).trans (intervalIntegral.integral_congr_ae_restrict hMline)
  have hLi := (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) hab.le).mpr
    (integrableOn_mul_deriv_of_piecewise ha hb hS (hL.continuousOn.comp hγcont hγU)
      (fun u v hu hv huv hgap => (hpieces u v hu hv huv hgap).fst))
  have hMi := (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) hab.le).mpr
    (integrableOn_mul_deriv_of_piecewise ha hb hS (hM.continuousOn.comp hγcont hγU)
      (fun u v hu hv huv hgap => (hpieces u v hu hv huv hgap).snd))
  have hLarea := (((continuousOn_vertical_partial hU hL).mono hclU).integrableOn_compact
    (μ := volume) hD_bdd.isCompact_closure).mono_set subset_closure
  have hMarea := (((continuousOn_horizontal_partial hU hM).mono hclU).integrableOn_compact
    (μ := volume) hD_bdd.isCompact_closure).mono_set subset_closure
  change IntervalIntegrable (fun t => L (γ t) * deriv (fun s => (γ s).1) t) volume a b at hLi
  change IntervalIntegrable (fun t => M (γ t) * deriv (fun s => (γ s).2) t) volume a b at hMi
  rw [intervalIntegral.integral_add hLi hMi, integral_sub hMarea hLarea, hMH, hLV]
  ring

end

end MetaMathlibExt
