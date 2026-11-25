/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import MathlibExt.MeasureTheory.OptimalTransport.Existence
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Support

/-!
# Brenier's theorem

The theorem `brenier` proves that the unique optimal coupling for the quadratic cost
is induced by the gradient of a convex potential.

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 9.4
(Monge problem for quadratic cost), for an absolutely continuous source measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.MeasureTheory.OptimalTransport.Existence

namespace MathlibExt.MeasureTheory.BrenierWanted

private abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable def quadraticCost {n : ℕ}
    (π : ProbabilityMeasure (Space n × Space n)) : ℝ≥0∞ :=
  ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π : Measure (Space n × Space n))

private theorem exists_finite_optimizer {n : ℕ} (μ ν : ProbabilityMeasure (Space n))
    (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure (Space n)) < ∞)
    (hν : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(ν : Measure (Space n)) < ∞) :
    ∃ π : ProbabilityMeasure (Space n × Space n), IsCoupling μ ν π ∧
      quadraticCost π = transportCost 2 μ ν ∧ transportCost 2 μ ν < ⊤ := by
  obtain ⟨π, hπ, hmin⟩ := exists_isCoupling_lintegral_eq_transportCost 2 μ ν
  refine ⟨π, hπ, hmin, ?_⟩
  have hW := wasserstein_lt_top (p := 2) (by norm_num) (0 : Space n) (μ := μ) (ν := ν)
    (by simpa [eNorm_eq_nnNorm] using hμ) (by simpa [eNorm_eq_nnNorm] using hν)
  by_contra! ht
  simp [wasserstein, top_unique ht, ENNReal.top_rpow_of_pos] at hW

private theorem eq_graph_of_ae {n : ℕ} {μ ν : ProbabilityMeasure (Space n)}
    {π : ProbabilityMeasure (Space n × Space n)} (hπ : IsCoupling μ ν π)
    {T : Space n → Space n} (hT : Measurable T)
    (hae : ∀ᵐ z ∂(π : Measure (Space n × Space n)), z.2 = T z.1) :
    (π : Measure (Space n × Space n)) = (μ : Measure (Space n)).map (fun x => (x, T x)) := by
  have hm : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [hπ.1, Measure.map_map hm measurable_fst]
  conv_lhs => rw [← Measure.map_id (μ := (π : Measure (Space n × Space n)))]
  exact Measure.map_congr (hae.mono fun z hz => Prod.ext rfl hz)

private noncomputable def avgLaw {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype I] (q : Measure A) (g : I → A → B) : Measure B :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, q.map (g i)

private theorem avgLaw_integral {A B I : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype I] (q : Measure A) (g : I → A → B) (hg : ∀ i, Measurable (g i))
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(avgLaw q g) = (Fintype.card I : ℝ≥0∞)⁻¹ *
      ∫⁻ x, ∑ i, f (g i x) ∂q := by
  rw [avgLaw, lintegral_smul_measure, lintegral_finsetSum_measure,
    lintegral_finsetSum _ (f := fun i x => f (g i x)) (fun i _ => hf.comp (hg i))]
  congr 1
  exact Finset.sum_congr rfl fun i _ => lintegral_map hf (hg i)

private theorem avgLaw_eval {B I : Type*} [MeasurableSpace B] [Fintype I] [Nonempty I]
    (π : Measure B) [IsProbabilityMeasure π] :
    avgLaw (Measure.pi (fun _ : I => π)) (fun i u => u i) = π := by
  classical
  have hπ (i : I) := (measurePreserving_eval (fun _ : I => π) i).map_eq
  change (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i : I, (Measure.pi _).map (Function.eval i) = π
  simp_rw [hπ]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp), one_smul]

private theorem pi_mem_support {B I : Type*} [MetricSpace B] [MeasurableSpace B]
    [Fintype I] (π : Measure B) [IsProbabilityMeasure π] {u : I → B}
    (hu : ∀ i, u i ∈ π.support) : u ∈ (Measure.pi (fun _ : I => π)).support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport]
  intro r hr
  rw [Measure.pi_ball (fun _ : I => π) u hr]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
    (Metric.nhds_basis_ball.mem_measureSupport.mp (hu i) r hr).ne')

private theorem optimal_cycles {n : ℕ} {μ ν : ProbabilityMeasure (Space n)}
    {π : ProbabilityMeasure (Space n × Space n)} (hπ : IsCoupling μ ν π)
    (hmin : quadraticCost π = transportCost 2 μ ν) (hfin : transportCost 2 μ ν < ⊤)
    {I : Type} [Fintype I] [Nonempty I] (σ : Equiv.Perm I)
    (u : I → Space n × Space n) (hu : ∀ i, u i ∈ (π : Measure _).support) :
    ∑ i, edist (u i).1 (u i).2 ^ (2 : ℝ) ≤ ∑ i, edist (u (σ i)).1 (u i).2 ^ (2 : ℝ) := by
  classical
  let q := Measure.pi fun _ : I => (π : Measure (Space n × Space n))
  let c (z : Space n × Space n) := edist z.1 z.2 ^ (2 : ℝ)
  have hc : Continuous c := (ENNReal.continuous_rpow_const).comp
    (continuous_fst.edist continuous_snd)
  let orig (v : I → Space n × Space n) := ∑ i, c (v i)
  let alt (v : I → Space n × Space n) := ∑ i, c ((v (σ i)).1, (v i).2)
  have ho : Continuous orig := by unfold orig; fun_prop
  have ha : Continuous alt := by unfold alt; fun_prop
  -- Draw a tuple of independent pairs from the coupling. Permute its first coordinates
  -- whenever the permutation lowers the total cost, then sample one of the pairs uniformly.
  let g (i : I) (v : I → Space n × Space n) :=
    if alt v ≤ orig v then ((v (σ i)).1, (v i).2) else v i
  have hg (i : I) : Measurable (g i) := by
    exact Measurable.ite (measurableSet_le ha.measurable ho.measurable)
      (((measurable_pi_apply (σ i)).fst).prodMk (measurable_pi_apply i).snd) (measurable_pi_apply i)
  let m := avgLaw q g
  have evalLaw : avgLaw q (fun (i : I) v => v i) = π := avgLaw_eval _
  -- The empirical marginals of each tuple survive the permutation.
  have marg (k : (Space n × Space n) → Space n) (hk : Measurable k)
      (hk' : ∀ (f : Space n → ℝ≥0∞) v, ∑ i, f (k (g i v)) = ∑ i, f (k (v i))) :
      m.map k = (π : Measure _).map k := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_map hf hk, lintegral_map hf hk]
    change (∫⁻ z, (f ∘ k) z ∂(avgLaw q g)) = ∫⁻ z, (f ∘ k) z ∂(π : Measure _)
    rw [← evalLaw, avgLaw_integral _ _ hg (hf.comp hk),
      avgLaw_integral _ _ (fun i => measurable_pi_apply i) (hf.comp hk)]
    exact congrArg _ (lintegral_congr (hk' f))
  have hm1 : m.map Prod.fst = μ := by
    rw [hπ.1]
    apply marg _ measurable_fst
    intro f v
    by_cases h : alt v ≤ orig v
    · simpa only [g, h, ↓reduceIte] using Equiv.sum_comp σ (fun i => f (v i).1)
    · simp only [g, h, ↓reduceIte]
  have hm2 : m.map Prod.snd = ν := by
    rw [hπ.2]
    apply marg _ measurable_snd
    intro f v
    by_cases h : alt v ≤ orig v <;> simp only [g, h, ↓reduceIte]
  have hmP : IsProbabilityMeasure m := ⟨by
    have h := congrArg (fun ρ : Measure (Space n) => ρ univ) hm1
    simpa [Measure.map_apply measurable_fst] using h⟩
  have hmin' := transportCost_le_of_isCoupling (p := 2) (π := ⟨m, hmP⟩) (μ := μ) (ν := ν)
    (show IsCoupling μ ν ⟨m, hmP⟩ from ⟨hm1.symm, hm2.symm⟩)
  let w := (Fintype.card I : ℝ≥0∞)⁻¹
  have hW : w ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  have hW' : w ≠ ⊤ := ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)
  have hbase : (∫⁻ z, c z ∂(π : Measure _)) = w * ∫⁻ v, orig v ∂q := by
    rw [← evalLaw, avgLaw_integral _ _ (fun i => measurable_pi_apply i) hc.measurable]
  have hnew : (∫⁻ z, c z ∂m) = w * ∫⁻ v, min (alt v) (orig v) ∂q := by
    dsimp only [m]
    rw [avgLaw_integral _ _ hg hc.measurable]
    congr 1
    apply lintegral_congr
    intro v
    by_cases h : alt v ≤ orig v
    · simp only [g, h, ↓reduceIte, min_eq_left h, alt]
    · simp only [g, h, ↓reduceIte, min_eq_right (le_of_not_ge h), orig]
  change transportCost 2 μ ν ≤ ∫⁻ z, c z ∂m at hmin'
  change (∫⁻ z, c z ∂(π : Measure _)) = transportCost 2 μ ν at hmin
  rw [← hmin, hbase, hnew, ENNReal.mul_le_mul_iff_right hW hW'] at hmin'
  have hOFin : (∫⁻ v, orig v ∂q) ≠ ⊤ := by
    intro h
    rw [← hmin, hbase, h, ENNReal.mul_top hW] at hfin
    exact lt_irrefl _ hfin
  -- Optimality forces the improvement to vanish almost surely. Continuity extends the
  -- cycle inequality to every tuple of support points.
  have hle : (fun v => min (alt v) (orig v)) ≤ᵐ[q] orig :=
    Eventually.of_forall fun _ => min_le_right _ _
  have he := ae_eq_of_ae_le_of_lintegral_le hle
    (ne_top_of_le_ne_top hOFin (lintegral_mono_ae hle)) ho.measurable.aemeasurable hmin'
  have hset : {v | orig v ≤ alt v} ∈ ae q := he.mono fun v hv => (min_eq_right_iff.mp hv)
  exact Measure.support_subset_of_isClosed (isClosed_le ho ha) hset (pi_mem_support _ hu)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def pathValue {k : ℕ} (u : Fin (k + 1) → E × E) (x : E) : ℝ :=
  ∑ i : Fin k, ⟪(u i.succ).1 - (u i.castSucc).1, (u i.castSucc).2⟫ +
    ⟪x - (u (Fin.last k)).1, (u (Fin.last k)).2⟫

private theorem pathValue_snoc {k : ℕ} (u : Fin (k + 1) → E × E) (z : E × E) (x : E) :
    pathValue (k := k + 1) (Fin.snoc u z) x = pathValue u z.1 + ⟪x - z.1, z.2⟫ := by
  simp only [pathValue, Fin.sum_univ_castSucc (n := k), ← Fin.castSucc_succ, Fin.snoc_castSucc,
    Fin.succ_last, Fin.snoc_last]

private theorem pathValue_affine {k : ℕ} (u : Fin (k + 1) → E × E) (x y : E)
    (a b : ℝ) (hab : a + b = 1) :
    pathValue u (a • x + b • y) = a * pathValue u x + b * pathValue u y := by
  obtain rfl : b = 1 - a := by linarith
  simp only [pathValue, inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

private theorem pathValue_closed {k : ℕ} (u : Fin (k + 1) → E × E)
    (hc : ∑ i, edist (u i).1 (u i).2 ^ (2 : ℝ) ≤
      ∑ i, edist (u (finRotate (k + 1) i)).1 (u i).2 ^ (2 : ℝ)) :
    pathValue u (u 0).1 ≤ 0 := by
  let σ := finRotate (k + 1)
  have hsq : ∑ i, dist (u i).1 (u i).2 ^ 2 ≤ ∑ i, dist (u (σ i)).1 (u i).2 ^ 2 := by
    simp only [ENNReal.rpow_two] at hc
    have hr := ENNReal.toReal_mono (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ =>
      ENNReal.pow_lt_top (edist_lt_top ..))) hc
    have convertSum (x y : Fin (k + 1) → E) :
        (∑ i, edist (x i) (y i) ^ 2).toReal = ∑ i, dist (x i) (y i) ^ 2 := by
      rw [ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top (edist_ne_top (x i) (y i)))]
      simp only [ENNReal.toReal_pow, ← dist_edist]
    exact (convertSum (fun i => (u i).1) (fun i => (u i).2)) ▸
      (convertSum (fun i => (u (σ i)).1) (fun i => (u i).2)) ▸ hr
  simp only [dist_eq_norm, norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Equiv.sum_comp σ (fun i => ‖(u i).1‖ ^ 2)] at hsq
  have hroute : (∑ i, ⟪(u (σ i)).1 - (u i).1, (u i).2⟫) ≤ 0 := by
    simp only [inner_sub_left, Finset.sum_sub_distrib]
    linarith
  rw [Fin.sum_univ_castSucc] at hroute
  have hstep (i : Fin k) : σ i.castSucc = i.succ := finRotate_of_lt i.isLt
  simpa only [pathValue, hstep, σ, finRotate_last] using hroute

private theorem potential_of_cycles (S : Set (E × E)) (hS : S.Nonempty)
    (hcyc : ∀ (k : ℕ) (u : Fin (k + 1) → E × E), (∀ i, u i ∈ S) →
      pathValue u (u 0).1 ≤ 0) :
    ∃ (D : Set E) (ψ : E → ℝ), ConvexOn ℝ D ψ ∧
      ∀ z ∈ S, z.1 ∈ D ∧ ∀ x ∈ D, ψ z.1 + ⟪x - z.1, z.2⟫ ≤ ψ x := by
  classical
  obtain ⟨base, hbase⟩ := hS
  -- Each path from the base point gives an affine lower bound for the potential.
  -- Extending a path through a support pair adds its proposed supporting plane.
  let V (x : E) := {v : ℝ | ∃ (k : ℕ) (u : Fin (k + 1) → E × E),
    (∀ i, u i ∈ S) ∧ u 0 = base ∧ v = pathValue u x}
  have hne (x : E) : (V x).Nonempty :=
    ⟨_, 0, fun _ => base, fun _ => hbase, rfl, rfl⟩
  have hext {x : E} {r : ℝ} (z : E × E) (hz : z ∈ S) (hr : r ∈ V z.1) :
      r + ⟪x - z.1, z.2⟫ ∈ V x := by
    obtain ⟨k, u, hu, hb, rfl⟩ := hr
    refine ⟨k + 1, Fin.snoc u z, ?_, ?_, (pathValue_snoc ..).symm⟩
    · exact Fin.lastCases (by simpa using hz) (fun i => by simpa using hu i)
    · simpa using hb
  have hzero {r : ℝ} (hr : r ∈ V base.1) : r ≤ 0 := by
    obtain ⟨k, u, hu, hb, rfl⟩ := hr
    simpa [hb] using hcyc k u hu
  -- Closing a path at the base bounds its value by zero. Thus the supremum is finite
  -- at the first coordinate of every support pair.
  let D := {x | BddAbove (V x)}
  let ψ (x : E) := sSup (V x)
  have hsup {x : E} (hx : x ∈ D) {r : ℝ} (hr : r ∈ V x) : r ≤ ψ x := le_csSup hx hr
  have hmix {x y : E} (hx : x ∈ D) (hy : y ∈ D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a + b = 1) : a * ψ x + b * ψ y ∈ upperBounds (V (a • x + b • y)) := by
    rintro r ⟨k, u, hu, hbase', rfl⟩
    rw [pathValue_affine u x y a b hab]
    have hx' := hsup hx (r := pathValue u x) ⟨k, u, hu, hbase', rfl⟩
    have hy' := hsup hy (r := pathValue u y) ⟨k, u, hu, hbase', rfl⟩
    gcongr
  refine ⟨D, ψ, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact ⟨_, hmix hx hy ha hb hab⟩
  · intro x hx y hy a b ha hb hab
    exact csSup_le (hne _) (hmix hx hy ha hb hab)
  · intro z hz
    constructor
    · refine ⟨-⟪base.1 - z.1, z.2⟫, ?_⟩
      intro r hr
      linarith [hzero (hext z hz hr)]
    · intro x hx
      apply (le_sub_iff_add_le).mp
      apply csSup_le (hne _)
      intro r hr
      exact (le_sub_iff_add_le).mpr (hsup hx (hext z hz hr))

private theorem ae_diff_on_open {n : ℕ} {U : Set (Space n)} {ψ : Space n → ℝ}
    (hU : IsOpen U) (hf : ConvexOn ℝ U ψ) :
    ∀ᵐ x ∂volume, x ∈ U → DifferentiableAt ℝ ψ x := by
  let bad := {x ∈ U | ¬DifferentiableAt ℝ ψ x}
  suffices h : volume bad = 0 by
    exact ae_iff.mpr (measure_mono_null (fun x hx => by simpa [bad] using hx) h)
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨K, t, ht, hLip⟩ := hf.locallyLipschitzOn hU hx.1
  rw [hU.nhdsWithin_eq hx.1] at ht
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  let b := Metric.ball x r
  have hR := (hLip.mono hrt).ae_differentiableWithinAt_of_mem_of_real (μ := volume)
  have hb := inter_mem_nhdsWithin bad (Metric.ball_mem_nhds x hr)
  refine ⟨b ∩ bad, by simpa only [inter_comm] using hb, ?_⟩
  apply measure_mono_null _ (ae_iff.mp hR)
  intro y hy h
  exact hy.2.2 ((h hy.1).differentiableAt (Metric.isOpen_ball.mem_nhds hy.1))

private theorem gradient_of_supporting_plane {n : ℕ} {ψ : Space n → ℝ} {D : Set (Space n)}
    {x y : Space n} (hx : x ∈ interior D) (hf : DifferentiableAt ℝ ψ x)
    (hsub : ∀ z ∈ D, ψ x + ⟪z - x, y⟫ ≤ ψ z) : y = gradient ψ x := by
  let L := InnerProductSpace.toDual ℝ (Space n) y
  have hmin : IsLocalMin (fun z => ψ z - L z) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    have h := hsub z hz
    rw [inner_sub_left, real_inner_comm y z, real_inner_comm y x] at h
    change ψ x - ⟪y, x⟫ ≤ ψ z - ⟪y, z⟫
    linarith
  have hL := sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hf.hasFDerivAt.sub L.hasFDerivAt))
  exact (InnerProductSpace.toDual ℝ (Space n)).injective (by simpa [toDual_gradient] using hL.symm)

private theorem graph_of_potential {n : ℕ} {μ ν : ProbabilityMeasure (Space n)}
    {π : ProbabilityMeasure (Space n × Space n)} (hπ : IsCoupling μ ν π)
    (hac : (μ : Measure (Space n)) ≪ volume)
    {D : Set (Space n)} {ψ : Space n → ℝ} (hψ : ConvexOn ℝ D ψ)
    (hs : ∀ z ∈ (π : Measure (Space n × Space n)).support, z.1 ∈ D ∧
      ∀ x ∈ D, ψ z.1 + ⟪x - z.1, z.2⟫ ≤ ψ x) :
    ∃ (T : Space n → Space n) (U : Set (Space n)), Measurable T ∧
      (∀ᵐ z ∂(π : Measure (Space n × Space n)), z.2 = T z.1) ∧ IsOpen U ∧ Convex ℝ U ∧
      (μ : Measure (Space n)) Uᶜ = 0 ∧ ConvexOn ℝ U ψ ∧
      ∀ᵐ x ∂(μ : Measure (Space n)), HasGradientAt ψ (T x) x := by
  let U := interior D
  have hU : IsOpen U := isOpen_interior
  have hψU := hψ.subset interior_subset hψ.1.interior
  have push {P : Space n → Prop} (h : ∀ᵐ x ∂(μ : Measure (Space n)), P x) :
      ∀ᵐ z ∂(π : Measure (Space n × Space n)), P z.1 := by
    rw [hπ.1] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hbound : ∀ᵐ x ∂(μ : Measure (Space n)), x ∉ frontier D :=
    ae_iff.mpr (by simpa using hac (hψ.1.addHaar_frontier volume))
  have hsπ : ∀ᵐ z ∂(π : Measure (Space n × Space n)), z ∈ (π : Measure _).support :=
    Measure.support_mem_ae
  have huπ : ∀ᵐ z ∂(π : Measure (Space n × Space n)), z.1 ∈ U := by
    filter_upwards [hsπ, push hbound] with z hz hz'
    by_contra h
    exact hz' ⟨subset_closure (hs z hz).1, h⟩
  have huμ : ∀ᵐ x ∂(μ : Measure (Space n)), x ∈ U := by
    rw [hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable hU.measurableSet).mpr huπ
  have hdiff : ∀ᵐ x ∂(μ : Measure (Space n)), DifferentiableAt ℝ ψ x := by
    filter_upwards [hac.ae_le (ae_diff_on_open hU hψU), huμ] with x hd hx using hd hx
  refine ⟨gradient ψ, U, ?_, ?_, hU, hψ.1.interior, ae_iff.mp huμ, hψU,
    hdiff.mono (fun x hx => hx.hasGradientAt)⟩
  · exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ ψ)
  · filter_upwards [hsπ, huπ, push hdiff] with z hz hu hd
    exact gradient_of_supporting_plane hu hd (hs z hz).2

private theorem optimal_graph {n : ℕ} {μ ν : ProbabilityMeasure (Space n)}
    {π : ProbabilityMeasure (Space n × Space n)} (hπ : IsCoupling μ ν π)
    (hmin : quadraticCost π = transportCost 2 μ ν) (hfin : transportCost 2 μ ν < ⊤)
    (hac : (μ : Measure (Space n)) ≪ volume) :
    ∃ (T : Space n → Space n) (U : Set (Space n)) (ψ : Space n → ℝ), Measurable T ∧
      (∀ᵐ z ∂(π : Measure (Space n × Space n)), z.2 = T z.1) ∧ IsOpen U ∧ Convex ℝ U ∧
      (μ : Measure (Space n)) Uᶜ = 0 ∧ ConvexOn ℝ U ψ ∧
      ∀ᵐ x ∂(μ : Measure (Space n)), HasGradientAt ψ (T x) x := by
  let S := (π : Measure (Space n × Space n)).support
  have hs : S.Nonempty := (show ∀ᵐ z ∂(π : Measure _), z ∈ S from Measure.support_mem_ae).exists
  obtain ⟨D, ψ, hψ, hsub⟩ := potential_of_cycles S hs (fun k u hu =>
    pathValue_closed u (optimal_cycles hπ hmin hfin (finRotate (k + 1)) u hu))
  obtain ⟨T, U, hT⟩ := graph_of_potential hπ hac hψ hsub
  exact ⟨T, U, ψ, hT⟩

private theorem optimal_unique {n : ℕ} {μ ν : ProbabilityMeasure (Space n)}
    {π ρ : ProbabilityMeasure (Space n × Space n)} (hπ : IsCoupling μ ν π)
    (hρ : IsCoupling μ ν ρ) (hminπ : quadraticCost π = transportCost 2 μ ν)
    (hminρ : quadraticCost ρ = transportCost 2 μ ν) (hfin : transportCost 2 μ ν < ⊤)
    (hac : (μ : Measure (Space n)) ≪ volume) : π = ρ := by
  -- The average is optimal, so both couplings concentrate on the same graph.
  let m := (2 : ℝ≥0∞)⁻¹ • ((π : Measure (Space n × Space n)) + (ρ : Measure _))
  have hmP : IsProbabilityMeasure m := ⟨by
    simp [m, ENNReal.inv_two_add_inv_two]⟩
  let avg : ProbabilityMeasure (Space n × Space n) := ⟨m, hmP⟩
  have marg {k : Space n × Space n → Space n} (hk : Measurable k)
      {η : Measure (Space n)} (hp : η = (π : Measure _).map k)
      (hr : η = (ρ : Measure _).map k) : η = m.map k := by
    dsimp only [m]
    rw [Measure.map_smul _ hk.aemeasurable, Measure.map_add _ _ hk, ← hp, ← hr,
      smul_add, ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
  have hm : IsCoupling μ ν avg :=
    ⟨marg measurable_fst hπ.1 hρ.1, marg measurable_snd hπ.2 hρ.2⟩
  have hmin : quadraticCost avg = transportCost 2 μ ν := by
    change (∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂m) = _
    dsimp only [m]
    rw [lintegral_smul_measure, lintegral_add_measure]
    change (2 : ℝ≥0∞)⁻¹ * (quadraticCost π + quadraticCost ρ) = _
    rw [hminπ, hminρ, mul_add, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  obtain ⟨T, _, _, hT, hgraph, _⟩ := optimal_graph hm hmin hfin hac
  change ∀ᵐ z : Space n × Space n ∂(2 : ℝ≥0∞)⁻¹ • ((π : Measure _) + (ρ : Measure _)),
    z.2 = T z.1 at hgraph
  rw [Measure.ae_ennreal_smul_measure_iff (by norm_num), ae_add_measure_iff] at hgraph
  exact Subtype.ext ((eq_graph_of_ae hπ hT hgraph.1).trans (eq_graph_of_ae hρ hT hgraph.2).symm)

/-- **Brenier's theorem** (absolutely continuous source). Let `μ, ν` be probability measures on
`ℝⁿ` with finite second moments, `μ` absolutely continuous with respect to Lebesgue measure.
For the quadratic cost `|x - y|²` there is a measurable map `T` such that the coupling
`π_T = (id, T)_# μ` of `μ` and `ν` is optimal, every optimal coupling equals `π_T`, and `T` is
`μ`-almost everywhere the gradient of a convex function `ψ`: there is an open convex set `U` of
full `μ`-measure on which `ψ` is convex, with `∇ψ(x) = T x` for `μ`-almost every `x`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 9.4, in the absolutely
continuous case named in its statement; there the optimal coupling is characterized by
`y ∈ ∂ψ(x)` for a lower semicontinuous convex `ψ : ℝⁿ → ℝ ∪ {+∞}`. For `μ` absolutely
continuous, `μ`-almost every `x` lies in the interior `U` of the domain of `ψ`, where `ψ` is
finite, convex and differentiable almost everywhere with `∂ψ(x) = {∇ψ(x)}`). -/
theorem brenier {n : ℕ} (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ2 : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) < ∞)
    (hν2 : ∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) < ∞)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Measurable T ∧
      ∃ πT : ProbabilityMeasure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        (πT : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
          (μ : Measure (EuclideanSpace ℝ (Fin n))).map (fun x => (x, T x)) ∧
        IsCoupling μ ν πT ∧
        ∫⁻ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), edist z.1 z.2 ^ (2 : ℝ)
          ∂(πT : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
            transportCost 2 μ ν ∧
        (∀ π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
          IsCoupling μ ν π →
          ∫⁻ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), edist z.1 z.2 ^ (2 : ℝ)
            ∂(π : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =
              transportCost 2 μ ν → π = πT) ∧
        ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
          IsOpen U ∧ Convex ℝ U ∧ (μ : Measure (EuclideanSpace ℝ (Fin n))) Uᶜ = 0 ∧
          ConvexOn ℝ U ψ ∧
            ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), HasGradientAt ψ (T x) x := by
  obtain ⟨π, hπ, hmin, hfin⟩ := exists_finite_optimizer μ ν hμ2 hν2
  obtain ⟨T, U, ψ, hT, hgraph, hU, hconv, hfull, hψ, hgrad⟩ := optimal_graph hπ hmin hfin hac
  exact ⟨T, hT, π, eq_graph_of_ae hπ hT hgraph, hπ, hmin,
    fun ρ hρ hopt => optimal_unique hρ hπ hopt hmin hfin hac, U, ψ, hU, hconv, hfull, hψ, hgrad⟩

end MathlibExt.MeasureTheory.BrenierWanted
