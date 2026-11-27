/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import MathlibExt.MeasureTheory.OptimalTransport.WassersteinConvergence

/-!
# The Kantorovich–Rubinstein formula

For probability measures with finite first moments on a Polish metric space, the order-one
Wasserstein distance is the supremum of integral differences over real-valued 1-Lipschitz functions.

We use compact Kantorovich duality on finite subsets and pass to the limit using nearest-point
approximations from a countable dense sequence.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
  (DualFeasible IsCoupling kantorovich_duality_compact primalValues)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.MeasureTheory.WassersteinWanted

section

variable {X : Type*} [MetricSpace X]

/-- The nearest of the base point and the first `n` terms of a sequence, with ties resolved
recursively. -/
private noncomputable def nearestPoint (x₀ : X) (u : ℕ → X) : ℕ → X → X
  | 0 => fun _ => x₀
  | n + 1 => fun x =>
    if dist x (u n) ≤ dist x (nearestPoint x₀ u n x) then u n else nearestPoint x₀ u n x

private theorem finite_range_nearestPoint (x₀ : X) (u : ℕ → X) (n : ℕ) :
    (range (nearestPoint x₀ u n)).Finite := by
  induction n with
  | zero => exact finite_range_const
  | succ n ih =>
    refine (ih.insert (u n)).subset ?_
    rintro _ ⟨x, rfl⟩
    change (if _ then _ else _) ∈ _
    split
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_range_self x)

private theorem dist_nearestPoint_succ (x₀ : X) (u : ℕ → X) (n : ℕ) (x : X) :
    dist x (nearestPoint x₀ u (n + 1) x) =
      min (dist x (u n)) (dist x (nearestPoint x₀ u n x)) := by
  simp only [nearestPoint]
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

private theorem antitone_dist_nearestPoint (x₀ : X) (u : ℕ → X) (x : X) :
    Antitone fun n => dist x (nearestPoint x₀ u n x) :=
  antitone_nat_of_succ_le fun n => by rw [dist_nearestPoint_succ]; exact min_le_right _ _

variable [MeasurableSpace X] [BorelSpace X]

private theorem integrable_lipschitz {ρ : ProbabilityMeasure X} {x₀ : X}
    (hρ : ∫⁻ x, edist x₀ x ∂(ρ : Measure X) < ∞) {f : X → ℝ} (hf : LipschitzWith 1 f) :
    Integrable f (ρ : Measure X) := by
  have hd : Integrable (dist x₀) (ρ : Measure X) := by
    refine ⟨(continuous_const.dist continuous_id).aestronglyMeasurable, ?_⟩
    simpa only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs, abs_of_nonneg dist_nonneg,
      ← edist_dist] using hρ
  refine ((integrable_const ‖f x₀‖).add hd).mono' hf.continuous.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => calc
    ‖f x‖ ≤ ‖f x₀‖ + ‖f x - f x₀‖ := norm_le_insert' _ _
    _ ≤ ‖f x₀‖ + dist x₀ x := by
      gcongr
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm, dist_comm x x₀] using hf.dist_le_mul x x₀

variable [SecondCountableTopology X]

private theorem measurable_nearestPoint (x₀ : X) (u : ℕ → X) (n : ℕ) :
    Measurable (nearestPoint x₀ u n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_const.ite (measurableSet_le (measurable_id.dist measurable_const)
      (measurable_id.dist ih)) ih

private theorem tendsto_lintegral_nearestPoint {ρ : ProbabilityMeasure X} (x₀ : X)
    (hρ : ∫⁻ x, edist x₀ x ∂(ρ : Measure X) < ∞) {u : ℕ → X} (hu : DenseRange u) :
    Tendsto (fun n => ∫⁻ x, edist x (nearestPoint x₀ u n x) ∂(ρ : Measure X)) atTop (𝓝 0) := by
  rw [← lintegral_zero]
  refine tendsto_lintegral_of_dominated_convergence (edist x₀)
    (fun n => measurable_id.edist (measurable_nearestPoint x₀ u n)) (fun n => ?_) hρ.ne ?_
  · refine ae_of_all _ fun x => ?_
    have h := antitone_dist_nearestPoint x₀ u x (Nat.zero_le n)
    simpa only [edist_dist, nearestPoint, dist_comm x₀] using ENNReal.ofReal_le_ofReal h
  · refine ae_of_all _ fun x => ?_
    simp only [edist_dist]
    have h : Tendsto (fun n => dist x (nearestPoint x₀ u n x)) atTop (𝓝 0) := by
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun _ => ha.trans_le dist_nonneg,
        fun b hb => ?_⟩
      obtain ⟨n, hn⟩ := hu.exists_dist_lt x hb
      filter_upwards [eventually_ge_atTop (n + 1)] with m hm
      refine (antitone_dist_nearestPoint x₀ u x hm).trans_lt ?_
      change dist x (nearestPoint x₀ u (n + 1) x) < b
      rw [dist_nearestPoint_succ]
      exact (min_le_left _ _).trans_lt hn
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h

private theorem wasserstein_map_le (ρ : ProbabilityMeasure X) {T : X → X} (hT : Measurable T) :
    wasserstein 1 ρ (ρ.map T) ≤ ∫⁻ x, edist x (T x) ∂(ρ : Measure X) := by
  let j : X → X × X := fun x => (x, T x)
  have hj : Measurable j := measurable_id.prodMk hT
  have hjc : IsCoupling ρ (ρ.map T) (ρ.map j) := by
    constructor
    · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hj]
      exact Measure.map_id.symm
    · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        Measure.map_map measurable_snd hj]
      rfl
  simpa only [ProbabilityMeasure.toMeasure_map, div_one, ENNReal.rpow_one,
    lintegral_map measurable_edist hj] using
    wasserstein_le_of_isCoupling (by norm_num : (0 : ℝ) ≤ 1) hjc

private theorem integrable_of_compact {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : Y → ℝ} (hf : Continuous f)
    (ρ : ProbabilityMeasure Y) : Integrable f (ρ : Measure Y) := by
  rw [← integrableOn_univ]
  exact hf.continuousOn.integrableOn_compact isCompact_univ

/-- Compact duality on a finite subset gives an upper bound using Lipschitz tests on the
ambient space. -/
private theorem wasserstein_map_subtype_le {s : Set X} [Finite s] [Nonempty s]
    (μ ν : ProbabilityMeasure s) {B : ℝ≥0∞}
    (hB : ∀ f : X → ℝ, LipschitzWith 1 f →
      ENNReal.ofReal (∫ x : s, f x ∂(μ : Measure s) - ∫ x : s, f x ∂(ν : Measure s)) ≤ B) :
    wasserstein 1 (μ.map Subtype.val) (ν.map Subtype.val) ≤ B := by
  by_cases htop : B = ⊤
  · exact htop ▸ le_top
  let c : s × s → ℝ := fun z => dist z.1 z.2
  have hc : Continuous c := continuous_fst.dist continuous_snd
  have hc0 (z : s × s) : 0 ≤ c z := dist_nonneg
  have hcost (π : ProbabilityMeasure (s × s)) (hπ : IsCoupling μ ν π) :
      wasserstein 1 (μ.map Subtype.val) (ν.map Subtype.val) ≤
        ENNReal.ofReal (∫ z, c z ∂(π : Measure (s × s))) := by
    let j : s × s → X × X := Prod.map Subtype.val Subtype.val
    have hj : Measurable j := measurable_subtype_coe.prodMap measurable_subtype_coe
    obtain ⟨h₁, h₂⟩ := hπ
    have hπ' : IsCoupling (μ.map Subtype.val) (ν.map Subtype.val) (π.map j) := by
      constructor
      · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h₁,
          Measure.map_map measurable_subtype_coe measurable_fst, Measure.map_map measurable_fst hj]
        rfl
      · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h₂,
          Measure.map_map measurable_subtype_coe measurable_snd, Measure.map_map measurable_snd hj]
        rfl
    have h := wasserstein_le_of_isCoupling (by norm_num : (0 : ℝ) ≤ 1) hπ'
    simp only [div_one, ENNReal.rpow_one, ProbabilityMeasure.toMeasure_map,
      lintegral_map measurable_edist hj] at h
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_of_compact hc π) (ae_of_all _ hc0)]
    simpa only [c, j, Prod.map_fst, Prod.map_snd, Subtype.dist_eq, edist_dist] using h
  have hW : wasserstein 1 (μ.map Subtype.val) (ν.map Subtype.val) ≠ ⊤ :=
    ((hcost (μ.prod ν) (isCoupling_prod μ ν)).trans_lt ENNReal.ofReal_lt_top).ne
  rw [← ENNReal.ofReal_toReal hW, ← ENNReal.ofReal_toReal htop]
  apply ENNReal.ofReal_le_ofReal
  calc
    (wasserstein 1 (μ.map Subtype.val) (ν.map Subtype.val)).toReal
      ≤ sInf (primalValues μ ν c) := by
        refine le_csInf ⟨_, μ.prod ν, isCoupling_prod μ ν, rfl⟩ ?_
        rintro _ ⟨π, hπ, rfl⟩
        exact (ENNReal.le_ofReal_iff_toReal_le hW (integral_nonneg hc0)).1 (hcost π hπ)
    _ = sSup {r : ℝ | ∃ a b : s → ℝ, DualFeasible c a b ∧
        r = (∫ x, a x ∂(μ : Measure s)) + ∫ y, b y ∂(ν : Measure s)} :=
      kantorovich_duality_compact μ ν c hc
    _ ≤ B.toReal := by
      apply csSup_le
      · refine ⟨0, fun _ => 0, fun _ => 0, ⟨continuous_const, continuous_const, ?_⟩, by simp⟩
        intro x y
        simpa only [add_zero] using hc0 (x, y)
      · rintro _ ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩
        -- The metric cost transform replaces both feasible potentials by one Lipschitz function.
        let f (x : X) : ℝ := ⨅ y : s, dist x y - b y
        have hbdd (x : X) : BddBelow (range fun y : s => dist x y - b y) :=
          Finite.bddBelow_range _
        have hf : LipschitzWith 1 f := by
          refine LipschitzWith.of_le_add fun x x' => ?_
          rw [← sub_le_iff_le_add]
          refine le_ciInf fun y => ?_
          have h := (ciInf_le (hbdd x) y).trans (sub_le_sub_right (dist_triangle x x' y) (b y))
          linarith only [h]
        have ha_le (x : s) : a x ≤ f x := by
          refine le_ciInf fun y => le_sub_iff_add_le.mpr ?_
          exact hab x y
        have hb_le (y : s) : b y ≤ -f y := by
          have h := ciInf_le (hbdd y) y
          change f y ≤ dist (y : X) y - b y at h
          rw [dist_self, zero_sub] at h
          linarith only [h]
        have hf' : Continuous (fun x : s => f x) := hf.continuous.comp continuous_subtype_val
        have hμ := integral_mono (integrable_of_compact ha μ) (integrable_of_compact hf' μ) ha_le
        have hν :=
          integral_mono (integrable_of_compact hb ν) (integrable_of_compact hf' ν).neg hb_le
        simp only [Pi.neg_apply, integral_neg] at hν
        exact (show _ ≤ _ by linarith only [hμ, hν]).trans
          ((ENNReal.ofReal_le_iff_le_toReal htop).mp (hB f hf))

private theorem ofReal_le_eNorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖ₑ := by
  rw [Real.eNorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- Replacing both measures by their pushforwards under a common finite-range map costs at
most twice the sum of the two mean displacements, including the error in the test integrals. -/
private theorem wasserstein_le_of_finite_range [CompleteSpace X] (μ ν : ProbabilityMeasure X)
    {x₀ : X} (hμ : ∫⁻ x, edist x₀ x ∂(μ : Measure X) < ∞)
    (hν : ∫⁻ x, edist x₀ x ∂(ν : Measure X) < ∞)
    {T : X → X} (hT : Measurable T) (hfin : (range T).Finite) {B : ℝ≥0∞}
    (hB : ∀ f : X → ℝ, LipschitzWith 1 f →
      ENNReal.ofReal (∫ x, f x ∂(μ : Measure X) - ∫ x, f x ∂(ν : Measure X)) ≤ B) :
    wasserstein 1 μ ν ≤ B + 2 * ((∫⁻ x, edist x (T x) ∂(μ : Measure X)) +
      ∫⁻ x, edist x (T x) ∂(ν : Measure X)) := by
  let A (ρ : ProbabilityMeasure X) := ∫⁻ x, edist x (T x) ∂(ρ : Measure X)
  let s := range T
  let q (x : X) : s := ⟨T x, mem_range_self x⟩
  have : Finite s := hfin.to_subtype
  have : Nonempty s := ⟨q x₀⟩
  have hq : Measurable q := hT.subtype_mk
  have hmap (ρ : ProbabilityMeasure X) : (ρ.map q).map Subtype.val = ρ.map T := by
    apply Subtype.ext
    change ((ρ.map q).map Subtype.val : Measure X) = (ρ.map T : Measure X)
    simp only [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_subtype_coe hq]
    rfl
  have hleft : wasserstein 1 μ (μ.map T) ≤ A μ := wasserstein_map_le μ hT
  have hright : wasserstein 1 (ν.map T) ν ≤ A ν := by
    rw [wasserstein_comm]
    exact wasserstein_map_le ν hT
  have hmiddle : wasserstein 1 (μ.map T) (ν.map T) ≤ A μ + B + A ν := by
    rw [← hmap μ, ← hmap ν]
    apply wasserstein_map_subtype_le
    intro f hf
    have hf' : Continuous (fun x : s => f x) := hf.continuous.comp continuous_subtype_val
    have hInt (ρ : ProbabilityMeasure X) :
        ∫ x, f x ∂(ρ.map T : Measure X) = ∫ x : s, f x ∂(ρ.map q : Measure s) := by
      rw [← hmap ρ, ProbabilityMeasure.toMeasure_map,
        integral_map measurable_subtype_coe.aemeasurable hf.continuous.aestronglyMeasurable]
    have hi (ρ : ProbabilityMeasure X) : Integrable f (ρ.map T : Measure X) := by
      rw [← hmap ρ, ProbabilityMeasure.toMeasure_map]
      exact (integrable_map_measure hf.continuous.aestronglyMeasurable
        measurable_subtype_coe.aemeasurable).2 (integrable_of_compact hf' _)
    rw [← hInt μ, ← hInt ν]
    have hμf := enorm_integral_sub_le_mul_wasserstein_one hf (hi μ) (integrable_lipschitz hμ hf)
    have hνf := enorm_integral_sub_le_mul_wasserstein_one hf (integrable_lipschitz hν hf) (hi ν)
    simp only [ENNReal.coe_one, one_mul] at hμf hνf
    rw [wasserstein_comm 1 (μ.map T) μ] at hμf
    rw [wasserstein_comm 1 ν (ν.map T)] at hνf
    let intμ' := ∫ x, f x ∂(μ.map T : Measure X)
    let intμ := ∫ x, f x ∂(μ : Measure X)
    let intν := ∫ x, f x ∂(ν : Measure X)
    let intν' := ∫ x, f x ∂(ν.map T : Measure X)
    change ENNReal.ofReal (intμ' - intν') ≤ A μ + B + A ν
    rw [show intμ' - intν' = (intμ' - intμ) + (intμ - intν) + (intν - intν') by ring]
    calc
      ENNReal.ofReal ((intμ' - intμ) + (intμ - intν) + (intν - intν')) ≤
          ENNReal.ofReal (intμ' - intμ) + ENNReal.ofReal (intμ - intν) +
            ENNReal.ofReal (intν - intν') :=
        ENNReal.ofReal_add_le.trans (add_le_add_left ENNReal.ofReal_add_le _)
      _ ≤ A μ + B + A ν := by
        gcongr
        · exact (ofReal_le_eNorm _).trans (hμf.trans hleft)
        · exact hB f hf
        · exact (ofReal_le_eNorm _).trans (hνf.trans hright)
  calc
    wasserstein 1 μ ν ≤ wasserstein 1 μ (μ.map T) + wasserstein 1 (μ.map T) ν :=
      wasserstein_triangle le_rfl μ (μ.map T) ν
    _ ≤ wasserstein 1 μ (μ.map T) + (wasserstein 1 (μ.map T) (ν.map T) +
        wasserstein 1 (ν.map T) ν) := by
      gcongr
      exact wasserstein_triangle le_rfl (μ.map T) (ν.map T) ν
    _ ≤ A μ + (A μ + B + A ν + A ν) := by gcongr
    _ = B + 2 * (A μ + A ν) := by rw [two_mul]; ac_rfl

end

/-- **Kantorovich–Rubinstein formula.** On a Polish metric space `X`, for probability measures
`μ, ν` with finite first moments, `W_1(μ, ν) = sup (∫ ψ dμ - ∫ ψ dν)` over all `1`-Lipschitz
functions `ψ : X → ℝ` (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Remark 6.5, formula (6.3), a consequence of Theorem 5.10(i) and Particular Case 5.4). The
supremum is nonnegative (take `ψ = 0`), so it is stated through `ENNReal.ofReal`. -/
public theorem wasserstein_one_eq_iSup_lipschitz {X : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ ν : ProbabilityMeasure X) (x₀ : X)
    (hμ : ∫⁻ x, edist x₀ x ∂(μ : Measure X) < ∞) (hν : ∫⁻ x, edist x₀ x ∂(ν : Measure X) < ∞) :
    wasserstein 1 μ ν = ⨆ (ψ : X → ℝ) (_ : LipschitzWith 1 ψ),
      ENNReal.ofReal (∫ x, ψ x ∂(μ : Measure X) - ∫ x, ψ x ∂(ν : Measure X)) := by
  apply le_antisymm
  · let : Nonempty X := ⟨x₀⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
    let B := ⨆ (ψ : X → ℝ) (_ : LipschitzWith 1 ψ),
      ENNReal.ofReal (∫ x, ψ x ∂(μ : Measure X) - ∫ x, ψ x ∂(ν : Measure X))
    have hB (ψ : X → ℝ) (hψ : LipschitzWith 1 ψ) :
        ENNReal.ofReal (∫ x, ψ x ∂(μ : Measure X) - ∫ x, ψ x ∂(ν : Measure X)) ≤ B :=
      le_iSup₂ (f := fun f _ =>
        ENNReal.ofReal (∫ x, f x ∂(μ : Measure X) - ∫ x, f x ∂(ν : Measure X))) ψ hψ
    have hμ0 := tendsto_lintegral_nearestPoint x₀ hμ hu
    have hν0 := tendsto_lintegral_nearestPoint x₀ hν hu
    have hlim := tendsto_const_nhds (x := B) |>.add
      (ENNReal.Tendsto.const_mul (hμ0.add hν0) (Or.inr ENNReal.ofNat_ne_top) (a := 2))
    simp only [add_zero, mul_zero] at hlim
    exact ge_of_tendsto hlim <| Eventually.of_forall fun n =>
      wasserstein_le_of_finite_range μ ν hμ hν (measurable_nearestPoint x₀ u n)
        (finite_range_nearestPoint x₀ u n) hB
  · refine iSup₂_le fun ψ hψ => ?_
    rw [← one_mul (wasserstein 1 μ ν)]
    exact (ofReal_le_eNorm _).trans (enorm_integral_sub_le_mul_wasserstein_one hψ
      (integrable_lipschitz hμ hψ) (integrable_lipschitz hν hψ))

end MathlibExt.MeasureTheory.WassersteinWanted
