/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Existence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Kantorovich duality for lower semicontinuous costs

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.10(i).
The compact, continuous-cost case is proved in
`MathlibExt.MeasureTheory.OptimalTransport.Kantorovich`.
A complete separable metric space with its Borel σ-algebra stands for Villani's Polish space.

The theorem `kantorovich_duality_lsc` follows by embedding each space into the Hilbert cube.
Continuous costs on the product of the cubes approximate the original cost from below.
Compact duality gives couplings of the image measures for each approximant, and compactness
gives a single coupling satisfying all the integral bounds.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (isCoupling_prod)
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
open MathlibExt.MeasureTheory.OptimalTransport.Existence

namespace MathlibExt.MeasureTheory.KantorovichDualityWanted

/-- Increasing continuous costs on the ambient space recover a lower semicontinuous cost
on an embedded subspace, including where the cost is infinite. -/
private lemma exists_cost_approx {S K : Type*} [TopologicalSpace S] [Nonempty S]
    [MetricSpace K] {e : S → K} (he : IsEmbedding e) {c : S → ℝ≥0∞}
    (hc : LowerSemicontinuous c) :
    ∃ f : ℕ → K → ℝ, (∀ n, Continuous (f n)) ∧ (∀ n z, 0 ≤ f n z) ∧
      Monotone f ∧ ∀ p, (⨆ n, ENNReal.ofReal (f n (e p))) = c p := by
  let a (n : ℕ) (p : S) := min (n : ℝ≥0∞) (c p)
  have afin (n : ℕ) (p : S) : a n p ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_left ..)
  -- The distance penalty gives an n-Lipschitz minorant on the image.
  let g (n : ℕ) (z : K) (p : S) := (a n p).toReal + n * dist z (e p)
  let f (n : ℕ) (z : K) := ⨅ p, g n z p
  have gpos (n z p) : 0 ≤ g n z p :=
    add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg _) dist_nonneg)
  have gbdd (n z) : BddBelow (range (g n z)) :=
    ⟨0, forall_mem_range.mpr (gpos n z)⟩
  refine ⟨f, ?_, fun n z => le_ciInf (gpos n z), ?_, ?_⟩
  · intro n
    refine (LipschitzWith.of_le_add_mul (n : ℝ≥0) fun x y => ?_).continuous
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun p => ?_
    have h := ciInf_le (gbdd n x) p
    have hd := mul_le_mul_of_nonneg_left (dist_triangle x y (e p)) (show (0 : ℝ) ≤ n by positivity)
    change f n x ≤ (a n p).toReal + n * dist x (e p) at h
    change f n x - (n : ℝ) * dist x y ≤ (a n p).toReal + n * dist y (e p)
    linarith
  · intro m n h z
    refine le_ciInf fun p => (ciInf_le (gbdd m z) p).trans ?_
    exact add_le_add (ENNReal.toReal_mono (afin n p) (min_le_min_right _ (Nat.cast_le.mpr h)))
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) dist_nonneg)
  · intro p
    apply le_antisymm
    · refine iSup_le fun n => ?_
      have h : f n (e p) ≤ (a n p).toReal := by simpa [g, f] using ciInf_le (gbdd n (e p)) p
      exact (ENNReal.ofReal_le_ofReal h).trans
        ((ENNReal.ofReal_toReal (afin n p)).le.trans (min_le_right ..))
    · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
      have hnh := hc p (r : ℝ≥0∞) hr
      rw [Filter.Eventually, he.nhds_eq_comap, Filter.mem_comap] at hnh
      obtain ⟨U, hU, hcost⟩ := hnh
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
      obtain ⟨n, hn⟩ := exists_nat_ge (max (r : ℝ) (r / δ))
      have hrn : (r : ℝ) ≤ n := (le_max_left ..).trans hn
      have hrδ : (r : ℝ) ≤ n * δ := (div_le_iff₀ hδ).mp ((le_max_right ..).trans hn)
      refine le_iSup_of_le n ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      refine le_ciInf fun q => ?_
      -- Near p the cost exceeds r. Outside the ball the distance penalty alone reaches r.
      by_cases hq : dist (e p) (e q) < δ
      · have hrc : (r : ℝ≥0∞) ≤ c q :=
          (hcost (hball (Metric.mem_ball.mpr (by rwa [dist_comm])))).le
        have hra : (r : ℝ≥0∞) ≤ a n q := le_min (by exact_mod_cast hrn) hrc
        exact (ENNReal.toReal_mono (afin n q) hra).trans
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) dist_nonneg))
      · exact (hrδ.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hq) (Nat.cast_nonneg _))).trans
          (le_add_of_nonneg_left ENNReal.toReal_nonneg)

private lemma weak_duality {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞)
    (π : ProbabilityMeasure (X × Y)) (hπ : IsCoupling μ ν π)
    (ψ : X →ᵇ ℝ) (φ : Y →ᵇ ℝ) (h : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ c (x, y)) :
    ENNReal.ofReal (∫ y, φ y ∂(ν : Measure Y) - ∫ x, ψ x ∂(μ : Measure X)) ≤
      ∫⁻ z, c z ∂(π : Measure (X × Y)) := by
  have hiφ : Integrable (fun z : X × Y => φ z.2) (π : Measure (X × Y)) :=
    (integrable_map_measure φ.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp
      (hπ.2 ▸ φ.integrable (ν : Measure Y))
  have hiψ : Integrable (fun z : X × Y => ψ z.1) (π : Measure (X × Y)) :=
    (integrable_map_measure ψ.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (hπ.1 ▸ ψ.integrable (μ : Measure X))
  rw [hπ.1, hπ.2, integral_map measurable_fst.aemeasurable ψ.continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable φ.continuous.aestronglyMeasurable,
    ← integral_sub hiφ hiψ, integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (f := fun z : X × Y => φ z.2 - ψ z.1) (hiφ.sub hiψ)]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans
    (ENNReal.ofReal_toReal_le.trans (lintegral_mono fun z => h z.1 z.2))

/-- Pull a coupling of the image measures back to the original spaces. -/
private lemma lift_coupling {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [MeasurableSpace B] {u : X → A} {v : Y → B}
    (hu : MeasurableEmbedding u) (hv : MeasurableEmbedding v)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (ρ : ProbabilityMeasure (A × B))
    (hρ : IsCoupling (μ.map u) (ν.map v) ρ) :
    ∃ π : ProbabilityMeasure (X × Y), IsCoupling μ ν π ∧
      (π : Measure (X × Y)).map (Prod.map u v) = (ρ : Measure (A × B)) := by
  have := μ.nonempty
  have := ν.nonempty
  let w := Prod.map hu.invFun hv.invFun
  have hw : Measurable w := hu.measurable_invFun.prodMap hv.measurable_invFun
  have hμ : (μ : Measure X).map u = (ρ : Measure (A × B)).map Prod.fst := hρ.1
  have hν : (ν : Measure Y).map v = (ρ : Measure (A × B)).map Prod.snd := hρ.2
  refine ⟨ρ.map w, ⟨?_, ?_⟩, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hw]
    change _ = (ρ : Measure (A × B)).map (hu.invFun ∘ Prod.fst)
    rw [← Measure.map_map hu.measurable_invFun measurable_fst, ← hμ,
      Measure.map_map hu.measurable_invFun hu.measurable, hu.leftInverse_invFun.comp_eq_id,
      Measure.map_id]
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd hw]
    change _ = (ρ : Measure (A × B)).map (hv.invFun ∘ Prod.snd)
    rw [← Measure.map_map hv.measurable_invFun measurable_snd, ← hν,
      Measure.map_map hv.measurable_invFun hv.measurable, hv.leftInverse_invFun.comp_eq_id,
      Measure.map_id]
  · have hx : ∀ᵐ z ∂(ρ : Measure (A × B)), z.1 ∈ range u := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [← hμ, ae_map_iff (p := fun x => x ∈ range u) hu.measurable.aemeasurable
        hu.measurableSet_range]
      exact ae_of_all _ fun x => ⟨x, rfl⟩
    have hy : ∀ᵐ z ∂(ρ : Measure (A × B)), z.2 ∈ range v := by
      apply ae_of_ae_map measurable_snd.aemeasurable
      rw [← hν, ae_map_iff (p := fun x => x ∈ range v) hv.measurable.aemeasurable
        hv.measurableSet_range]
      exact ae_of_all _ fun x => ⟨x, rfl⟩
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (hu.measurable.prodMap hv.measurable) hw]
    refine (Measure.map_congr (g := id) ?_).trans Measure.map_id
    filter_upwards [hx, hy] with z hx hy
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    change (u (hu.invFun z.1), v (hv.invFun z.2)) = z
    rw [← hx, ← hy, hu.leftInverse_invFun x, hv.leftInverse_invFun y, hx, hy]

/-- Use compact duality at a strict upper bound for the dual objective. -/
private lemma exists_compact_sublevel {A B : Type*} [MetricSpace A] [MetricSpace B]
    [CompactSpace A] [CompactSpace B] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace B] [BorelSpace B] (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure B)
    {f : A × B → ℝ} (hf : Continuous f) (hpos : ∀ z, 0 ≤ f z) {b t : ℝ} (ht : b < t)
    (hdual : ∀ (g : A → ℝ) (h : B → ℝ), DualFeasible f g h →
      (∫ x, g x ∂(μ : Measure A)) + ∫ y, h y ∂(ν : Measure B) ≤ b) :
    ∃ π : ProbabilityMeasure (A × B), IsCoupling μ ν π ∧
      ∫ z, f z ∂(π : Measure (A × B)) ≤ t := by
  have := μ.nonempty
  have := ν.nonempty
  have hP : (primalValues μ ν f).Nonempty :=
    ⟨_, μ.prod ν, isCoupling_prod μ ν, rfl⟩
  have hD : sInf (primalValues μ ν f) ≤ b := by
    rw [kantorovich_duality_compact μ ν f hf]
    apply csSup_le
    · refine ⟨_, (fun _ => 0), (fun _ => 0), ⟨continuous_const, continuous_const, ?_⟩, rfl⟩
      exact fun x y => by simpa using hpos (x, y)
    · rintro _ ⟨g, h, hh, rfl⟩
      exact hdual g h hh
  by_contra! hn
  have : t ≤ sInf (primalValues μ ν f) := by
    apply le_csInf hP
    rintro _ ⟨π, hπ, rfl⟩
    exact (hn π hπ).le
  exact ht.not_ge (this.trans hD)

/-- A common bound for the increasing costs is attained on one coupling by compactness. -/
private lemma common_sublevel {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ ν : ProbabilityMeasure K) (f : ℕ → K × K → ℝ)
    (hf : ∀ n, Continuous (f n)) (hm : Monotone f) (t : ℝ)
    (hne : ∀ n, ∃ π : ProbabilityMeasure (K × K), IsCoupling μ ν π ∧
      ∫ z, f n z ∂(π : Measure (K × K)) ≤ t) :
    ∃ π : ProbabilityMeasure (K × K), IsCoupling μ ν π ∧
      ∀ n, ∫ z, f n z ∂(π : Measure (K × K)) ≤ t := by
  let F (n : ℕ) : (K × K) →ᵇ ℝ := .mkOfCompact ⟨f n, hf n⟩
  let S (n : ℕ) := {π : ProbabilityMeasure (K × K) | IsCoupling μ ν π ∧
    ∫ z, F n z ∂(π : Measure (K × K)) ≤ t}
  have hclosed n : IsClosed (S n) :=
    (isClosed_setOf_isCoupling μ ν).inter
      (isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (F n))
        continuous_const)
  have hdec n : S (n + 1) ⊆ S n := by
    intro π hπ
    exact ⟨hπ.1, (integral_mono ((F n).integrable _) ((F (n + 1)).integrable _)
      (hm (Nat.le_succ n))).trans hπ.2⟩
  obtain ⟨π, hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hdec hne (hclosed 0).isCompact hclosed
  exact ⟨π, (mem_iInter.mp hπ 0).1, fun n => (mem_iInter.mp hπ n).2⟩

/-- Transport a bound for the original dual objective to the compact problem for every
continuous minorant, then take the monotone limit on a single coupling. -/
private lemma exists_primal_le {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) {c : X × Y → ℝ≥0∞}
    (hc : LowerSemicontinuous c) {b t : ℝ} (ht : b < t)
    (hdual : ∀ (ψ : X →ᵇ ℝ) (φ : Y →ᵇ ℝ), (∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ c (x, y)) →
      ∫ y, φ y ∂(ν : Measure Y) - ∫ x, ψ x ∂(μ : Measure X) ≤ b) :
    ∃ π : ProbabilityMeasure (X × Y), IsCoupling μ ν π ∧
      ∫⁻ z, c z ∂(π : Measure (X × Y)) ≤ ENNReal.ofReal t := by
  have := μ.nonempty
  have := ν.nonempty
  let K := ℕ → unitInterval
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨u, hu⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  obtain ⟨v, hv⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Y)
  let e : X × Y → K × K := Prod.map u v
  have he : IsEmbedding e := hu.prodMap hv
  obtain ⟨f, hf, hpos, hm, hsup⟩ := exists_cost_approx he hc
  let μ' : ProbabilityMeasure K := μ.map u
  let ν' : ProbabilityMeasure K := ν.map v
  obtain ⟨ρ, hρ, hcost⟩ := common_sublevel μ' ν' f hf hm t (by
    intro n
    apply exists_compact_sublevel μ' ν' (hf n) (hpos n) ht
    rintro g h ⟨hg, hh, hle⟩
    let G : X →ᵇ ℝ :=
      (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩).compContinuous ⟨u, hu.continuous⟩
    let H : Y →ᵇ ℝ :=
      (BoundedContinuousFunction.mkOfCompact ⟨h, hh⟩).compContinuous ⟨v, hv.continuous⟩
    have hpair := hdual (-G) H (by
      intro x y
      change ENNReal.ofReal (h (v y) - -g (u x)) ≤ c (x, y)
      rw [sub_neg_eq_add, add_comm, ← hsup (x, y)]
      exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (hle (u x) (v y))))
    change (∫ y, h (v y) ∂(ν : Measure Y)) - ∫ x, -g (u x) ∂(μ : Measure X) ≤ b at hpair
    change (∫ x, g x ∂(μ : Measure X).map u) + ∫ y, h y ∂(ν : Measure Y).map v ≤ b
    rw [integral_map hu.continuous.measurable.aemeasurable hg.aestronglyMeasurable,
      integral_map hv.continuous.measurable.aemeasurable hh.aestronglyMeasurable]
    rwa [integral_neg, sub_neg_eq_add, add_comm] at hpair)
  obtain ⟨π, hπ, hmap⟩ := lift_coupling (hu.continuous.measurableEmbedding hu.injective)
    (hv.continuous.measurableEmbedding hv.injective) μ ν ρ hρ
  refine ⟨π, hπ, ?_⟩
  calc
    ∫⁻ z, c z ∂(π : Measure (X × Y)) =
        ∫⁻ z, ⨆ n, ENNReal.ofReal (f n (e z)) ∂(π : Measure (X × Y)) := by
          exact lintegral_congr fun z => (hsup z).symm
    _ = ⨆ n, ∫⁻ z, ENNReal.ofReal (f n (e z)) ∂(π : Measure (X × Y)) :=
      lintegral_iSup
        (fun n => (ENNReal.continuous_ofReal.comp ((hf n).comp he.continuous)).measurable)
        fun i j hij z => ENNReal.ofReal_le_ofReal (hm hij (e z))
    _ ≤ ENNReal.ofReal t := by
      refine iSup_le fun n => ?_
      rw [← lintegral_map (f := fun z => ENNReal.ofReal (f n z))
        (ENNReal.continuous_ofReal.comp (hf n)).measurable he.continuous.measurable, hmap]
      let F : (K × K) →ᵇ ℝ := .mkOfCompact ⟨f n, hf n⟩
      rw [← ofReal_integral_eq_lintegral_ofReal (f := f n) (F.integrable _)
        (ae_of_all _ (hpos n))]
      exact ENNReal.ofReal_le_ofReal (hcost n)

/-- **Kantorovich duality for lower semicontinuous costs.** Let `X` and `Y` be Polish spaces
with Borel probability measures `μ` and `ν`, and let `c : X × Y → [0, ∞]` be lower
semicontinuous. Then the minimal transport cost `inf_π ∫ c dπ` over couplings `π` of `μ` and `ν`
equals the supremum of `∫ φ dν - ∫ ψ dμ` over bounded continuous `ψ` on `X` and `φ` on `Y` with
`φ(y) - ψ(x) ≤ c(x, y)` for all `x, y` (C. Villani, *Optimal Transport: Old and New*, Springer
2009, Theorem 5.10(i), first equality, in the case `a = b = 0` of the lower bound
`c ≥ a + b`). The supremum is nonnegative (take `ψ = φ = 0`), so it is stated through
`ENNReal.ofReal`. -/
theorem kantorovich_duality_lsc {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞)
    (hc : LowerSemicontinuous c) :
    ⨅ (π : ProbabilityMeasure (X × Y)) (_ : IsCoupling μ ν π), ∫⁻ z, c z ∂(π : Measure (X × Y)) =
      ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
        (_ : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ c (x, y)),
        ENNReal.ofReal (∫ y, φ y ∂(ν : Measure Y) - ∫ x, ψ x ∂(μ : Measure X)) := by
  let D := ⨆ (ψ : X →ᵇ ℝ) (φ : Y →ᵇ ℝ) (_ : ∀ x y, ENNReal.ofReal (φ y - ψ x) ≤ c (x, y)),
    ENNReal.ofReal (∫ y, φ y ∂(ν : Measure Y) - ∫ x, ψ x ∂(μ : Measure X))
  change _ = D
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hD
    obtain ⟨π, hπ, hcost⟩ := exists_primal_le μ ν hc (b := D.toReal) (t := D.toReal + ε)
      (lt_add_of_pos_right _ (by exact_mod_cast hε)) (by
        intro ψ φ h
        apply (ENNReal.ofReal_le_iff_le_toReal hD.ne).mp
        exact le_iSup_of_le ψ (le_iSup_of_le φ (le_iSup_of_le h le_rfl)))
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg, ENNReal.ofReal_toReal hD.ne,
      ENNReal.ofReal_coe_nnreal] at hcost
    exact iInf_le_of_le π (iInf_le_of_le hπ hcost)
  · refine iSup_le fun ψ => iSup_le fun φ => iSup_le fun h => le_iInf₂ fun π hπ => ?_
    exact weak_duality μ ν c π hπ ψ φ h

end MathlibExt.MeasureTheory.KantorovichDualityWanted
