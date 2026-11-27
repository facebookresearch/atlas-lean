/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon
public import MathlibExt.Combinatorics.FinitelyForcibleGraphons
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Counting lemma for graphons

The change in homomorphism density between two graphons is bounded by the number of edges times
the cut norm of their difference.
-/

public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted

open MeasureTheory Set
open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)

private noncomputable abbrev unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

private instance unitMeasureProbability : IsProbabilityMeasure unitMeasure :=
  ⟨by simp [unitMeasure, Real.volume_Icc]⟩

private def IsWeight {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ ∀ x, f x ∈ Icc 0 1

private lemma IsWeight.norm_le {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : IsWeight f) (x : α) : ‖f x‖ ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (hf.2 x).1] using (hf.2 x).2

private lemma IsWeight.comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → ℝ} (hf : IsWeight f) {g : β → α} (hg : Measurable g) :
    IsWeight (fun x => f (g x)) := ⟨hf.1.comp hg, fun x => hf.2 (g x)⟩

private lemma IsWeight.prod {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    {f : ι → α → ℝ} (hf : ∀ i ∈ s, IsWeight (f i)) :
    IsWeight (fun x => ∏ i ∈ s, f i x) := by
  refine ⟨Finset.measurable_prod _ fun i hi => (hf i hi).1, fun x => ⟨?_, ?_⟩⟩
  · exact Finset.prod_nonneg fun i hi => ((hf i hi).2 x).1
  · exact Finset.prod_le_one₀ (fun i hi => ((hf i hi).2 x).1) fun i hi => ((hf i hi).2 x).2

private lemma integrable_of_unit_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable 1 (.of_forall hb))

-- A weight in [0,1] can be replaced by the indicator of a sign set.
private lemma exists_setIntegral {a g : ℝ → ℝ} (ha : IsWeight a) (hg : Measurable g)
    (hgi : Integrable g unitMeasure) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      |∫ x, a x * g x ∂unitMeasure| ≤ |∫ x in S, g x ∂unitMeasure| := by
  have upper (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f unitMeasure) :
      (∫ x, a x * f x ∂unitMeasure) ≤ ∫ x in {x | 0 ≤ f x}, f x ∂unitMeasure := by
    have hs : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hf
    rw [← integral_indicator hs]
    refine integral_mono (hi.bdd_mul ha.1.aestronglyMeasurable (.of_forall ha.norm_le))
      (hi.indicator hs) fun x => ?_
    by_cases hx : 0 ≤ f x
    · simpa [Set.indicator, hx] using mul_le_of_le_one_left hx (ha.2 x).2
    · simpa [Set.indicator, hx] using mul_nonpos_of_nonneg_of_nonpos (ha.2 x).1 (le_of_not_ge hx)
  by_cases h : 0 ≤ ∫ x, a x * g x ∂unitMeasure
  · refine ⟨{x | 0 ≤ g x}, measurableSet_le measurable_const hg, ?_⟩
    rw [abs_of_nonneg h]
    exact (upper g hg hgi).trans (le_abs_self _)
  · refine ⟨{x | 0 ≤ -g x}, measurableSet_le measurable_const hg.neg, ?_⟩
    rw [abs_of_neg (lt_of_not_ge h)]
    have hn := upper (fun x => -g x) hg.neg hgi.neg
    simp only [mul_neg, integral_neg] at hn
    exact hn.trans (neg_le_abs _)

-- With both marginals restricted to the unit interval, any two measurable sets specify a cut.
private lemma rectangle_le_cutNorm {d : ℝ × ℝ → ℝ} (hb : ∀ z, ‖d z‖ ≤ 1)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |∫ z, d z ∂(unitMeasure.restrict S).prod (unitMeasure.restrict T)| ≤
      graphonCutNorm (fun x y => d (x, y)) := by
  let p : CutPair := ⟨(S ∩ Icc 0 1, T ∩ Icc 0 1), hS.inter measurableSet_Icc,
    hT.inter measurableSet_Icc, inter_subset_right, inter_subset_right⟩
  have cut_eq (q : CutPair) :
      (unitMeasure.restrict q.1.1).prod (unitMeasure.restrict q.1.2) =
        volume.restrict (q.1.1 ×ˢ q.1.2) := by
    rw [unitMeasure, Measure.restrict_restrict q.2.1, Measure.restrict_restrict q.2.2.1,
      inter_eq_left.mpr q.2.2.2.1, inter_eq_left.mpr q.2.2.2.2, Measure.prod_restrict]
    rfl
  have bound (q : CutPair) : |∫ z in q.1.1 ×ˢ q.1.2, d z| ≤ 1 := by
    rw [← cut_eq]
    have h := norm_integral_le_of_norm_le_const
      (μ := (unitMeasure.restrict q.1.1).prod (unitMeasure.restrict q.1.2)) (.of_forall hb)
    simp only [Real.norm_eq_abs, one_mul] at h
    apply h.trans
    rw [Measure.prod_restrict, measureReal_restrict_apply_univ]
    exact measureReal_le_one
  have hp := le_ciSup (f := fun q : CutPair => |∫ z in q.1.1 ×ˢ q.1.2, d z|)
    ⟨1, by simpa [upperBounds] using bound⟩ p
  change _ ≤ ⨆ q : CutPair, |∫ z in q.1.1 ×ˢ q.1.2, d z|
  simpa [unitMeasure, Measure.restrict_restrict hS, Measure.restrict_restrict hT,
    Measure.prod_restrict, p, Measure.volume_eq_prod] using hp

private lemma norm_mul_le_one {x y : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  simpa using mul_le_mul hx hy (norm_nonneg _) zero_le_one

-- First choose a sign set for each marginal, using Fubini between the two choices.
private lemma weighted_cut_bound {d : ℝ × ℝ → ℝ} (hd : Measurable d) (hb : ∀ z, ‖d z‖ ≤ 1)
    {a b : ℝ → ℝ} (ha : IsWeight a) (hB : IsWeight b) :
    |∫ z, a z.1 * (b z.2 * d z) ∂unitMeasure.prod unitMeasure| ≤
      graphonCutNorm (fun x y => d (x, y)) := by
  let f (z : ℝ × ℝ) := b z.2 * d z
  have hf : Measurable f := (hB.1.comp measurable_snd).mul hd
  have hfb (z : ℝ × ℝ) : ‖f z‖ ≤ 1 := norm_mul_le_one (hB.norm_le _) (hb z)
  have hfull := integrable_of_unit_bound (μ := unitMeasure.prod unitMeasure)
    ((ha.1.comp measurable_fst).mul hf) (fun z => norm_mul_le_one (ha.norm_le _) (hfb z))
  change |∫ z, a z.1 * f z ∂unitMeasure.prod unitMeasure| ≤ _
  rw [integral_prod (fun z => a z.1 * f z) hfull]
  simp_rw [integral_const_mul]
  have hfi := integrable_of_unit_bound (μ := unitMeasure.prod unitMeasure) hf hfb
  obtain ⟨S, hS, h₁⟩ := exists_setIntegral ha
    (hf.stronglyMeasurable.integral_prod_right'.measurable) hfi.integral_prod_left
  apply h₁.trans
  have hfS := integrable_of_unit_bound (μ := (unitMeasure.restrict S).prod unitMeasure) hf hfb
  rw [← integral_prod f hfS, integral_prod_symm f hfS]
  simp only [f, integral_const_mul]
  have hdS := integrable_of_unit_bound (μ := (unitMeasure.restrict S).prod unitMeasure) hd hb
  obtain ⟨T, hT, h₂⟩ := exists_setIntegral hB
    (hd.stronglyMeasurable.integral_prod_left'.measurable) hdS.integral_prod_right
  apply h₂.trans
  rw [← integral_prod_symm d (integrable_of_unit_bound hd hb)]
  exact rectangle_le_cutNorm hb hS hT

private noncomputable abbrev cubeMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ => unitMeasure

-- Resampling one coordinate independently preserves product measure.
private lemma measurePreserving_update {k : ℕ} (i : Fin k) :
    MeasurePreserving (fun p : (Fin k → ℝ) × ℝ => Function.update p.1 i p.2)
      ((cubeMeasure k).prod unitMeasure) (cubeMeasure k) := by
  refine ⟨measurable_update', (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have pre : (fun p : (Fin k → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' univ.pi s =
      univ.pi (Function.update s i univ) ×ˢ s i := by
    ext ⟨x, y⟩
    simp only [mem_preimage, mem_prod, mem_univ_pi, Function.update_apply]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      split_ifs with hj
      · exact mem_univ _
      · simpa [hj] using h j
    · rintro ⟨h, hy⟩ j
      split_ifs with hj
      · simpa [hj] using hy
      · simpa [hj] using h j
  rw [pre, Measure.prod_prod, Measure.pi_pi]
  change (∏ j, (unitMeasure ∘ Function.update s i univ) j) * _ = _
  rw [Function.comp_update]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

private def resample {k : ℕ} (u v : Fin k) (φ : Fin k → ℝ) (z : ℝ × ℝ) : Fin k → ℝ :=
  Function.update (Function.update φ u z.1) v z.2

private lemma measurePreserving_resample {k : ℕ} (u v : Fin k) :
    MeasurePreserving (fun p => resample u v p.1 p.2)
      ((cubeMeasure k).prod (unitMeasure.prod unitMeasure)) (cubeMeasure k) :=
  (measurePreserving_update v).comp (((measurePreserving_update u).prod
    (MeasurePreserving.id unitMeasure)).comp
      (measurePreserving_prodAssoc (cubeMeasure k) unitMeasure unitMeasure).symm)

private def edgeProduct {k : ℕ} (s : Finset (Fin k × Fin k))
    (K : Fin k × Fin k → ℝ × ℝ → ℝ) (φ : Fin k → ℝ) : ℝ :=
  ∏ e ∈ s, K e (φ e.1, φ e.2)

private lemma edgeProduct_weight {k : ℕ} (s : Finset (Fin k × Fin k))
    {K : Fin k × Fin k → ℝ × ℝ → ℝ} (hK : ∀ e, IsWeight (K e)) :
    IsWeight (edgeProduct s K) :=
  IsWeight.prod s fun e _ => (hK e).comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

-- Once the other vertices are fixed, every remaining edge depends on at most one endpoint.
private lemma factor_edgeProduct {k : ℕ} (u v : Fin k) (huv : u < v)
    (s : Finset (Fin k × Fin k)) (hs : ∀ e ∈ s, e.1 < e.2 ∧ e ≠ (u, v))
    {K : Fin k × Fin k → ℝ × ℝ → ℝ} (hK : ∀ e, IsWeight (K e)) (φ : Fin k → ℝ) :
    ∃ a b : ℝ → ℝ, IsWeight a ∧ IsWeight b ∧
      ∀ z, edgeProduct s K (resample u v φ z) = a z.1 * b z.2 := by
  let p (e : Fin k × Fin k) := e.1 ≠ v ∧ e.2 ≠ v
  refine ⟨fun x => edgeProduct (s.filter p) K (Function.update φ u x),
    fun y => edgeProduct (s.filter fun e => ¬p e) K (Function.update φ v y),
    (edgeProduct_weight _ hK).comp (measurable_update φ),
    (edgeProduct_weight _ hK).comp (measurable_update φ), fun z => ?_⟩
  unfold edgeProduct
  rw [← Finset.prod_filter_mul_prod_filter_not s p]
  congr 1
  · refine Finset.prod_congr rfl fun e he => ?_
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp he).2
    simp [resample, Function.update_of_ne, h₁, h₂]
  · refine Finset.prod_congr rfl fun e he => ?_
    obtain ⟨he, hp⟩ := Finset.mem_filter.mp he
    obtain ⟨hlt, hne⟩ := hs e he
    have hu : e.1 ≠ u ∧ e.2 ≠ u := by
      dsimp [p] at hp
      grind [Prod.ext_iff]
    simp [resample, Function.update_apply, hu.1, hu.2]

-- Integrate a single changed edge against all the other edge weights.
private lemma single_edge_bound {k : ℕ} (u v : Fin k) (huv : u < v)
    (s : Finset (Fin k × Fin k)) (hs : ∀ e ∈ s, e.1 < e.2 ∧ e ≠ (u, v))
    {K : Fin k × Fin k → ℝ × ℝ → ℝ} (hK : ∀ e, IsWeight (K e))
    {d : ℝ × ℝ → ℝ} (hd : Measurable d) (hb : ∀ z, ‖d z‖ ≤ 1) :
    |∫ φ, d (φ u, φ v) * edgeProduct s K φ ∂cubeMeasure k| ≤
      graphonCutNorm (fun x y => d (x, y)) := by
  let f (φ : Fin k → ℝ) := d (φ u, φ v) * edgeProduct s K φ
  have hf : Measurable f := (hd.comp ((measurable_pi_apply u).prodMk
    (measurable_pi_apply v))).mul (edgeProduct_weight s hK).1
  have hf_bound (φ : Fin k → ℝ) : ‖f φ‖ ≤ 1 :=
    norm_mul_le_one (hb _) ((edgeProduct_weight s hK).norm_le _)
  let r (p : (Fin k → ℝ) × ℝ × ℝ) := resample u v p.1 p.2
  have hr := measurePreserving_resample u v
  have hfi := integrable_of_unit_bound (μ := (cubeMeasure k).prod (unitMeasure.prod unitMeasure))
    (hf.comp hr.measurable) (fun p => hf_bound (r p))
  change |∫ φ, f φ ∂cubeMeasure k| ≤ _
  calc
    _ = |∫ p, f (r p) ∂(cubeMeasure k).prod (unitMeasure.prod unitMeasure)| := by
      conv_lhs => rw [← hr.map_eq]
      rw [integral_map hr.measurable.aemeasurable hf.aestronglyMeasurable]
    _ = _ := congrArg abs (integral_prod (fun p => f (r p)) hfi)
    _ ≤ _ := by
      suffices h : ∀ φ, ‖∫ z, f (r (φ, z)) ∂unitMeasure.prod unitMeasure‖ ≤
          graphonCutNorm (fun x y => d (x, y)) by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_of_norm_le_const (μ := cubeMeasure k) (.of_forall h)
      intro φ
      obtain ⟨a, b, ha, hB, hab⟩ := factor_edgeProduct u v huv s hs hK φ
      have heq (z : ℝ × ℝ) : f (r (φ, z)) = a z.1 * (b z.2 * d z) := by
        change d (_, _) * edgeProduct s K (resample u v φ z) = _
        rw [hab]
        simp [r, resample, huv.ne, mul_comm, mul_left_comm]
      simpa only [heq, Real.norm_eq_abs] using weighted_cut_bound hd hb ha hB

private def orientedEdges {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    Finset (Fin k × Fin k) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

private lemma card_orientedEdges {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] :
    (orientedEdges F).card = F.edgeFinset.card := by
  have mem (e : Fin k × Fin k) : e ∈ orientedEdges F ↔ e.1 < e.2 ∧ F.Adj e.1 e.2 := by
    simp [orientedEdges]
  refine Finset.card_bij (fun e _ => s(e.1, e.2))
    (fun e he => SimpleGraph.mem_edgeFinset.mpr (F.mem_edgeSet.mpr ((mem e).mp he).2)) ?_ ?_
  · intro e he f hf h
    have he' := ((mem e).mp he).1
    have hf' := ((mem f).mp hf).1
    grind [Sym2.eq_iff, Prod.ext_iff]
  · intro e
    induction e using Sym2.ind with
    | _ i j =>
      intro he
      have hij := F.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
      rcases lt_or_gt_of_ne hij.ne with h | h
      · exact ⟨(i, j), (mem _).mpr ⟨h, hij⟩, rfl⟩
      · exact ⟨(j, i), (mem _).mpr ⟨h, hij.symm⟩, Sym2.eq_swap⟩

private lemma density_eq_integral {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    (W : ℝ → ℝ → ℝ) : graphonHomDensity F W =
      ∫ φ, edgeProduct (orientedEdges F) (fun _ => Function.uncurry W) φ ∂cubeMeasure k := by
  unfold graphonHomDensity
  rw [volume_pi, Measure.restrict_pi_pi]
  congr 1
  funext φ
  simp [edgeProduct, orientedEdges, Finset.prod_filter, Fintype.prod_prod_type]

/-- **Counting lemma for graphons.** For graphons `U, W` with values in `[0, 1]` and every simple
graph `F`, `|t(F, U) - t(F, W)| ≤ |E(F)| · ‖U - W‖_□` (Lovász–Szegedy, *Limits of dense graph
sequences* (2006), Lemma 4.1; the finite-graph case is `abs_homDensity_sub_homDensity_le`). -/
theorem abs_graphonHomDensity_sub_le {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] {U W : ℝ → ℝ → ℝ} (hU : IsGraphon U) (hW : IsGraphon W) :
    |graphonHomDensity F U - graphonHomDensity F W| ≤
      F.edgeFinset.card * graphonCutNorm (fun x y => U x y - W x y) := by
  let E := orientedEdges F
  let K (S : Finset (Fin k × Fin k)) (e : Fin k × Fin k) :=
    if e ∈ S then Function.uncurry U else Function.uncurry W
  let t (S : Finset (Fin k × Fin k)) := ∫ φ, edgeProduct E (K S) φ ∂cubeMeasure k
  let d (z : ℝ × ℝ) := U z.1 z.2 - W z.1 z.2
  have hK (S) (e) : IsWeight (K S e) := by
    dsimp [K]
    split_ifs
    · exact ⟨hU.1, fun z => hU.2.2 z.1 z.2⟩
    · exact ⟨hW.1, fun z => hW.2.2 z.1 z.2⟩
  have hd : Measurable d := hU.1.sub hW.1
  have hb (z : ℝ × ℝ) : ‖d z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h₁, h₂⟩ := hU.2.2 z.1 z.2
    obtain ⟨h₃, h₄⟩ := hW.2.2 z.1 z.2
    dsimp [d]
    constructor <;> linarith
  let C := graphonCutNorm (fun x y => U x y - W x y)
  have step (S : Finset (Fin k × Fin k)) (q : Fin k × Fin k) (hq : q ∈ E) (hqS : q ∉ S) :
      |t (insert q S) - t S| ≤ C := by
    have hi (A) : Integrable (edgeProduct E (K A)) (cubeMeasure k) :=
      integrable_of_unit_bound (edgeProduct_weight E (hK A)).1 (edgeProduct_weight E (hK A)).norm_le
    have split_prod (A) (φ : Fin k → ℝ) : edgeProduct E (K A) φ =
        K A q (φ q.1, φ q.2) * edgeProduct (E.erase q) (K A) φ :=
      (E.mul_prod_erase _ hq).symm
    have same (φ) : edgeProduct (E.erase q) (K (insert q S)) φ = edgeProduct (E.erase q) (K S) φ :=
      Finset.prod_congr rfl fun e he => by simp [K, (Finset.mem_erase.mp he).1]
    have diff (φ) : edgeProduct E (K (insert q S)) φ - edgeProduct E (K S) φ =
        d (φ q.1, φ q.2) * edgeProduct (E.erase q) (K S) φ := by
      rw [split_prod, split_prod, same, sub_mul]
      simp [K, hqS]
    dsimp only [t]
    rw [← integral_sub (hi _) (hi _)]
    simp_rw [diff]
    exact single_edge_bound q.1 q.2 (Finset.mem_filter.mp hq).2.1 _ (fun e he =>
      ⟨(Finset.mem_filter.mp (Finset.mem_erase.mp he).2).2.1, (Finset.mem_erase.mp he).1⟩)
      (hK S) hd hb
  have telescope (S : Finset (Fin k × Fin k)) : S ⊆ E → |t S - t ∅| ≤ S.card * C := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert q S hq ih =>
      intro hsub
      calc
        _ ≤ |t (insert q S) - t S| + |t S - t ∅| := abs_sub_le _ _ _
        _ ≤ C + S.card * C := add_le_add (step S q (hsub (Finset.mem_insert_self ..)) hq)
          (ih (Finset.Subset.trans (Finset.subset_insert ..) hsub))
        _ = _ := by
          rw [Finset.card_insert_of_notMem hq, Nat.cast_add_one, add_mul, one_mul, add_comm]
  have htU : graphonHomDensity F U = t E := by
    rw [density_eq_integral]
    congr 1
    funext φ
    exact Finset.prod_congr rfl fun e he => by simp [K, he]
  have htW : graphonHomDensity F W = t ∅ := by simp [density_eq_integral, t, E, K]
  rw [htU, htW, ← card_orientedEdges]
  exact telescope E (Finset.Subset.refl _)

end MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
