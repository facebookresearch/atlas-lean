/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.TietzeExtension
import MathlibExt.MeasureTheory.Function.Lusin
import MathlibExt.Probability.CdfContinuityPoints
import MathlibExt.Probability.QuantileLink

/-!
# Szpilrajn's Problem 170

A plane set whose homeomorphic copies in the plane are all Lebesgue measurable is
Carathéodory measurable for every Borel measure on the plane.

The proof constructs a Borel injection carrying a finite measure with null singletons to
a measure absolutely continuous with respect to area. It uses a Borel isomorphism with the
line, followed by a distribution function and a quantile function.

Lusin's theorem gives compact sets of arbitrarily large measure on which the injection is
continuous. We choose them so that the coordinates of both the points and their images avoid
a dense sequence of cuts. On each compact set, the comparisons of the two coordinates with
those cuts can be encoded in alternating ternary digits. This makes the first coordinate
injective after an ambient change of coordinates. Two shears then give a plane homeomorphism
that agrees with the Borel injection on the compact set.

The hypothesis now gives measurability on a countable union of these compacts of full measure.
The points of positive mass form a countable set. For an arbitrary measure, the Carathéodory
inequality can be checked on test sets of finite outer measure, using a Borel hull of equal mass.
-/

open Set Function MeasureTheory Metric Filter Topology
open scoped ENNReal

noncomputable section
namespace MathlibExt.MeasureTheory.ScottishBook170Wanted

private abbrev Plane := ℝ × ℝ

-- Each cut separates the compact set by a continuous ramp, with value 1 at its center.
private def ramp (q r x : ℝ) : ℝ := min 2 (max 0 (1 + (x - q) / r))

private lemma ramp_mono (q : ℝ) {r : ℝ} (hr : 0 < r) : Monotone (ramp q r) := by
  intro x y h
  dsimp [ramp]
  gcongr

private lemma ramp_straddles {x q y r : ℝ} (hr : 0 < r) (hx : x < q) (hy : q < y) :
    ramp q r x < ramp q r y := by
  have h₁ : (x - q) / r < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hx) hr
  have h₂ : 0 < (y - q) / r := div_pos (sub_pos.mpr hy) hr
  unfold ramp
  exact lt_trans (b := 1) (min_lt_of_right_lt (max_lt (by norm_num) (by linarith)))
    (lt_min (by norm_num) (lt_max_of_lt_right (by linarith)))

-- On a compact set missing the cuts, the ramps take just the two ternary digits 0 and 2.
private lemma ramp_digit {K : Set ℝ} (hK : IsClosed K) {q : ℝ} (hq : q ∉ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ramp q r x = if x < q then 0 else 2 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl q hq
  refine ⟨r, hr, fun x hx => ?_⟩
  have hd : r ≤ |x - q| := by
    by_contra! h
    exact hball (show x ∈ ball q r by simpa [Real.dist_eq] using h) hx
  split_ifs with hl
  · rw [abs_of_neg (sub_neg.mpr hl)] at hd
    have h : (x - q) / r ≤ -1 := (div_le_iff₀ hr).2 (by linarith)
    simp [ramp, max_eq_left (show 1 + (x - q) / r ≤ 0 by linarith)]
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hl))] at hd
    have h : 1 ≤ (x - q) / r := (le_div_iff₀ hr).2 (by linarith)
    simp [ramp, min_eq_left (show 2 ≤ max 0 (1 + (x - q) / r) from
      le_max_of_le_right (by linarith))]

private def coordinateTerm (b : ℕ) (q r : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if n % 2 = b then ramp (q (n / 2)) (r (n / 2)) x * ((3 : ℝ) ^ (n + 1))⁻¹ else 0

private def coordinateCode (b : ℕ) (q r : ℕ → ℝ) (x : ℝ) := ∑' n, coordinateTerm b q r n x

private lemma coordinateTerm_bound (b : ℕ) (q r : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ‖coordinateTerm b q r n x‖ ≤ 2 * (3⁻¹ : ℝ) ^ (n + 1) := by
  simp only [coordinateTerm, ← inv_pow]
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min (by norm_num) (le_max_left ..))
      (by positivity))]
    exact mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)
  · simp

private lemma summable_bound : Summable (fun n : ℕ => 2 * (3⁻¹ : ℝ) ^ (n + 1)) :=
  ((summable_nat_add_iff 1).2
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_left _

private lemma summable_coordinateTerm (b : ℕ) (q r : ℕ → ℝ) (x : ℝ) :
    Summable (fun n => coordinateTerm b q r n x) :=
  summable_bound.of_norm_bounded (fun n => coordinateTerm_bound b q r n x)

private lemma continuous_coordinateCode (b : ℕ) (q r : ℕ → ℝ) :
    Continuous (coordinateCode b q r) := by
  apply continuous_tsum _ summable_bound (fun n x => coordinateTerm_bound b q r n x)
  intro n
  unfold coordinateTerm
  split_ifs
  · unfold ramp
    fun_prop
  · exact continuous_const

private lemma strictMono_coordinateCode (b : ℕ) (hb : b < 2) {q r : ℕ → ℝ}
    (hq : DenseRange q) (hr : ∀ n, 0 < r n) : StrictMono (coordinateCode b q r) := by
  intro x y hxy
  obtain ⟨_, ⟨n, rfl⟩, hxn, hny⟩ := hq.exists_between hxy
  apply Summable.tsum_lt_tsum (i := 2 * n + b) _ _
    (summable_coordinateTerm ..) (summable_coordinateTerm ..)
  · intro i
    dsimp only [coordinateTerm]
    split_ifs
    · gcongr
      exact ramp_mono _ (hr _) hxy.le
    · rfl
  · have h₁ : (2 * n + b) % 2 = b := by omega
    have h₂ : (2 * n + b) / 2 = n := by omega
    simp only [coordinateTerm, h₁, h₂, ite_true]
    exact mul_lt_mul_of_pos_right (ramp_straddles (hr n) hxn hny) (by positivity)

private def cutDigit (q : ℕ → ℝ) (z : Plane) (n : ℕ) : Fin 3 :=
  if (if n % 2 = 0 then z.1 else z.2) < q (n / 2) then 0 else 2

private lemma coordinateCode_add {K : Set ℝ} {q r : ℕ → ℝ}
    (hr : ∀ n x, x ∈ K → ramp (q n) (r n) x = if x < q n then 0 else 2)
    (z : Plane) (hx : z.1 ∈ K) (hy : z.2 ∈ K) :
    coordinateCode 0 q r z.1 + coordinateCode 1 q r z.2 = Real.ofDigits (cutDigit q z) := by
  unfold coordinateCode Real.ofDigits
  rw [← (summable_coordinateTerm ..).tsum_add (summable_coordinateTerm ..)]
  apply tsum_congr
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [coordinateTerm, cutDigit, Real.ofDigitsTerm, h, hr _ _ hx, hr _ _ hy] <;>
    split_ifs <;> norm_num

private lemma injOn_coordinateCode_add {K : Set ℝ} {q r : ℕ → ℝ} (hq : DenseRange q)
    (hr : ∀ n x, x ∈ K → ramp (q n) (r n) x = if x < q n then 0 else 2) :
    InjOn (fun z : Plane => coordinateCode 0 q r z.1 + coordinateCode 1 q r z.2) (K ×ˢ K) := by
  intro z hz w hw h
  dsimp only at h
  rw [coordinateCode_add hr z hz.1 hz.2, coordinateCode_add hr w hw.1 hw.2] at h
  have hd (p : Plane) (n : ℕ) : cutDigit q p n ≠ 1 := by unfold cutDigit; split_ifs <;> decide
  have he := ofDigits_zero_two_sequence_unique (hd z) (hd w) h
  have aux (x y : ℝ) (h : ∀ n, x < q n ↔ y < q n) : x = y := by
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨_, ⟨n, rfl⟩, hx, hy⟩ := hq.exists_between hlt
      exact (not_lt.mpr hy.le) ((h n).mp hx)
    · obtain ⟨_, ⟨n, rfl⟩, hy, hx⟩ := hq.exists_between hlt
      exact (not_lt.mpr hx.le) ((h n).mpr hy)
  apply Prod.ext <;> apply aux <;> intro n
  · have hh := congrFun he (2 * n)
    simp [cutDigit, Nat.mul_comm] at hh
    split_ifs at hh <;> simp_all
    grind
  · have hh := congrFun he (2 * n + 1)
    have hm : (2 * n + 1) % 2 = 1 := by omega
    have hv : (2 * n + 1) / 2 = n := by omega
    simp [cutDigit, hm, hv] at hh
    split_ifs at hh <;> simp_all
    grind

-- Extend the compressed coordinate to all of the line by giving it unbounded tails.
private lemma extend_coordinate {f : ℝ → ℝ} (hf : Continuous f) (hm : StrictMono f)
    {K : Set ℝ} (hc : IsCompact K) : ∃ e : ℝ ≃ₜ ℝ, EqOn e f K := by
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  let g (x : ℝ) := f x + min 0 (x - a) + max 0 (x - b)
  have hg : StrictMono g := by
    apply StrictMono.add_monotone (StrictMono.add_monotone hm ?_) <;>
      intro x y h <;> dsimp <;> gcongr
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hs : Surjective g := by
    apply hgc.surjective
    · apply hg.monotone.tendsto_atTop_atTop_iff.mpr
      intro y
      let x := max (max a 0) (y + b - f 0)
      refine ⟨x, ?_⟩
      have hax : a ≤ x := (le_max_left ..).trans (le_max_left ..)
      have h0x : 0 ≤ x := (le_max_right ..).trans (le_max_left ..)
      have hx : y + b - f 0 ≤ x := le_max_right ..
      dsimp only [g]
      rw [min_eq_left (sub_nonneg.mpr hax)]
      linarith [hm.monotone h0x, le_max_right 0 (x - b)]
    · apply hg.monotone.tendsto_atBot_atBot_iff.mpr
      intro y
      let x := min (min b 0) (y + a - f 0)
      refine ⟨x, ?_⟩
      have hxb : x ≤ b := (min_le_left ..).trans (min_le_left ..)
      have hx0 : x ≤ 0 := (min_le_left ..).trans (min_le_right ..)
      have hx : x ≤ y + a - f 0 := min_le_right ..
      dsimp only [g]
      rw [max_eq_left (sub_nonpos.mpr hxb)]
      linarith [hm.monotone hx0, min_le_right 0 (x - a)]
  refine ⟨(hg.orderIsoOfSurjective g hs).toHomeomorph, fun x hx => ?_⟩
  change f x + min 0 (x - a) + max 0 (x - b) = f x
  simp [min_eq_left (sub_nonneg.mpr (ha hx)), max_eq_left (sub_nonpos.mpr (hb hx))]

private def shear (f : C(ℝ, ℝ)) : Plane ≃ₜ Plane where
  toFun z := (z.1, z.2 + f z.1)
  invFun z := (z.1, z.2 - f z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

-- Put the compact product in coordinates where the first coordinate distinguishes its points.
private lemma exists_injOn_fst {K : Set ℝ} (hK : IsCompact K) {q : ℕ → ℝ} (hq : DenseRange q)
    (hqK : ∀ n, q n ∉ K) :
    ∃ e : Plane ≃ₜ Plane, InjOn (fun z => (e z).1) (K ×ˢ K) := by
  choose r hr hdr using fun n => ramp_digit hK.isClosed (hqK n)
  obtain ⟨e, he⟩ := extend_coordinate (continuous_coordinateCode 0 q r)
    (strictMono_coordinateCode 0 (by decide) hq hr) hK
  let s := Homeomorph.prodComm ℝ ℝ
  let a := (e.prodCongr (Homeomorph.refl ℝ)).trans <|
    s.trans <| (shear ⟨coordinateCode 1 q r, continuous_coordinateCode 1 q r⟩).trans s
  refine ⟨a, fun z hz w hw heq => injOn_coordinateCode_add hq hdr hz hw ?_⟩
  change e z.1 + coordinateCode 1 q r z.2 = e w.1 + coordinateCode 1 q r w.2 at heq
  rwa [he hz.1, he hw.1] at heq

-- Two shears match both coordinates once the first projections are injective.
private lemma match_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (u v : X → Plane) (hu : Continuous u) (hv : Continuous v)
    (hi : Injective fun x => (u x).1) (hj : Injective fun x => (v x).1) :
    ∃ e : Plane ≃ₜ Plane, ∀ x, e (u x) = v x := by
  obtain ⟨f, hf⟩ := ContinuousMap.exists_extension' (hu.fst.isClosedEmbedding hi)
    (⟨fun x => (v x).1 - (u x).2, hv.fst.sub hu.snd⟩ : C(X, ℝ))
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension' (hv.fst.isClosedEmbedding hj)
    (⟨fun x => (v x).2 - (u x).1, hv.snd.sub hu.fst⟩ : C(X, ℝ))
  refine ⟨(shear f).trans ((Homeomorph.prodComm ℝ ℝ).trans (shear g)), fun x => ?_⟩
  have hf' : f (u x).1 = (v x).1 - (u x).2 := congrFun hf x
  have hg' : g (v x).1 = (v x).2 - (u x).1 := congrFun hg x
  change ((u x).2 + f (u x).1, (u x).1 + g ((u x).2 + f (u x).1)) = v x
  simp [hf', hg', add_sub_cancel]

private lemma extend_on_compact {K : Set Plane} (hc : IsCompact K) {F : Plane → Plane}
    (hF : ContinuousOn F K) (hi : InjOn F K) {q : ℕ → ℝ} (hq : DenseRange q)
    (hcut : ∀ z ∈ K, ∀ n, z.1 ≠ q n ∧ z.2 ≠ q n ∧ (F z).1 ≠ q n ∧ (F z).2 ≠ q n) :
    ∃ e : Plane ≃ₜ Plane, EqOn e F K := by
  let A := K ∪ F '' K
  have hA : IsCompact A := hc.union (hc.image_of_continuousOn hF)
  let B := Prod.fst '' A ∪ Prod.snd '' A
  have hB : IsCompact B := (hA.image continuous_fst).union (hA.image continuous_snd)
  have hqB (n) : q n ∉ B := by
    rintro (⟨p, hp | ⟨z, hz, rfl⟩, h⟩ | ⟨p, hp | ⟨z, hz, rfl⟩, h⟩)
    exacts [(hcut _ hp n).1 h, (hcut _ hz n).2.2.1 h,
      (hcut _ hp n).2.1 h, (hcut _ hz n).2.2.2 h]
  obtain ⟨s, hs⟩ := exists_injOn_fst hB hq hqB
  have sub : A ⊆ B ×ˢ B := fun z hz =>
    ⟨Or.inl (mem_image_of_mem _ hz), Or.inr (mem_image_of_mem _ hz)⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let u (x : K) := s x.val
  let v (x : K) := s (F x.val)
  obtain ⟨e, he⟩ := match_compact u v (s.continuous.comp continuous_subtype_val)
    (s.continuous.comp hF.domRestrict) (fun x y h =>
      Subtype.ext (hs (sub (.inl x.property)) (sub (.inl y.property)) h))
    (fun x y h => Subtype.ext (hi x.property y.property (hs
      (sub (.inr (mem_image_of_mem _ x.property))) (sub (.inr (mem_image_of_mem _ y.property))) h)))
  refine ⟨s.trans (e.trans s.symm), fun z hz => s.injective ?_⟩
  simpa [u, v] using he ⟨z, hz⟩

private lemma dense_cuts (μ : Measure Plane) [IsFiniteMeasure μ] :
    ∃ q : ℕ → ℝ, DenseRange q ∧ ∀ᵐ z ∂μ, ∀ n, z.1 ≠ q n ∧ z.2 ≠ q n := by
  have hx := Measure.countable_meas_level_set_pos (μ := μ) (measurable_fst (β := ℝ) (α := ℝ))
  have hy := Measure.countable_meas_level_set_pos (μ := μ) (measurable_snd (β := ℝ) (α := ℝ))
  obtain ⟨D, hD, hc, hd⟩ := ((hx.union hy).dense_compl ℝ).exists_countable_dense_subset
  obtain ⟨q, rfl⟩ := hc.exists_eq_range hd.nonempty
  refine ⟨q, hd, ae_all_iff.mpr (fun n => ?_)⟩
  have hn := hD (mem_range_self n)
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_lt,
    nonpos_iff_eq_zero] at hn
  exact (show ∀ᵐ z ∂μ, z.1 ≠ q n from ae_iff.mpr (by simpa using hn.1)).and
    (show ∀ᵐ z ∂μ, z.2 ≠ q n from ae_iff.mpr (by simpa using hn.2))

private lemma compact_agreement (μ : Measure Plane) [IsFiniteMeasure μ] {F : Plane → Plane}
    (hm : Measurable F) (hi : Injective F) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : Set Plane) (e : Plane ≃ₜ Plane), IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ EqOn e F K := by
  obtain ⟨q, hq, hboth⟩ := dense_cuts (μ + μ.map F)
  obtain ⟨h₁, h₂⟩ := ae_add_measure_iff.mp hboth
  let P (z : Plane) := ∀ n, z.1 ≠ q n ∧ z.2 ≠ q n ∧ (F z).1 ≠ q n ∧ (F z).2 ≠ q n
  have hP : ∀ᵐ z ∂μ, P z := by
    filter_upwards [h₁, ae_of_ae_map hm.aemeasurable h₂] with z hz hf n
    exact ⟨(hz n).1, (hz n).2, hf n⟩
  obtain ⟨N, hN, hNm, hNμ⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hpos : 0 < ε / 2 := half_pos hε
  obtain ⟨L, hL, hLμ, hLF⟩ := _root_.MathlibExt.MeasureTheory.Function.Lusin.lusin (μ := μ) hm hpos
  obtain ⟨K, hKL, hK, hKμ⟩ := (hL.measurableSet.diff hNm).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (ENNReal.ofReal_pos.mpr hpos).ne'
  obtain ⟨e, he⟩ := extend_on_compact hK (hLF.mono (hKL.trans sdiff_subset)) hi.injOn hq
    (fun z hz => of_not_not (fun h => (hKL hz).2 (hN h)))
  refine ⟨K, e, hK, ?_, he⟩
  have sub : Kᶜ ⊆ Lᶜ ∪ (N ∪ ((L \ N) \ K)) := by grind
  calc
    μ Kᶜ ≤ μ Lᶜ + (μ N + μ ((L \ N) \ K)) :=
      (measure_mono sub).trans ((measure_union_le ..).trans
        (add_le_add_right (measure_union_le ..) _))
    _ = μ Lᶜ + μ ((L \ N) \ K) := by rw [hNμ, zero_add]
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hLμ hKμ
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hpos.le hpos.le, add_halves]

private lemma nullMeasurable_of_caratheodory {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {S : Set α} (hS : MeasurableSet[μ.toOuterMeasure.caratheodory] S) :
    NullMeasurableSet S μ := by
  have localize (n : ℕ) : NullMeasurableSet (S ∩ spanningSets μ n) μ := by
    let A := S ∩ spanningSets μ n
    have hA : MeasurableSet[μ.toOuterMeasure.caratheodory] A :=
      hS.inter (le_toOuterMeasure_caratheodory μ _ (measurableSet_spanningSets μ n))
    obtain ⟨B, hAB, hB, heq⟩ := exists_measurable_superset μ A
    have hsum : μ B = μ (B ∩ A) + μ (B \ A) := hA B
    rw [inter_eq_self_of_subset_right hAB, heq] at hsum
    have hfin : μ A ≠ ∞ := ((measure_mono inter_subset_right).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
    have hnull : μ (B \ A) = 0 := by
      exact ENNReal.add_right_inj hfin |>.mp (by simpa only [add_zero] using hsum.symm)
    change NullMeasurableSet A μ
    exact hB.nullMeasurableSet.congr
      (ae_eq_set.mpr ⟨hnull, by rw [sdiff_eq_empty.mpr hAB, measure_empty]⟩)
  simpa [← inter_iUnion, iUnion_spanningSets] using NullMeasurableSet.iUnion localize

open ProbabilityTheory
open _root_.MathlibExt.Probability.CdfContinuityPoints

private lemma probability_equivalent {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] (hμ : μ univ ≠ 0) :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ := by
  obtain ⟨ρ, hρ, hμρ, hρμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  exact ⟨cond ρ univ, cond_isProbabilityMeasure (fun hz => hμ (hμρ hz)),
    hμρ.trans absolutelyContinuous_cond_univ, cond_absolutelyContinuous.trans hρμ⟩

-- A Borel injection can move a finite diffuse measure into the Lebesgue measure class.
private lemma diffuse_transport (μ : Measure Plane) [IsFiniteMeasure μ]
    (hμ : ∀ x, μ {x} = 0) :
    ∃ F : Plane → Plane, Measurable F ∧ Injective F ∧ μ.map F ≪ volume := by
  have hℝ : ¬Countable ℝ := fun _ => Cardinal.not_countable_real (countable_univ)
  let e : Plane ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => hℝ <| (show Injective (fun x : ℝ => (x, (0 : ℝ))) from
      fun _ _ hh => congrArg Prod.fst hh).countable)
    hℝ
  -- Adding length makes the source distribution function strictly increasing.
  let η := μ.map e + (volume : Measure ℝ)
  have hη : η univ ≠ 0 := by simp [η]
  obtain ⟨ρ, hρ, hηρ, hρη⟩ := probability_equivalent η hη
  have h₁ : μ.map e ≪ ρ :=
    (Measure.AbsolutelyContinuous.rfl.add_right _).trans hηρ
  have h₂ : (volume : Measure ℝ) ≪ ρ :=
    (Measure.AbsolutelyContinuous.rfl.add_right' _).trans hηρ
  have hpre (x : ℝ) : e ⁻¹' {x} = {e.symm x} := by
    ext z
    exact e.toEquiv.eq_symm_apply.symm
  have hcρ : Continuous (cdf ρ) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (continuousAt_cdf_iff_measure_singleton_eq_zero ρ x).mpr
    apply hρη
    simp [η, e.map_apply, hpre, hμ]
  have hsρ : StrictMono (cdf ρ) := by
    intro x y hxy
    have hn : ρ (Ioc x y) ≠ 0 := fun h => (ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)).ne'
      (by simpa using h₂ h)
    rw [measure_Ioc_eq_ofReal_cdf] at hn
    exact sub_pos.mp (ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hn))
  have hvol : (volume : Measure Plane) univ ≠ 0 := by
    rw [Measure.volume_eq_prod, ← univ_prod_univ, Measure.prod_prod]
    simp
  obtain ⟨ν, hν, _, hνv⟩ := probability_equivalent (volume : Measure Plane) hvol
  let τ := ν.map e
  have hτ : IsProbabilityMeasure τ := inferInstanceAs (IsProbabilityMeasure (ν.map e))
  have hcτ : Continuous (cdf τ) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (continuousAt_cdf_iff_measure_singleton_eq_zero τ x).mpr
    change (ν.map e) {x} = 0
    rw [e.map_apply, hpre]
    apply hνv
    rw [Measure.volume_eq_prod]
    exact measure_singleton _
  -- The target law has null singletons, so its quantile is injective on (0, 1).
  let f := cdfQuantile τ ∘ cdf ρ
  have hf : Measurable f := (measurable_cdfQuantile τ).comp hcρ.measurable
  have hi : Injective f := by
    intro x y h
    apply hsρ.injective
    have hleft (t : ℝ) := cdf_cdfQuantile_eq_of_continuous τ hcτ
      (QuantileLink.cdf_mem_Ioo_of_strictMono ρ hsρ t)
    exact (hleft x).symm.trans ((congrArg (cdf τ) h).trans (hleft y))
  have hmap : ρ.map f = τ := by
    rw [show f = cdfQuantile τ ∘ cdf ρ from rfl, ← Measure.map_map (measurable_cdfQuantile τ)
      hcρ.measurable, QuantileLink.cdf_pushforward_eq_volume_restrict_Icc ρ hcρ hsρ,
      map_cdfQuantile_restrict_Icc]
  refine ⟨e.symm ∘ f ∘ e, e.symm.measurable.comp (hf.comp e.measurable),
    e.symm.injective.comp (hi.comp e.injective), ?_⟩
  rw [← Measure.map_map e.symm.measurable (hf.comp e.measurable),
    ← Measure.map_map hf e.measurable]
  have H := (h₁.map hf).map e.symm.measurable
  rw [hmap, show τ.map e.symm = ν from e.map_symm_map] at H
  exact H.trans hνv

private lemma diffuse_measurable {S : Set Plane}
    (hS : ∀ e : Plane ≃ₜ Plane, NullMeasurableSet (e '' S) volume)
    (μ : Measure Plane) [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} = 0) : NullMeasurableSet S μ := by
  obtain ⟨F, hm, hi, hmap⟩ := diffuse_transport μ hμ
  obtain ⟨u, _, hpos, hlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose K e hc hsmall he using fun n => compact_agreement μ hm hi (hpos n)
  have piece (n) : NullMeasurableSet (S ∩ K n) μ := by
    have heq : S ∩ K n = F ⁻¹' (e n '' S) ∩ K n := by
      ext z
      by_cases hz : z ∈ K n
      · simp only [mem_inter_iff, hz, and_true, mem_preimage, ← he n hz,
          (e n).injective.mem_set_image]
      · simp [hz]
    rw [heq]
    exact ((hS (e n)).preimage ⟨hm.aemeasurable, hmap⟩).inter (hc n).measurableSet.nullMeasurableSet
  have hzero : μ (⋃ n, K n)ᶜ = 0 := by
    apply le_antisymm _ zero_le
    have ht : Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    apply ge_of_tendsto' ht (fun n => ?_)
    exact (measure_mono (compl_subset_compl.mpr (subset_iUnion K n))).trans (hsmall n).le
  have hmU := NullMeasurableSet.iUnion piece
  rw [← inter_iUnion] at hmU
  apply hmU.congr
  filter_upwards [show ∀ᵐ z ∂μ, z ∈ ⋃ n, K n from ae_iff.mpr hzero] with z hz
  simp [hz]

private lemma finite_measurable {S : Set Plane}
    (hS : ∀ e : Plane ≃ₜ Plane, NullMeasurableSet (e '' S) volume)
    (μ : Measure Plane) [IsFiniteMeasure μ] : NullMeasurableSet S μ := by
  -- Every subset of the points of positive mass is countable and hence Borel.
  let A := {x : Plane | 0 < μ {x}}
  have hc : A.Countable := by
    simpa [A] using Measure.countable_meas_level_set_pos (μ := μ) (measurable_id (α := Plane))
  have hn (x : Plane) : μ.restrict Aᶜ {x} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ A
    · have : {x} ∩ Aᶜ = ∅ := by simpa
      simp [this]
    · have : μ {x} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hx)
      exact measure_mono_null inter_subset_left this
  have hrest := (nullMeasurableSet_restrict hc.measurableSet.compl.nullMeasurableSet).mp
    (diffuse_measurable hS (μ.restrict Aᶜ) hn)
  have hcount : NullMeasurableSet (S ∩ A) μ :=
    (hc.mono inter_subset_right).measurableSet.nullMeasurableSet
  simpa [← inter_union_distrib_left] using hcount.union hrest

/--
**Szpilrajn's Problem 170: plane sets with measurable homeomorphic copies.** Let $S$ be a subset
of the plane $\mathbb{R}^2$ such that every subset $T$ of $\mathbb{R}^2$ homeomorphic to $S$ (as
a subspace) is Lebesgue measurable, that is, Carathéodory measurable with respect to Lebesgue
outer measure on $\mathbb{R}^2$. Then $S$ is absolutely measurable: for every measure $\mu$ on
the Borel $\sigma$-algebra of $\mathbb{R}^2$, the set $S$ is Carathéodory measurable with respect
to the outer measure induced by $\mu$.

The hypothesis concerns every subset of the plane homeomorphic to $S$, not only the images of $S$
under homeomorphisms of the whole plane.

Source: E. Szpilrajn, Problem 170 of the Scottish
Book; the affirmative answer follows from an unpublished result of
J. von Neumann, as recorded in Ad 170 of the typescript. See the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed.
(Birkhäuser, 2015). Lebesgue measurability is stated as Carathéodory
measurability with respect to `volume`; the case of linear sets, and
the analogue for generalized homeomorphisms in the sense of Kuratowski,
were already known.
-/
public theorem szpilrajn170_homeomorphic_images_measurable_imp_absolute :
    ∀ S : Set (ℝ × ℝ),
      (∀ T : Set (ℝ × ℝ), Nonempty (↥S ≃ₜ ↥T) →
        @MeasurableSet (ℝ × ℝ) (MeasureTheory.volume.toOuterMeasure.caratheodory) T) →
      ∀ μ : MeasureTheory.Measure (ℝ × ℝ),
        @MeasurableSet (ℝ × ℝ) (μ.toOuterMeasure.caratheodory) S := by
  intro S hS μ
  have hcopy (e : Plane ≃ₜ Plane) : NullMeasurableSet (e '' S) volume :=
    nullMeasurable_of_caratheodory (hS _ ⟨e.isEmbedding.homeomorphImage S⟩)
  apply (OuterMeasure.isCaratheodory_iff_le _).mpr
  intro t
  change μ (t ∩ S) + μ (t \ S) ≤ μ t
  by_cases ht : μ t = ∞
  · simp [ht]
  obtain ⟨B, hsub, hB, hmass⟩ := exists_measurable_superset μ t
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr (hmass.trans_ne ht)
  have h := measure_inter_add_sdiff₀ t (finite_measurable hcopy (μ.restrict B))
  rw [Measure.restrict_apply' hB, Measure.restrict_apply' hB, Measure.restrict_apply' hB,
    inter_eq_self_of_subset_left (inter_subset_left.trans hsub),
    inter_eq_self_of_subset_left (sdiff_subset.trans hsub), inter_eq_self_of_subset_left hsub] at h
  exact h.le

end MathlibExt.MeasureTheory.ScottishBook170Wanted
