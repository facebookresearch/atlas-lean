/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import MathlibExt.Dynamics.Ergodic.Birkhoff

@[expose] public section

section
open MeasureTheory Filter Topology

namespace MathlibExt.Dynamics.Ergodic.KingmanWanted

/-!
# Kingman's subadditive ergodic theorem

The nonnegative integrable cocycle form.
-/

/-- N5a: subadditive cocycle bounded by Birkhoff sums of `f 1` (everywhere version). -/
private theorem le_birkhoffSum_one
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∀ n x, f n x ≤ birkhoffSum T (f 1) n x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [hf_zero x]
    have h0 := congrFun (birkhoffSum_zero T (f 1)) x
    simp only [Pi.zero_apply] at h0
    rw [h0]
  | succ n ih =>
    intro x
    have hsub := hf_subadd 1 n x
    rw [Function.iterate_one] at hsub
    have hshift : f (n + 1) x = f (1 + n) x := by rw [Nat.add_comm]
    rw [hshift]
    have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
    simp only [Pi.add_apply, Function.comp_apply] at hbs
    rw [hbs]
    exact le_trans hsub (add_le_add_right (ih (T x)) _)

/-- N5b: integral bound via Birkhoff sums (everywhere version). -/
private theorem integral_le_mul_integral_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_int : ∀ n, Integrable (f n) μ)
    (hle : ∀ n x, f n x ≤ birkhoffSum T (f 1) n x) :
    ∀ n, ∫ x, f n x ∂μ ≤ n * ∫ x, f 1 x ∂μ := by
  have hint : ∀ n, Integrable (fun x => birkhoffSum T (f 1) n x) μ := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
      have hcomp : Integrable (fun x => birkhoffSum T (f 1) n (T x)) μ :=
        hT.integrable_comp_of_integrable ih
      have ef : (fun x => birkhoffSum T (f 1) (n + 1) x) =
          fun x => (f 1 x + birkhoffSum T (f 1) n (T x)) := by
        funext x
        have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
        simp only [Pi.add_apply, Function.comp_apply] at hbs
        exact hbs
      rw [ef]
      exact (hf_int 1).add hcomp
  have hident : ∀ n, ∫ x, birkhoffSum T (f 1) n x ∂μ = n * ∫ x, f 1 x ∂μ := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
      have hcomp : Integrable (fun x => birkhoffSum T (f 1) n (T x)) μ :=
        hT.integrable_comp_of_integrable (hint n)
      have eadd : ∫ x, (f 1 x + birkhoffSum T (f 1) n (T x)) ∂μ =
          (∫ x, f 1 x ∂μ) + ∫ x, birkhoffSum T (f 1) n (T x) ∂μ :=
        integral_add (hf_int 1) hcomp
      have emap : (∫ x, birkhoffSum T (f 1) n (T x) ∂μ) =
          (∫ x, birkhoffSum T (f 1) n x ∂μ) := by
        have haes : AEStronglyMeasurable (fun x => birkhoffSum T (f 1) n x)
            (Measure.map T μ) := by
          rw [hT.map_eq]
          exact (hint n).1
        have h1 : (∫ y, birkhoffSum T (f 1) n y ∂(Measure.map T μ)) =
            (∫ x, birkhoffSum T (f 1) n (T x) ∂μ) :=
          integral_map hT.measurable.aemeasurable haes
        rw [← h1, hT.map_eq]
      have ef : (fun x => birkhoffSum T (f 1) (n + 1) x) =
          fun x => (f 1 x + birkhoffSum T (f 1) n (T x)) := by
        funext x
        have hbs := congrFun (birkhoffSum_succ' T (f 1) n) x
        simp only [Pi.add_apply, Function.comp_apply] at hbs
        exact hbs
      rw [← ef] at eadd
      rw [eadd, emap, ih]
      push_cast
      ring
  intro n
  calc ∫ x, f n x ∂μ ≤ ∫ x, birkhoffSum T (f 1) n x ∂μ :=
        integral_mono (hf_int n) (hint n) (hle n)
    _ = ↑n * ∫ x, f 1 x ∂μ := hident n

/-- N6: integrable stationary sequences are o(n) along orbits. -/
private theorem ae_tendsto_comp_iterate_div_nat
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφmeas : Measurable φ) (hφint : Integrable φ μ) (hφnn : ∀ x, 0 ≤ φ x) :
    ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => φ ((T^[m]) x) / (m : ℝ)) atTop (nhds 0) := by
  have hbound : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ m in atTop,
      φ ((T^[m]) x) / (m : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hXint : Integrable (fun y => ((k : ℝ) + 1) * φ y) μ := hφint.const_mul _
    have hXnn : ∀ y, 0 ≤ ((k : ℝ) + 1) * φ y := fun y =>
      mul_nonneg (by positivity) (hφnn y)
    have htsum : ∑' (m : ℕ), μ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} < ⊤ := by
      let : MeasureSpace α := ⟨μ⟩
      exact ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hXint hXnn
    have hmeas_set : ∀ m : ℕ,
        MeasurableSet {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} := by
      intro m
      have h : MeasurableSet {y | ((m : ℝ)) < ((k : ℝ) + 1) * φ y} :=
        measurableSet_lt measurable_const (measurable_const.mul hφmeas)
      simpa only [Set.mem_Ioi] using h
    have htsum2 : ∑' (m : ℕ),
        μ ((T^[m]) ⁻¹' {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}) ≠ ⊤ := by
      have hpre : ∀ m : ℕ, μ ((T^[m]) ⁻¹' {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}) =
          μ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))} :=
        fun m => (hT.iterate m).measure_preimage ((hmeas_set m).nullMeasurableSet)
      exact ne_of_lt (by simpa only [hpre] using htsum)
    have hbc := MeasureTheory.ae_eventually_notMem htsum2
    filter_upwards [hbc] with x hx
    filter_upwards [hx, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hK : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
    have hle : ((k : ℝ) + 1) * φ ((T^[m]) x) ≤ (m : ℝ) := by
      rw [← not_lt]
      intro hcon
      apply hm
      change (T^[m]) x ∈ {y | ((k : ℝ) + 1) * φ y ∈ Set.Ioi ((m : ℝ))}
      change ((m : ℝ)) < ((k : ℝ) + 1) * φ ((T^[m]) x)
      exact hcon
    have h1 : φ ((T^[m]) x) ≤ (m : ℝ) / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hK, mul_comm]
      exact hle
    have h2 : (1 / ((k : ℝ) + 1)) * (m : ℝ) = (m : ℝ) / ((k : ℝ) + 1) := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [div_le_iff₀ hm0, h2]
    exact h1
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ᶠ m in atTop,
      φ ((T^[m]) x) / (m : ℝ) ≤ 1 / ((k : ℝ) + 1) :=
    (MeasureTheory.ae_all_iff).mpr hbound
  filter_upwards [hall] with x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hx k)
  refine ⟨N1, fun m hm => ?_⟩
  have hmb := hN1 m hm
  have hnn : 0 ≤ φ ((T^[m]) x) / (m : ℝ) := div_nonneg (hφnn _) (Nat.cast_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact lt_of_le_of_lt hmb hk

/-- N7: sub-invariant ENNReal functions are invariant a.e. -/
private theorem ae_comp_eq_of_le_comp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {h : α → ENNReal} (hh : Measurable h) (hle : ∀ x, h x ≤ h (T x)) :
    h ∘ T =ᵐ[μ] h := by
  set S : ℚ → Set α := fun q => {x | (↑(Real.toNNReal (q : ℝ)) : ENNReal) < h x} with hS
  have hmeas : ∀ q : ℚ, MeasurableSet (S q) :=
    fun q => measurableSet_lt measurable_const hh
  have hsub : ∀ q : ℚ, S q ⊆ T ⁻¹' (S q) := by
    intro q x hx
    simp only [hS, Set.mem_ofPred_eq, Set.mem_preimage]
    exact lt_of_lt_of_le hx (hle x)
  have hnull : ∀ q : ℚ, NullMeasurableSet (S q) μ :=
    fun q => (hmeas q).nullMeasurableSet
  have hmeas_eq : ∀ q : ℚ, μ (T ⁻¹' (S q)) = μ (S q) :=
    fun q => hT.measure_preimage (hnull q)
  have hae : ∀ q : ℚ, S q =ᵐ[μ] (T ⁻¹' (S q)) := by
    intro q
    exact MeasureTheory.ae_eq_of_subset_of_measure_ge (hsub q) (by rw [hmeas_eq q])
      (hnull q) (measure_ne_top μ _)
  have hall : ∀ᵐ x ∂μ, ∀ q : ℚ, (x ∈ S q ↔ T x ∈ S q) := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    filter_upwards [hae q] with x hx
    have hx' : x ∈ S q ↔ x ∈ T ⁻¹' (S q) := by rw [hx]
    rw [Set.mem_preimage] at hx'
    exact hx'
  filter_upwards [hall] with x hx
  change h (T x) = h x
  by_contra hne
  have hlt : h x < h (T x) := lt_of_le_of_ne (hle x) (Ne.symm hne)
  obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
  have hTx_mem : T x ∈ S q := h2
  have hx_mem : x ∈ S q := (hx q).mpr hTx_mem
  have hcon : (↑(Real.toNNReal (q : ℝ)) : ENNReal) < h x := hx_mem
  exact (lt_irrefl _) (lt_trans h1 hcon)

/-- N4: reduce a.e. hypotheses to everywhere hypotheses via an invariant full-measure set. -/
private theorem kingman_reduce_everywhere
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hf_zero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hf_subadd : ∀ m n, ∀ᵐ x ∂μ, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∃ f' : ℕ → α → ℝ, (∀ n, Measurable (f' n)) ∧ (∀ n, f' n =ᵐ[μ] f n) ∧
      (∀ n x, 0 ≤ f' n x) ∧ (∀ x, f' 0 x = 0) ∧
      (∀ m n x, f' (m + n) x ≤ f' m x + f' n ((T^[m]) x)) := by
  have hTm : ∀ k, Measurable (T^[k]) := fun k => (hT.measurable.iterate k)
  set G1 : Set α :=
    (⋂ n, (f n) ⁻¹' (Set.Ici 0)) ∩ ((f 0) ⁻¹' {0}) ∩
      (⋂ m, ⋂ n, {x | f (m + n) x ≤ f m x + f n ((T^[m]) x)}) with hG1
  have hG1meas : MeasurableSet G1 := by
    rw [hG1]
    refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact MeasurableSet.iInter (fun n => (hf_meas n) measurableSet_Ici)
    · exact (hf_meas 0) (measurableSet_singleton 0)
    · exact MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun n =>
        measurableSet_le (hf_meas (m + n)) ((hf_meas m).add ((hf_meas n).comp (hTm m)))))
  have hA : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x := (MeasureTheory.ae_all_iff).mpr hf_nonneg
  have hC1 : ∀ m, ∀ᵐ x ∂μ, ∀ n, f (m + n) x ≤ f m x + f n ((T^[m]) x) := by
    intro m
    exact (MeasureTheory.ae_all_iff).mpr (hf_subadd m)
  have hC : ∀ᵐ x ∂μ, ∀ m n, f (m + n) x ≤ f m x + f n ((T^[m]) x) :=
    (MeasureTheory.ae_all_iff).mpr hC1
  have hG1ae : ∀ᵐ x ∂μ, x ∈ G1 := by
    filter_upwards [hA, hf_zero, hC] with x hxA hx0 hxC
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Set.mem_iInter]
      intro n
      exact hxA n
    · exact hx0
    · rw [Set.mem_iInter]
      intro m
      rw [Set.mem_iInter]
      intro n
      exact hxC m n
  set G0 : Set α := ⋂ k, (T^[k]) ⁻¹' G1 with hG0
  have hG0meas : MeasurableSet G0 := by
    rw [hG0]
    exact MeasurableSet.iInter (fun k => (hTm k) hG1meas)
  have hG1null : μ G1ᶜ = 0 := MeasureTheory.ae_iff.mp hG1ae
  have hpre : ∀ k, μ ((T^[k]) ⁻¹' G1)ᶜ = 0 := by
    intro k
    have h1 : ((T^[k]) ⁻¹' G1)ᶜ = (T^[k]) ⁻¹' (G1ᶜ) := (Set.preimage_compl).symm
    rw [h1, (hT.iterate k).measure_preimage (hG1meas.compl.nullMeasurableSet), hG1null]
  have hG0ae : ∀ᵐ x ∂μ, x ∈ G0 := by
    have h2 : ∀ k, ∀ᵐ x ∂μ, x ∈ (T^[k]) ⁻¹' G1 := by
      intro k
      exact MeasureTheory.ae_iff.mpr (hpre k)
    have h3 : ∀ᵐ x ∂μ, ∀ k, x ∈ (T^[k]) ⁻¹' G1 := (MeasureTheory.ae_all_iff).mpr h2
    filter_upwards [h3] with x hx
    rw [hG0, Set.mem_iInter]
    exact hx
  have hfwd : ∀ m x, x ∈ G0 → (T^[m]) x ∈ G0 := by
    intro m x hx
    rw [hG0, Set.mem_iInter] at hx ⊢
    intro k
    have hk := hx (k + m)
    rw [Set.mem_preimage] at hk ⊢
    have heq : (T^[k + m]) x = (T^[k]) ((T^[m]) x) := Function.iterate_add_apply T k m x
    rw [← heq]
    exact hk
  have hmemG1 : ∀ x, x ∈ G0 → x ∈ G1 := by
    intro x hx
    rw [hG0, Set.mem_iInter] at hx
    have h0 := hx 0
    rw [Set.mem_preimage, Function.iterate_zero, id_eq] at h0
    exact h0
  have hG1A : ∀ x, x ∈ G1 → ∀ n, 0 ≤ f n x := by
    intro x hx n
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨⟨hA', -⟩, -⟩ := hx
    exact Set.mem_iInter.mp hA' n
  have hG1B : ∀ x, x ∈ G1 → f 0 x = 0 := by
    intro x hx
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨⟨-, hB⟩, -⟩ := hx
    exact hB
  have hG1C : ∀ x, x ∈ G1 → ∀ m n, f (m + n) x ≤ f m x + f n ((T^[m]) x) := by
    intro x hx m n
    rw [hG1, Set.mem_inter_iff, Set.mem_inter_iff] at hx
    obtain ⟨-, hC'⟩ := hx
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hC' m) n
  refine ⟨fun n => G0.indicator (f n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hf_meas n).indicator hG0meas
  · intro n
    filter_upwards [hG0ae] with x hx
    exact Set.indicator_of_mem hx (f n)
  · intro n x
    change 0 ≤ G0.indicator (f n) x
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx]
      exact hG1A x (hmemG1 x hx) n
    · rw [Set.indicator_of_notMem hx]
  · intro x
    change G0.indicator (f 0) x = 0
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx]
      exact hG1B x (hmemG1 x hx)
    · rw [Set.indicator_of_notMem hx]
  · intro m n x
    change G0.indicator (f (m + n)) x ≤ G0.indicator (f m) x + G0.indicator (f n) ((T^[m]) x)
    by_cases hx : x ∈ G0
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_mem (hfwd m x hx)]
      exact hG1C x (hmemG1 x hx) m n
    · rw [Set.indicator_of_notMem hx]
      have h1 : 0 ≤ G0.indicator (f m) x := by
        rw [Set.indicator_of_notMem hx]
      have h2 : 0 ≤ G0.indicator (f n) ((T^[m]) x) := by
        by_cases hTx : (T^[m]) x ∈ G0
        · rw [Set.indicator_of_mem hTx]
          exact hG1A _ (hmemG1 _ hTx) n
        · rw [Set.indicator_of_notMem hTx]
      exact add_nonneg h1 h2

/-- N9: Steele's greedy block decomposition bound (pure combinatorics). -/
private theorem greedy_block_bound
    (F : ℕ → ℕ → ℝ) (hFnonneg : ∀ k n, 0 ≤ F k n) (hF0 : ∀ k, F k 0 = 0)
    (hFsub : ∀ k m n, F k (m + n) ≤ F k m + F (k + m) n)
    (B : ℕ → Prop) [DecidablePred B]
    (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hgood : ∀ k, ¬ B k → ∃ n, 1 ≤ n ∧ n ≤ N ∧ F k n ≤ n * c) :
    ∀ M : ℕ, F 0 M ≤ M * c + (∑ k ∈ Finset.range M, if B k then F k 1 else 0) +
      (∑ k ∈ Finset.range M, if M ≤ k + N then F k 1 else 0) := by
  intro M
  have hifnn : ∀ k, 0 ≤ (if B k then F k 1 else 0) := by
    intro k
    split_ifs with h
    · exact hFnonneg k 1
    · exact le_rfl
  have hifnn2 : ∀ k, 0 ≤ (if M ≤ k + N then F k 1 else 0) := by
    intro k
    split_ifs with h
    · exact hFnonneg k 1
    · exact le_rfl
  -- split off the first term of a sum over Ico
  have hsplit : ∀ (g : ℕ → ℝ) (a b : ℕ), a < b →
      (∑ k ∈ Finset.Ico a b, g k) = g a + ∑ k ∈ Finset.Ico (a + 1) b, g k := by
    intro g a b hab
    have hIco : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hIco, Finset.sum_insert (by rw [Finset.mem_Ico]; omega)]
  have key : ∀ r, r ≤ M → ∀ j, M - r = j → F j r ≤ r * c +
      (∑ k ∈ Finset.Ico j M, if B k then F k 1 else 0) +
      (∑ k ∈ Finset.Ico j M, if M ≤ k + N then F k 1 else 0) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrM j hrj
      by_cases r0 : r = 0
      · subst r0
        simp only [Nat.sub_zero] at hrj
        subst hrj
        rw [hF0 M]
        have s1 : 0 ≤ (∑ k ∈ Finset.Ico M M, if B k then F k 1 else 0) :=
          Finset.sum_nonneg (fun k _ => hifnn k)
        have s2 : 0 ≤ (∑ k ∈ Finset.Ico M M, if M ≤ k + N then F k 1 else 0) :=
          Finset.sum_nonneg (fun k _ => hifnn2 k)
        simp only [Nat.cast_zero, zero_mul, zero_add]
        exact add_nonneg s1 s2
      · have hpos : 0 < r := Nat.pos_of_ne_zero r0
        have hjM : j < M := by omega
        have hjr : j + r = M := by omega
        by_cases hBj : B j
        · -- bad position: peel off one step, charge to first sum
          have hr1 : r = 1 + (r - 1) := by omega
          have step1 : F j r ≤ F j 1 + F (j + 1) (r - 1) := by
            conv_lhs => rw [hr1]
            exact hFsub j 1 (r - 1)
          have ihr := ih (r - 1) (by omega) (by omega) (j + 1) (by omega)
          have e1 := hsplit (fun k => if B k then F k 1 else 0) j M hjM
          have e2 := hsplit (fun k => if M ≤ k + N then F k 1 else 0) j M hjM
          rw [ite_eq_left hBj] at e1
          have ht : 0 ≤ (if M ≤ j + N then F j 1 else 0) := hifnn2 j
          have hcast : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast Nat.sub_le r 1
          have hmul : ((r - 1 : ℕ) : ℝ) * c ≤ (r : ℝ) * c :=
            mul_le_mul_of_nonneg_right hcast hc
          linarith
        · -- good position: take the whole block given by hgood
          obtain ⟨n, h1n, hnN, hFn⟩ := hgood j hBj
          by_cases hleM : j + n ≤ M
          · have hnr : n ≤ r := by omega
            have hr2 : r = n + (r - n) := by omega
            have step : F j r ≤ F j n + F (j + n) (r - n) := by
              conv_lhs => rw [hr2]
              exact hFsub j n (r - n)
            have ihr := ih (r - n) (by omega) (by omega) (j + n) (by omega)
            have hsub12 : Finset.Ico (j + n) M ⊆ Finset.Ico j M :=
              Finset.Ico_subset_Ico (by omega) le_rfl
            have s1le : (∑ k ∈ Finset.Ico (j + n) M, if B k then F k 1 else 0) ≤
                (∑ k ∈ Finset.Ico j M, if B k then F k 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub12 (fun i _ _ => hifnn i)
            have s2le : (∑ k ∈ Finset.Ico (j + n) M, if M ≤ k + N then F k 1 else 0) ≤
                (∑ k ∈ Finset.Ico j M, if M ≤ k + N then F k 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub12 (fun i _ _ => hifnn2 i)
            have hcast2 : ((r - n : ℕ) : ℝ) + (n : ℝ) = (r : ℝ) := by
              exact_mod_cast Nat.sub_add_cancel hnr
            have hmul2 : ((r - n : ℕ) : ℝ) * c + (n : ℝ) * c = (r : ℝ) * c := by
              rw [← add_mul, hcast2]
            linarith
          · -- block overruns M: peel off one step, charge to tail sum
            have htail : M ≤ j + N := by omega
            have hr3 : r = 1 + (r - 1) := by omega
            have step : F j r ≤ F j 1 + F (j + 1) (r - 1) := by
              conv_lhs => rw [hr3]
              exact hFsub j 1 (r - 1)
            have ihr := ih (r - 1) (by omega) (by omega) (j + 1) (by omega)
            have e1 := hsplit (fun k => if B k then F k 1 else 0) j M hjM
            have e2 := hsplit (fun k => if M ≤ k + N then F k 1 else 0) j M hjM
            rw [ite_eq_right hBj] at e1
            rw [ite_eq_left htail] at e2
            have hcast : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
              exact_mod_cast Nat.sub_le r 1
            have hmul : ((r - 1 : ℕ) : ℝ) * c ≤ (r : ℝ) * c :=
              mul_le_mul_of_nonneg_right hcast hc
            linarith
  have hfin := key M le_rfl 0 (Nat.sub_self M)
  rw [← Finset.range_eq_Ico] at hfin
  -- hfin has Ico 0 M? no: range_eq_Ico : range n = Ico 0 n; ← rewrites Ico 0 M to range M
  simpa using hfin

-- Shared maximal-ergodic infrastructure (maximal ergodic theorem, `DickSet`
-- and its basic lemmas) lives in `BirkhoffWanted`; see Birkhoff.lean.

/-- N3a: integral of `φ - c` over the shared `DickSet` is nonnegative. -/
private theorem setIntegral_kingmanDick_sub_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hφi : Integrable φ μ) (c : ℝ) :
    0 ≤ ∫ x in BirkhoffWanted.DickSet T φ c, (φ x - c) ∂μ := by
  have hDmeas : MeasurableSet (BirkhoffWanted.DickSet T φ c) :=
    BirkhoffWanted.dick_measurable hT hφ c
  have hiter : ∀ (k : ℕ) (x : α),
      (T^[k] x ∈ BirkhoffWanted.DickSet T φ c) ↔ (x ∈ BirkhoffWanted.DickSet T φ c) :=
    fun k x => BirkhoffWanted.dick_iter k x
  set hfun : α → ℝ := (BirkhoffWanted.DickSet T φ c).indicator (fun y => φ y - c) with hfundef
  have hm_h : Measurable hfun := Measurable.indicator (hφ.sub measurable_const) hDmeas
  have hi_h : Integrable hfun μ :=
    Integrable.indicator (hφi.sub (integrable_const c)) hDmeas
  have hfundef' : ∀ y : α,
      hfun y = (BirkhoffWanted.DickSet T φ c).indicator (fun y => φ y - c) y :=
    fun y => rfl
  have hsum_in : ∀ x : α, x ∈ BirkhoffWanted.DickSet T φ c → ∀ n : ℕ,
      birkhoffSum T hfun n x = birkhoffSum T φ n x - n * c :=
    fun x hx n => BirkhoffWanted.dick_sum_in _ hiter hfun hfundef' x hx n
  have hsum_out : ∀ x : α, x ∉ BirkhoffWanted.DickSet T φ c → ∀ n : ℕ,
      birkhoffSum T hfun n x = 0 :=
    fun x hx n => BirkhoffWanted.dick_sum_out _ hiter hfun hfundef' x hx n
  have hE : {x | ∃ n, 0 < birkhoffSum T hfun n x} = BirkhoffWanted.DickSet T φ c := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := hx
      by_contra hxD
      rw [hsum_out x hxD n] at hn
      exact lt_irrefl 0 hn
    · intro hx
      have hxD : x ∈ BirkhoffWanted.DickSet T φ c := hx
      rw [BirkhoffWanted.dick_mem] at hx
      obtain ⟨q, hcq, hfreq⟩ := hx
      obtain ⟨n, hn1, hnq⟩ := hfreq 1
      refine ⟨n, ?_⟩
      rw [hsum_in x hxD n]
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have h0n : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
        exact_mod_cast h0n
      have hqc : (0 : ℝ) < (q : ℝ) - c := sub_pos.mpr hcq
      have hmul : (0 : ℝ) < (n : ℝ) * ((q : ℝ) - c) := mul_pos hnpos hqc
      have heq : (n : ℝ) * (q : ℝ) - (n : ℝ) * c = (n : ℝ) * ((q : ℝ) - c) := by ring
      linarith
  have hmax := BirkhoffWanted.maximal_ergodic hT hm_h hi_h
  rw [hE] at hmax
  have hcongr : ∫ x in BirkhoffWanted.DickSet T φ c, hfun x ∂μ
      = ∫ x in BirkhoffWanted.DickSet T φ c, (φ x - c) ∂μ := by
    apply setIntegral_congr_ae hDmeas
    filter_upwards with x
    intro hx
    exact Set.indicator_of_mem hx _
  rw [hcongr] at hmax
  exact hmax

/-- N3b: weak maximal inequality for nonnegative `φ`. -/
private theorem measure_kingmanDick_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hφi : Integrable φ μ) (hφnn : ∀ x, 0 ≤ φ x)
    {c : ℝ} (hc : 0 < c) :
    μ (BirkhoffWanted.DickSet T φ c) ≤ ENNReal.ofReal ((∫ x, φ x ∂μ) / c) := by
  have h3a := setIntegral_kingmanDick_sub_nonneg hT hφ hφi c
  have hconst : (∫ x in BirkhoffWanted.DickSet T φ c, c ∂μ)
      = c * (μ (BirkhoffWanted.DickSet T φ c)).toReal := by
    rw [setIntegral_const, Measure.real_def, smul_eq_mul]
    exact mul_comm _ _
  have hsub : (∫ x in BirkhoffWanted.DickSet T φ c, (φ x - c) ∂μ)
      = (∫ x in BirkhoffWanted.DickSet T φ c, φ x ∂μ)
        - c * (μ (BirkhoffWanted.DickSet T φ c)).toReal := by
    have h1 : (∫ x in BirkhoffWanted.DickSet T φ c, (φ x - c) ∂μ)
        = (∫ x in BirkhoffWanted.DickSet T φ c, φ x ∂μ)
          - ∫ x in BirkhoffWanted.DickSet T φ c, c ∂μ :=
      integral_sub (μ := μ.restrict (BirkhoffWanted.DickSet T φ c))
        hφi.integrableOn (integrable_const c).integrableOn
    rw [hconst] at h1
    exact h1
  have hle1 : c * (μ (BirkhoffWanted.DickSet T φ c)).toReal
      ≤ ∫ x in BirkhoffWanted.DickSet T φ c, φ x ∂μ := by
    linarith [h3a, hsub]
  have hle2 : (∫ x in BirkhoffWanted.DickSet T φ c, φ x ∂μ) ≤ ∫ x, φ x ∂μ :=
    setIntegral_le_integral hφi (Filter.Eventually.of_forall hφnn)
  have hle : c * (μ (BirkhoffWanted.DickSet T φ c)).toReal ≤ ∫ x, φ x ∂μ :=
    le_trans hle1 hle2
  have hdiv : (μ (BirkhoffWanted.DickSet T φ c)).toReal ≤ (∫ x, φ x ∂μ) / c := by
    rw [le_div_iff₀ hc]
    linarith [hle]
  calc μ (BirkhoffWanted.DickSet T φ c)
      = ENNReal.ofReal ((μ (BirkhoffWanted.DickSet T φ c)).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal ((∫ x, φ x ∂μ) / c) := ENNReal.ofReal_le_ofReal hdiv

/-- N8: liminf rate function (ENNReal to avoid boundedness side conditions). -/
private noncomputable def kingmanLiminf {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (x : α) : ENNReal :=
  Filter.liminf (fun n : ℕ => ENNReal.ofReal (f n x / (n : ℝ))) atTop

/-- N8a: measurability of the liminf rate. -/
private theorem kingmanLiminf_measurable
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (hf_meas : ∀ n, Measurable (f n)) :
    Measurable (kingmanLiminf f) := by
  unfold kingmanLiminf
  apply Measurable.liminf
  intro n
  exact ((hf_meas n).div measurable_const).ennreal_ofReal

/-- N8bc: Fatou bound and a.e. finiteness of the liminf rate. -/
private theorem kingmanLiminf_lintegral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hN5 : ∀ n, ∫ x, f n x ∂μ ≤ (n : ℝ) * ∫ x, f 1 x ∂μ) :
    ∫⁻ x, kingmanLiminf f x ∂μ ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) ∧
      ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤ := by
  have hmeas_seq : ∀ n, Measurable (fun x => ENNReal.ofReal (f n x / (n : ℝ))) :=
    fun n => ((hf_meas n).div measurable_const).ennreal_ofReal
  have hfat : ∫⁻ x, kingmanLiminf f x ∂μ
      ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ) atTop := by
    have := lintegral_liminf_le hmeas_seq (μ := μ) (u := (atTop : Filter ℕ))
    simpa only [kingmanLiminf] using this
  have hper : ∀ n, (∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ)
      ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hz : (fun x => ENNReal.ofReal (f 0 x / ((0 : ℕ) : ℝ))) = fun _ => 0 := by
        funext x
        rw [hf_zero x]
        simp
      rw [hz]
      simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
      have hint : Integrable (fun x => f n x / (n : ℝ)) μ := (hf_int n).div_const _
      have hnnm : 0 ≤ᵐ[μ] (fun x => f n x / (n : ℝ)) :=
        Filter.Eventually.of_forall
          (fun x => div_nonneg (hf_nn n x) (Nat.cast_nonneg _))
      have hof : (∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ)
          = ENNReal.ofReal (∫ x, (f n x / (n : ℝ)) ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint hnnm]
      have hval : (∫ x, (f n x / (n : ℝ)) ∂μ) = ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ := by
        have heq : (fun x => f n x / (n : ℝ)) = (fun x => ((n : ℝ))⁻¹ * f n x) := by
          funext x
          rw [div_eq_mul_inv, mul_comm]
        rw [heq, integral_const_mul]
      have hle : ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ ≤ ∫ x, f 1 x ∂μ := by
        have h1 := hN5 n
        have h2 : ((n : ℝ))⁻¹ * ∫ x, f n x ∂μ ≤ ((n : ℝ))⁻¹ * ((n : ℝ) * ∫ x, f 1 x ∂μ) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hnn)
        have h3 : ((n : ℝ))⁻¹ * ((n : ℝ) * ∫ x, f 1 x ∂μ) = ∫ x, f 1 x ∂μ := by
          field_simp
        rw [h3] at h2
        exact h2
      rw [hof, hval]
      exact ENNReal.ofReal_le_ofReal hle
  have hlim : Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x / (n : ℝ)) ∂μ) atTop
      ≤ ENNReal.ofReal (∫ x, f 1 x ∂μ) :=
    Filter.liminf_le_of_frequently_le (Frequently.of_forall hper)
      ⟨⊥, Filter.Eventually.of_forall fun _ => bot_le⟩
  refine ⟨le_trans hfat hlim, ?_⟩
  apply ae_lt_top (kingmanLiminf_measurable f hf_meas)
  exact ne_of_lt (lt_of_le_of_lt (le_trans hfat hlim) ENNReal.ofReal_lt_top)

/-- N8d: the liminf rate is sub-invariant. -/
private theorem kingmanLiminf_le_comp
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∀ x, kingmanLiminf f x ≤ kingmanLiminf f (T x) := by
  intro x
  have hpt : ∀ n : ℕ, ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))
      ≤ ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
        + ENNReal.ofReal (f n (T x) / (n : ℝ)) := by
    intro n
    have hreal : f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
        ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ) := by
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hf_zero (T x)]
        simp
      · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hN1 : (0 : ℝ) < (((n + 1 : ℕ)) : ℝ) := by
          exact_mod_cast Nat.succ_pos n
        have hsub := hf_subadd 1 n x
        rw [Function.iterate_one, Nat.add_comm (1 : ℕ) n] at hsub
        have hleN : (n : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hdiv : f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
            ≤ (f 1 x + f n (T x)) / (((n + 1 : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_right hsub (le_of_lt hN1)
        have h2 : f n (T x) / (((n + 1 : ℕ)) : ℝ) ≤ f n (T x) / (n : ℝ) :=
          div_le_div_of_nonneg_left (hf_nn n (T x)) hN hleN
        calc f (n + 1) x / (((n + 1 : ℕ)) : ℝ)
            ≤ (f 1 x + f n (T x)) / (((n + 1 : ℕ)) : ℝ) := hdiv
          _ = f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (((n + 1 : ℕ)) : ℝ) :=
              add_div _ _ _
          _ ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ) :=
              add_le_add_right h2 _
    have hb : 0 ≤ f 1 x / (((n + 1 : ℕ)) : ℝ) :=
      div_nonneg (hf_nn 1 x) (Nat.cast_nonneg _)
    have hd : 0 ≤ f n (T x) / (n : ℝ) :=
      div_nonneg (hf_nn n (T x)) (Nat.cast_nonneg _)
    calc ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))
        ≤ ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ) + f n (T x) / (n : ℝ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
          + ENNReal.ofReal (f n (T x) / (n : ℝ)) := ENNReal.ofReal_add hb hd
  have hzero : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))) atTop (nhds 0) := by
    have hreal0 : Filter.Tendsto (fun n : ℕ => f 1 x / (((n + 1 : ℕ)) : ℝ)) atTop
        (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Filter.Tendsto (fun n : ℕ => f 1 x * ((1 : ℝ) / ((n : ℝ) + 1))) atTop
          (nhds 0) := by
        have h := Filter.Tendsto.const_mul (f 1 x) h1
        rw [mul_zero] at h
        exact h
      have heq : (fun n : ℕ => f 1 x / (((n + 1 : ℕ)) : ℝ))
          = fun n : ℕ => f 1 x * ((1 : ℝ) / ((n : ℝ) + 1)) := by
        funext n
        have hc : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [hc, mul_one_div]
      rw [heq]
      exact h2
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hreal0
    rw [ENNReal.ofReal_zero] at hcont
    exact hcont
  have hLHS : kingmanLiminf f x
      = Filter.liminf
        (fun n : ℕ => ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))) atTop := by
    have h := (Filter.liminf_nat_add
      (fun n : ℕ => ENNReal.ofReal (f n x / (n : ℝ))) 1).symm
    unfold kingmanLiminf
    exact h
  have hRHS : Filter.liminf (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
        + ENNReal.ofReal (f n (T x) / (n : ℝ))) atTop
      = kingmanLiminf f (T x) := by
    have hz := ENNReal.liminf_add_of_left_tendsto_zero hzero
      (fun n : ℕ => ENNReal.ofReal (f n (T x) / (n : ℝ)))
    unfold kingmanLiminf
    exact hz
  calc kingmanLiminf f x
      = Filter.liminf
        (fun n : ℕ => ENNReal.ofReal (f (n + 1) x / (((n + 1 : ℕ)) : ℝ))) atTop := hLHS
    _ ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (f 1 x / (((n + 1 : ℕ)) : ℝ))
          + ENNReal.ofReal (f n (T x) / (n : ℝ))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hpt)
    _ = kingmanLiminf f (T x) := hRHS

/-- N8e: the liminf rate is invariant a.e. -/
private theorem kingmanLiminf_ae_comp_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hle : ∀ x, kingmanLiminf f x ≤ kingmanLiminf f (T x)) :
    ∀ᵐ x ∂μ, kingmanLiminf f (T x) = kingmanLiminf f x := by
  have h := ae_comp_eq_of_le_comp hT (kingmanLiminf_measurable f hf_meas) hle
  filter_upwards [h] with x hx
  exact hx

/-- N8f: the liminf rate is constant along orbits a.e. -/
private theorem kingmanLiminf_ae_iterate_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (he : ∀ᵐ x ∂μ, kingmanLiminf f (T x) = kingmanLiminf f x) :
    ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x := by
  have hq : ∀ k, QuasiMeasurePreserving (T^[k]) μ μ :=
    fun k => (hT.iterate k).quasiMeasurePreserving
  have hall : ∀ᵐ x ∂μ, ∀ k,
      kingmanLiminf f (T ((T^[k]) x)) = kingmanLiminf f ((T^[k]) x) :=
    MeasureTheory.ae_all_iff.mpr (fun k => MeasureTheory.QuasiMeasurePreserving.ae (hq k) he)
  filter_upwards [hall] with x hx
  intro k
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih =>
    have h1 := hx k
    change kingmanLiminf f ((T^[k.succ]) x) = kingmanLiminf f x
    rw [Function.iterate_succ_apply', h1, ih]

/-- N10/N11: bad set where averages exceed `ℓ + ε` on all of `Icc 1 N`. -/
private def kingmanBadSet {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) : Set α :=
  {y | ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y}

/-- Measurability of the bad sets. -/
private theorem kingmanBadSet_measurable
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (hf_meas : ∀ n, Measurable (f n)) (ε : ℝ) (N : ℕ) :
    MeasurableSet (kingmanBadSet f ε N) := by
  have hℓ : Measurable (fun y => (kingmanLiminf f y).toReal) :=
    (kingmanLiminf_measurable f hf_meas).ennreal_toReal
  unfold kingmanBadSet
  have heq : {y | ∀ n : ℕ, 1 ≤ n → n ≤ N →
        (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y}
      = ⋂ (n : ℕ) (_ : 1 ≤ n) (_ : n ≤ N),
        {y | (n : ℝ) * ((kingmanLiminf f y).toReal + ε) < f n y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_const.mul (hℓ.add measurable_const)) (hf_meas n)

/-- N10: Steele's pointwise bound from the greedy decomposition. -/
private theorem kingman_pointwise_bound
    {α : Type*} [MeasurableSpace α]
    {T : α → α} (f : ℕ → α → ℝ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x))
    (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (x : α)
    (hinv : ∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal) :
    ∀ M : ℕ, f M x ≤ (M : ℝ) * ((kingmanLiminf f x).toReal + ε)
      + birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) M x
      + ∑ k ∈ Finset.range M, (if M ≤ k + N then f 1 ((T^[k]) x) else 0) := by
  have hc : 0 ≤ (kingmanLiminf f x).toReal + ε :=
    add_nonneg ENNReal.toReal_nonneg hε
  classical
  have hFsub : ∀ k m n, (fun k n => f n ((T^[k]) x)) k (m + n)
      ≤ (fun k n => f n ((T^[k]) x)) k m
        + (fun k n => f n ((T^[k]) x)) (k + m) n := by
    intro k m n
    have h := hf_subadd m n ((T^[k]) x)
    have e : (T^[m]) ((T^[k]) x) = (T^[k + m]) x := by
      rw [← Function.iterate_add_apply T m k x, Nat.add_comm m k]
    rw [e] at h
    exact h
  have hgood : ∀ k, ¬ (fun k => (T^[k]) x ∈ kingmanBadSet f ε N) k →
      ∃ n, 1 ≤ n ∧ n ≤ N ∧ (fun k n => f n ((T^[k]) x)) k n
        ≤ (n : ℝ) * ((kingmanLiminf f x).toReal + ε) := by
    intro k hk
    simp only [kingmanBadSet, Set.mem_ofPred_eq] at hk
    rw [not_forall] at hk
    obtain ⟨n, hn⟩ := hk
    rw [not_imp, not_imp] at hn
    obtain ⟨h1n, hnN, hcon⟩ := hn
    refine ⟨n, h1n, hnN, ?_⟩
    have hle : f n ((T^[k]) x)
        ≤ (n : ℝ) * ((kingmanLiminf f ((T^[k]) x)).toReal + ε) :=
      not_lt.mp hcon
    rw [hinv k] at hle
    exact hle
  have hmain := greedy_block_bound (fun k n => f n ((T^[k]) x))
    (fun k n => hf_nn n _) (fun k => hf_zero _) hFsub
    (fun k => (T^[k]) x ∈ kingmanBadSet f ε N)
    ((kingmanLiminf f x).toReal + ε) hc N hgood
  intro M
  have hM := hmain M
  have e0 : f M ((T^[0]) x) = f M x := by rw [Function.iterate_zero_apply]
  have hsum1 : (∑ k ∈ Finset.range M,
        (if (T^[k]) x ∈ kingmanBadSet f ε N then f 1 ((T^[k]) x) else 0))
      = birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) M x := by
    unfold birkhoffSum
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (T^[k]) x ∈ kingmanBadSet f ε N
    · rw [ite_eq_left hk, Set.indicator_of_mem hk]
    · rw [ite_eq_right hk, Set.indicator_of_notMem hk]
  rw [← e0, ← hsum1]
  exact hM

/-- N11: the bad sets shrink and their `f 1`-integrals tend to zero. -/
private theorem tendsto_setIntegral_kingmanBad
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (ε : ℝ) (hε : 0 < ε)
    (hfin : ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤) :
    Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop (nhds 0) := by
  have hAmeas : ∀ N, MeasurableSet (kingmanBadSet f ε N) :=
    fun N => kingmanBadSet_measurable f hf_meas ε N
  have hanti : Antitone (kingmanBadSet f ε) := by
    intro a b hab y hy
    simp only [kingmanBadSet, Set.mem_ofPred_eq] at hy ⊢
    intro n h1n hnN
    exact hy n h1n (le_trans hnN hab)
  have hsub : (⋂ N, kingmanBadSet f ε N) ⊆ {x | kingmanLiminf f x = ⊤} := by
    intro y hy
    simp only [Set.mem_iInter, kingmanBadSet, Set.mem_ofPred_eq] at hy
    by_contra hcon
    simp only [Set.mem_ofPred_eq] at hcon
    have hlt : kingmanLiminf f y < ⊤ := lt_of_le_of_ne le_top hcon
    have hLy : kingmanLiminf f y = ENNReal.ofReal ((kingmanLiminf f y).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hlt)).symm
    have hpos : (0 : ℝ) < (kingmanLiminf f y).toReal + ε :=
      add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε
    have hlt2 : kingmanLiminf f y
        < ENNReal.ofReal ((kingmanLiminf f y).toReal + ε) := by
      conv_lhs => rw [hLy]
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith [hε])
    unfold kingmanLiminf at hlt2
    have hfreq : ∃ᶠ n in atTop,
        ENNReal.ofReal (f n y / (n : ℝ))
          < ENNReal.ofReal ((kingmanLiminf f y).toReal + ε) :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt2
    obtain ⟨n, hn_lt, hn1⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    have hreal : f n y / (n : ℝ) < (kingmanLiminf f y).toReal + ε :=
      (ENNReal.ofReal_lt_ofReal_iff'.mp hn_lt).1
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfin' : f n y < (n : ℝ) * ((kingmanLiminf f y).toReal + ε) := by
      have h := (div_lt_iff₀ hnR).mp hreal
      rwa [mul_comm] at h
    have hmem := hy n n hn1 (le_refl n)
    exact lt_irrefl _ (lt_trans hfin' hmem)
  have htop0 : μ {x | kingmanLiminf f x = ⊤} = 0 := by
    have hcompl : {x | kingmanLiminf f x = ⊤} = {x | kingmanLiminf f x < ⊤}ᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt, top_le_iff]
    have hae : ∀ᵐ x ∂μ, x ∈ {x | kingmanLiminf f x < ⊤} := hfin
    have h0 : μ ({x | kingmanLiminf f x < ⊤}ᶜ) = 0 := MeasureTheory.ae_iff.mp hae
    rwa [← hcompl] at h0
  have hinter0 : μ (⋂ N, kingmanBadSet f ε N) = 0 :=
    le_antisymm (le_trans (measure_mono hsub) (le_of_eq htop0)) zero_le
  have hlim : Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop
      (nhds (∫ y in ⋂ N, kingmanBadSet f ε N, f 1 y ∂μ)) :=
    tendsto_setIntegral_of_antitone hAmeas hanti ⟨0, (hf_int 1).integrableOn⟩
  rw [setIntegral_measure_zero _ hinter0] at hlim
  exact hlim

/-- N12: upper bound `f M x / M ≤ ℓ x + 4ε` eventually a.e. -/
private theorem kingman_upper
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x))
    (hLinv : ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x)
    (hfin : ∀ᵐ x ∂μ, kingmanLiminf f x < ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ x ∂μ, ∀ᶠ M in atTop,
      f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε := by
  intro ε hε
  have hN6 := ae_tendsto_comp_iterate_div_nat hT (hf_meas 1) (hf_int 1) (hf_nn 1)
  have hOmega : ∀ᵐ x ∂μ, (∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal)
      ∧ Tendsto (fun m : ℕ => f 1 ((T^[m]) x) / (m : ℝ)) atTop (nhds 0) := by
    filter_upwards [hLinv, hN6] with x hx1 hx2
    exact ⟨fun k => by rw [hx1 k], hx2⟩
  set Bad : Set α := {x | (∀ k, (kingmanLiminf f ((T^[k]) x)).toReal
      = (kingmanLiminf f x).toReal)
    ∧ Tendsto (fun m : ℕ => f 1 ((T^[m]) x) / (m : ℝ)) atTop (nhds 0)
    ∧ ¬ ∀ᶠ M in atTop, f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε}
    with hBad
  have hBadsub : ∀ N : ℕ, 1 ≤ N →
      Bad ⊆ BirkhoffWanted.DickSet T ((kingmanBadSet f ε N).indicator (f 1)) ε := by
    intro N hN x hx
    simp only [hBad, Set.mem_ofPred_eq] at hx
    obtain ⟨hinv, hlim0, hbad⟩ := hx
    by_contra hxD
    rw [BirkhoffWanted.dick_mem] at hxD
    obtain ⟨q, hεq, hq2⟩ := exists_rat_btwn (show ε < 2 * ε by linarith)
    have hnotfreq : ¬ ∀ N' : ℕ, ∃ n : ℕ, N' ≤ n ∧ (n : ℝ) * (q : ℝ)
        < birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x := by
      intro hall
      exact hxD ⟨q, hεq, hall⟩
    rw [not_forall] at hnotfreq
    obtain ⟨N', hN'⟩ := hnotfreq
    have hSbound : ∀ n : ℕ, N' ≤ n →
        birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (2 * ε) := by
      intro n hn
      have hle : birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (q : ℝ) := by
        by_contra hcon
        rw [not_le] at hcon
        exact hN' ⟨n, hn, hcon⟩
      calc birkhoffSum T ((kingmanBadSet f ε N).indicator (f 1)) n x
          ≤ (n : ℝ) * (q : ℝ) := hle
        _ ≤ (n : ℝ) * (2 * ε) :=
            mul_le_mul_of_nonneg_left (le_of_lt hq2) (Nat.cast_nonneg _)
    have hδ : (0 : ℝ) < ε / (N : ℝ) := by
      have hNR : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
      exact div_pos hε hNR
    have hev1 : ∀ᶠ m in atTop, f 1 ((T^[m]) x) / (m : ℝ) < ε / (N : ℝ) :=
      hlim0.eventually (gt_mem_nhds hδ)
    have hev2 : ∀ᶠ m in atTop,
        (f 1 ((T^[m]) x) / (m : ℝ) < ε / (N : ℝ)) ∧ 1 ≤ m :=
      hev1.and (eventually_ge_atTop 1)
    obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hev2
    have htail : ∀ᶠ M in atTop, (∑ k ∈ Finset.range M,
        (if M ≤ k + N then f 1 ((T^[k]) x) else 0)) ≤ ε * (M : ℝ) := by
      filter_upwards [eventually_ge_atTop (K₀ + N)] with M hM
      have hIco_sub : Finset.Ico (M - N) M ⊆ Finset.range M := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_range]
        omega
      have hvanish : ∀ k ∈ Finset.range M, k ∉ Finset.Ico (M - N) M →
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0) = 0 := by
        intro k hk_range hk_nmem
        rw [Finset.mem_range] at hk_range
        rw [Finset.mem_Ico] at hk_nmem
        have hneg : ¬ M ≤ k + N := by omega
        rw [ite_eq_right hneg]
      have hsub_eq := Finset.sum_subset hIco_sub hvanish
      have hif_eq : (∑ k ∈ Finset.Ico (M - N) M,
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0))
          = ∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        have hMkN : M ≤ k + N := by omega
        rw [ite_eq_left hMkN]
      have hsum_eq : (∑ k ∈ Finset.range M,
          (if M ≤ k + N then f 1 ((T^[k]) x) else 0))
          = ∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x) :=
        hsub_eq.symm.trans hif_eq
      rw [hsum_eq]
      have hterm : ∀ k ∈ Finset.Ico (M - N) M,
          f 1 ((T^[k]) x) ≤ (ε / (N : ℝ)) * (M : ℝ) := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk0 : K₀ ≤ k := by omega
        have ⟨hrat, hk1⟩ := hK₀ k hk0
        have hkR : (0 : ℝ) < (k : ℝ) := by
          exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk1
        have h1 : f 1 ((T^[k]) x) ≤ (ε / (N : ℝ)) * (k : ℝ) :=
          le_of_lt ((div_lt_iff₀ hkR).mp hrat)
        have h2 : (ε / (N : ℝ)) * (k : ℝ) ≤ (ε / (N : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast le_of_lt hk.2) (le_of_lt hδ)
        exact le_trans h1 h2
      have hcard : (Finset.Ico (M - N) M).card ≤ N := by
        rw [Nat.card_Ico]
        omega
      have hBnn : (0 : ℝ) ≤ (ε / (N : ℝ)) * (M : ℝ) :=
        mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
      have hNR : (N : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN)
      calc (∑ k ∈ Finset.Ico (M - N) M, f 1 ((T^[k]) x))
          ≤ (Finset.Ico (M - N) M).card • ((ε / (N : ℝ)) * (M : ℝ)) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((Finset.Ico (M - N) M).card : ℝ) * ((ε / (N : ℝ)) * (M : ℝ)) :=
            nsmul_eq_mul _ _
        _ ≤ (N : ℝ) * ((ε / (N : ℝ)) * (M : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hBnn
        _ = ε * (M : ℝ) := by
            rw [← mul_assoc, mul_div_cancel₀ _ hNR]
    have hN10 := kingman_pointwise_bound f hf_nn hf_zero hf_subadd ε (le_of_lt hε)
      N x hinv
    have hfinal : ∀ᶠ M in atTop,
        f M x / (M : ℝ) ≤ (kingmanLiminf f x).toReal + 4 * ε := by
      filter_upwards [eventually_ge_atTop N', eventually_ge_atTop 1, htail] with M
        hMN' hM1 htailM
      have hS := hSbound M hMN'
      have hMR : (0 : ℝ) < (M : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM1
      rw [div_le_iff₀ hMR]
      have hN10M := hN10 M
      linarith [hN10M, hS, htailM]
    exact hbad hfinal
  have hmeasD : ∀ N : ℕ, 1 ≤ N →
      μ Bad ≤ ENNReal.ofReal ((∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε) := by
    intro N hN
    have hsub := hBadsub N hN
    have hAmeas : MeasurableSet (kingmanBadSet f ε N) :=
      kingmanBadSet_measurable f hf_meas ε N
    have hφm : Measurable ((kingmanBadSet f ε N).indicator (f 1)) :=
      (hf_meas 1).indicator hAmeas
    have hφi : Integrable ((kingmanBadSet f ε N).indicator (f 1)) μ :=
      (hf_int 1).indicator hAmeas
    have hφnn : ∀ x, 0 ≤ ((kingmanBadSet f ε N).indicator (f 1)) x :=
      Set.indicator_nonneg (fun a _ => hf_nn 1 a)
    have hN3 := measure_kingmanDick_le hT hφm hφi hφnn hε
    have hint : (∫ x, (kingmanBadSet f ε N).indicator (f 1) x ∂μ)
        = ∫ y in kingmanBadSet f ε N, f 1 y ∂μ :=
      integral_indicator hAmeas
    rw [hint] at hN3
    exact le_trans (measure_mono hsub) hN3
  have hN11 : Tendsto (fun N : ℕ => ∫ y in kingmanBadSet f ε N, f 1 y ∂μ) atTop
      (nhds 0) :=
    tendsto_setIntegral_kingmanBad f hf_meas hf_int ε hε hfin
  have htoZero : Tendsto
      (fun N : ℕ => ENNReal.ofReal ((∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε))
      atTop (nhds 0) := by
    have hdiv : Tendsto (fun N : ℕ => (∫ y in kingmanBadSet f ε N, f 1 y ∂μ) / ε)
        atTop (nhds (0 / ε)) :=
      hN11.div_const ε
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 / ε)).comp hdiv
    rw [zero_div, ENNReal.ofReal_zero] at hcomp
    exact hcomp
  have hBad0 : μ Bad = 0 := by
    have hle : μ Bad ≤ 0 := by
      apply ge_of_tendsto htoZero
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact hmeasD N hN
    exact le_antisymm hle zero_le
  have hBadmem : ∀ᵐ x ∂μ, x ∉ Bad := measure_eq_zero_iff_ae_notMem.mp hBad0
  filter_upwards [hOmega, hBadmem] with x hxO hxB
  by_contra hcon
  apply hxB
  rw [hBad]
  exact ⟨hxO.1, hxO.2, hcon⟩

/-- N13: convergence under everywhere hypotheses. -/
private theorem kingman_core
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nn : ∀ n x, 0 ≤ f n x)
    (hf_zero : ∀ x, f 0 x = 0)
    (hf_subadd : ∀ m n x, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / (n : ℝ)) atTop (nhds (g x)) := by
  have hN5a : ∀ n x, f n x ≤ birkhoffSum T (f 1) n x :=
    le_birkhoffSum_one f hf_zero hf_subadd
  have hN5b : ∀ n, ∫ x, f n x ∂μ ≤ (n : ℝ) * ∫ x, f 1 x ∂μ :=
    integral_le_mul_integral_one hT f hf_int hN5a
  have hLmeas : Measurable (kingmanLiminf f) := kingmanLiminf_measurable f hf_meas
  obtain ⟨hLbound, hfin⟩ :=
    kingmanLiminf_lintegral_le f hf_meas hf_int hf_nn hf_zero hN5b
  have hsub : ∀ x, kingmanLiminf f x ≤ kingmanLiminf f (T x) :=
    kingmanLiminf_le_comp f hf_nn hf_zero hf_subadd
  have hLinv1 : ∀ᵐ x ∂μ, kingmanLiminf f (T x) = kingmanLiminf f x :=
    kingmanLiminf_ae_comp_eq hT f hf_meas hsub
  have hLinv : ∀ᵐ x ∂μ, ∀ k, kingmanLiminf f ((T^[k]) x) = kingmanLiminf f x :=
    kingmanLiminf_ae_iterate_eq hT f hLinv1
  refine ⟨fun x => (kingmanLiminf f x).toReal, ?_, ?_, ?_⟩
  · apply integrable_toReal_of_lintegral_ne_top hLmeas.aemeasurable
    exact ne_of_lt (lt_of_le_of_lt hLbound ENNReal.ofReal_lt_top)
  · filter_upwards [hLinv1] with x hx
    exact congrArg ENNReal.toReal hx
  · have hup : ∀ j : ℕ, ∀ᵐ x ∂μ, ∀ᶠ M in atTop,
        f M x / (M : ℝ)
          ≤ (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) :=
      fun j => kingman_upper hT f hf_meas hf_int hf_nn hf_zero hf_subadd hLinv hfin
        (1 / ((j : ℝ) + 1)) (by positivity)
    have hupall : ∀ᵐ x ∂μ, ∀ j : ℕ, ∀ᶠ M in atTop,
        f M x / (M : ℝ)
          ≤ (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) :=
      MeasureTheory.ae_all_iff.mpr hup
    filter_upwards [hfin, hupall] with x hxfin hxup
    have hLy : kingmanLiminf f x = ENNReal.ofReal ((kingmanLiminf f x).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hxfin)).symm
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rcases lt_or_ge a' 0 with ha0 | ha0
      · exact Filter.Eventually.of_forall (fun M => lt_of_lt_of_le ha0
          (div_nonneg (hf_nn M x) (Nat.cast_nonneg _)))
      · have h0ℓ : (0 : ℝ) < (kingmanLiminf f x).toReal :=
          lt_of_le_of_lt ha0 ha'
        have hlt : ENNReal.ofReal a' < kingmanLiminf f x := by
          conv_rhs => rw [hLy]
          exact (ENNReal.ofReal_lt_ofReal_iff h0ℓ).mpr ha'
        unfold kingmanLiminf at hlt
        have hev := Filter.eventually_lt_of_lt_liminf hlt
        filter_upwards [hev] with M hM
        exact (ENNReal.ofReal_lt_ofReal_iff'.mp hM).1
    · intro a' ha'
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (a' - (kingmanLiminf f x).toReal) / 4 by linarith)
      have hj' : (kingmanLiminf f x).toReal + 4 * (1 / ((j : ℝ) + 1)) < a' := by
        linarith [hj]
      filter_upwards [hxup j] with M hM
      exact lt_of_le_of_lt hM hj'

/--
Nonnegative integrable cocycle: invariant a.e. limit of `fₙ/n`.
Source: J. F. C. Kingman, "The Ergodic Theory of Subadditive Stochastic Processes", Journal of the
Royal Statistical Society Series B 30 (1968), 499–510, DOI 10.1111/j.2517-6161.1968.tb00749.x.

Proves `Wanted` entry `kingman_subadditive`.
-/
theorem kingman_subadditive
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    (f : ℕ → α → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_int : ∀ n, Integrable (f n) μ)
    (hf_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hf_zero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hf_subadd : ∀ m n, ∀ᵐ x ∂μ, f (m + n) x ≤ f m x + f n ((T^[m]) x)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, g (T x) = g x) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / (n : ℝ)) atTop (nhds (g x)) := by
  obtain ⟨f', hf'_meas, hf'_ae, hf'_nn, hf'_zero, hf'_subadd⟩ :=
    kingman_reduce_everywhere hT f hf_meas hf_nonneg hf_zero hf_subadd
  have hf'_int : ∀ n, Integrable (f' n) μ := fun n => (hf_int n).congr (hf'_ae n).symm
  obtain ⟨g, hg_int, hg_inv, hg_lim⟩ :=
    kingman_core hT f' hf'_meas hf'_int hf'_nn hf'_zero hf'_subadd
  refine ⟨g, hg_int, hg_inv, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, f' n x = f n x := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact hf'_ae n
  filter_upwards [hg_lim, hall] with x hx hallx
  exact hx.congr (fun n => by rw [hallx n])

end MathlibExt.Dynamics.Ergodic.KingmanWanted
end
