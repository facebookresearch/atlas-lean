/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Dynamics.Ergodic.BirkhoffWanted

open MeasureTheory

/-!
# Birkhoff pointwise ergodic theorem

Proves the ergodic-case Birkhoff pointwise ergodic theorem for real integrable functions.
-/

/-- Hopf maximal ergodic theorem: the integral of `f` over the maximal set is nonnegative. -/
theorem maximal_ergodic
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T f n x}, f x ∂μ := by
  have hne : ∀ n : ℕ, (Finset.range (n + 1)).Nonempty :=
    fun n => ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
  set M : ℕ → α → ℝ := fun n => (Finset.range (n + 1)).sup' (hne n)
    (fun k : ℕ => fun x : α => birkhoffSum T f k x) with hMdef
  have hS_meas : ∀ k : ℕ, Measurable (fun x : α => birkhoffSum T f k x) := by
    intro k
    unfold birkhoffSum
    apply Finset.measurable_sum
    intro j _
    exact hf.comp ((hT.iterate j).measurable)
  have hM_meas : ∀ n : ℕ, Measurable (M n) := by
    intro n
    rw [hMdef]
    exact Finset.measurable_sup' _ (fun k _ => hS_meas k)
  have hS_int : ∀ k : ℕ, Integrable (fun x : α => birkhoffSum T f k x) μ := by
    intro k
    unfold birkhoffSum
    apply integrable_finsetSum
    intro j _
    exact (hT.iterate j).integrable_comp_of_integrable hfi
  have hM_pt : ∀ (n : ℕ) (x : α), M n x =
      (Finset.range (n + 1)).sup' (hne n) (fun k => birkhoffSum T f k x) := by
    intro n x
    have hmeq : M n x = ((Finset.range (n + 1)).sup' (hne n)
      (fun k : ℕ => fun x : α => birkhoffSum T f k x)) x := by rw [hMdef]
    rw [hmeq, Finset.sup'_apply]
  have hS0 : ∀ x : α, birkhoffSum T f 0 x = 0 := fun x => birkhoffSum_zero_apply T f x
  have hM_nonneg : ∀ (n : ℕ) (x : α), 0 ≤ M n x := by
    intro n x
    rw [hM_pt n x, ← hS0 x]
    exact Finset.le_sup' (fun k => birkhoffSum T f k x)
      (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  have hM_int : ∀ n : ℕ, Integrable (M n) μ := by
    intro n
    apply Integrable.mono' (g := fun x => ∑ k ∈ Finset.range (n + 1), ‖birkhoffSum T f k x‖)
    · apply integrable_finsetSum
      intro k _
      exact (hS_int k).norm
    · exact (hM_meas n).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hM_nonneg n x), hM_pt n x]
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (hne n)
        (fun k => birkhoffSum T f k x)
      rw [hkeq]
      calc birkhoffSum T f k x ≤ ‖birkhoffSum T f k x‖ := le_abs_self _
        _ ≤ ∑ k ∈ Finset.range (n + 1), ‖birkhoffSum T f k x‖ :=
          Finset.single_le_sum (f := fun j => ‖birkhoffSum T f j x‖)
            (fun j _ => norm_nonneg _) hk
  have hkey : ∀ (n : ℕ) (x : α), 0 < M n x → M n x ≤ f x + M n (T x) := by
    intro n x hx
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (hne n)
      (fun k => birkhoffSum T f k x)
    have hk0 : k ≠ 0 := by
      intro hkk
      subst hkk
      rw [hM_pt n x, hkeq, hS0 x] at hx
      exact lt_irrefl 0 hx
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    subst hj
    have hkmem : j + 1 ∈ Finset.range (n + 1) := hk
    have hjmem : j ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range] at hkmem ⊢
      omega
    have hS : birkhoffSum T f (j + 1) x = f x + birkhoffSum T f j (T x) :=
      birkhoffSum_succ_apply' T f j x
    have hle : birkhoffSum T f j (T x) ≤ M n (T x) := by
      rw [hM_pt n (T x)]
      exact Finset.le_sup' (fun k => birkhoffSum T f k (T x)) hjmem
    rw [hM_pt n x, hkeq, hS]
    gcongr
  have hper : ∀ n : ℕ, 0 ≤ ∫ x in {x | 0 < M n x}, f x ∂μ := by
    intro n
    have hA_meas : MeasurableSet {x : α | 0 < M n x} :=
      measurableSet_lt measurable_const (hM_meas n)
    have hMT_int : Integrable (fun x => M n (T x)) μ :=
      hT.integrable_comp_of_integrable (hM_int n)
    have hM_on : IntegrableOn (M n) {x : α | 0 < M n x} μ := (hM_int n).integrableOn
    have hMT_on : IntegrableOn (fun x => M n (T x)) {x : α | 0 < M n x} μ :=
      hMT_int.integrableOn
    have hf_on : IntegrableOn f {x : α | 0 < M n x} μ := hfi.integrableOn
    have hsub_on : IntegrableOn (fun x => M n x - M n (T x)) {x : α | 0 < M n x} μ :=
      hM_on.sub hMT_on
    have hmono : ∫ x in {x : α | 0 < M n x}, (M n x - M n (T x)) ∂μ
        ≤ ∫ x in {x : α | 0 < M n x}, f x ∂μ := by
      apply setIntegral_mono_on hsub_on hf_on hA_meas
      intro x hx
      have h := hkey n x hx
      linarith
    have hsplit : (∫ x in {x : α | 0 < M n x}, (M n x - M n (T x)) ∂μ)
        = (∫ x in {x : α | 0 < M n x}, M n x ∂μ)
          - (∫ x in {x : α | 0 < M n x}, M n (T x) ∂μ) := by
      have h := integral_sub (μ := μ.restrict {x : α | 0 < M n x}) hM_on hMT_on
      simpa using h
    have hMeq : (∫ x in {x : α | 0 < M n x}, M n x ∂μ) = (∫ x, M n x ∂μ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxle : M n x ≤ 0 := le_of_not_gt hx
      have hnn := hM_nonneg n x
      have hzero : M n x = 0 := le_antisymm hxle hnn
      exact hzero
    have hMTle : (∫ x in {x : α | 0 < M n x}, M n (T x) ∂μ)
        ≤ (∫ x, M n (T x) ∂μ) := by
      apply setIntegral_le_integral hMT_int
      filter_upwards with x
      exact hM_nonneg n (T x)
    have hTMeq : (∫ x, M n (T x) ∂μ) = (∫ x, M n x ∂μ) := by
      have hmap : Measure.map T μ = μ := hT.map_eq
      have hint : ∫ y, M n y ∂(Measure.map T μ) = ∫ x, M n (T x) ∂μ :=
        integral_map (μ := μ) (φ := T) (f := M n) hT.measurable.aemeasurable
          ((hM_meas n).aestronglyMeasurable (μ := Measure.map T μ))
      rw [hmap] at hint
      exact hint.symm
    linarith
  have hmono : Monotone (fun n => {x : α | 0 < M n x}) := by
    intro n m hnm x hx
    change 0 < M m x
    have hsub : Finset.range (n + 1) ⊆ Finset.range (m + 1) := by
      intro y hy
      rw [Finset.mem_range] at hy ⊢
      omega
    have hle : M n x ≤ M m x := by
      rw [hM_pt n x]
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (hne n)
        (fun k => birkhoffSum T f k x)
      rw [hkeq, hM_pt m x]
      exact Finset.le_sup' (fun k => birkhoffSum T f k x) (hsub hk)
    exact lt_of_lt_of_le hx hle
  have hmeas : ∀ n : ℕ, MeasurableSet ((fun n => {x : α | 0 < M n x}) n) :=
    fun n => measurableSet_lt measurable_const (hM_meas n)
  have hunion : (⋃ n, {x : α | 0 < M n x}) = {x | ∃ n, 0 < birkhoffSum T f n x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro ⟨n, hn⟩
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (hne n)
        (fun k => birkhoffSum T f k x)
      rw [hM_pt n x] at hn
      rw [hkeq] at hn
      exact ⟨k, hn⟩
    · intro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [hM_pt n x]
      exact lt_of_lt_of_le hn (Finset.le_sup' (fun k => birkhoffSum T f k x)
        (Finset.mem_range.mpr (Nat.lt_succ_self n)))
  have hlim := tendsto_setIntegral_of_monotone (E := ℝ) (f := f)
    (fun n => hmeas n) hmono hfi.integrableOn
  rw [hunion] at hlim
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hper)

/-- Maximal divergence set where some Birkhoff sum exceeds `n * q` for a rational `q > c`. -/
noncomputable def DickSet {α : Type*} [MeasurableSpace α]
    (T : α → α) (g : α → ℝ) (c : ℝ) : Set α :=
  ⋃ (q : ℚ) (_ : c < (q : ℝ)), ⋂ (N : ℕ), ⋃ (n : ℕ) (_ : N ≤ n),
    {x | (n : ℝ) * (q : ℝ) < birkhoffSum T g n x}

/-- The maximal divergence set is measurable. -/
theorem dick_measurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {g : α → ℝ} (hg : Measurable g) (c : ℝ) :
    MeasurableSet (DickSet T g c) := by
  unfold DickSet
  apply MeasurableSet.iUnion; intro q
  apply MeasurableSet.iUnion; intro _
  apply MeasurableSet.iInter; intro N
  apply MeasurableSet.iUnion; intro n
  apply MeasurableSet.iUnion; intro _
  apply measurableSet_lt measurable_const
  unfold birkhoffSum
  apply Finset.measurable_sum
  intro j _
  exact hg.comp ((hT.iterate j).measurable)

/-- Membership in the maximal divergence set, unfolded. -/
theorem dick_mem {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ} {x : α} :
    x ∈ DickSet T g c ↔ ∃ q : ℚ, c < (q : ℝ) ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (n : ℝ) * (q : ℝ) < birkhoffSum T g n x := by
  unfold DickSet
  simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, exists_prop]

private theorem large_n_pos (d B : ℝ) (hd : 0 < d) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < (n : ℝ) * d + B := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((-B + 1) / d)
  refine ⟨K, fun n hn => ?_⟩
  have hnR : (K : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hKd : -B + 1 < (K : ℝ) * d := by
    have := (div_lt_iff₀ hd).mp hK
    linarith
  have hnd : (K : ℝ) * d ≤ (n : ℝ) * d :=
    mul_le_mul_of_nonneg_right hnR hd.le
  linarith

private theorem dick_fwd {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ}
    {x : α} (hx : x ∈ DickSet T g c) : T x ∈ DickSet T g c := by
  rw [dick_mem] at hx ⊢
  obtain ⟨q, hcq, hfreq⟩ := hx
  obtain ⟨q', hcq', hqq'⟩ := exists_rat_btwn hcq
  refine ⟨q', hcq', fun N => ?_⟩
  have hd : (0 : ℝ) < (q : ℝ) - (q' : ℝ) := sub_pos.mpr hqq'
  obtain ⟨K, hK⟩ := large_n_pos ((q : ℝ) - (q' : ℝ)) ((q : ℝ) - g x) hd
  obtain ⟨m, hmN, hm⟩ := hfreq (N + K + 1)
  have hm0 : m ≠ 0 := by
    intro hmm
    subst hmm
    simp [birkhoffSum_zero_apply] at hm
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  subst hj
  have hjN : N ≤ j := by omega
  have hjK : K ≤ j := by omega
  refine ⟨j, hjN, ?_⟩
  have hS : birkhoffSum T g (j + 1) x = g x + birkhoffSum T g j (T x) :=
    birkhoffSum_succ_apply' T g j x
  have hpos := hK j hjK
  have hm' : ((j + 1 : ℕ) : ℝ) * (q : ℝ) < birkhoffSum T g (j + 1) x := hm
  push_cast at hm'
  have hST : birkhoffSum T g j (T x) = birkhoffSum T g (j + 1) x - g x := by
    rw [hS]; ring
  rw [hST]
  nlinarith [hm', hpos, hS]

private theorem dick_bwd {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ}
    {x : α} (hx : T x ∈ DickSet T g c) : x ∈ DickSet T g c := by
  rw [dick_mem] at hx ⊢
  obtain ⟨q, hcq, hfreq⟩ := hx
  obtain ⟨q', hcq', hqq'⟩ := exists_rat_btwn hcq
  refine ⟨q', hcq', fun N => ?_⟩
  have hd : (0 : ℝ) < (q : ℝ) - (q' : ℝ) := sub_pos.mpr hqq'
  obtain ⟨K, hK⟩ := large_n_pos ((q : ℝ) - (q' : ℝ)) (g x - (q' : ℝ)) hd
  obtain ⟨n, hnNK, hn⟩ := hfreq (N + K)
  have hnK : K ≤ n := by omega
  have hnN : N ≤ n + 1 := by omega
  refine ⟨n + 1, hnN, ?_⟩
  have hS : birkhoffSum T g (n + 1) x = g x + birkhoffSum T g n (T x) :=
    birkhoffSum_succ_apply' T g n x
  have hpos := hK n hnK
  rw [hS]
  push_cast
  nlinarith [hn, hpos, hS]

/-- The maximal divergence set is invariant under `T`. -/
theorem dick_inv {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ} :
    T ⁻¹' DickSet T g c = DickSet T g c := by
  ext y
  rw [Set.mem_preimage]
  exact ⟨fun h => dick_bwd h, fun h => dick_fwd h⟩

private theorem dick_step_iff {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ} {x : α} :
    (T x ∈ DickSet T g c) ↔ (x ∈ DickSet T g c) := ⟨dick_bwd, dick_fwd⟩

/-- The maximal divergence set is invariant under iterates of `T`. -/
theorem dick_iter {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ} (k : ℕ) (x : α) :
    (T^[k] x ∈ DickSet T g c) ↔ (x ∈ DickSet T g c) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact Iff.trans (ih (T x)) dick_step_iff

/-- Birkhoff sums of the truncated function agree with shifted sums inside an invariant set. -/
theorem dick_sum_in {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ}
    (D : Set α)
    (hiter : ∀ (k : ℕ) (x : α), (T^[k] x ∈ D) ↔ (x ∈ D))
    (hfun : α → ℝ) (hfundef : ∀ y : α, hfun y = D.indicator (fun y => g y - c) y)
    (x : α) (hx : x ∈ D) (n : ℕ) :
    birkhoffSum T hfun n x = birkhoffSum T g n x - n * c := by
  unfold birkhoffSum
  have hterm : ∀ k ∈ Finset.range n, hfun (T^[k] x) = g (T^[k] x) - c := by
    intro k _
    rw [hfundef]
    exact Set.indicator_of_mem ((hiter k x).mpr hx) _
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- Birkhoff sums of the truncated function vanish outside an invariant set. -/
theorem dick_sum_out {α : Type*} [MeasurableSpace α]
    {T : α → α} {g : α → ℝ} {c : ℝ}
    (D : Set α)
    (hiter : ∀ (k : ℕ) (x : α), (T^[k] x ∈ D) ↔ (x ∈ D))
    (hfun : α → ℝ) (hfundef : ∀ y : α, hfun y = D.indicator (fun y => g y - c) y)
    (x : α) (hx : x ∉ D) (n : ℕ) :
    birkhoffSum T hfun n x = 0 := by
  unfold birkhoffSum
  apply Finset.sum_eq_zero
  intro k _
  rw [hfundef]
  apply Set.indicator_of_notMem
  exact fun hmem => hx ((hiter k x).mp hmem)

private theorem dick_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [IsProbabilityMeasure μ]
    {T : α → α} (hT : Ergodic T μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g μ)
    {c : ℝ} (hc : ∫ y, g y ∂μ < c) :
    μ (DickSet T g c) = 0 := by
  have hmp := hT.toMeasurePreserving
  have hDmeas : MeasurableSet (DickSet T g c) := dick_measurable hmp hg c
  have hinv : T ⁻¹' DickSet T g c = DickSet T g c := dick_inv
  have hiter : ∀ (k : ℕ) (x : α),
      (T^[k] x ∈ DickSet T g c) ↔ (x ∈ DickSet T g c) := fun k x => dick_iter k x
  set hfun : α → ℝ := (DickSet T g c).indicator (fun y => g y - c) with hfundef
  have hm_h : Measurable hfun := Measurable.indicator (hg.sub measurable_const) hDmeas
  have hi_h : Integrable hfun μ :=
    Integrable.indicator (hgi.sub (integrable_const c)) hDmeas
  have hfundef' : ∀ y : α,
      hfun y = (DickSet T g c).indicator (fun y => g y - c) y := fun y => rfl
  have hsum_in : ∀ x : α, x ∈ DickSet T g c → ∀ n : ℕ,
      birkhoffSum T hfun n x = birkhoffSum T g n x - n * c :=
    fun x hx n => dick_sum_in _ hiter hfun hfundef' x hx n
  have hsum_out : ∀ x : α, x ∉ DickSet T g c → ∀ n : ℕ,
      birkhoffSum T hfun n x = 0 :=
    fun x hx n => dick_sum_out _ hiter hfun hfundef' x hx n
  have hE : {x | ∃ n, 0 < birkhoffSum T hfun n x} = DickSet T g c := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := hx
      by_contra hxD
      rw [hsum_out x hxD n] at hn
      exact lt_irrefl 0 hn
    · intro hx
      have hxD : x ∈ DickSet T g c := hx
      rw [dick_mem] at hx
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
  have hmax := maximal_ergodic hmp hm_h hi_h
  rw [hE] at hmax
  have hcongr : ∫ x in DickSet T g c, hfun x ∂μ = ∫ x in DickSet T g c, (g x - c) ∂μ := by
    apply setIntegral_congr_ae hDmeas
    filter_upwards with x
    intro hx
    exact Set.indicator_of_mem hx _
  rw [hcongr] at hmax
  rcases hT.toPreErgodic.measure_self_or_compl_eq_zero hDmeas.nullMeasurableSet
      (Filter.Eventually.of_forall (fun x => by rw [hinv])) with h0 | hc0
  · exact h0
  · exfalso
    have hgc : Integrable (fun y => g y - c) μ := hgi.sub (integrable_const c)
    have hadd := integral_add_compl hDmeas hgc
    have hcompl : ∫ x in (DickSet T g c)ᶜ, (g x - c) ∂μ = 0 :=
      setIntegral_measure_zero _ hc0
    have hint : ∫ x, (g x - c) ∂μ = (∫ y, g y ∂μ) - c := by
      rw [integral_sub hgi (integrable_const c)]
      congr 1
      rw [integral_const, probReal_univ, one_smul]
    have hDeq : ∫ x in DickSet T g c, (g x - c) ∂μ = (∫ y, g y ∂μ) - c := by
      linarith [hadd, hcompl, hint]
    linarith

private theorem upper_of_not_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} {g : α → ℝ}
    {x : α} (hx : ∀ r : ℚ, (∫ y, g y ∂μ) < (r : ℝ) → x ∉ DickSet T g (r : ℝ))
    {b : ℝ} (hb : ∫ y, g y ∂μ < b) :
    ∀ᶠ n in Filter.atTop, birkhoffAverage ℝ T g n x < b := by
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hb
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc2
  have hxD : x ∉ DickSet T g (c : ℝ) := hx c hc1
  rw [dick_mem, not_exists] at hxD
  have hxq : ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (n : ℝ) * (q : ℝ) < birkhoffSum T g n x :=
    not_and.mp (hxD q) hq1
  rw [not_forall] at hxq
  obtain ⟨N, hN⟩ := hxq
  rw [not_exists] at hN
  have hball : ∀ n : ℕ, N ≤ n → birkhoffSum T g n x ≤ (n : ℝ) * (q : ℝ) := by
    intro n hn
    exact le_of_not_gt ((not_and.mp (hN n)) hn)
  rw [Filter.eventually_atTop]
  refine ⟨N ⊔ 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans le_sup_left hn
  have hn1 : 1 ≤ n := le_trans le_sup_right hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
    have h1n : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hnpos : ((n : ℝ)) ≠ 0 := ne_of_gt hnR
  have hle := hball n hnN
  have havg : birkhoffAverage ℝ T g n x = (n : ℝ)⁻¹ * birkhoffSum T g n x := by
    unfold birkhoffAverage
    rw [smul_eq_mul]
  rw [havg]
  calc (n : ℝ)⁻¹ * birkhoffSum T g n x
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hnR.le)
    _ = (q : ℝ) := inv_mul_cancel_left₀ hnpos _
    _ < b := hq2

private theorem birkhoff_measurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : Ergodic T μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n => birkhoffAverage ℝ T g n x) Filter.atTop
      (nhds (∫ y, g y ∂μ)) := by
  have hnullU : ∀ q : ℚ, μ (if (∫ y, g y ∂μ) < (q : ℝ) then DickSet T g (q : ℝ) else ∅) = 0 := by
    intro q
    by_cases h : (∫ y, g y ∂μ) < (q : ℝ)
    · rw [ite_eq_left h]
      exact dick_null hT hg hgi h
    · rw [ite_eq_right h]
      exact measure_empty
  have hnullL : ∀ q : ℚ, μ (if (∫ y, -g y ∂μ) < (q : ℝ) then DickSet T (-g) (q : ℝ) else ∅) =
      0 := by
    intro q
    by_cases h : (∫ y, -g y ∂μ) < (q : ℝ)
    · rw [ite_eq_left h]
      exact dick_null hT hg.neg hgi.neg h
    · rw [ite_eq_right h]
      exact measure_empty
  have hU : ∀ᵐ x ∂μ, ∀ q : ℚ, x ∉ (if (∫ y, g y ∂μ) < (q : ℝ) then DickSet T g (q : ℝ) else ∅) := by
    rw [ae_all_iff]
    intro q
    exact measure_eq_zero_iff_ae_notMem.mp (hnullU q)
  have hL : ∀ᵐ x ∂μ, ∀ q : ℚ, x ∉
      (if (∫ y, -g y ∂μ) < (q : ℝ) then DickSet T (-g) (q : ℝ) else ∅) := by
    rw [ae_all_iff]
    intro q
    exact measure_eq_zero_iff_ae_notMem.mp (hnullL q)
  filter_upwards [hU.and hL] with x hx
  obtain ⟨hxU, hxL⟩ := hx
  have hxU' : ∀ r : ℚ, (∫ y, g y ∂μ) < (r : ℝ) → x ∉ DickSet T g (r : ℝ) := by
    intro r hr
    have h := hxU r
    rwa [ite_eq_left hr] at h
  have hxL' : ∀ r : ℚ, (∫ y, -g y ∂μ) < (r : ℝ) → x ∉ DickSet T (-g) (r : ℝ) := by
    intro r hr
    have h := hxL r
    rwa [ite_eq_left hr] at h
  rw [tendsto_order]
  constructor
  · intro a ha
    have hineg : ∫ y, -g y ∂μ = -∫ y, g y ∂μ := integral_neg g
    have hb : ∫ y, -g y ∂μ < -a := by
      rw [hineg]
      exact neg_lt_neg ha
    have hev := upper_of_not_mem (g := -g) hxL' hb
    filter_upwards [hev] with n hn
    rw [birkhoffAverage_neg_apply] at hn
    exact neg_lt_neg_iff.mp hn
  · intro b hb
    exact upper_of_not_mem hxU' hb

/--
If `μ` is a probability measure, `T` is ergodic measure-preserving, and `g : α → ℝ` is integrable,
then `birkhoffAverage ℝ T g n x` converges for `μ`-a.e. `x` to `∫ y, g y ∂μ`. Source: G. D.
Birkhoff, Proc. Natl. Acad. Sci. USA 17 (1931); Walters, Intro to Ergodic Theory; Lean states
ergodic case for ℝ-valued integrable functions while general theorem gives conditional expectation
onto invariant σ-algebra.

Proves `Wanted` entry `birkhoff_pointwise_ergodic`.
-/
theorem birkhoff_pointwise_ergodic
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : Ergodic T μ)
    {g : α → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n => birkhoffAverage ℝ T g n x) Filter.atTop
      (nhds (∫ y, g y ∂μ)) := by
  set g' : α → ℝ := AEStronglyMeasurable.mk g hg.aestronglyMeasurable with hg'def
  have hm_g' : Measurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hi_g' : Integrable g' μ := hg.congr hae
  have hint_eq : ∫ y, g' y ∂μ = ∫ y, g y ∂μ := integral_congr_ae hae.symm
  have hqmp := hT.toMeasurePreserving.quasiMeasurePreserving
  have havg : ∀ n : ℕ, birkhoffAverage ℝ T g n =ᵐ[μ] birkhoffAverage ℝ T g' n :=
    fun n => Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hqmp hae n
  have hmain := birkhoff_measurable hT hm_g' hi_g'
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffAverage ℝ T g n x = birkhoffAverage ℝ T g' n x := by
    rw [ae_all_iff]
    intro n
    exact havg n
  filter_upwards [hmain, hall] with x hx hallx
  rw [← hint_eq]
  exact hx.congr (fun n => (hallx n).symm)

end MathlibExt.Dynamics.Ergodic.BirkhoffWanted
end
