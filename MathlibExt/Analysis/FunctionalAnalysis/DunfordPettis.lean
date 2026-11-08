/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
import MathlibExt.Analysis.FunctionalAnalysis.EberleinSmulian
import MathlibExt.Analysis.FunctionalAnalysis.MilmanPettis

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted

open Filter Topology

/-- Weakly compact sets are norm bounded. -/
private theorem dpc_isBounded_preimage_toWeakSpace_of_isCompact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set (WeakSpace ℝ X)} (hK : IsCompact K) :
    Bornology.IsBounded ((toWeakSpace ℝ X) ⁻¹' K) := by
  have hpt : ∀ φ : StrongDual ℝ X, ∃ C, ∀ x : ↥((toWeakSpace ℝ X) ⁻¹' K),
      ‖NormedSpace.inclusionInDoubleDual ℝ X x.val φ‖ ≤ C := by
    intro φ
    have hcont : Continuous (fun k : WeakSpace ℝ X => φ ((toWeakSpace ℝ X).symm k)) :=
      WeakBilin.eval_continuous _ φ
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun x => hC _ x.property⟩
  obtain ⟨M, hM⟩ := banach_steinhaus
    (g := fun x : ↥((toWeakSpace ℝ X) ⁻¹' K) =>
      NormedSpace.inclusionInDoubleDual ℝ X x.val) hpt
  refine isBounded_iff_forall_norm_le.mpr ⟨max M 0, fun x hx => ?_⟩
  refine NormedSpace.norm_le_dual_bound ℝ x (le_max_right _ _) (fun φ => ?_)
  calc ‖φ x‖ = ‖NormedSpace.inclusionInDoubleDual ℝ X x φ‖ := by
        rw [NormedSpace.dual_def ℝ X x φ]
    _ ≤ ‖NormedSpace.inclusionInDoubleDual ℝ X x‖ * ‖φ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ max M 0 * ‖φ‖ := by
        gcongr
        exact (hM ⟨x, hx⟩).trans (le_max_left _ _)

/-- Bidual half of Grothendieck's criterion. -/
private theorem dpc_closure_image_inclusionInDoubleDualWeak_subset_range_of_approx
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {S : Set (WeakSpace ℝ X)}
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : Set (WeakSpace ℝ X), IsCompact K ∧
      ∀ x : X, toWeakSpace ℝ X x ∈ S →
        ∃ y : X, toWeakSpace ℝ X y ∈ K ∧ ‖x - y‖ ≤ ε) :
    closure (NormedSpace.inclusionInDoubleDualWeak ℝ X '' S) ⊆
      Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ X) := by
  set J := NormedSpace.inclusionInDoubleDualWeak ℝ X with hJdef
  have hJeval : ∀ (w : WeakSpace ℝ X) (φ : StrongDual ℝ X),
      (J w) φ = φ ((toWeakSpace ℝ X).symm w) := fun w φ =>
    NormedSpace.inclusionInDoubleDualWeak_apply_apply ℝ X w φ
  have hJstrong : ∀ w : WeakSpace ℝ X, WeakDual.toStrongDual (J w) =
      NormedSpace.inclusionInDoubleDual ℝ X ((toWeakSpace ℝ X).symm w) := by
    intro w
    apply ContinuousLinearMap.ext
    intro φ
    rw [WeakDual.toStrongDual_apply, hJeval, NormedSpace.dual_def]
  -- Covering: for each ε, the closure lies in `J '' K + B ε`.
  have hcov : ∀ ε : ℝ, 0 < ε → ∀ Φ : WeakDual ℝ (StrongDual ℝ X),
      Φ ∈ closure (J '' S) → ∃ y : X, ∃ b : WeakDual ℝ (StrongDual ℝ X),
        Φ = J (toWeakSpace ℝ X y) + b ∧ ‖WeakDual.toStrongDual b‖ ≤ ε := by
    intro ε hε Φ hΦ
    obtain ⟨K, hKcomp, happrox⟩ := h ε hε
    set B := WeakDual.toStrongDual ⁻¹'
      (Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) ε) with hBdef
    have hBcomp : IsCompact B :=
      WeakDual.isCompact_closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) ε
    have hclosed : IsClosed (J '' K + B) :=
      (hKcomp.image J.continuous |>.add hBcomp).isClosed
    have hsub : J '' S ⊆ J '' K + B := by
      rintro Ψ ⟨w, hwS, rfl⟩
      obtain ⟨x, rfl⟩ := (toWeakSpace ℝ X).surjective w
      obtain ⟨y, hyK, hxy⟩ := happrox x hwS
      have hdecomp : J (toWeakSpace ℝ X x) =
          J (toWeakSpace ℝ X y) +
            (J (toWeakSpace ℝ X x) - J (toWeakSpace ℝ X y)) := by
        abel
      rw [hdecomp]
      refine Set.add_mem_add ⟨toWeakSpace ℝ X y, hyK, rfl⟩ ?_
      have hlin : J (toWeakSpace ℝ X x) - J (toWeakSpace ℝ X y) =
          J (toWeakSpace ℝ X (x - y)) := by
        rw [← map_sub J _ _, map_sub (toWeakSpace ℝ X) _ _]
      have heq : WeakDual.toStrongDual
            (J (toWeakSpace ℝ X x) - J (toWeakSpace ℝ X y)) =
          NormedSpace.inclusionInDoubleDual ℝ X (x - y) := by
        rw [hlin, hJstrong, LinearEquiv.symm_apply_apply]
      rw [hBdef, Set.mem_preimage, heq]
      have hle : ‖NormedSpace.inclusionInDoubleDual ℝ X (x - y)‖ ≤ ε :=
        (NormedSpace.double_dual_bound ℝ X _).trans hxy
      have hmem : NormedSpace.inclusionInDoubleDual ℝ X (x - y) ∈
          Metric.closedBall 0 ε := by
        have h1 : dist (NormedSpace.inclusionInDoubleDual ℝ X (x - y)) 0 ≤ ε := by
          have h2 : dist (NormedSpace.inclusionInDoubleDual ℝ X (x - y)) 0 =
              ‖NormedSpace.inclusionInDoubleDual ℝ X (x - y) - 0‖ :=
            dist_eq_norm (NormedSpace.inclusionInDoubleDual ℝ X (x - y)) 0
          have h3 : NormedSpace.inclusionInDoubleDual ℝ X (x - y) - 0 =
              NormedSpace.inclusionInDoubleDual ℝ X (x - y) := by
            abel
          rw [h2, h3]
          exact hle
        exact Metric.mem_closedBall.mpr h1
      exact hmem
    have hmem : Φ ∈ J '' K + B := closure_minimal hsub hclosed hΦ
    obtain ⟨j, hjK, b, hbB, hdecomp⟩ := Set.mem_add.mp hmem
    obtain ⟨k, hkK, rfl⟩ := hjK
    refine ⟨(toWeakSpace ℝ X).symm k, b, ?_, ?_⟩
    · rw [LinearEquiv.apply_symm_apply]
      exact hdecomp.symm
    · rw [hBdef, Set.mem_preimage] at hbB
      have hb1 : dist (WeakDual.toStrongDual b) 0 ≤ ε :=
        Metric.mem_closedBall.mp hbB
      have hb2 : dist (WeakDual.toStrongDual b) 0 =
          ‖WeakDual.toStrongDual b - 0‖ :=
        dist_eq_norm (WeakDual.toStrongDual b) 0
      have hb3 : WeakDual.toStrongDual b - 0 = WeakDual.toStrongDual b := by
        abel
      rw [hb2, hb3] at hb1
      exact hb1
  -- Extract approximating sequences and pass to a norm limit.
  intro Φ hΦ
  have hε : ∀ n : ℕ, (0:ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose y hy using fun n => hcov _ (hε n) Φ hΦ
  choose b hb using hy
  -- `hb k : Φ = J (toWeakSpace (y k)) + b k ∧ ‖toStrongDual (b k)‖ ≤ 1/(k+1)`
  have hbnorm : ∀ k : ℕ,
      ‖WeakDual.toStrongDual (b k)‖ ≤ 1 / ((k : ℝ) + 1) :=
    fun k => (hb k).2
  have hdecomp : ∀ k : ℕ, Φ = J (toWeakSpace ℝ X (y k)) + b k :=
    fun k => (hb k).1
  have hval : ∀ (k : ℕ) (φ : StrongDual ℝ X),
      φ (y k) = Φ φ - WeakDual.toStrongDual (b k) φ := by
    intro k φ
    have hkk : WeakDual.toStrongDual Φ
        = WeakDual.toStrongDual (J (toWeakSpace ℝ X (y k)))
          + WeakDual.toStrongDual (b k) := by
      rw [hdecomp k, map_add]
    have hkkφ := congrArg (fun F : StrongDual ℝ (StrongDual ℝ X) => F φ) hkk
    rw [add_apply, hJstrong, LinearEquiv.symm_apply_apply,
      NormedSpace.dual_def] at hkkφ
    have hkk2 : Φ φ = φ (y k) + WeakDual.toStrongDual (b k) φ := hkkφ
    linarith
  have hbd : ∀ (k : ℕ) (φ : StrongDual ℝ X),
      ‖WeakDual.toStrongDual (b k) φ‖ ≤ (1 / ((k : ℝ) + 1)) * ‖φ‖ := by
    intro k φ
    calc ‖WeakDual.toStrongDual (b k) φ‖
        ≤ ‖WeakDual.toStrongDual (b k)‖ * ‖φ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / ((k : ℝ) + 1)) * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (hbnorm k) (norm_nonneg _)
  have hlim2 : Filter.Tendsto (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have hmul : Filter.Tendsto (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)))
        atTop (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hmul
  have hanti : ∀ {m n : ℕ}, m ≤ n →
      (1:ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hcauchy : CauchySeq y := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 2 * (1 / ((N : ℝ) + 1))) ?_ hlim2
    intro n m N hNn hNm
    rw [dist_eq_norm]
    have hnm : ∀ φ : StrongDual ℝ X,
        ‖φ (y n - y m)‖ ≤ (2 * (1 / ((N : ℝ) + 1))) * ‖φ‖ := by
      intro φ
      have hdiff : φ (y n - y m)
          = WeakDual.toStrongDual (b m) φ - WeakDual.toStrongDual (b n) φ := by
        rw [map_sub, hval n φ, hval m φ]
        abel
      have g1 : (1/((m:ℝ)+1)) * ‖φ‖ ≤ (1/((N:ℝ)+1)) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (hanti hNm) (norm_nonneg _)
      have g2 : (1/((n:ℝ)+1)) * ‖φ‖ ≤ (1/((N:ℝ)+1)) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (hanti hNn) (norm_nonneg _)
      calc ‖φ (y n - y m)‖
          = ‖WeakDual.toStrongDual (b m) φ - WeakDual.toStrongDual (b n) φ‖ := by
            rw [hdiff]
        _ ≤ ‖WeakDual.toStrongDual (b m) φ‖ + ‖WeakDual.toStrongDual (b n) φ‖ :=
            norm_sub_le _ _
        _ ≤ (1/((m:ℝ)+1)) * ‖φ‖ + (1/((n:ℝ)+1)) * ‖φ‖ :=
            add_le_add (hbd m φ) (hbd n φ)
        _ ≤ (1/((N:ℝ)+1)) * ‖φ‖ + (1/((N:ℝ)+1)) * ‖φ‖ :=
            add_le_add g1 g2
        _ = (2 * (1/((N:ℝ)+1))) * ‖φ‖ := by ring
    exact NormedSpace.norm_le_dual_bound ℝ _ (by positivity) hnm
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : ∀ φ : StrongDual ℝ X, Φ φ = φ x := by
    intro φ
    have h1 : Filter.Tendsto (fun n => φ (y n)) atTop (𝓝 (φ x)) :=
      (φ.continuous.tendsto x).comp hx
    have hb0 : Filter.Tendsto (fun n => WeakDual.toStrongDual (b n) φ)
        atTop (𝓝 0) := by
      have hnorm : Filter.Tendsto (fun n => ‖WeakDual.toStrongDual (b n) φ‖)
          atTop (𝓝 0) := by
        have hmul : Filter.Tendsto (fun n : ℕ => (1/((n:ℝ)+1)) * ‖φ‖)
              atTop (𝓝 (0 * ‖φ‖)) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul
              tendsto_const_nhds
        have htop : Filter.Tendsto (fun n : ℕ => (1/((n:ℝ)+1)) * ‖φ‖)
              atTop (𝓝 0) := by
          simpa using hmul
        have hnn : ∀ᶠ n in atTop,
            (0:ℝ) ≤ ‖WeakDual.toStrongDual (b n) φ‖ :=
          Filter.Eventually.of_forall fun n => norm_nonneg _
        have hle : ∀ᶠ n in atTop,
            ‖WeakDual.toStrongDual (b n) φ‖ ≤ (1/((n:ℝ)+1)) * ‖φ‖ :=
          Filter.Eventually.of_forall fun n => hbd n φ
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          htop hnn hle
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    have h2 : Filter.Tendsto (fun n => φ (y n)) atTop (𝓝 (Φ φ)) := by
      have hsub : Filter.Tendsto (fun n => Φ φ - WeakDual.toStrongDual (b n) φ)
          atTop (𝓝 (Φ φ - 0)) := tendsto_const_nhds.sub hb0
      have heq : (fun n => φ (y n))
          = (fun n => Φ φ - WeakDual.toStrongDual (b n) φ) :=
        funext fun n => hval n φ
      rw [heq]
      simpa using hsub
    exact tendsto_nhds_unique h2 h1
  refine ⟨toWeakSpace ℝ X x, ?_⟩
  rw [← WeakDual.toStrongDual_inj]
  apply ContinuousLinearMap.ext
  intro φ
  rw [hJstrong, LinearEquiv.symm_apply_apply, NormedSpace.dual_def]
  change φ x = Φ φ
  exact (hlim φ).symm

/-- Grothendieck's criterion. -/
private theorem dpc_isCompact_closure_weakSpace_of_approx
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {S : Set (WeakSpace ℝ X)}
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : Set (WeakSpace ℝ X), IsCompact K ∧
      ∀ x : X, toWeakSpace ℝ X x ∈ S →
        ∃ y : X, toWeakSpace ℝ X y ∈ K ∧ ‖x - y‖ ≤ ε) :
    IsCompact (closure S) := by
  apply NormedSpace.isCompact_closure_of_isBounded
  · obtain ⟨K, hKcomp, happrox⟩ := h 1 one_pos
    have hbK := dpc_isBounded_preimage_toWeakSpace_of_isCompact hKcomp
    rw [isBounded_iff_forall_norm_le] at hbK
    obtain ⟨M, hM⟩ := hbK
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M + 1, fun x hx => ?_⟩
    obtain ⟨y, hyK, hxy⟩ := happrox x hx
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      _ ≤ M + 1 := add_le_add (hM y hyK) hxy
  · exact dpc_closure_image_inclusionInDoubleDualWeak_subset_range_of_approx h

/-- Closed balls of uniformly convex Banach spaces are relatively weakly compact. -/
private theorem dpc_isCompact_closure_toWeakSpace_closedBall
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [UniformConvexSpace H] [CompleteSpace H]
    (r : ℝ) :
    IsCompact (closure (toWeakSpace ℝ H '' Metric.closedBall 0 r)) := by
  apply NormedSpace.isCompact_closure_of_isBounded
  · rw [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective]
    exact Metric.isBounded_closedBall
  · intro Φ _
    obtain ⟨x, hx⟩ := MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted.milman_pettis
      (WeakDual.toStrongDual Φ)
    refine ⟨toWeakSpace ℝ H x, ?_⟩
    rw [← WeakDual.toStrongDual_inj]
    apply ContinuousLinearMap.ext
    intro φ
    have heval : (NormedSpace.inclusionInDoubleDualWeak ℝ H)
        (toWeakSpace ℝ H x) φ
        = φ ((toWeakSpace ℝ H).symm (toWeakSpace ℝ H x)) :=
      NormedSpace.inclusionInDoubleDualWeak_apply_apply ℝ H _ _
    rw [LinearEquiv.symm_apply_apply] at heval
    have heval2 : WeakDual.toStrongDual
        ((NormedSpace.inclusionInDoubleDualWeak ℝ H) (toWeakSpace ℝ H x)) φ
        = φ x := heval
    rw [heval2]
    exact (hx φ).symm

/-- The `L² → L¹` inclusion as a continuous linear map. -/
private noncomputable def dpcLpTwoToLpOneCLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 1 μ) :=
  LinearMap.mkContinuous
    { toFun := fun g => ((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)
      map_add' := fun g₁ g₂ => by
        change ((Lp.memLp (g₁ + g₂)).mono_exponent one_le_two).toLp (⇑(g₁ + g₂)) =
          ((Lp.memLp g₁).mono_exponent one_le_two).toLp (⇑g₁) +
            ((Lp.memLp g₂).mono_exponent one_le_two).toLp (⇑g₂)
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add g₁ g₂)
      map_smul' := fun c g => by
        change ((Lp.memLp (c • g)).mono_exponent one_le_two).toLp (⇑(c • g)) =
          c • ((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c g) }
    ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) (fun g => by
      have hmem : AEStronglyMeasurable (⇑g) μ := (Lp.memLp g).aestronglyMeasurable
      have hfin : eLpNorm (⇑g) 2 μ ≠ ⊤ := (Lp.memLp g).eLpNorm_lt_top.ne
      have hle : eLpNorm (⇑g) 1 μ ≤
          eLpNorm (⇑g) 2 μ *
            μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two hmem
      have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by
        rw [ENNReal.toReal_one, ENNReal.toReal_ofNat]
        norm_num
      have hMfin :
          μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ := by
        rw [hexp]
        exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)).ne
      have h2norm : ‖g‖ = (eLpNorm (⇑g) 2 μ).toReal := by
        conv_lhs => rw [← Lp.toLp_coeFn g (Lp.memLp g)]
        exact Lp.norm_toLp _ _
      calc ‖((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)‖
            = (eLpNorm (⇑g) 1 μ).toReal := Lp.norm_toLp _ _
          _ ≤ (eLpNorm (⇑g) 2 μ *
              μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hMfin) hle
          _ = (μ Set.univ).toReal ^ (1 / 2 : ℝ) * (eLpNorm (⇑g) 2 μ).toReal := by
              rw [ENNReal.toReal_mul, hexp, ← ENNReal.toReal_rpow, mul_comm]
          _ = (μ Set.univ).toReal ^ (1 / 2 : ℝ) * ‖g‖ := by rw [h2norm])

/-- CoeFn lemma. -/
private theorem dpcLpTwoToLpOneCLM_coeFn
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (g : Lp ℝ 2 μ) : ⇑(dpcLpTwoToLpOneCLM (μ := μ) g) =ᵐ[μ] ⇑g :=
  MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent one_le_two)

/-- Truncation approximants. -/
private theorem dpc_truncation_mem_closedBall_and_dist
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (v : Lp ℝ 1 μ) (C : NNReal) :
    ∃ G : Lp ℝ 2 μ,
      ‖G‖ ≤ measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ * (C : ℝ) ∧
      ‖v - dpcLpTwoToLpOneCLM (μ := μ) G‖ ≤
        (eLpNorm (({x | (↑C : ℝ≥0∞) ≤ ‖v x‖₊}).indicator ⇑v) 1 μ).toReal := by
  set A : Set α := {x | (↑C : ℝ≥0∞) ≤ ‖⇑v x‖₊} with hAdef
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const
      ((Lp.stronglyMeasurable v).measurable.nnnorm).coe_nnreal_ennreal
  set B : Set α := Aᶜ with hBdef
  have hBmeas : MeasurableSet B := hAmeas.compl
  have hAE : AEStronglyMeasurable (B.indicator ⇑v) μ :=
    (Lp.aestronglyMeasurable v).indicator hBmeas
  have hbnd : ∀ x, ‖B.indicator ⇑v x‖ ≤ (C : ℝ) := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx _]
      have hxA : x ∉ A := by simpa [hBdef] using hx
      rw [hAdef] at hxA
      have hxA' : ¬ (↑C : ℝ≥0∞) ≤ (‖⇑v x‖₊ : ℝ≥0∞) := hxA
      have hlt : (‖⇑v x‖₊ : ℝ≥0∞) < (C : ℝ≥0∞) := lt_of_not_ge hxA'
      have hltR : ‖⇑v x‖₊ < C := by exact_mod_cast hlt
      calc ‖⇑v x‖ = (‖⇑v x‖₊ : ℝ) := (coe_nnnorm (⇑v x)).symm
        _ ≤ (C : ℝ) := le_of_lt (by exact_mod_cast hltR)
    · rw [Set.indicator_of_notMem hx _]
      exact norm_zero.le.trans (by positivity)
  have hGmem : MemLp (B.indicator ⇑v) 2 μ :=
    MemLp.of_bound hAE _ (Filter.Eventually.of_forall hbnd)
  refine ⟨hGmem.toLp _, ?_, ?_⟩
  · have hfC : ∀ᵐ x ∂μ, ‖⇑(hGmem.toLp (B.indicator ⇑v)) x‖ ≤ (C : ℝ) := by
      filter_upwards [MemLp.coeFn_toLp hGmem] with x hx
      rw [hx]
      exact hbnd x
    exact Lp.norm_le_of_ae_bound (C := (C : ℝ)) (by positivity) hfC
  · have hAind : MemLp (A.indicator ⇑v) 1 μ := MemLp.indicator hAmeas.nullMeasurableSet (Lp.memLp v)
    have heq : v - dpcLpTwoToLpOneCLM (hGmem.toLp (B.indicator ⇑v)) =
        hAind.toLp _ := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub v (dpcLpTwoToLpOneCLM (hGmem.toLp (B.indicator ⇑v))),
        dpcLpTwoToLpOneCLM_coeFn (hGmem.toLp (B.indicator ⇑v)),
        MemLp.coeFn_toLp hGmem, MemLp.coeFn_toLp hAind] with x hx1 hx2 hx3 hx4
      rw [hx1, Pi.sub_apply, hx2, hx3, hx4]
      by_cases hxA : x ∈ A
      · have hxB : x ∉ B := by simpa [hBdef] using hxA
        rw [Set.indicator_of_notMem hxB _, sub_zero, Set.indicator_of_mem hxA _]
      · have hxB : x ∈ B := by simpa [hBdef] using hxA
        rw [Set.indicator_of_mem hxB _, Set.indicator_of_notMem hxA _, sub_self]
    rw [heq]
    exact (Lp.norm_toLp _ _).le

/-- Forward direction. -/
private theorem dpc_isCompact_closure_of_uniformIntegrable_Lp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {ι : Type*} {u : ι → Lp ℝ 1 μ}
    (hu : UniformIntegrable (fun i ↦ ⇑(u i)) 1 μ) :
    IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range u)) := by
  apply dpc_isCompact_closure_weakSpace_of_approx
  intro ε hε
  obtain ⟨C, hC⟩ := UniformIntegrable.spec one_ne_zero ENNReal.one_ne_top hu
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  have hCi : ∀ i, eLpNorm ({x | C ≤ ‖⇑(u i) x‖₊}.indicator ⇑(u i)) 1 μ ≤
      ENNReal.ofReal ε := fun i => hC i
  refine ⟨WeakSpace.map dpcLpTwoToLpOneCLM ''
      closure (toWeakSpace ℝ (Lp ℝ 2 μ) ''
        Metric.closedBall 0 (measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ * (C : ℝ))),
    (dpc_isCompact_closure_toWeakSpace_closedBall _).image
      (WeakSpace.map dpcLpTwoToLpOneCLM).continuous,
    fun x hxS => ?_⟩
  obtain ⟨z, ⟨i, rfl⟩, hzx⟩ := hxS
  have hxu : x = u i := ((toWeakSpace ℝ (Lp ℝ 1 μ)).injective hzx).symm
  obtain ⟨G, hGball, hGdist⟩ := dpc_truncation_mem_closedBall_and_dist (u i) C
  have hGin : G ∈ Metric.closedBall (0 : Lp ℝ 2 μ)
      (measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ * (C : ℝ)) := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hGball
  have hmem : toWeakSpace ℝ (Lp ℝ 2 μ) G ∈
      closure (toWeakSpace ℝ (Lp ℝ 2 μ) ''
        Metric.closedBall 0 (measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ * (C : ℝ))) :=
    subset_closure (Set.mem_image_of_mem _ hGin)
  have hmap : WeakSpace.map dpcLpTwoToLpOneCLM (toWeakSpace ℝ (Lp ℝ 2 μ) G) =
      toWeakSpace ℝ (Lp ℝ 1 μ) (dpcLpTwoToLpOneCLM G) :=
    WeakSpace.map_apply _ _
  subst hxu
  refine ⟨dpcLpTwoToLpOneCLM G, ⟨toWeakSpace ℝ (Lp ℝ 2 μ) G, hmem, hmap⟩, ?_⟩
  have hset : ({x | ((C : ℝ≥0∞)) ≤ ‖⇑(u i) x‖₊}) = {x | C ≤ ‖⇑(u i) x‖₊} := by
    ext x
    exact ENNReal.coe_le_coe
  have herr : (eLpNorm ((({x | (↑C : ℝ≥0∞) ≤ ‖⇑(u i) x‖₊}).indicator ⇑(u i))) 1 μ).toReal
      ≤ ε := by
    have h1 : eLpNorm (({x | (↑C : ℝ≥0∞) ≤ ‖⇑(u i) x‖₊}).indicator ⇑(u i)) 1 μ ≤
        ENNReal.ofReal ε := by
      rw [hset]
      exact hCi i
    exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hε) h1
  exact hGdist.trans herr

/-- Set integrals as elements of the dual of `L¹`. -/
private noncomputable def dpcSetIntegralL1CLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : Set α) :
    StrongDual ℝ (Lp ℝ 1 μ) :=
  L1.integralCLM.comp (LpToLpRestrictCLM α ℝ ℝ μ 1 s)

/-- Apply lemma. -/
private theorem dpcSetIntegralL1CLM_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : Set α)
    (v : Lp ℝ 1 μ) :
    dpcSetIntegralL1CLM (μ := μ) s v = ∫ x in s, v x ∂μ := by
  change L1.integralCLM (LpToLpRestrictCLM α ℝ ℝ μ 1 s v) = ∫ x in s, v x ∂μ
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s v)

/-- Sign split. -/
private theorem dpc_exists_subset_abs_setIntegral_ge_half
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : α → ℝ} (hv : StronglyMeasurable v) (hvi : Integrable v μ)
    {C : Set α} (hC : MeasurableSet C) :
    ∃ D : Set α, MeasurableSet D ∧ D ⊆ C ∧
      (1 / 2 : ℝ) * (∫ x in C, |v x| ∂μ) ≤ |∫ x in D, v x ∂μ| := by
  have hPm : MeasurableSet (C ∩ {x | 0 ≤ v x}) :=
    hC.inter (measurableSet_le measurable_const hv.measurable)
  have hQm : MeasurableSet (C ∩ {x | v x < 0}) :=
    hC.inter (measurableSet_lt hv.measurable measurable_const)
  have hdisj : Disjoint (C ∩ {x | 0 ≤ v x}) (C ∩ {x | v x < 0}) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, h1⟩ ⟨-, h2⟩
    have h1' : (0 : ℝ) ≤ v x := h1
    have h2' : v x < 0 := h2
    exact absurd (h1'.trans_lt h2') (lt_irrefl _)
  have hunion : (C ∩ {x | 0 ≤ v x}) ∪ (C ∩ {x | v x < 0}) = C := by
    have hAB : {x | (0 : ℝ) ≤ v x} ∪ {x | v x < 0} = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      by_cases h : 0 ≤ v x
      · have hm : x ∈ ({x | (0 : ℝ) ≤ v x} : Set α) := h
        exact Or.inl hm
      · have hm : x ∈ ({x | v x < 0} : Set α) := lt_of_not_ge h
        exact Or.inr hm
    rw [← Set.inter_union_distrib_left, hAB, Set.inter_univ]
  have habs : Integrable (fun x => |v x|) μ :=
    hvi.norm.congr (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (v x)).symm)
  have hsplit : ∫ x in C, |v x| ∂μ =
      (∫ x in C ∩ {x | 0 ≤ v x}, |v x| ∂μ) + ∫ x in C ∩ {x | v x < 0}, |v x| ∂μ := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union hdisj hQm habs.integrableOn habs.integrableOn
  have hPeq : ∫ x in C ∩ {x | 0 ≤ v x}, |v x| ∂μ
      = ∫ x in C ∩ {x | 0 ≤ v x}, v x ∂μ :=
    setIntegral_congr_fun hPm (fun x hx => by
      have h0 : (0 : ℝ) ≤ v x := hx.2
      rw [abs_of_nonneg h0])
  have hQeq : ∫ x in C ∩ {x | v x < 0}, |v x| ∂μ
      = -∫ x in C ∩ {x | v x < 0}, v x ∂μ := by
    have h1 : ∫ x in C ∩ {x | v x < 0}, |v x| ∂μ
        = ∫ x in C ∩ {x | v x < 0}, -v x ∂μ :=
      setIntegral_congr_fun hQm (fun x hx => by
        have h0 : v x < 0 := hx.2
        rw [abs_of_neg h0])
    rw [h1, integral_neg]
  have heq : ∫ x in C, |v x| ∂μ =
      (∫ x in C ∩ {x | 0 ≤ v x}, v x ∂μ)
        + (-∫ x in C ∩ {x | v x < 0}, v x ∂μ) := by
    rw [hsplit, hPeq, hQeq]
  by_cases hcase : (1 / 2 : ℝ) * (∫ x in C, |v x| ∂μ)
      ≤ ∫ x in C ∩ {x | 0 ≤ v x}, v x ∂μ
  · exact ⟨_, hPm, Set.inter_subset_left, hcase.trans (le_abs_self _)⟩
  · refine ⟨_, hQm, Set.inter_subset_left, ?_⟩
    push Not at hcase
    have hle : (1 / 2 : ℝ) * (∫ x in C, |v x| ∂μ)
        ≤ -∫ x in C ∩ {x | v x < 0}, v x ∂μ := by
      linarith
    exact hle.trans (neg_le_abs _)

/-- Subsequence with geometrically small measures relative to per-index moduli. -/
private theorem dpc_exists_seq_small_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : ℕ → Set α}
    (hμ : ∀ n, μ (s n) ≤ (4⁻¹ : ℝ≥0∞) ^ n)
    {δ : ℕ → ℝ≥0∞} (hδpos : ∀ x, 0 < δ x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ m n, m < n → μ (s (φ n)) ≤ (2⁻¹ : ℝ≥0∞) ^ (φ n + 1) * δ (φ m) := by
  have h42 : (4⁻¹ : ℝ≥0∞) = 2⁻¹ * 2⁻¹ := by
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  have hev : ∀ x : ℕ, ∀ᶠ y in atTop, x < y ∧ μ (s y) ≤ (2⁻¹ : ℝ≥0∞) ^ (y + 1) * δ x := by
    intro x
    have hgt : ∀ᶠ y in atTop, x < y := Filter.eventually_gt_atTop x
    have hsmall2 : ∀ᶠ y in atTop, (2⁻¹ : ℝ≥0∞) ^ y ≤ 2⁻¹ * δ x := by
      have hpos : (0 : ℝ≥0∞) < 2⁻¹ * δ x :=
        ENNReal.mul_pos (by simp) (ne_of_gt (hδpos x))
      have htend :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one
      exact (htend.eventually (Iio_mem_nhds hpos)).mono fun y hy => le_of_lt hy
    have hmeas : ∀ᶠ y in atTop, μ (s y) ≤ (2⁻¹ : ℝ≥0∞) ^ (y + 1) * δ x := by
      filter_upwards [hsmall2] with y hy
      calc μ (s y) ≤ (4⁻¹ : ℝ≥0∞) ^ y := hμ y
        _ = (2⁻¹ : ℝ≥0∞) ^ y * (2⁻¹ : ℝ≥0∞) ^ y := by rw [h42, mul_pow]
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ (y + 1) * δ x := by
            rw [pow_succ, mul_assoc]
            exact mul_le_mul_of_nonneg_left hy (by positivity)
    exact hgt.and hmeas
  obtain ⟨φ, _, hφr⟩ := exists_seq_of_forall_finset_exists (fun _ : ℕ => True)
    (fun x y => x < y ∧ μ (s y) ≤ (2⁻¹ : ℝ≥0∞) ^ (y + 1) * δ x)
    (fun σ _ => by
      obtain ⟨y, hy⟩ := ((Filter.eventually_all_finset σ).mpr fun x _ => hev x).exists
      exact ⟨y, trivial, hy⟩)
  exact ⟨φ, fun a b hab => (hφr a b hab).1, fun m n hmn => (hφr m n hmn).2⟩

/-- Disjointification. -/
private theorem dpc_exists_disjoint_of_small_sets
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} (hv : ∀ n, MemLp (v n) 1 μ)
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hμ : ∀ n, μ (s n) ≤ (4⁻¹ : ℝ≥0∞) ^ n)
    {η : ℝ} (hη : 0 < η)
    (hmass : ∀ n, η ≤ ∫ x in s n, |v n x| ∂μ) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ C : ℕ → Set α,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (Function.onFun Disjoint C) ∧
      ∀ j, η / 2 ≤ ∫ x in C j, |v (φ j) x| ∂μ := by
  have hδ : ∀ n, ∃ δ : ℝ≥0∞, δ > 0 ∧ ∀ t : Set α, MeasurableSet t → μ t ≤ δ →
      eLpNorm (t.indicator (v n)) 1 μ ≤ ENNReal.ofReal (η / 2) := by
    intro n
    obtain ⟨δ, hδpos, hδ⟩ := (hv n).eLpNorm_indicator_le le_rfl ENNReal.one_ne_top
      (ENNReal.ofReal_pos.mpr (half_pos hη))
    exact ⟨δ, hδpos, fun t ht => hδ t ht.nullMeasurableSet⟩
  choose δ hδ using hδ
  obtain ⟨φ, hφm, hφb⟩ := dpc_exists_seq_small_measure hμ (fun x => (hδ x).1)
  have hUmeas : ∀ j, MeasurableSet (⋃ l, s (φ (l + j + 1))) :=
    fun j => MeasurableSet.iUnion (fun l => hs _)
  have hgeom : (∑' m, (2⁻¹ : ℝ≥0∞) ^ (m + 1)) = 1 := by
    have h12 : ((1 : ℝ≥0∞) - 2⁻¹)⁻¹ = 2 := by
      rw [ENNReal.one_sub_inv_two, inv_inv]
    rw [ENNReal.tsum_geometric_add_one, h12]
    exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm ENNReal.top_ne_ofNat)
  have hUle : ∀ j, μ (⋃ l, s (φ (l + j + 1))) ≤ δ (φ j) := by
    intro j
    have hinj : Function.Injective (fun l => φ (l + j + 1)) := by
      intro a b hab
      have h2 := hφm.injective hab
      omega
    have hsum : (∑' l, (2⁻¹ : ℝ≥0∞) ^ (φ (l + j + 1) + 1)) ≤ 1 := by
      calc ∑' l, (2⁻¹ : ℝ≥0∞) ^ (φ (l + j + 1) + 1)
          ≤ ∑' m, (2⁻¹ : ℝ≥0∞) ^ (m + 1) :=
            ENNReal.tsum_comp_le_tsum_of_injective (f := fun l => φ (l + j + 1))
              hinj (fun m => (2⁻¹ : ℝ≥0∞) ^ (m + 1))
        _ = 1 := hgeom
    calc μ (⋃ l, s (φ (l + j + 1))) ≤ ∑' l, μ (s (φ (l + j + 1))) :=
          measure_iUnion_le _
      _ ≤ ∑' l, (2⁻¹ : ℝ≥0∞) ^ (φ (l + j + 1) + 1) * δ (φ j) :=
          ENNReal.tsum_le_tsum (fun l => hφb j (l + j + 1) (by omega))
      _ = (∑' l, (2⁻¹ : ℝ≥0∞) ^ (φ (l + j + 1) + 1)) * δ (φ j) :=
          ENNReal.tsum_mul_right
      _ ≤ 1 * δ (φ j) :=
          mul_le_mul_of_nonneg_right hsum (hδ (φ j)).1.le
      _ = δ (φ j) := one_mul _
  have habsI : ∀ n, Integrable (fun x => |v n x|) μ := fun n =>
    (memLp_one_iff_integrable.mp (hv n)).norm.congr
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (v n x)).symm)
  have hsmall : ∀ j,
      ∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), |v (φ j) x| ∂μ ≤ η / 2 := by
    intro j
    have hTmeas : MeasurableSet (s (φ j) ∩ ⋃ l, s (φ (l + j + 1))) :=
      (hs _).inter (hUmeas j)
    have hTle : μ (s (φ j) ∩ ⋃ l, s (φ (l + j + 1))) ≤ δ (φ j) :=
      (measure_mono Set.inter_subset_right).trans (hUle j)
    have hAE : AEStronglyMeasurable
        ((s (φ j) ∩ ⋃ l, s (φ (l + j + 1))).indicator (v (φ j))) μ :=
      ((hv (φ j)).aestronglyMeasurable).indicator hTmeas
    have e1 : eLpNorm ((s (φ j) ∩ ⋃ l, s (φ (l + j + 1))).indicator (v (φ j))) 1 μ
        = ∫⁻ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), ‖v (φ j) x‖ₑ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_enorm hAE, ← lintegral_indicator hTmeas]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change ‖(s (φ j) ∩ ⋃ l, s (φ (l + j + 1))).indicator (v (φ j)) x‖ₑ = _
      by_cases hx : x ∈ s (φ j) ∩ ⋃ l, s (φ (l + j + 1))
      · rw [Set.indicator_of_mem hx _, Set.indicator_of_mem hx _]
      · rw [Set.indicator_of_notMem hx _, Set.indicator_of_notMem hx _]
        simp
    have hint : Integrable (v (φ j))
        (μ.restrict (s (φ j) ∩ ⋃ l, s (φ (l + j + 1)))) :=
      (memLp_one_iff_integrable.mp (hv (φ j))).integrableOn
    have e2 : ∫⁻ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), ‖v (φ j) x‖ₑ ∂μ
        = ENNReal.ofReal
          (∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), ‖v (φ j) x‖ ∂μ) :=
      (ofReal_integral_norm_eq_lintegral_enorm hint).symm
    have h1 : ENNReal.ofReal
        (∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), |v (φ j) x| ∂μ)
        ≤ ENNReal.ofReal (η / 2) := by
      have hcongr : (∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), |v (φ j) x| ∂μ)
          = ∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), ‖v (φ j) x‖ ∂μ :=
        setIntegral_congr_fun hTmeas (fun x _ => (Real.norm_eq_abs _).symm)
      rw [hcongr, ← e2, ← e1]
      exact (hδ (φ j)).2 _ hTmeas hTle
    exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (half_pos hη))).mp h1
  have hsub : ∀ a b : ℕ, a < b →
      s (φ b) \ ⋃ l, s (φ (l + b + 1)) ⊆ ⋃ l, s (φ (l + a + 1)) := by
    intro a b hab x hx
    have hx2 : x ∈ s (φ b) := hx.1
    have heq : (b - a - 1) + a + 1 = b := by omega
    have hmem : x ∈ s (φ ((b - a - 1) + a + 1)) := by rw [heq]; exact hx2
    exact Set.mem_iUnion.mpr ⟨b - a - 1, hmem⟩
  have hunion2 : ∀ j, (s (φ j) \ ⋃ l, s (φ (l + j + 1)))
      ∪ (s (φ j) ∩ ⋃ l, s (φ (l + j + 1))) = s (φ j) := by
    intro j
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      by_cases hxU : x ∈ ⋃ l, s (φ (l + j + 1))
      · exact Or.inr ⟨hx, hxU⟩
      · exact Or.inl ⟨hx, hxU⟩
  have hdisj2 : ∀ j, Disjoint (s (φ j) \ ⋃ l, s (φ (l + j + 1)))
      (s (φ j) ∩ ⋃ l, s (φ (l + j + 1))) :=
    fun j => Set.disjoint_left.mpr (fun x hxC hxI => hxC.2 hxI.2)
  have hsplit : ∀ j, ∫ x in s (φ j), |v (φ j) x| ∂μ =
      (∫ x in s (φ j) \ ⋃ l, s (φ (l + j + 1)), |v (φ j) x| ∂μ)
        + ∫ x in s (φ j) ∩ ⋃ l, s (φ (l + j + 1)), |v (φ j) x| ∂μ := by
    intro j
    conv_lhs => rw [← hunion2 j]
    exact setIntegral_union (hdisj2 j) ((hs _).inter (hUmeas j))
      ((habsI (φ j)).integrableOn) ((habsI (φ j)).integrableOn)
  refine ⟨φ, hφm, fun j => s (φ j) \ ⋃ l, s (φ (l + j + 1)), ?_, ?_, ?_⟩
  · intro j
    exact (hs _).diff (hUmeas j)
  · intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact (Set.disjoint_left.mpr (fun x hxC hxU => hxC.2 hxU)).mono le_rfl
        (hsub a b h)
    · exact ((Set.disjoint_left.mpr (fun x hxC hxU => hxC.2 hxU)).mono le_rfl
        (hsub b a h)).symm
  · intro j
    have hle := hsmall j
    have hmassj := hmass (φ j)
    have hsp := hsplit j
    linarith

/-- Index extraction for the gliding hump (tail moduli plus subsequence). -/
private theorem dpc_gliding_hump_index
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : ℕ → α → ℝ} (hw : ∀ k, Integrable (w k) μ)
    {D : ℕ → Set α} (hDm : ∀ k, MeasurableSet (D k))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    {η : ℝ} (hη : 0 < η)
    (htend : ∀ A : Set α, MeasurableSet A →
      Filter.Tendsto (fun k ↦ ∫ x in A, w k x ∂μ) Filter.atTop (𝓝 0)) :
    ∃ N : ℕ → ℕ, ∃ j : ℕ → ℕ, StrictMono j ∧
      (∀ c, ∫ x in ⋃ k, D (N c + k), |w c x| ∂μ < η / 4) ∧
      ∀ m n, m < n → N (j m) ≤ j n ∧
        |∫ x in D (j m), w (j n) x ∂μ| ≤ (η / 8) * (1 / 2) ^ (j m) := by
  have habs : ∀ c, Integrable (fun x => |w c x|) μ := fun c =>
    (hw c).norm.congr
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (w c x)).symm)
  have hTmeas : ∀ N, MeasurableSet (⋃ k, D (N + k)) :=
    fun N => MeasurableSet.iUnion (fun k => hDm _)
  have hTanti : Antitone (fun N => ⋃ k, D (N + k)) := by
    intro a b hab x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have heq : a + (b - a + k) = b + k := by omega
    exact Set.mem_iUnion.mpr ⟨b - a + k, by rw [heq]; exact hk⟩
  have hinter : ⋂ N, (⋃ k, D (N + k)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨k0, hk0⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx 0)
    obtain ⟨k1, hk1⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx (k0 + 1))
    have hk0' : x ∈ D k0 := by simpa using hk0
    have hne : k0 ≠ k0 + 1 + k1 := by omega
    exact Set.disjoint_left.mp (hDdisj hne) hk0' hk1
  have hN : ∀ c, ∃ N, ∫ x in (⋃ k, D (N + k)), |w c x| ∂μ < η / 4 := by
    intro c
    have hfi : ∃ i, IntegrableOn (fun x => |w c x|) (⋃ k, D (i + k)) μ :=
      ⟨0, (habs c).integrableOn⟩
    have htend2 := tendsto_setIntegral_of_antitone
      (s := fun N => ⋃ k, D (N + k)) (fun k => hTmeas k) hTanti hfi
    rw [hinter, setIntegral_empty] at htend2
    have hpos : (0:ℝ) < η / 4 := by linarith
    obtain ⟨N, hN⟩ := (htend2.eventually (Metric.ball_mem_nhds 0 hpos)).exists
    rw [dist_zero_right] at hN
    have hnn : 0 ≤ ∫ x in ⋃ k, D (N + k), |w c x| ∂μ :=
      setIntegral_nonneg (hTmeas N) (fun x _ => abs_nonneg _)
    rw [Real.norm_of_nonneg hnn] at hN
    exact ⟨N, hN⟩
  choose N hN using hN
  have hev : ∀ x : ℕ, ∀ᶠ y in atTop,
      x < y ∧ N x ≤ y ∧ |∫ x_ in D x, w y x_ ∂μ| ≤ (η / 8) * (1 / 2) ^ x := by
    intro x
    have hgt : ∀ᶠ y in atTop, x < y := Filter.eventually_gt_atTop x
    have hge : ∀ᶠ y in atTop, N x ≤ y := Filter.eventually_ge_atTop (N x)
    have hpos : (0:ℝ) < (η / 8) * (1 / 2) ^ x :=
      mul_pos (by linarith) (pow_pos (by norm_num) _)
    have hev3 : ∀ᶠ y in atTop,
        |∫ x_ in D x, w y x_ ∂μ| ≤ (η / 8) * (1 / 2) ^ x := by
      have hmem := Metric.closedBall_mem_nhds (0:ℝ) hpos
      have hevY := (htend (D x) (hDm x)).eventually hmem
      refine hevY.mono fun y hy => ?_
      rw [dist_zero_right, Real.norm_eq_abs] at hy
      exact hy
    filter_upwards [hgt, hge, hev3] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨j, _, hjr⟩ := exists_seq_of_forall_finset_exists (fun _ : ℕ => True)
    (fun x y => x < y ∧ N x ≤ y ∧ |∫ x_ in D x, w y x_ ∂μ| ≤ (η / 8) * (1 / 2) ^ x)
    (fun σ _ => by
      obtain ⟨y, hy⟩ := ((Filter.eventually_all_finset σ).mpr fun x _ => hev x).exists
      exact ⟨y, trivial, hy⟩)
  exact ⟨N, j, fun a b hab => (hjr a b hab).1,
    fun c => hN c, fun m n hmn => (hjr m n hmn).2⟩

/-- Gliding hump. -/
private theorem dpc_false_of_gliding_hump
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : ℕ → α → ℝ} (hw : ∀ k, Integrable (w k) μ)
    {D : ℕ → Set α} (hDm : ∀ k, MeasurableSet (D k))
    (hDdisj : Pairwise (Function.onFun Disjoint D))
    {η : ℝ} (hη : 0 < η)
    (hmass : ∀ k, η ≤ |∫ x in D k, w k x ∂μ|)
    (htend : ∀ A : Set α, MeasurableSet A →
      Filter.Tendsto (fun k ↦ ∫ x in A, w k x ∂μ) Filter.atTop (𝓝 0)) :
    False := by
  obtain ⟨N, j, hjm, hNmod, hjrel⟩ :=
    dpc_gliding_hump_index hw hDm hDdisj hη htend
  have hDmeas : MeasurableSet (⋃ l, D (j l)) :=
    MeasurableSet.iUnion (fun l => hDm _)
  have hBmeas : ∀ m, MeasurableSet (⋃ k, D (j (m + 1 + k))) :=
    fun m => MeasurableSet.iUnion (fun k => hDm _)
  have hFmem : ∀ m, ∀ x, x ∈ (⋃ l ∈ Finset.range m, D (j l)) → ∃ l < m, x ∈ D (j l) := by
    intro m x hx
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hm, hxl⟩ := Set.mem_iUnion.mp hl
    exact ⟨l, Finset.mem_range.mp (Finset.mem_coe.mp hm), hxl⟩
  have hDstar : ∀ m, (⋃ l, D (j l))
      = (⋃ l ∈ Finset.range m, D (j l))
        ∪ (D (j m) ∪ ⋃ k, D (j (m + 1 + k))) := by
    intro m
    ext x
    constructor
    · intro hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
      rcases lt_trichotomy l m with h | h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr
          ⟨Finset.mem_coe.mpr (Finset.mem_range.mpr h), hl⟩⟩)
      · subst h
        exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l - m - 1, by
          rw [show m + 1 + (l - m - 1) = l by omega]; exact hl⟩))
    · intro hx
      rcases hx with hx | hx | hx
      · obtain ⟨l, -, hxl⟩ := hFmem m x hx
        exact Set.mem_iUnion.mpr ⟨l, hxl⟩
      · exact Set.mem_iUnion.mpr ⟨m, hx⟩
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨m + 1 + k, hk⟩
  have hFR : ∀ m, Disjoint (⋃ l ∈ Finset.range m, D (j l))
      (D (j m) ∪ ⋃ k, D (j (m + 1 + k))) := by
    intro m
    apply Set.disjoint_left.mpr
    intro x hxF hxR
    obtain ⟨l, hlm, hxl⟩ := hFmem m x hxF
    rcases hxR with hxmid | hxB
    · have hne : j l ≠ j m := fun h => ne_of_lt hlm (hjm.injective h)
      exact Set.disjoint_left.mp (hDdisj hne) hxl hxmid
    · obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxB
      have hne : j l ≠ j (m + 1 + k) := fun h =>
        ne_of_lt (lt_of_lt_of_le hlm (by omega : m ≤ m + 1 + k)) (hjm.injective h)
      exact Set.disjoint_left.mp (hDdisj hne) hxl hxk
  have hmidB : ∀ m, Disjoint (D (j m)) (⋃ k, D (j (m + 1 + k))) := by
    intro m
    apply Set.disjoint_left.mpr
    intro x hxmid hxB
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxB
    have hne : j m ≠ j (m + 1 + k) := fun h => by
      have h2 := hjm.injective h
      omega
    exact Set.disjoint_left.mp (hDdisj hne) hxmid hxk
  have heq : ∀ m, (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
      = (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
        + (∫ x in D (j m), w (j m) x ∂μ)
        + (∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ) := by
    intro m
    have heqFR : (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
        = (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
          + ∫ x in (D (j m) ∪ ⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ := by
      rw [hDstar m]
      exact setIntegral_union (hFR m) ((hDm _).union (hBmeas m))
        ((hw _).integrableOn) ((hw _).integrableOn)
    have heqR : (∫ x in (D (j m) ∪ ⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ)
        = (∫ x in D (j m), w (j m) x ∂μ)
          + ∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ :=
      setIntegral_union (hmidB m) (hBmeas m)
        ((hw _).integrableOn) ((hw _).integrableOn)
    rw [heqFR, heqR, add_assoc]
  have hFint : ∀ m, (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
      = ∑ l ∈ Finset.range m, ∫ x in D (j l), w (j m) x ∂μ := by
    intro m
    refine integral_biUnion_finset (Finset.range m) ?_ ?_ ?_
    · intro l _
      exact hDm _
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact hDdisj (fun h => hab (hjm.injective h))
    · intro l _
      exact (hw _).integrableOn
  have hsum2 : ∀ m, (∑ l ∈ Finset.range m, (1 / 2 : ℝ) ^ l) ≤ 2 := by
    intro m
    have hnn : ∀ i, i ∉ Finset.range m → (0:ℝ) ≤ (1 / 2 : ℝ) ^ i :=
      fun i _ => by positivity
    calc ∑ l ∈ Finset.range m, (1 / 2 : ℝ) ^ l
        ≤ ∑' l, (1 / 2 : ℝ) ^ l :=
          Summable.sum_le_tsum _ hnn summable_geometric_two
      _ = 2 := tsum_geometric_two
  have hfin4 : ∀ m, |∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ| ≤ η / 4 := by
    intro m
    rw [hFint m]
    calc |∑ l ∈ Finset.range m, ∫ x in D (j l), w (j m) x ∂μ|
        = ‖∑ l ∈ Finset.range m, ∫ x in D (j l), w (j m) x ∂μ‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑ l ∈ Finset.range m, ‖∫ x in D (j l), w (j m) x ∂μ‖ :=
          norm_sum_le _ _
      _ = ∑ l ∈ Finset.range m, |∫ x in D (j l), w (j m) x ∂μ| :=
          Finset.sum_congr rfl (fun l _ => Real.norm_eq_abs _)
      _ ≤ ∑ l ∈ Finset.range m, (η / 8) * (1 / 2) ^ l := by
          apply Finset.sum_le_sum
          intro l hl
          have h1 := (hjrel l m (Finset.mem_range.mp hl)).2
          have h2 : (1 / 2 : ℝ) ^ (j l) ≤ (1 / 2 : ℝ) ^ l :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (StrictMono.id_le hjm l)
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
      _ ≤ η / 4 := by
          rw [← Finset.mul_sum]
          calc (η / 8) * ∑ l ∈ Finset.range m, (1 / 2 : ℝ) ^ l
              ≤ (η / 8) * 2 :=
                mul_le_mul_of_nonneg_left (hsum2 m) (by linarith)
            _ = η / 4 := by ring
  have hBT : ∀ m, (⋃ k, D (j (m + 1 + k))) ⊆ ⋃ k, D (N (j m) + k) := by
    intro m x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have h1 : N (j m) ≤ j (m + 1) := (hjrel m (m + 1) (by omega)).1
    have h2 : j (m + 1) ≤ j (m + 1 + k) := hjm.monotone (by omega)
    have heq : N (j m) + (j (m + 1 + k) - N (j m)) = j (m + 1 + k) := by omega
    exact Set.mem_iUnion.mpr ⟨j (m + 1 + k) - N (j m), by rw [heq]; exact hk⟩
  have hB4 : ∀ m, |∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ| ≤ η / 4 := by
    intro m
    have hB1 : ‖∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ‖
        ≤ ∫ x in (⋃ k, D (j (m + 1 + k))), ‖w (j m) x‖ ∂μ :=
      norm_integral_le_integral_norm _
    have h2 : (∫ x in (⋃ k, D (j (m + 1 + k))), ‖w (j m) x‖ ∂μ)
        = ∫ x in (⋃ k, D (j (m + 1 + k))), |w (j m) x| ∂μ :=
      setIntegral_congr_fun (hBmeas m) (fun x _ => Real.norm_eq_abs _)
    have habsB : Integrable (fun x => |w (j m) x|) μ :=
      (hw (j m)).norm.congr
        (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (w (j m) x)).symm)
    have hB2mono : (∫ x in (⋃ k, D (j (m + 1 + k))), |w (j m) x| ∂μ)
        ≤ ∫ x in (⋃ k, D (N (j m) + k)), |w (j m) x| ∂μ :=
      setIntegral_mono_set (habsB.integrableOn)
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hBT m hx)
    calc |∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ|
        = ‖∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in (⋃ k, D (j (m + 1 + k))), ‖w (j m) x‖ ∂μ := hB1
      _ = ∫ x in (⋃ k, D (j (m + 1 + k))), |w (j m) x| ∂μ := h2
      _ ≤ ∫ x in (⋃ k, D (N (j m) + k)), |w (j m) x| ∂μ := hB2mono
      _ ≤ η / 4 := le_of_lt (hNmod (j m))
  have hlow : ∀ m, η / 2 ≤ |∫ x in (⋃ l, D (j l)), w (j m) x ∂μ| := by
    intro m
    have hdiag : η ≤ |∫ x in D (j m), w (j m) x ∂μ| := hmass (j m)
    have htri : |∫ x in D (j m), w (j m) x ∂μ|
        ≤ |∫ x in (⋃ l, D (j l)), w (j m) x ∂μ|
          + |∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ|
          + |∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ| := by
      have heq' : (∫ x in D (j m), w (j m) x ∂μ)
          = (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ) := by
        linarith [heq m]
      have g1 : |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ)|
          ≤ |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)|
            + |∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ| := by
        have e : (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ)
            = ((∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ))
              + (-(∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ)) := by
          ring
        calc |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ)|
            = |((∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ))
              + (-(∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ))| := by
              rw [e]
          _ ≤ |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)|
              + |(-(∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ))| :=
              abs_add_le _ _
          _ = |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)|
              + |∫ x in (⋃ k, D (j (m + 1 + k))), w (j m) x ∂μ| := by
              rw [abs_neg]
      have g2 : |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
            - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)|
          ≤ |∫ x in (⋃ l, D (j l)), w (j m) x ∂μ|
            + |∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ| := by
        have e : (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)
            = (∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              + (-(∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)) := by
          ring
        calc |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              - (∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ)|
            = |(∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
              + (-(∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ))| := by
              rw [e]
          _ ≤ |∫ x in (⋃ l, D (j l)), w (j m) x ∂μ|
              + |(-(∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ))| :=
              abs_add_le _ _
          _ = |∫ x in (⋃ l, D (j l)), w (j m) x ∂μ|
              + |∫ x in (⋃ l ∈ Finset.range m, D (j l)), w (j m) x ∂μ| := by
              rw [abs_neg]
      rw [heq']
      exact g1.trans (add_le_add g2 le_rfl)
    have hF := hfin4 m
    have hB := hB4 m
    linarith
  have htendD : Filter.Tendsto (fun m ↦ ∫ x in (⋃ l, D (j l)), w (j m) x ∂μ)
      Filter.atTop (𝓝 0) :=
    (htend _ hDmeas).comp hjm.tendsto_atTop
  obtain ⟨M, hM⟩ := (htendD.eventually
    (Metric.ball_mem_nhds 0 (by linarith : (0:ℝ) < η / 2))).exists
  rw [dist_zero_right] at hM
  have hMlt : |∫ x in (⋃ l, D (j l)), w (j M) x ∂μ| < η / 2 := by
    rwa [Real.norm_eq_abs] at hM
  exact (not_lt_of_ge (hlow M)) hMlt

/-- Weakly null sequences have vanishing mass on small sets. -/
private theorem dpc_tendsto_eLpNorm_restrict_of_weakly_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {v : ℕ → Lp ℝ 1 μ}
    (hv : ∀ φ : StrongDual ℝ (Lp ℝ 1 μ),
      Filter.Tendsto (fun k ↦ φ (v k)) Filter.atTop (𝓝 0))
    {s : ℕ → Set α} (hs : ∀ k, MeasurableSet (s k))
    (hμ : ∀ k, μ (s k) ≤ (4⁻¹ : ℝ≥0∞) ^ k) :
    Filter.Tendsto (fun k ↦ eLpNorm (⇑(v k)) 1 (μ.restrict (s k)))
      Filter.atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · subst htop
    exact Filter.Eventually.of_forall fun k => le_top
  · by_contra hnot
    rw [Filter.not_eventually] at hnot
    have hfreq : ∃ᶠ k in Filter.atTop,
        ε < eLpNorm (⇑(v k)) 1 (μ.restrict (s k)) :=
      hnot.mono fun k hk => lt_of_not_ge hk
    obtain ⟨ψ, hψm, hψ⟩ := Filter.extraction_of_frequently_atTop hfreq
    have hηpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
    have hεeq : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal htop
    have hmass : ∀ n, ε.toReal ≤ ∫ x in s (ψ n), |⇑(v (ψ n)) x| ∂μ := by
      intro n
      have hmem : MemLp (⇑(v (ψ n))) 1 μ := Lp.memLp _
      have hae : AEStronglyMeasurable (⇑(v (ψ n))) (μ.restrict (s (ψ n))) :=
        hmem.aestronglyMeasurable.restrict
      have hintR : Integrable (⇑(v (ψ n))) (μ.restrict (s (ψ n))) :=
        (memLp_one_iff_integrable.mp hmem).integrableOn
      have e1 : eLpNorm (⇑(v (ψ n))) 1 (μ.restrict (s (ψ n)))
          = ∫⁻ x, ‖⇑(v (ψ n)) x‖ₑ ∂(μ.restrict (s (ψ n))) :=
        eLpNorm_one_eq_lintegral_enorm hae
      have e2 : (∫⁻ x, ‖⇑(v (ψ n)) x‖ₑ ∂(μ.restrict (s (ψ n))))
          = ENNReal.ofReal (∫ x in s (ψ n), ‖⇑(v (ψ n)) x‖ ∂μ) :=
        (ofReal_integral_norm_eq_lintegral_enorm hintR).symm
      have e3 : (∫ x in s (ψ n), ‖⇑(v (ψ n)) x‖ ∂μ)
          = ∫ x in s (ψ n), |⇑(v (ψ n)) x| ∂μ :=
        setIntegral_congr_fun (hs _) fun x _ => Real.norm_eq_abs _
      have hlt : ε < ENNReal.ofReal (∫ x in s (ψ n), |⇑(v (ψ n)) x| ∂μ) := by
        rw [← e3, ← e2, ← e1]
        exact hψ n
      have hInonneg : 0 ≤ ∫ x in s (ψ n), |⇑(v (ψ n)) x| ∂μ :=
        setIntegral_nonneg (hs _) fun x _ => abs_nonneg _
      have hle : ENNReal.ofReal ε.toReal ≤
          ENNReal.ofReal (∫ x in s (ψ n), |⇑(v (ψ n)) x| ∂μ) := by
        rw [hεeq]
        exact le_of_lt hlt
      exact (ENNReal.ofReal_le_ofReal_iff hInonneg).mp hle
    have hμψ : ∀ n, μ (s (ψ n)) ≤ (4⁻¹ : ℝ≥0∞) ^ n := by
      intro n
      calc μ (s (ψ n)) ≤ (4⁻¹ : ℝ≥0∞) ^ (ψ n) := hμ _
        _ ≤ (4⁻¹ : ℝ≥0∞) ^ n :=
          pow_le_pow_of_le_one zero_le (by norm_num)
            (StrictMono.id_le hψm n)
    obtain ⟨φ, hφm, C, hCmeas, hCdisj, hCmass⟩ :=
      dpc_exists_disjoint_of_small_sets (v := fun k => ⇑(v (ψ k)))
        (fun n => Lp.memLp _) (fun n => hs _) hμψ hηpos hmass
    have hN9 : ∀ j, ∃ D, MeasurableSet D ∧ D ⊆ C j ∧
        (1 / 2 : ℝ) * (∫ x in C j, |⇑(v (ψ (φ j))) x| ∂μ) ≤
          |∫ x in D, ⇑(v (ψ (φ j))) x ∂μ| := by
      intro j
      exact dpc_exists_subset_abs_setIntegral_ge_half (Lp.stronglyMeasurable _)
        (memLp_one_iff_integrable.mp (Lp.memLp _)) (hCmeas j)
    choose D hDmeas hDsub hDint using hN9
    have hDdisj : Pairwise (Function.onFun Disjoint D) := by
      intro i j hne
      exact Disjoint.mono (hDsub i) (hDsub j) (hCdisj hne)
    have hmassD : ∀ k, ε.toReal / 4 ≤
        |∫ x in D k, ⇑(v (ψ (φ k))) x ∂μ| := by
      intro k
      have hC := hCmass k
      have hD := hDint k
      calc ε.toReal / 4 = (1 / 2 : ℝ) * (ε.toReal / 2) := by ring
        _ ≤ (1 / 2 : ℝ) * (∫ x in C k, |⇑(v (ψ (φ k))) x| ∂μ) :=
          mul_le_mul_of_nonneg_left hC (by norm_num)
        _ ≤ |∫ x in D k, ⇑(v (ψ (φ k))) x ∂μ| := hD
    have hwint : ∀ k, Integrable (⇑(v (ψ (φ k)))) μ := fun k =>
      memLp_one_iff_integrable.mp (Lp.memLp _)
    have htend : ∀ A : Set α, MeasurableSet A →
        Filter.Tendsto (fun k ↦ ∫ x in A, ⇑(v (ψ (φ k))) x ∂μ) Filter.atTop
          (𝓝 0) := by
      intro A hA
      have h1 : Filter.Tendsto
          (fun k ↦ dpcSetIntegralL1CLM (μ := μ) A (v k)) Filter.atTop (𝓝 0) :=
        hv _
      have hcomp : StrictMono (ψ ∘ φ) := hψm.comp hφm
      have h2 := h1.comp hcomp.tendsto_atTop
      have heq : (fun k ↦ ∫ x in A, ⇑(v (ψ (φ k))) x ∂μ)
          = (fun k ↦ dpcSetIntegralL1CLM (μ := μ) A (v ((ψ ∘ φ) k))) := by
        funext k
        rw [dpcSetIntegralL1CLM_apply, Function.comp_apply]
      rw [heq]
      exact h2
    exact dpc_false_of_gliding_hump (w := fun k => ⇑(v (ψ (φ k)))) hwint
      hDmeas hDdisj (by linarith) hmassD htend

/-- Reverse direction. -/
private theorem dpc_uniformIntegrable_of_isCompact_closure_Lp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {ι : Type*} {u : ι → Lp ℝ 1 μ}
    (hK : IsCompact (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range u))) :
    UniformIntegrable (fun i ↦ ⇑(u i)) 1 μ := by
  have hb := dpc_isBounded_preimage_toWeakSpace_of_isCompact hK
  rw [isBounded_iff_forall_norm_le] at hb
  obtain ⟨M, hM⟩ := hb
  have hmem : ∀ i, toWeakSpace ℝ (Lp ℝ 1 μ) (u i) ∈
      closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range u) := fun i =>
    subset_closure (Set.mem_image_of_mem _ (Set.mem_range_self i))
  have hnorm : ∀ i, ‖u i‖ ≤ max M 0 := fun i =>
    (hM _ (hmem i)).trans (le_max_left _ _)
  have hbound : ∃ C : NNReal, ∀ i, eLpNorm (⇑(u i)) 1 μ ≤ C := by
    refine ⟨Real.toNNReal (max M 0), fun i => ?_⟩
    have hne : eLpNorm ⇑(u i) 1 μ ≠ ⊤ := Lp.eLpNorm_ne_top _
    have h1 : ENNReal.ofReal ‖u i‖ = eLpNorm ⇑(u i) 1 μ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal hne]
    rw [← h1, ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal (hnorm i)
  refine ⟨?_, hbound⟩
  rw [unifIntegrable_iff']
  intro ε hε
  by_contra hnot
  push Not at hnot
  have hδpos : ∀ n : ℕ, (0 : ℝ≥0∞) < (4⁻¹ : ℝ≥0∞) ^ n := fun n =>
    ENNReal.pow_pos (by simp) n
  have hchoice : ∀ n : ℕ, ∃ i, ∃ s, MeasurableSet s ∧
      μ s ≤ (4⁻¹ : ℝ≥0∞) ^ n ∧ ε < eLpNorm ⇑(u i) 1 (μ.restrict s) :=
    fun n => hnot _ (hδpos n)
  choose i s hs hμs hlt using hchoice
  have htop : ε ≠ ⊤ := by
    rintro rfl
    exact (not_lt_of_ge le_top) (hlt 0)
  have hseq : IsSeqCompact
      (closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range u)) :=
    (MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.eberlein_smulian).mp
      hK
  have hmemseq : ∀ n, toWeakSpace ℝ (Lp ℝ 1 μ) (u (i n)) ∈
      closure (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range u) := fun n =>
    subset_closure (Set.mem_image_of_mem _ (Set.mem_range_self (i n)))
  obtain ⟨a, ha, ψ, hψm, hlim⟩ := hseq hmemseq
  set g : Lp ℝ 1 μ := (toWeakSpace ℝ (Lp ℝ 1 μ)).symm a with hgdef
  have hweak : ∀ f : StrongDual ℝ (Lp ℝ 1 μ),
      Filter.Tendsto (fun j => f (u (i (ψ j)))) Filter.atTop (𝓝 (f g)) := by
    intro f
    have hcont : Continuous
        (fun w : WeakSpace ℝ (Lp ℝ 1 μ) =>
          f ((toWeakSpace ℝ (Lp ℝ 1 μ)).symm w)) :=
      WeakBilin.eval_continuous _ f
    have hcomp := (hcont.tendsto a).comp hlim
    have heqfun : (fun j => f (u (i (ψ j))))
        = ((fun w : WeakSpace ℝ (Lp ℝ 1 μ) =>
          f ((toWeakSpace ℝ (Lp ℝ 1 μ)).symm w)) ∘
          ((fun n => toWeakSpace ℝ (Lp ℝ 1 μ) (u (i n))) ∘ ψ)) := by
      funext j
      simp [Function.comp_apply, LinearEquiv.symm_apply_apply]
    have heqlim : f g = f ((toWeakSpace ℝ (Lp ℝ 1 μ)).symm a) := by
      rw [hgdef]
    rw [heqfun, heqlim]
    exact hcomp
  have hnull : ∀ f : StrongDual ℝ (Lp ℝ 1 μ),
      Filter.Tendsto (fun j => f (u (i (ψ j)) - g)) Filter.atTop (𝓝 0) := by
    intro f
    have hsub : Filter.Tendsto (fun j => f (u (i (ψ j))) - f g) Filter.atTop
        (𝓝 0) := by
      have h : Filter.Tendsto (fun _ : ℕ => f g) Filter.atTop (𝓝 (f g)) :=
        tendsto_const_nhds
      have h2 := (hweak f).sub h
      rwa [sub_self] at h2
    have heq : (fun j => f (u (i (ψ j)) - g))
        = (fun j => f (u (i (ψ j))) - f g) :=
      funext fun j => map_sub _ _ _
    rw [heq]
    exact hsub
  have hμψ : ∀ k, μ (s (ψ k)) ≤ (4⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    calc μ (s (ψ k)) ≤ (4⁻¹ : ℝ≥0∞) ^ (ψ k) := hμs _
      _ ≤ (4⁻¹ : ℝ≥0∞) ^ k :=
        pow_le_pow_of_le_one zero_le (by norm_num)
          (StrictMono.id_le hψm k)
  have hN12 : Filter.Tendsto
      (fun k ↦ eLpNorm (⇑(u (i (ψ k)) - g)) 1 (μ.restrict (s (ψ k))))
      Filter.atTop (𝓝 0) :=
    dpc_tendsto_eLpNorm_restrict_of_weakly_null hnull (fun k => hs _)
      hμψ
  have hg0 : Filter.Tendsto
      (fun k ↦ eLpNorm (⇑g) 1 (μ.restrict (s (ψ k)))) Filter.atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε' hε'
    obtain ⟨δ, hδpos', hδ⟩ :=
      (Lp.memLp g).eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε'
    have hpow : Filter.Tendsto (fun k => (4⁻¹ : ℝ≥0∞) ^ (ψ k)) Filter.atTop
        (𝓝 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).comp
        hψm.tendsto_atTop
    have hev2 : ∀ᶠ k in Filter.atTop, (4⁻¹ : ℝ≥0∞) ^ (ψ k) ≤ δ :=
      (ENNReal.tendsto_nhds_zero.mp hpow) δ hδpos'
    filter_upwards [hev2] with k hk
    have hμk : μ (s (ψ k)) ≤ (4⁻¹ : ℝ≥0∞) ^ (ψ k) := hμs _
    have hle : μ (s (ψ k)) ≤ δ := hμk.trans hk
    have hcongr : eLpNorm (⇑g) 1 (μ.restrict (s (ψ k)))
        = eLpNorm ((s (ψ k)).indicator ⇑g) 1 μ :=
      (eLpNorm_indicator_eq_eLpNorm_restrict (hs _).nullMeasurableSet).symm
    rw [hcongr]
    exact hδ _ (hs _).nullMeasurableSet hle
  have hae_eq : ∀ k, (⇑(u (i (ψ k))) : α → ℝ) =ᵐ[μ.restrict (s (ψ k))]
      (⇑(u (i (ψ k)) - g) + ⇑g) := by
    intro k
    have hsub : ⇑(u (i (ψ k)) - g) =ᵐ[μ]
        ⇑(u (i (ψ k))) - ⇑g :=
      Lp.coeFn_sub _ _
    filter_upwards [ae_restrict_of_ae hsub] with x hx
    simp only [Pi.add_apply]
    rw [hx]
    exact (sub_add_cancel _ _).symm
  have hleF : ∀ k, eLpNorm ⇑(u (i (ψ k))) 1 (μ.restrict (s (ψ k)))
      ≤ eLpNorm ⇑(u (i (ψ k)) - g) 1 (μ.restrict (s (ψ k)))
        + eLpNorm ⇑g 1 (μ.restrict (s (ψ k))) := by
    intro k
    rw [eLpNorm_congr_ae (hae_eq k)]
    exact eLpNorm_add_le le_rfl
  have hsum : Filter.Tendsto
      (fun k ↦ eLpNorm ⇑(u (i (ψ k)) - g) 1 (μ.restrict (s (ψ k)))
        + eLpNorm ⇑g 1 (μ.restrict (s (ψ k)))) Filter.atTop (𝓝 0) := by
    simpa using hN12.add hg0
  have hF0 : Filter.Tendsto
      (fun k ↦ eLpNorm ⇑(u (i (ψ k))) 1 (μ.restrict (s (ψ k))))
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => zero_le) hleF
  obtain ⟨k, hk⟩ :=
    ((ENNReal.tendsto_nhds_zero.mp hF0) (ε / 2)
      (ENNReal.half_pos hε.ne')).exists
  have hhalf : ε / 2 < ε := ENNReal.half_lt_self hε.ne' htop
  exact (lt_irrefl ε) ((hlt (ψ k)).trans (hk.trans_lt hhalf))

/--
On a finite measure space, a family `f : ι → α → ℝ` with `MemLp 1` is uniformly integrable
`UniformIntegrable f 1 μ` iff its image in `WeakSpace ℝ (Lp ℝ 1 μ)` has weakly compact closure,
i.e. relative weak compactness in `L¹`. Source: N. Dunford and B. J. Pettis,
Linear Operations on Summable Functions, Trans. Amer. Math. Soc. 47 (1940), 323–392,
DOI 10.1090/S0002-9947-1940-0002020-4, criterion for weak compactness in `L¹`;
Dunford-Schwartz IV; Lean states finite-measure real `L¹` specialization with weak-space
closure characterization.

Proves `Wanted` entry `dunford_pettis_compactness`.
-/
public theorem dunford_pettis_compactness
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {ι : Type*} (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 1 μ) :
    UniformIntegrable f (1 : ℝ≥0∞) μ ↔
      IsCompact
        (closure
          (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range (fun i => (hf i).toLp (f i))
            : Set (WeakSpace ℝ (Lp ℝ 1 μ)))) := by
  rw [uniformIntegrable_congr_ae
    (fun i => (MemLp.coeFn_toLp (hf i)).symm)]
  exact ⟨dpc_isCompact_closure_of_uniformIntegrable_Lp,
    dpc_uniformIntegrable_of_isCompact_closure_Lp⟩

end MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted
