/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.KacWardRectilinearDeletion
import Code.Onsager.DecorationFormalMultiaffine

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphLoopExponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Sym2 V →₀ ℕ :=
  ∑ k, Finsupp.single (loop k).edge 1


noncomputable def kwGraphLoopScalar
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : ℂ :=
  ∏ k, kwGraphTransition G (fun _ ↦ 1) phase (loop k) (loop (k + 1))

@[simp] theorem kwGraphLoopExponent_totalDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    ons_finsuppTotalDegree (kwGraphLoopExponent G loop) = n := by
  unfold kwGraphLoopExponent
  rw [ons_finsuppTotalDegree_finset_sum]
  simp

theorem kwGraphTransition_entry_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (dart next : G.Dart) :
    kwGraphTransition G weight phase dart next =
      kwGraphTransition G (fun _ ↦ 1) phase dart next * weight dart.edge := by
  unfold kwGraphTransition
  split
  · ring
  · simp_all

theorem kwGraphLoopWeight_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    ons_loopWeight (kwGraphTransition G weight phase) loop =
      kwGraphLoopScalar G phase loop *
        (kwGraphLoopExponent G loop).prod
          (fun edge k ↦ weight edge ^ k) := by
  unfold ons_loopWeight kwGraphLoopScalar kwGraphLoopExponent
  rw [Finset.prod_congr rfl (fun k _ ↦
    kwGraphTransition_entry_factor G weight phase (loop k) (loop (k + 1)))]
  rw [Finset.prod_mul_distrib, ons_finsuppProd_sum_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Finsupp.prod_single_index] <;> simp


noncomputable def kwGraphFormalLogCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (m : Sym2 V →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) / ((r : ℂ) + 1)) / 2

noncomputable def kwGraphFormalLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : MvPowerSeries (Sym2 V) ℂ :=
  kwGraphFormalLogCoeff G phase

theorem kwGraphFormalLogCoeff_eq_tsum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (m : Sym2 V →₀ ℕ) :
    kwGraphFormalLogCoeff G phase m =
      -(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) / 2 := by
  unfold kwGraphFormalLogCoeff
  congr 2
  symm
  apply tsum_eq_sum
  intro r hr
  rw [Finset.mem_range, not_lt] at hr
  have hsum :
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro loop _
    rw [if_neg]
    intro heq
    have hdegree := kwGraphLoopExponent_totalDegree G loop
    rw [heq] at hdegree
    omega
  rw [hsum, zero_div]

@[simp] theorem kwGraphFormalLog_constantCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) :
    MvPowerSeries.constantCoeff (kwGraphFormalLog G phase) = 0 := by
  change kwGraphFormalLogCoeff G phase 0 = 0
  simp [kwGraphFormalLogCoeff, ons_finsuppTotalDegree]

theorem kwGraphFormalLog_hasSubst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) :
    PowerSeries.HasSubst (kwGraphFormalLog G phase) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (kwGraphFormalLog_constantCoeff G phase)


noncomputable def kwGraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : MvPowerSeries (Sym2 V) ℂ :=
  PowerSeries.subst (kwGraphFormalLog G phase) (PowerSeries.exp ℂ)

theorem kwGraphFormalBucket_eval_eq_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) * ons_mvMonomialValue weight m) =
      ∑ loop : Fin (r + 1) → G.Dart,
        ons_loopWeight (kwGraphTransition G weight phase) loop := by
  rw [ons_tsum_finite_exponent_buckets]
  apply Finset.sum_congr rfl
  intro loop _
  exact (kwGraphLoopWeight_factor G weight phase loop).symm

theorem kwGraphFormalBucket_eval_div_eq_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      ((∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) / ((r : ℂ) + 1)) * ons_mvMonomialValue weight m) =
      (∑ loop : Fin (r + 1) → G.Dart,
        ons_loopWeight (kwGraphTransition G weight phase) loop) /
          ((r : ℂ) + 1) := by
  rw [← kwGraphFormalBucket_eval_eq_loopSum G phase weight r]
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

noncomputable def kwGraphFormalBucketTerm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) (m : Sym2 V →₀ ℕ) : ℂ :=
  ((∑ loop : Fin (r + 1) → G.Dart,
      if kwGraphLoopExponent G loop = m then
        kwGraphLoopScalar G phase loop
      else 0) / ((r : ℂ) + 1)) * ons_mvMonomialValue weight m

theorem norm_kwGraphFormalBucketTerm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) (m : Sym2 V →₀ ℕ) :
    ‖kwGraphFormalBucketTerm G phase weight r m‖ ≤
      ∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
        else 0 := by
  unfold kwGraphFormalBucketTerm
  rw [Finset.sum_div, Finset.sum_mul]
  calc
    ‖∑ loop : Fin (r + 1) → G.Dart,
        (if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop else 0) /
            ((r : ℂ) + 1) * ons_mvMonomialValue weight m‖ ≤
        ∑ loop : Fin (r + 1) → G.Dart,
          ‖(if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop else 0) /
              ((r : ℂ) + 1) * ons_mvMonomialValue weight m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
        else 0 := by
      apply Finset.sum_le_sum
      intro loop _
      by_cases heq : kwGraphLoopExponent G loop = m
      · rw [if_pos heq, if_pos heq, ← heq,
          kwGraphLoopWeight_factor]
        rw [norm_mul, norm_div, norm_mul]
        have hden : 1 ≤ ‖(r : ℂ) + 1‖ := by
          rw [show (r : ℂ) + 1 = ((r + 1 : ℕ) : ℂ) by norm_num,
            norm_natCast]
          norm_num
        exact mul_le_mul_of_nonneg_right
          (div_le_self (norm_nonneg (kwGraphLoopScalar G phase loop)) hden)
          (norm_nonneg (ons_mvMonomialValue weight
            (kwGraphLoopExponent G loop)))
      · simp [heq]

theorem tsum_norm_kwGraphFormalBucketTerm_le_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
      ∑ loop : Fin (r + 1) → G.Dart,
        ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖ := by
  classical
  let exponent := fun loop : Fin (r + 1) → G.Dart ↦
    kwGraphLoopExponent G loop
  let S : Finset (Sym2 V →₀ ℕ) := Finset.univ.image exponent
  have hterm : Summable fun m : Sym2 V →₀ ℕ ↦
      ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ loop : Fin (r + 1) → G.Dart,
        kwGraphLoopExponent G loop ≠ m := by
      intro loop heq
      apply hm
      simp [S, exponent, ← heq]
    simp [kwGraphFormalBucketTerm, hnone]
  let major := fun m : Sym2 V →₀ ℕ ↦
    ∑ loop : Fin (r + 1) → G.Dart,
      if kwGraphLoopExponent G loop = m then
        ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
      else 0
  have hmajor : Summable major := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ loop : Fin (r + 1) → G.Dart,
        kwGraphLoopExponent G loop ≠ m := by
      intro loop heq
      apply hm
      simp [S, exponent, ← heq]
    simp [major, hnone]
  calc
    (∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
        ∑' m : Sym2 V →₀ ℕ, major m :=
      Summable.tsum_le_tsum
        (fun m ↦ norm_kwGraphFormalBucketTerm_le
          G phase weight r m) hterm hmajor
    _ = _ := ons_tsum_finite_exponent_buckets_real exponent
      (fun loop ↦ ‖ons_loopWeight
        (kwGraphTransition G weight phase) loop‖)

theorem kw_summable_norm_GraphFormalBucketTerm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun r : ℕ ↦
      ∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
  let M := kwGraphTransition G weight phase
  have hC0 : 0 ≤ (Fintype.card G.Dart : ℝ) := by positivity
  have hgeomNorm : ‖(Fintype.card G.Dart : ℝ) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 hq)]
    exact hcard
  have hgeom : Summable fun r : ℕ ↦
      ((Fintype.card G.Dart : ℝ) * q) ^ (r + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hgeomNorm)
  apply Summable.of_nonneg_of_le
    (fun r ↦ tsum_nonneg (fun m ↦ norm_nonneg _)) (fun r ↦ ?_) hgeom
  calc
    (∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
      ∑ loop : Fin (r + 1) → G.Dart, ‖ons_loopWeight M loop‖ :=
        tsum_norm_kwGraphFormalBucketTerm_le_loopSum G phase weight r
    _ ≤ ∑ _loop : Fin (r + 1) → G.Dart, q ^ (r + 1) := by
      apply Finset.sum_le_sum
      intro loop _
      exact norm_ons_loopWeight_le_pow M q hq hentry loop
    _ = ((Fintype.card G.Dart : ℝ) * q) ^ (r + 1) := by
      simp
      ring

theorem kw_summable_norm_GraphFormalBucketTerm_fixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) :
    Summable fun m : Sym2 V →₀ ℕ ↦
      ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
  classical
  let exponent := fun loop : Fin (r + 1) → G.Dart ↦
    kwGraphLoopExponent G loop
  let S : Finset (Sym2 V →₀ ℕ) := Finset.univ.image exponent
  apply summable_of_ne_finset_zero (s := S)
  intro m hm
  have hnone : ∀ loop : Fin (r + 1) → G.Dart,
      kwGraphLoopExponent G loop ≠ m := by
    intro loop heq
    apply hm
    simp [S, exponent, ← heq]
  simp [kwGraphFormalBucketTerm, hnone]

theorem kw_summable_norm_GraphFormalBucketTerm_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖kwGraphFormalBucketTerm G phase weight p.1 p.2‖ := by
  rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
  constructor
  · intro r
    exact kw_summable_norm_GraphFormalBucketTerm_fixed
      G phase weight r
  · exact kw_summable_norm_GraphFormalBucketTerm
      G phase weight q hq hentry hcard

theorem kw_summable_GraphFormalBucketTerm_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      kwGraphFormalBucketTerm G phase weight p.1 p.2 :=
  Summable.of_norm <| kw_summable_norm_GraphFormalBucketTerm_product
    G phase weight q hq hentry hcard

theorem kwGraphFormalLog_evalTerm_eq_bucketTsum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (m : Sym2 V →₀ ℕ) :
    MvPowerSeries.coeff m (kwGraphFormalLog G phase) *
        ons_mvMonomialValue weight m =
      ∑' r : ℕ, -kwGraphFormalBucketTerm G phase weight r m / 2 := by
  change kwGraphFormalLogCoeff G phase m *
    ons_mvMonomialValue weight m = _
  rw [kwGraphFormalLogCoeff_eq_tsum]
  calc
    (-(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) / 2) *
        ons_mvMonomialValue weight m =
      -(∑' r : ℕ,
        ((∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) *
          ons_mvMonomialValue weight m) / 2 := by
            rw [tsum_mul_right]
            ring
    _ = ∑' r : ℕ,
        -kwGraphFormalBucketTerm G phase weight r m / 2 := by
      rw [← tsum_neg, ← tsum_div_const]
      apply tsum_congr
      intro r
      rfl

theorem kw_MvSeriesEvalSummable_GraphFormalLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable (kwGraphFormalLog G phase) weight := by
  let term := fun r : ℕ ↦ fun m : Sym2 V →₀ ℕ ↦
    kwGraphFormalBucketTerm G phase weight r m
  have hnorm : Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖term p.1 p.2‖ :=
    kw_summable_norm_GraphFormalBucketTerm_product
      G phase weight q hq hentry hcard
  have hnormScaled : Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖-term p.1 p.2 / 2‖ := by
    have hdiv := hnorm.div_const 2
    simpa only [norm_div, norm_neg, Complex.norm_ofNat] using hdiv
  have hswap : Summable fun p : (Sym2 V →₀ ℕ) × ℕ ↦
      ‖-term p.2 p.1 / 2‖ := by
    simpa only [Function.comp_apply] using
      ((Equiv.prodComm (Sym2 V →₀ ℕ) ℕ).summable_iff.mpr hnormScaled)
  have houter : Summable fun m : Sym2 V →₀ ℕ ↦
      ∑' r : ℕ, ‖-term r m / 2‖ := hswap.prod
  apply Summable.of_nonneg_of_le
    (fun m ↦ norm_nonneg _) (fun m ↦ ?_) houter
  rw [kwGraphFormalLog_evalTerm_eq_bucketTsum]
  have hfixedNorm : Summable fun r : ℕ ↦ ‖-term r m / 2‖ := by
    simpa only [Function.comp_apply] using
      hswap.comp_injective (i := fun r : ℕ ↦ (m, r))
        (fun _ _ h ↦ congrArg Prod.snd h)
  exact norm_tsum_le_tsum_norm hfixedNorm

theorem kw_mvSeriesEval_GraphFormalLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_mvSeriesEval (kwGraphFormalLog G phase) weight =
      -(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1)) / 2 := by
  let term := fun r : ℕ ↦ fun m : Sym2 V →₀ ℕ ↦
    kwGraphFormalBucketTerm G phase weight r m
  have hterm : Summable (Function.uncurry term) :=
    kw_summable_GraphFormalBucketTerm_product
      G phase weight q hq hentry hcard
  have hscaled : Summable (Function.uncurry fun r m ↦ -term r m / 2) :=
    hterm.neg.div_const 2
  unfold ons_mvSeriesEval
  change (∑' m : Sym2 V →₀ ℕ,
      kwGraphFormalLogCoeff G phase m *
        ons_mvMonomialValue weight m) = _
  simp_rw [kwGraphFormalLogCoeff_eq_tsum]
  calc
    (∑' m : Sym2 V →₀ ℕ,
        (-(∑' r : ℕ,
          (∑ loop : Fin (r + 1) → G.Dart,
            if kwGraphLoopExponent G loop = m then
              kwGraphLoopScalar G phase loop
            else 0) / ((r : ℂ) + 1)) / 2) *
          ons_mvMonomialValue weight m) =
        ∑' m, ∑' r, -term r m / 2 := by
      apply tsum_congr
      intro m
      calc
        (-(∑' r : ℕ,
            (∑ loop : Fin (r + 1) → G.Dart,
              if kwGraphLoopExponent G loop = m then
                kwGraphLoopScalar G phase loop
              else 0) / ((r : ℂ) + 1)) / 2) *
            ons_mvMonomialValue weight m =
          -(∑' r : ℕ,
            ((∑ loop : Fin (r + 1) → G.Dart,
              if kwGraphLoopExponent G loop = m then
                kwGraphLoopScalar G phase loop
              else 0) / ((r : ℂ) + 1)) *
              ons_mvMonomialValue weight m) / 2 := by
                rw [tsum_mul_right]
                ring
        _ = ∑' r, -term r m / 2 := by
          rw [← tsum_neg, ← tsum_div_const]
          apply tsum_congr
          intro r
          rfl
    _ = ∑' r, ∑' m, -term r m / 2 := hscaled.tsum_comm
    _ = ∑' r : ℕ,
        -(∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1) / 2 := by
      apply tsum_congr
      intro r
      rw [tsum_div_const, tsum_neg]
      dsimp only [term]
      simp only [kwGraphFormalBucketTerm]
      rw [kwGraphFormalBucket_eval_div_eq_loopSum]
      ring
    _ = ∑' r : ℕ,
        -((∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1)) / 2 := by
      apply tsum_congr
      intro r
      ring
    _ = _ := by rw [tsum_div_const, tsum_neg]



theorem kw_mvSeriesEval_GraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_mvSeriesEval (kwGraphFormalRoot G phase) weight =
      ons_detWalkRoot (kwGraphTransition G weight phase) := by
  rw [kwGraphFormalRoot,
    ons_mvSeriesEval_subst_exp
      (kwGraphFormalLog G phase) weight
      (kwGraphFormalLog_hasSubst G phase)
      (kw_MvSeriesEvalSummable_GraphFormalLog
        G phase weight q hq hentry hcard),
    kw_mvSeriesEval_GraphFormalLog G phase weight q hq hentry hcard]
  rfl

theorem kw_MvSeriesEvalSummable_GraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable (kwGraphFormalRoot G phase) weight := by
  unfold kwGraphFormalRoot
  exact ons_MvSeriesEvalSummable_subst_exp
    (kwGraphFormalLog G phase) weight
    (kwGraphFormalLog_hasSubst G phase)
    (kw_MvSeriesEvalSummable_GraphFormalLog
      G phase weight q hq hentry hcard)

theorem kw_mvMonomialValue_scaleGraphEdgeWeight
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V → ℂ) (edge : Sym2 V) (t : ℂ)
    (m : Sym2 V →₀ ℕ) :
    ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge t) m =
      t ^ m edge * ons_mvMonomialValue weight m := by
  classical
  unfold ons_mvMonomialValue
  calc
    m.prod (fun f n ↦ kwScaleGraphEdgeWeight weight edge t f ^ n) =
        m.prod (fun f n ↦
          (if f = edge then t ^ n else 1) * weight f ^ n) := by
      apply Finsupp.prod_congr
      intro f _
      unfold kwScaleGraphEdgeWeight
      by_cases hfe : f = edge
      · simp [hfe, mul_pow]
      · simp [hfe]
    _ = m.prod (fun f n ↦ if f = edge then t ^ n else 1) *
          m.prod (fun f n ↦ weight f ^ n) := Finsupp.prod_mul
    _ = t ^ m edge * m.prod (fun f n ↦ weight f ^ n) := by
      congr 1
      unfold Finsupp.prod
      by_cases hedge : edge ∈ m.support
      · rw [Finset.prod_eq_single edge]
        · simp
        · intro f _ hfe
          simp [hfe]
        · exact fun hnot ↦ (hnot hedge).elim
      · have hzero : m edge = 0 := Finsupp.notMem_support_iff.mp hedge
        rw [hzero, pow_zero]
        apply Finset.prod_eq_one
        intro f hf
        have hfe : f ≠ edge := by
          intro h
          subst f
          exact hedge hf
        simp [hfe]

noncomputable def kwGraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V) :
    MvPowerSeries (Sym2 V) ℂ :=
  fun m ↦ ons_secondDifferenceFactor (m edge) *
    MvPowerSeries.coeff m series

theorem kw_MvSeriesEvalSummable_GraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V)
    (weight : Sym2 V → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 0)) :
    ons_MvSeriesEvalSummable
      (kwGraphFormalSecondDifference series edge) weight := by
  let term2 := fun m : Sym2 V →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 2) m‖
  let term1 := fun m : Sym2 V →₀ ℕ ↦
    2 * ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖
  let term0 := fun m : Sym2 V →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 0) m‖
  have hs2 : Summable term2 := h2
  have hs1 : Summable term1 := h1.mul_left 2
  have hs0 : Summable term0 := h0
  apply Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) ((hs2.add hs1).add hs0)
  unfold kwGraphFormalSecondDifference ons_secondDifferenceFactor
  simp only [MvPowerSeries.coeff_apply, term2, term1, term0]
  rw [kw_mvMonomialValue_scaleGraphEdgeWeight,
    kw_mvMonomialValue_scaleGraphEdgeWeight]
  let A := (2 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  let B := 2 * (MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m)
  let C := (0 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  calc
    ‖((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖ ≤
      ‖A‖ + ‖B‖ + ‖C‖ := by
      have heq : ((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        A - B + C := by simp only [A, B, C]; ring
      rw [heq]
      nlinarith [norm_add_le (A - B) C, norm_sub_le A B]
    _ = _ := by
      simp only [A, B, C, norm_mul, MvPowerSeries.coeff_apply]
      norm_num
      ring

theorem kw_mvSeriesEval_GraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V)
    (weight : Sym2 V → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 0)) :
    ons_mvSeriesEval (kwGraphFormalSecondDifference series edge) weight =
      ons_mvSeriesEval series (kwScaleGraphEdgeWeight weight edge 2) -
        2 * ons_mvSeriesEval series weight +
        ons_mvSeriesEval series
          (kwScaleGraphEdgeWeight weight edge 0) := by
  let f2 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 2) m
  let f1 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series * ons_mvMonomialValue weight m
  let f0 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 0) m
  have hs2 : Summable f2 := Summable.of_norm h2
  have hs1 : Summable f1 := Summable.of_norm h1
  have hs0 : Summable f0 := Summable.of_norm h0
  unfold ons_mvSeriesEval kwGraphFormalSecondDifference
  simp only [MvPowerSeries.coeff_apply]
  have hterm : ∀ m : Sym2 V →₀ ℕ,
      ons_secondDifferenceFactor (m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        f2 m - 2 * f1 m + f0 m := by
    intro m
    rw [show f2 m = (2 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f2, kw_mvMonomialValue_scaleGraphEdgeWeight]; ring,
      show f0 m = (0 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f0, kw_mvMonomialValue_scaleGraphEdgeWeight]; ring]
    simp only [f1, ons_secondDifferenceFactor]
    ring
  change (∑' m, ons_secondDifferenceFactor (m edge) *
      MvPowerSeries.coeff m series * ons_mvMonomialValue weight m) =
    (∑' m, f2 m) - 2 * (∑' m, f1 m) + ∑' m, f0 m
  rw [tsum_congr hterm, (hs2.sub (hs1.mul_left 2)).tsum_add hs0,
    hs2.tsum_sub (hs1.mul_left 2), tsum_mul_left]

@[simp] theorem kwScaleGraphEdgeWeight_one
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V → ℂ) (edge : Sym2 V) :
    kwScaleGraphEdgeWeight weight edge 1 = weight := by
  funext other
  simp [kwScaleGraphEdgeWeight]

theorem kwGraphTransition_smulWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (c : ℂ) (dart next : G.Dart) :
    kwGraphTransition G (fun edge ↦ c * weight edge) phase dart next =
      c * kwGraphTransition G weight phase dart next := by
  unfold kwGraphTransition
  split
  · ring
  · simp

theorem norm_kwGraphTransition_scaleEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (selected : G.Dart) (t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ht : ‖t‖ ≤ 2)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ r)
    (dart next : G.Dart) :
    ‖kwGraphTransition G
      (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next‖ ≤
        2 * r := by
  rw [kwGraphTransition_scaleEdge_entry, norm_mul]
  by_cases hedge : dart.edge = selected.edge
  · rw [if_pos hedge]
    nlinarith [mul_le_mul ht (hentry dart next)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [if_neg hedge]
    norm_num
    linarith [hentry dart next]

theorem norm_kwScaleColumns_le
    {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (M : Matrix E E ℂ)
    (r : ℝ) (hr : 0 ≤ r) (ht : ‖t‖ ≤ 2)
    (hentry : ∀ i j, ‖M i j‖ ≤ r) (i j : E) :
    ‖ons_scaleColumns S t M i j‖ ≤ 2 * r := by
  unfold ons_scaleColumns
  by_cases hj : j ∈ S
  · rw [if_pos hj, norm_mul]
    nlinarith [mul_le_mul ht (hentry i j)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [if_neg hj]
    linarith [hentry i j]




theorem kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (m : Sym2 V →₀ ℕ)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (fun dart next ↦
        ons_turnW omega (direction next) (direction dart))) = 0 := by
  letI : Nonempty G.Dart := ⟨selected⟩
  let phase := fun dart next : G.Dart ↦
    ons_turnW omega (direction next) (direction dart)
  let root := kwGraphFormalRoot G phase
  let second := kwGraphFormalSecondDifference root selected.edge
  have hsecond : MvPowerSeries.coeff m second = 0 := by
    apply ons_coeff_eq_zero_of_degreeFiberCoeff second m
    intro weight
    let radius : ℝ := (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹
    let R : ℝ := min 1 radius
    let r : ℝ := R / 4
    let q : ℝ := 2 * r
    let S : ℝ := ∑ dart : G.Dart, ∑ next : G.Dart,
      ‖kwGraphTransition G weight phase dart next‖
    let c : ℂ := ((r / (1 + S) : ℝ) : ℂ)
    let base : Sym2 V → ℂ := fun edge ↦ c * weight edge
    have hradius : 0 < radius := by
      dsimp only [radius]
      positivity
    have hR : 0 < R := by
      dsimp only [R]
      exact lt_min (by norm_num) hradius
    have hRradius : R ≤ radius := min_le_right _ _
    have hr : 0 < r := by dsimp only [r]; linarith
    have hq : 0 < q := by dsimp only [q]; linarith
    have hsmall : q < radius := by
      dsimp only [q, r]
      linarith
    have hcard : (Fintype.card G.Dart : ℝ) * q < 1 :=
      ons_card_mul_lt_one_of_Sherman_small q hsmall
    have hS : 0 ≤ S := by
      dsimp only [S]
      exact Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hden : 0 < 1 + S := by linarith
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact_mod_cast div_ne_zero (ne_of_gt hr) (ne_of_gt hden)
    have hraw (dart next : G.Dart) :
        ‖kwGraphTransition G weight phase dart next‖ ≤ S := by
      have hinner :
          ‖kwGraphTransition G weight phase dart next‖ ≤
            ∑ e : G.Dart, ‖kwGraphTransition G weight phase dart e‖ :=
        Finset.single_le_sum
          (fun e _ ↦ norm_nonneg
            (kwGraphTransition G weight phase dart e))
          (Finset.mem_univ next)
      exact hinner.trans <| Finset.single_le_sum
        (fun d _ ↦ Finset.sum_nonneg fun e _ ↦ norm_nonneg
          (kwGraphTransition G weight phase d e))
        (Finset.mem_univ dart)
    have hbase (dart next : G.Dart) :
        ‖kwGraphTransition G base phase dart next‖ ≤ r := by
      rw [show base = fun edge ↦ c * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul]
      have hnormc : ‖c‖ = r / (1 + S) := by
        dsimp only [c]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr.le hden.le)]
      rw [hnormc, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hraw dart next]
    have hrootSummable (t : ℂ) (ht : ‖t‖ ≤ 2) :
        ons_MvSeriesEvalSummable root
          (kwScaleGraphEdgeWeight base selected.edge t) := by
      apply kw_MvSeriesEvalSummable_GraphFormalRoot
        G phase (kwScaleGraphEdgeWeight base selected.edge t)
          q hq.le
      · intro dart next
        simpa only [q] using norm_kwGraphTransition_scaleEdge_le
          G base phase selected t r hr.le ht hbase dart next
      · exact hcard
    have hsumSecond : ons_MvSeriesEvalSummable second base := by
      apply kw_MvSeriesEvalSummable_GraphFormalSecondDifference
      · exact hrootSummable 2 (by norm_num)
      · simpa only [kwScaleGraphEdgeWeight_one] using
          hrootSummable 1 (by norm_num)
      · exact hrootSummable 0 (by norm_num)
    have hzero : ∀ᶠ s : ℂ in nhds 0,
        ons_mvSeriesEval second (fun edge ↦ s * base edge) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1)] with s hs
      have hs1 : ‖s‖ ≤ 1 := by
        have : ‖s‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hs
        exact this.le
      let scaled : Sym2 V → ℂ := fun edge ↦ s * base edge
      have hscaled (dart next : G.Dart) :
          ‖kwGraphTransition G scaled phase dart next‖ ≤ r := by
        rw [show scaled = fun edge ↦ s * base edge from rfl,
          kwGraphTransition_smulWeight, norm_mul]
        calc
          ‖s‖ * ‖kwGraphTransition G base phase dart next‖ ≤
              1 * r := mul_le_mul hs1 (hbase dart next)
                (norm_nonneg _) (by norm_num)
          _ = r := one_mul r
      have hsum (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_MvSeriesEvalSummable root
            (kwScaleGraphEdgeWeight scaled selected.edge t) := by
        apply kw_MvSeriesEvalSummable_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      have heval (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_mvSeriesEval root
              (kwScaleGraphEdgeWeight scaled selected.edge t) =
            ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) := by
        apply kw_mvSeriesEval_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      let A := ons_detWalkRoot
        (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
          (kwGraphTransition G scaled phase))
      let B := ∑' path, ons_firstReturnWeight
        (kwGraphTransition G scaled phase) selected selected.symm path
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) =
            A * (1 - t * B) := by
        apply kw_rectilinearGraph_detWalkRoot_scaleEdge_affine
          G scaled direction hdirection omega homega homega_sq
            selected t q hq.le
        · intro dart next
          simpa only [q] using norm_kwScaleColumns_le
            ({selected, selected.symm} : Finset G.Dart) t
            (kwGraphTransition G scaled phase) r hr.le ht hscaled dart next
        · exact hsmall
        · exact hcard
      have hscaleOne :
          kwScaleGraphEdgeWeight scaled selected.edge 1 = scaled :=
        kwScaleGraphEdgeWeight_one scaled selected.edge
      rw [kw_mvSeriesEval_GraphFormalSecondDifference
        root selected.edge scaled
        (hsum 2 (by norm_num))
        (by simpa only [hscaleOne] using hsum 1 (by norm_num))
        (hsum 0 (by norm_num))]
      rw [heval 2 (by norm_num)]
      have heval1 : ons_mvSeriesEval root scaled =
          ons_detWalkRoot (kwGraphTransition G scaled phase) := by
        simpa only [hscaleOne] using heval 1 (by norm_num)
      have haff1 : ons_detWalkRoot (kwGraphTransition G scaled phase) =
          A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [heval1, heval 0 (by norm_num),
        haff 2 (by norm_num), haff1,
        haff 0 (by norm_num)]
      ring
    have hfiber :=
      ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero
        second base hsumSecond hzero (Finsupp.degree m)
    change ons_degreeFiberCoeff second
      (fun edge ↦ c * weight edge) (Finsupp.degree m) = 0 at hfiber
    rw [ons_degreeFiberCoeff_scale] at hfiber
    exact (mul_eq_zero.mp hfiber).resolve_left (pow_ne_zero _ hc)
  change ons_secondDifferenceFactor (m selected.edge) *
      MvPowerSeries.coeff m root = 0 at hsecond
  exact (mul_eq_zero.mp hsecond).resolve_left
    (ons_secondDifferenceFactor_ne_zero (m selected.edge) hrepeated)


theorem kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (fun dart next ↦
        ons_turnW omega (direction next) (direction dart))) = 0 := by
  rw [SimpleGraph.mem_edgeFinset] at hedge
  obtain ⟨v, w⟩ := edge
  let selected : G.Dart := ⟨(v, w), hedge⟩
  exact kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated
    G direction hdirection omega homega homega_sq selected m hrepeated

end StatMech.FrontierA
