/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationTransitionWalk
import Code.Onsager.DecorationFormalEvalAlgebra









namespace StatMech.Onsager

open BigOperators Finset

theorem ons_tsum_finite_exponent_buckets
    {I E : Type*} [Fintype I] [DecidableEq E]
    (exponent : I → E) (scalar : I → ℂ) (value : E → ℂ) :
    (∑' m : E,
      (∑ i : I, if exponent i = m then scalar i else 0) * value m) =
      ∑ i : I, scalar i * value (exponent i) := by
  classical
  let S : Finset E := Finset.univ.image exponent
  rw [tsum_eq_sum (s := S)]
  · calc
      (∑ m ∈ S,
          (∑ i : I, if exponent i = m then scalar i else 0) * value m) =
          ∑ m ∈ S, ∑ i : I,
            (if exponent i = m then scalar i else 0) * value m := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_mul]
      _ = ∑ i : I, ∑ m ∈ S,
            (if exponent i = m then scalar i else 0) * value m := by
              rw [Finset.sum_comm]
      _ = ∑ i : I, scalar i * value (exponent i) := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (∑ m ∈ S,
                    (if exponent i = m then scalar i else 0) * value m) =
                    (if exponent i = exponent i then scalar i else 0) *
                      value (exponent i) := by
                        apply Finset.sum_eq_single (exponent i)
                        · intro m hm hne
                          rw [if_neg (Ne.symm hne), zero_mul]
                        · simp [S]
                _ = scalar i * value (exponent i) := by simp
  · intro m hm
    have hnone : ∀ i : I, exponent i ≠ m := by
      intro i heq
      apply hm
      simp [S, ← heq]
    simp [hnone]

theorem ons_decFormalBucket_eval_eq_loopSum
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    (∑' m : ons_DecEdge L →₀ ℕ,
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) *
        m.prod (fun edge n ↦ decWeight edge ^ n)) =
      ∑ d : Fin (r + 1) → ons_Dart L,
        ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d := by
  rw [ons_tsum_finite_exponent_buckets]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ons_loopWeight_KWmatDecorationWeightedPhase]

theorem ons_decFormalBucket_eval_div_eq_loopSum
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    (∑' m : ons_DecEdge L →₀ ℕ,
      ((∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) / ((r : ℂ) + 1)) *
        m.prod (fun edge n ↦ decWeight edge ^ n)) =
      (∑ d : Fin (r + 1) → ons_Dart L,
        ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d) /
        ((r : ℂ) + 1) := by
  rw [← ons_decFormalBucket_eval_eq_loopSum L omega u v decWeight r]
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

theorem ons_tsum_finite_exponent_buckets_real
    {I E : Type*} [Fintype I] [DecidableEq E]
    (exponent : I → E) (scalar : I → ℝ) :
    (∑' m : E, ∑ i : I,
      if exponent i = m then scalar i else 0) = ∑ i : I, scalar i := by
  classical
  let S : Finset E := Finset.univ.image exponent
  rw [tsum_eq_sum (s := S)]
  · calc
      (∑ m ∈ S, ∑ i : I,
          if exponent i = m then scalar i else 0) =
          ∑ i : I, ∑ m ∈ S,
            if exponent i = m then scalar i else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ i : I, scalar i := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ m ∈ S, if exponent i = m then scalar i else 0) =
              (if exponent i = exponent i then scalar i else 0) := by
            apply Finset.sum_eq_single (exponent i)
            · intro m hm hne
              rw [if_neg (Ne.symm hne)]
            · simp [S]
          _ = scalar i := by simp
  · intro m hm
    have hnone : ∀ i : I, exponent i ≠ m := by
      intro i heq
      apply hm
      simp [S, ← heq]
    simp [hnone]

noncomputable def ons_decFormalBucketTerm
    (L : ℕ) [NeZero L] (omega u v : ℂ) (decWeight : ons_DecEdge L → ℂ)
    (r : ℕ) (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ((∑ d : Fin (r + 1) → ons_Dart L,
      if ons_decLoopExponent L d = m then
        ons_decLoopScalar L omega u v d
      else 0) / ((r : ℂ) + 1)) *
    m.prod (fun edge n ↦ decWeight edge ^ n)

theorem norm_ons_decFormalBucketTerm_le
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ)
    (m : ons_DecEdge L →₀ ℕ) :
    ‖ons_decFormalBucketTerm L omega u v decWeight r m‖ ≤
      ∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ‖ons_loopWeight
            (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖
        else 0 := by
  unfold ons_decFormalBucketTerm
  rw [Finset.sum_div, Finset.sum_mul]
  calc
    ‖∑ d : Fin (r + 1) → ons_Dart L,
        (if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d else 0) /
            ((r : ℂ) + 1) *
          m.prod (fun edge n ↦ decWeight edge ^ n)‖ ≤
        ∑ d : Fin (r + 1) → ons_Dart L,
          ‖(if ons_decLoopExponent L d = m then
            ons_decLoopScalar L omega u v d else 0) /
              ((r : ℂ) + 1) *
            m.prod (fun edge n ↦ decWeight edge ^ n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ‖ons_loopWeight
            (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖
        else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases heq : ons_decLoopExponent L d = m
      · rw [if_pos heq, if_pos heq, ← heq,
          ons_loopWeight_KWmatDecorationWeightedPhase]
        rw [norm_mul, norm_div]
        have hden : 1 ≤ ‖(r : ℂ) + 1‖ := by
          rw [show (r : ℂ) + 1 = ((r + 1 : ℕ) : ℂ) by norm_num,
            norm_natCast]
          norm_num
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (div_le_self
            (norm_nonneg (ons_decLoopScalar L omega u v d)) hden)
          (norm_nonneg ((ons_decLoopExponent L d).prod
            (fun edge n ↦ decWeight edge ^ n)))
      · simp [heq]

theorem tsum_norm_ons_decFormalBucketTerm_le_loopSum
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    (∑' m : ons_DecEdge L →₀ ℕ,
      ‖ons_decFormalBucketTerm L omega u v decWeight r m‖) ≤
      ∑ d : Fin (r + 1) → ons_Dart L,
        ‖ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖ := by
  classical
  let exponent := fun d : Fin (r + 1) → ons_Dart L ↦
    ons_decLoopExponent L d
  let S : Finset (ons_DecEdge L →₀ ℕ) :=
    Finset.univ.image exponent
  have hterm : Summable fun m : ons_DecEdge L →₀ ℕ ↦
      ‖ons_decFormalBucketTerm L omega u v decWeight r m‖ := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ d : Fin (r + 1) → ons_Dart L,
        ons_decLoopExponent L d ≠ m := by
      intro d heq
      apply hm
      simp [S, exponent, ← heq]
    simp [ons_decFormalBucketTerm, hnone]
  let major := fun m : ons_DecEdge L →₀ ℕ ↦
    ∑ d : Fin (r + 1) → ons_Dart L,
      if ons_decLoopExponent L d = m then
        ‖ons_loopWeight
          (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖
      else 0
  have hmajor : Summable major := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ d : Fin (r + 1) → ons_Dart L,
        ons_decLoopExponent L d ≠ m := by
      intro d heq
      apply hm
      simp [S, exponent, ← heq]
    simp [major, hnone]
  calc
    (∑' m : ons_DecEdge L →₀ ℕ,
      ‖ons_decFormalBucketTerm L omega u v decWeight r m‖) ≤
        ∑' m : ons_DecEdge L →₀ ℕ, major m :=
      Summable.tsum_le_tsum
        (fun m ↦ norm_ons_decFormalBucketTerm_le
          L omega u v decWeight r m) hterm hmajor
    _ = _ := ons_tsum_finite_exponent_buckets_real exponent
      (fun d ↦ ‖ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖)

theorem ons_summable_norm_decFormalBucketTerm
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    Summable fun r : ℕ ↦
      ∑' m : ons_DecEdge L →₀ ℕ,
        ‖ons_decFormalBucketTerm L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m‖ := by
  let M := ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  have hentry : ∀ d₂ d₁, ‖M d₂ d₁‖ ≤ q :=
    norm_ons_KWmatDecorationWeightedPhase_entry_le
      L decWeight a b q hq hall hext
  have hC0 : 0 ≤ (Fintype.card (ons_Dart L) : ℝ) := by positivity
  have hgeomNorm : ‖(Fintype.card (ons_Dart L) : ℝ) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 hq)]
    exact hcard
  have hgeom : Summable fun r : ℕ ↦
      ((Fintype.card (ons_Dart L) : ℝ) * q) ^ (r + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hgeomNorm)
  apply Summable.of_nonneg_of_le
    (fun r ↦ tsum_nonneg (fun m ↦ norm_nonneg _))
    (fun r ↦ ?_) hgeom
  calc
    (∑' m : ons_DecEdge L →₀ ℕ,
        ‖ons_decFormalBucketTerm L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m‖) ≤
      ∑ d : Fin (r + 1) → ons_Dart L,
        ‖ons_loopWeight M d‖ :=
      tsum_norm_ons_decFormalBucketTerm_le_loopSum
        L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
          decWeight r
    _ ≤ ∑ _d : Fin (r + 1) → ons_Dart L, q ^ (r + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_ons_loopWeight_le_pow M q hq hentry d
    _ = ((Fintype.card (ons_Dart L) : ℝ) * q) ^ (r + 1) := by
      simp
      ring

theorem ons_summable_norm_decFormalBucketTerm_fixed
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    (decWeight : ons_DecEdge L → ℂ) (r : ℕ) :
    Summable fun m : ons_DecEdge L →₀ ℕ ↦
      ‖ons_decFormalBucketTerm L omega u v decWeight r m‖ := by
  classical
  let exponent := fun d : Fin (r + 1) → ons_Dart L ↦
    ons_decLoopExponent L d
  let S : Finset (ons_DecEdge L →₀ ℕ) :=
    Finset.univ.image exponent
  apply summable_of_ne_finset_zero (s := S)
  intro m hm
  have hnone : ∀ d : Fin (r + 1) → ons_Dart L,
      ons_decLoopExponent L d ≠ m := by
    intro d heq
    apply hm
    simp [S, exponent, ← heq]
  simp [ons_decFormalBucketTerm, hnone]

theorem ons_summable_norm_decFormalBucketTerm_product
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦
      ‖ons_decFormalBucketTerm L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) decWeight p.1 p.2‖ := by
  rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
  constructor
  · intro r
    exact ons_summable_norm_decFormalBucketTerm_fixed L
      ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) decWeight r
  · exact ons_summable_norm_decFormalBucketTerm
      L decWeight a b q hq hall hext hcard

theorem ons_summable_decFormalBucketTerm_product
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦
      ons_decFormalBucketTerm L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) decWeight p.1 p.2 :=
  Summable.of_norm <|
    ons_summable_norm_decFormalBucketTerm_product
      L decWeight a b q hq hall hext hcard

theorem ons_decFormalLog_evalTerm_eq_bucketTsum
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m
        (ons_decFormalLog L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) *
        ons_mvMonomialValue decWeight m =
      ∑' r : ℕ,
        -ons_decFormalBucketTerm L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m / 2 := by
  change ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) m *
      m.prod (fun edge n ↦ decWeight edge ^ n) = _
  rw [ons_decFormalLogCoeff_eq_tsum]
  calc
    (-(∑' r : ℕ,
        (∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d
          else 0) / ((r : ℂ) + 1)) / 2) *
        m.prod (fun edge n ↦ decWeight edge ^ n) =
      -(∑' r : ℕ,
        ((∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d
          else 0) / ((r : ℂ) + 1)) *
          m.prod (fun edge n ↦ decWeight edge ^ n)) / 2 := by
            rw [tsum_mul_right]
            ring
    _ = ∑' r : ℕ,
        -ons_decFormalBucketTerm L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m / 2 := by
      rw [← tsum_neg, ← tsum_div_const]
      apply tsum_congr
      intro r
      rfl

theorem ons_MvSeriesEvalSummable_decFormalLog
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable
      (ons_decFormalLog L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) decWeight := by
  let term := fun r : ℕ ↦ fun m : ons_DecEdge L →₀ ℕ ↦
    ons_decFormalBucketTerm L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m
  have hnorm : Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦
      ‖term p.1 p.2‖ := by
    exact ons_summable_norm_decFormalBucketTerm_product
      L decWeight a b q hq hall hext hcard
  have hnormScaled : Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦
      ‖-term p.1 p.2 / 2‖ := by
    have hdiv := hnorm.div_const 2
    simpa only [norm_div, norm_neg, Complex.norm_ofNat] using hdiv
  have hswap : Summable fun p : (ons_DecEdge L →₀ ℕ) × ℕ ↦
      ‖-term p.2 p.1 / 2‖ := by
    simpa only [Function.comp_apply] using
      ((Equiv.prodComm (ons_DecEdge L →₀ ℕ) ℕ).summable_iff.mpr
        hnormScaled)
  have houter : Summable fun m : ons_DecEdge L →₀ ℕ ↦
      ∑' r : ℕ, ‖-term r m / 2‖ := hswap.prod
  apply Summable.of_nonneg_of_le
    (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) houter
  rw [ons_decFormalLog_evalTerm_eq_bucketTsum]
  have hfixedNorm : Summable fun r : ℕ ↦ ‖-term r m / 2‖ := by
    simpa only [Function.comp_apply] using
      hswap.comp_injective (i := fun r : ℕ ↦ (m, r))
        (fun _ _ h ↦ congrArg Prod.snd h)
  exact norm_tsum_le_tsum_norm hfixedNorm

theorem ons_mvSeriesEval_decFormalLog
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_mvSeriesEval
        (ons_decFormalLog L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) decWeight =
      -(∑' r : ℕ,
        (∑ d : Fin (r + 1) → ons_Dart L,
          ons_loopWeight
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) d) /
            ((r : ℂ) + 1)) / 2 := by
  let term := fun r : ℕ ↦ fun m : ons_DecEdge L →₀ ℕ ↦
    ons_decFormalBucketTerm L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m
  have hterm : Summable (Function.uncurry term) :=
    ons_summable_decFormalBucketTerm_product
      L decWeight a b q hq hall hext hcard
  have hscaled : Summable (Function.uncurry fun r m ↦ -term r m / 2) :=
    hterm.neg.div_const 2
  unfold ons_mvSeriesEval
  change (∑' m : ons_DecEdge L →₀ ℕ,
      ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) m *
        m.prod (fun edge n ↦ decWeight edge ^ n)) = _
  simp_rw [ons_decFormalLogCoeff_eq_tsum]
  calc
    (∑' m : ons_DecEdge L →₀ ℕ,
        (-(∑' r : ℕ,
          (∑ d : Fin (r + 1) → ons_Dart L,
            if ons_decLoopExponent L d = m then
              ons_decLoopScalar L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d
            else 0) / ((r : ℂ) + 1)) / 2) *
          m.prod (fun edge n ↦ decWeight edge ^ n)) =
        ∑' m, ∑' r, -term r m / 2 := by
      apply tsum_congr
      intro m
      calc
        (-(∑' r : ℕ,
            (∑ d : Fin (r + 1) → ons_Dart L,
              if ons_decLoopExponent L d = m then
                ons_decLoopScalar L ons_turnRoot
                  (ons_spinPhase L a) (ons_spinPhase L b) d
              else 0) / ((r : ℂ) + 1)) / 2) *
            m.prod (fun edge n ↦ decWeight edge ^ n) =
          -(∑' r : ℕ,
            ((∑ d : Fin (r + 1) → ons_Dart L,
              if ons_decLoopExponent L d = m then
                ons_decLoopScalar L ons_turnRoot
                  (ons_spinPhase L a) (ons_spinPhase L b) d
              else 0) / ((r : ℂ) + 1)) *
              m.prod (fun edge n ↦ decWeight edge ^ n)) / 2 := by
                rw [tsum_mul_right]
                ring
        _ = ∑' r, -term r m / 2 := by
          rw [← tsum_neg, ← tsum_div_const]
          apply tsum_congr
          intro r
          rfl
    _ = ∑' r, ∑' m, -term r m / 2 := hscaled.tsum_comm
    _ = ∑' r : ℕ,
        -(∑ d : Fin (r + 1) → ons_Dart L,
          ons_loopWeight
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) d) /
            ((r : ℂ) + 1) / 2 := by
      apply tsum_congr
      intro r
      rw [tsum_div_const, tsum_neg]
      dsimp only [term]
      simp only [ons_decFormalBucketTerm]
      rw [ons_decFormalBucket_eval_div_eq_loopSum]
      ring
    _ = ∑' r : ℕ,
        -((∑ d : Fin (r + 1) → ons_Dart L,
          ons_loopWeight
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) d) /
            ((r : ℂ) + 1)) / 2 := by
      apply tsum_congr
      intro r
      ring
    _ = _ := by rw [tsum_div_const, tsum_neg]

theorem ons_mvSeriesEval_decFormalRoot
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_mvSeriesEval
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) decWeight =
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) := by
  rw [ons_decFormalRoot,
    ons_mvSeriesEval_subst_exp
      (ons_decFormalLog L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) decWeight
      (ons_decFormalLog_hasSubst L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      (ons_MvSeriesEvalSummable_decFormalLog
        L decWeight a b q hq hall hext hcard),
    ons_mvSeriesEval_decFormalLog L decWeight a b q hq hall hext hcard]
  rfl

theorem ons_MvSeriesEvalSummable_decFormalRoot
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) decWeight := by
  unfold ons_decFormalRoot
  exact ons_MvSeriesEvalSummable_subst_exp
    (ons_decFormalLog L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)) decWeight
    (ons_decFormalLog_hasSubst L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b))
    (ons_MvSeriesEvalSummable_decFormalLog
      L decWeight a b q hq hall hext hcard)

theorem ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L)
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_decoratedFullWeightedSpinSum L decWeight a b := by
  rw [← ons_mvSeriesEval_decFormalRoot
      L decWeight a b q hq hall hext hcard,
    ons_decoratedFormalKacWardIdentity_eval L hformal]

end StatMech.Onsager
