/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationExternalDeletion









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_neg_one_add_eq_iff_eq_one_add
    {R : Type*} [CommRing R] (x y : R) :
    -1 + x = y ↔ x = 1 + y := by
  constructor
  · intro h
    calc
      x = 1 + (-1 + x) := by ring
      _ = 1 + y := by rw [h]
  · intro h
    calc
      -1 + x = -1 + (1 + y) := by rw [h]
      _ = y := by ring

theorem ons_one_add_eq_iff_eq_neg_one_add
    {R : Type*} [CommRing R] (x y : R) :
    1 + x = y ↔ x = -1 + y := by
  constructor
  · intro h
    calc
      x = -1 + (1 + x) := by ring
      _ = -1 + y := by rw [h]
  · intro h
    calc
      1 + x = 1 + (-1 + y) := by rw [h]
      _ = y := by ring

theorem ons_decChainPathIndices_zero_mem_iff
    (a b : Fin 4) :
    (0 : Fin 3) ∈ ons_decChainPathIndices a b ↔
      (a = 0) ≠ (b = 0) := by
  fin_cases a <;> fin_cases b <;>
    decide

theorem ons_decChainPathIndices_two_mem_iff
    (a b : Fin 4) :
    (2 : Fin 3) ∈ ons_decChainPathIndices a b ↔
      (a = 3) ≠ (b = 3) := by
  fin_cases a <;> fin_cases b <;>
    decide

theorem ons_decChainCross_zero_iff
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hnonUturn : ∀ k : Fin n,
      (loop k).2 ≠ (loop (k + 1)).2 + 2)
    (site : ZMod L × ZMod L) (k : Fin n) :
    ((loop k).1 = site ∧
      (0 : Fin 3) ∈ ons_decChainPathIndices
        ((loop (k + 1)).2 + 2) (loop k).2) ↔
      loop k = (site, 0) ∨
        loop (k + 1) = ons_dartRev L (site, 0) := by
  rcases hcur : loop k with ⟨currentSite, currentDir⟩
  rcases hnext : loop (k + 1) with ⟨nextSite, nextDir⟩
  have hv := hvalid k
  have hnu := hnonUturn k
  rw [hcur, hnext] at hv
  rw [hcur, hnext] at hnu
  fin_cases currentDir <;> fin_cases nextDir <;>
    simp [ons_decChainPathIndices_zero_mem_iff,
      ons_dartRev, ons_dirStep,
      ons_neg_one_add_eq_iff_eq_one_add] at hv hnu ⊢ <;>
    simp_all [Prod.ext_iff] <;> ring_nf
  all_goals
    intro _
    exact ons_neg_one_add_eq_iff_eq_one_add _ _

theorem ons_decChainCross_two_iff
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hnonUturn : ∀ k : Fin n,
      (loop k).2 ≠ (loop (k + 1)).2 + 2)
    (site : ZMod L × ZMod L) (k : Fin n) :
    ((loop k).1 = site ∧
      (2 : Fin 3) ∈ ons_decChainPathIndices
        ((loop (k + 1)).2 + 2) (loop k).2) ↔
      loop k = (site, 3) ∨
        loop (k + 1) = ons_dartRev L (site, 3) := by
  rcases hcur : loop k with ⟨currentSite, currentDir⟩
  rcases hnext : loop (k + 1) with ⟨nextSite, nextDir⟩
  have hv := hvalid k
  have hnu := hnonUturn k
  rw [hcur, hnext] at hv
  rw [hcur, hnext] at hnu
  fin_cases currentDir <;> fin_cases nextDir <;>
    simp [ons_decChainPathIndices_two_mem_iff,
      ons_dartRev, ons_dirStep,
      ons_one_add_eq_iff_eq_neg_one_add] at hv hnu ⊢ <;>
    simp_all [Prod.ext_iff] <;> ring_nf
  all_goals
    intro _
    exact ons_one_add_eq_iff_eq_neg_one_add _ _

theorem ons_decLoop_nonUturn_of_scalar_ne_zero
    (L : ℕ) (omega u v : ℂ) {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (hscalar : ons_decLoopScalar L omega u v loop ≠ 0) :
    ∀ k : Fin n, (loop k).2 ≠ (loop (k + 1)).2 + 2 := by
  intro k hturn
  have hfactor : ons_decTransitionScalar L omega u v
      (loop k) (loop (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold ons_decLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  have hvalid := ons_decLoop_valid_of_scalar_ne_zero
    L omega u v loop hscalar k
  unfold ons_decTransitionScalar at hfactor
  simp [hvalid, hturn, ons_turnW_uturn] at hfactor

theorem ons_sum_indicator_eq_visitCount
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (e : E) (loop : Fin n → E) :
    (∑ k, if loop k = e then 1 else 0) =
      ons_visitCount e loop := by
  rw [ons_visitCount_eq_card_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter]

theorem ons_decLoopExponent_chain_zero_eq_visits
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hnonUturn : ∀ k : Fin n,
      (loop k).2 ≠ (loop (k + 1)).2 + 2)
    (site : ZMod L × ZMod L) :
    ons_decLoopExponent L loop (ons_decChainEdge site 0) =
      ons_visitCount (site, 0) loop +
        ons_visitCount (ons_dartRev L (site, 0)) loop := by
  rw [ons_decLoopExponent_chain_apply]
  have hterm : ∀ k : Fin n,
      (if (loop k).1 = site ∧
          (0 : Fin 3) ∈ ons_decChainPathIndices
            ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0) =
        (if loop k = (site, 0) then 1 else 0) +
          if loop (k + 1) = ons_dartRev L (site, 0) then 1 else 0 := by
    intro k
    apply Eq.trans (if_congr
      (ons_decChainCross_zero_iff L loop hvalid hnonUturn site k)
      rfl rfl)
    by_cases hcur : loop k = (site, 0)
    · have hnext : loop (k + 1) ≠ ons_dartRev L (site, 0) := by
        intro hnext
        apply hnonUturn k
        rw [hcur, hnext]
        simp [ons_dartRev]
      simp [hcur, hnext]
    · by_cases hnext : loop (k + 1) = ons_dartRev L (site, 0)
      · simp [hcur, hnext]
      · simp [hcur, hnext]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Finset.sum_add_distrib, ons_sum_indicator_eq_visitCount]
  have hreindex :
      (∑ k, if loop (k + 1) = ons_dartRev L (site, 0) then 1 else 0) =
        ∑ k, if loop k = ons_dartRev L (site, 0) then 1 else 0 :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => if loop k = ons_dartRev L (site, 0) then 1 else 0)
  rw [hreindex, ons_sum_indicator_eq_visitCount]

theorem ons_decLoopExponent_chain_two_eq_visits
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hnonUturn : ∀ k : Fin n,
      (loop k).2 ≠ (loop (k + 1)).2 + 2)
    (site : ZMod L × ZMod L) :
    ons_decLoopExponent L loop (ons_decChainEdge site 2) =
      ons_visitCount (site, 3) loop +
        ons_visitCount (ons_dartRev L (site, 3)) loop := by
  rw [ons_decLoopExponent_chain_apply]
  have hterm : ∀ k : Fin n,
      (if (loop k).1 = site ∧
          (2 : Fin 3) ∈ ons_decChainPathIndices
            ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0) =
        (if loop k = (site, 3) then 1 else 0) +
          if loop (k + 1) = ons_dartRev L (site, 3) then 1 else 0 := by
    intro k
    apply Eq.trans (if_congr
      (ons_decChainCross_two_iff L loop hvalid hnonUturn site k)
      rfl rfl)
    by_cases hcur : loop k = (site, 3)
    · have hnext : loop (k + 1) ≠ ons_dartRev L (site, 3) := by
        intro hnext
        apply hnonUturn k
        rw [hcur, hnext]
        simp [ons_dartRev]
      simp [hcur, hnext]
    · by_cases hnext : loop (k + 1) = ons_dartRev L (site, 3)
      · simp [hcur, hnext]
      · simp [hcur, hnext]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Finset.sum_add_distrib, ons_sum_indicator_eq_visitCount]
  have hreindex :
      (∑ k, if loop (k + 1) = ons_dartRev L (site, 3) then 1 else 0) =
        ∑ k, if loop k = ons_dartRev L (site, 3) then 1 else 0 :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => if loop k = ons_dartRev L (site, 3) then 1 else 0)
  rw [hreindex, ons_sum_indicator_eq_visitCount]

theorem ons_finsuppProd_scaleDecEdgeWeight
    {L : ℕ} (m : ons_DecEdge L →₀ ℕ)
    (decWeight : ons_DecEdge L → ℂ)
    (edge : ons_DecEdge L) (t : ℂ) :
    m.prod (fun f n =>
        ons_scaleDecEdgeWeight decWeight edge t f ^ n) =
      t ^ m edge *
        m.prod (fun f n => decWeight f ^ n) := by
  classical
  calc
    m.prod (fun f n =>
        ons_scaleDecEdgeWeight decWeight edge t f ^ n) =
        m.prod (fun f n =>
          (if f = edge then t ^ n else 1) *
            decWeight f ^ n) := by
      apply Finsupp.prod_congr
      intro f hf
      unfold ons_scaleDecEdgeWeight
      by_cases hfe : f = edge
      · simp [hfe, mul_pow]
      · simp [hfe]
    _ = m.prod (fun f n => if f = edge then t ^ n else 1) *
          m.prod (fun f n => decWeight f ^ n) :=
      Finsupp.prod_mul
    _ = t ^ m edge *
          m.prod (fun f n => decWeight f ^ n) := by
      congr 1
      unfold Finsupp.prod
      by_cases hedge : edge ∈ m.support
      · rw [Finset.prod_eq_single edge]
        · simp
        · intro f hf hfe
          simp [hfe]
        · exact fun hnot => (hnot hedge).elim
      · have hzero : m edge = 0 :=
          Finsupp.notMem_support_iff.mp hedge
        rw [hzero, pow_zero]
        apply Finset.prod_eq_one
        intro f hf
        have hfe : f ≠ edge := by
          intro h
          subst f
          exact hedge hf
        simp [hfe]

theorem ons_prod_indicator_eq_pow_visitCount
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (e : E) (t : ℂ)
    (loop : Fin n → E) :
    (∏ k, if loop k = e then t else 1) =
      t ^ ons_visitCount e loop := by
  rw [ons_visitCount_eq_card_filter]
  calc
    (∏ k, if loop k = e then t else 1) =
        ∏ k ∈ Finset.univ.filter (fun k => loop k = e), t := by
      rw [Finset.prod_filter]
    _ = t ^ (Finset.univ.filter (fun k => loop k = e)).card := by
      rw [Finset.prod_const]

theorem ons_loopWeight_scaleColumns_pair
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (M : Matrix E E ℂ)
    (e r : E) (her : e ≠ r) (t : ℂ)
    (loop : Fin n → E) :
    ons_loopWeight
        (ons_scaleColumns ({e, r} : Finset E) t M) loop =
      t ^ (ons_visitCount e loop + ons_visitCount r loop) *
        ons_loopWeight M loop := by
  unfold ons_loopWeight ons_scaleColumns
  have hentry : ∀ k : Fin n,
      (if loop (k + 1) ∈ ({e, r} : Finset E) then
          t * M (loop k) (loop (k + 1))
        else M (loop k) (loop (k + 1))) =
        ((if loop (k + 1) = e then t else 1) *
          (if loop (k + 1) = r then t else 1)) *
            M (loop k) (loop (k + 1)) := by
    intro k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases he : loop (k + 1) = e
    · have hr : loop (k + 1) ≠ r := by
        intro hr
        apply her
        rw [← he, hr]
      simp [he, hr, her, Ne.symm her]
    · by_cases hr : loop (k + 1) = r
      · simp [he, hr, her, Ne.symm her]
      · simp [he, hr]
  rw [Finset.prod_congr rfl (fun k _ => hentry k),
    Finset.prod_mul_distrib]
  have hreindex (x : E) :
      (∏ k, if loop (k + 1) = x then t else 1) =
        ∏ k, if loop k = x then t else 1 :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k => if loop k = x then t else 1)
  rw [Finset.prod_mul_distrib, hreindex e, hreindex r,
    ons_prod_indicator_eq_pow_visitCount,
    ons_prod_indicator_eq_pow_visitCount, pow_add]

theorem ons_loopWeight_scale_chain_zero_eq_scaleColumns
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 0) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop =
      ons_loopWeight
        (ons_scaleColumns
          ({(site, 0), ons_dartRev L (site, 0)} :
            Finset (ons_Dart L)) t
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
  rw [ons_loopWeight_KWmatDecorationWeightedPhase,
    ons_finsuppProd_scaleDecEdgeWeight]
  by_cases hscalar : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
  · rw [hscalar, zero_mul]
    have hscaled := ons_loopWeight_scaleColumns_pair
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      (site, 0) (ons_dartRev L (site, 0))
      (ons_dartRev_ne L (site, 0)).symm t loop
    rw [hscaled, ons_loopWeight_KWmatDecorationWeightedPhase, hscalar,
      zero_mul, mul_zero]
  · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        loop hscalar
    have hnon := ons_decLoop_nonUturn_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        loop hscalar
    rw [ons_decLoopExponent_chain_zero_eq_visits
      L loop hvalid hnon site]
    have hscaled := ons_loopWeight_scaleColumns_pair
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      (site, 0) (ons_dartRev L (site, 0))
      (ons_dartRev_ne L (site, 0)).symm t loop
    rw [hscaled, ons_loopWeight_KWmatDecorationWeightedPhase]
    ring

theorem ons_loopWeight_scale_chain_two_eq_scaleColumns
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 2) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop =
      ons_loopWeight
        (ons_scaleColumns
          ({(site, 3), ons_dartRev L (site, 3)} :
            Finset (ons_Dart L)) t
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
  rw [ons_loopWeight_KWmatDecorationWeightedPhase,
    ons_finsuppProd_scaleDecEdgeWeight]
  by_cases hscalar : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
  · rw [hscalar, zero_mul]
    have hscaled := ons_loopWeight_scaleColumns_pair
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      (site, 3) (ons_dartRev L (site, 3))
      (ons_dartRev_ne L (site, 3)).symm t loop
    rw [hscaled, ons_loopWeight_KWmatDecorationWeightedPhase, hscalar,
      zero_mul, mul_zero]
  · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        loop hscalar
    have hnon := ons_decLoop_nonUturn_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        loop hscalar
    rw [ons_decLoopExponent_chain_two_eq_visits
      L loop hvalid hnon site]
    have hscaled := ons_loopWeight_scaleColumns_pair
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      (site, 3) (ons_dartRev L (site, 3))
      (ons_dartRev_ne L (site, 3)).symm t loop
    rw [hscaled, ons_loopWeight_KWmatDecorationWeightedPhase]
    ring

theorem ons_detWalkRoot_eq_of_loopWeight_eq
    {E : Type*} [Fintype E] [DecidableEq E]
    (M N : Matrix E E ℂ)
    (hloop : ∀ (n : ℕ) (loop : Fin (n + 1) → E),
      ons_loopWeight M loop = ons_loopWeight N loop) :
    ons_detWalkRoot M = ons_detWalkRoot N := by
  unfold ons_detWalkRoot
  apply congrArg Complex.exp
  congr 1
  apply congrArg Neg.neg
  apply tsum_congr
  intro n
  apply congrArg (· / ((n : ℂ) + 1))
  apply Finset.sum_congr rfl
  intro loop hmem
  simpa only [ons_loopWeight] using hloop n loop

theorem ons_detWalkRoot_scale_chain_zero_eq_scaleColumns
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 0) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
        (ons_scaleColumns
          ({(site, 0), ons_dartRev L (site, 0)} :
            Finset (ons_Dart L)) t
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact ons_loopWeight_scale_chain_zero_eq_scaleColumns
    L decWeight a b site t loop

theorem ons_detWalkRoot_scale_chain_two_eq_scaleColumns
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 2) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
        (ons_scaleColumns
          ({(site, 3), ons_dartRev L (site, 3)} :
            Finset (ons_Dart L)) t
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact ons_loopWeight_scale_chain_two_eq_scaleColumns
    L decWeight a b site t loop

theorem ons_detWalkRoot_scale_chain_zero_affine
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentryAux : ∀ d₂ d₁,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          s((site, 0), ons_dartRev L (site, 0)) t)
        ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        d₂ d₁‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 0) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({(site, 0), ons_dartRev L (site, 0)} :
              Finset (ons_Dart L))
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          (site, 0) (ons_dartRev L (site, 0)) s) := by
  have hroot := ons_detWalkRoot_scale_chain_zero_eq_scaleColumns
    L decWeight a b site t
  have haff := ons_detWalkRoot_decoration_scaleExternal_affine
    L decWeight a b q hq t (site, 0) hentryAux hsmall hcard
  rw [ons_KWmatDecorationWeightedPhase_scaleExternal] at haff
  exact hroot.trans haff

theorem ons_detWalkRoot_scale_chain_two_affine
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentryAux : ∀ d₂ d₁,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          s((site, 3), ons_dartRev L (site, 3)) t)
        ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        d₂ d₁‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 2) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({(site, 3), ons_dartRev L (site, 3)} :
              Finset (ons_Dart L))
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          (site, 3) (ons_dartRev L (site, 3)) s) := by
  have hroot := ons_detWalkRoot_scale_chain_two_eq_scaleColumns
    L decWeight a b site t
  have haff := ons_detWalkRoot_decoration_scaleExternal_affine
    L decWeight a b q hq t (site, 3) hentryAux hsmall hcard
  rw [ons_KWmatDecorationWeightedPhase_scaleExternal] at haff
  exact hroot.trans haff

end StatMech.Onsager
