/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargePerronIdentification

open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeRotatedNormalizedWave (r k : Nat) (c : Real) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeNormalizedWave r k c x).re

def sixVertexFixedChargeRotatedLimitingWave (r k : Nat) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeLimitingWave r k x).re

theorem tendsto_sixVertexFixedChargeRotatedNormalizedWave
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => sixVertexFixedChargeRotatedNormalizedWave r k c x)
      atTop (nhds (sixVertexFixedChargeRotatedLimitingWave r k x)) := by
  unfold sixVertexFixedChargeRotatedNormalizedWave
    sixVertexFixedChargeRotatedLimitingWave
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul
      (tendsto_sixVertexFixedChargeNormalizedWave r k x))

private theorem rotatedNormalizedWave_eigenrelation_of_complex
    {c mu : Real} (r k : Nat)
    (hcomplex : forall x, ∑ y,
      ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c x y : Real) : Complex) *
          sixVertexFixedChargeNormalizedWave r k c y =
        (mu : Complex) * sixVertexFixedChargeNormalizedWave r k c x) :
    sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheParticleCount r k) c *ᵥ
      sixVertexFixedChargeRotatedNormalizedWave r k c =
        mu • sixVertexFixedChargeRotatedNormalizedWave r k c := by
  funext x
  let a : Complex := (-Complex.I) ^ sixVertexFixedChargeBethePairCount r k
  have hx := hcomplex x
  have hrot := congrArg Complex.re (congrArg (fun z : Complex => a * z) hx)
  change (∑ y, sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) c x y *
        (a * sixVertexFixedChargeNormalizedWave r k c y).re) =
    mu * (a * sixVertexFixedChargeNormalizedWave r k c x).re
  calc
    _ = (a * ∑ y,
        (sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Complex) *
            sixVertexFixedChargeNormalizedWave r k c y).re := by
      rw [Finset.mul_sum]
      symm
      change Complex.reCLM (∑ y,
        a * ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c x y : Complex) *
            sixVertexFixedChargeNormalizedWave r k c y)) = _
      rw [map_sum Complex.reCLM]
      apply Finset.sum_congr rfl
      intro y _
      change (a *
          ((sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) c x y : Complex) *
              sixVertexFixedChargeNormalizedWave r k c y)).re =
        sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k) c x y *
          (a * sixVertexFixedChargeNormalizedWave r k c y).re
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring
    _ = (a * ((mu : Complex) *
        sixVertexFixedChargeNormalizedWave r k c x)).re := hrot
    _ = _ := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring

theorem eventually_sixVertexFixedEvenChargeRotatedNormalizedWave_eigenrelation
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) c *ᵥ
        sixVertexFixedChargeRotatedNormalizedWave (2 * s) k c =
      sixVertexFixedEvenChargeBetheCandidateNormalized s k c •
        sixVertexFixedChargeRotatedNormalizedWave (2 * s) k c := by
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  apply rotatedNormalizedWave_eigenrelation_of_complex (2 * s) k
  rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc]
  exact sixVertexFixedChargeNormalizedWave_eigenrelation hc (2 * s) k
    (sixVertexFixedEvenChargeBetheRoots_eigenrelation_value hc s k)

theorem eventually_sixVertexFixedOddChargeRotatedNormalizedWave_eigenrelation
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexSectorTransferNormalized (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c *ᵥ
        sixVertexFixedChargeRotatedNormalizedWave (2 * s + 1) k c =
      sixVertexFixedOddChargeBetheCandidateNormalized s k c •
        sixVertexFixedChargeRotatedNormalizedWave (2 * s + 1) k c := by
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  apply rotatedNormalizedWave_eigenrelation_of_complex (2 * s + 1) k
  rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc]
  exact sixVertexFixedChargeNormalizedWave_eigenrelation hc (2 * s + 1) k
    (sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge
      hc ⟨s, by omega⟩ k)

private theorem limitingWave_eq_zero_of_infinity_eigenrelation
    (r k : Nat) (mu : Real) (hmu : mu ≠ 0)
    (hfull : forall x, ∑ y,
      sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x y *
        sixVertexFixedChargeLimitingWave r k y =
      (mu : Complex) * sixVertexFixedChargeLimitingWave r k x)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : ¬ SixVertexSectorNoAdjacent x) :
    sixVertexFixedChargeLimitingWave r k x = 0 := by
  have heq := hfull x
  have hleft : (∑ y,
      sixVertexSectorTransferInfinity (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) x y *
        sixVertexFixedChargeLimitingWave r k y) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx]
    simp
  rw [hleft] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (by exact_mod_cast hmu)

theorem sixVertexFixedEvenChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent
    (s k : Nat)
    (x : SixVertexSector (sixVertexFourWidth (2 * s) k)
      (sixVertexFixedChargeBetheParticleCount (2 * s) k))
    (hx : ¬ SixVertexSectorNoAdjacent x) :
    sixVertexFixedChargeRotatedLimitingWave (2 * s) k x = 0 := by
  unfold sixVertexFixedChargeRotatedLimitingWave
  rw [limitingWave_eq_zero_of_infinity_eigenrelation (2 * s) k
    (sixVertexFixedEvenChargeBetheCandidateInfinity s k)
    (by
      rw [sixVertexFixedEvenChargeBetheCandidateInfinity_eq_Perron]
      exact (sixVertexNoAdjacentInfinityTopEigenvalue_pos
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k)).ne')
    (sixVertexFixedEvenChargeLimitingWave_eigenrelation s k) x hx]
  simp

theorem sixVertexFixedOddChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent
    (s k : Nat)
    (x : SixVertexSector (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k))
    (hx : ¬ SixVertexSectorNoAdjacent x) :
    sixVertexFixedChargeRotatedLimitingWave (2 * s + 1) k x = 0 := by
  unfold sixVertexFixedChargeRotatedLimitingWave
  rw [limitingWave_eq_zero_of_infinity_eigenrelation (2 * s + 1) k
    (sixVertexFixedOddChargeBetheCandidateInfinity s k)
    (by
      rw [sixVertexFixedOddChargeBetheCandidateInfinity_eq_Perron]
      exact (sixVertexNoAdjacentInfinityTopEigenvalue_pos
        (sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k)).ne')
    (sixVertexFixedOddChargeLimitingWave_eigenrelation s k) x hx]
  simp

private theorem eventually_eq_top_of_rotatedWave_limit
    (r k : Nat) (mu : Real -> Real)
    (heig : ∀ᶠ c : Real in atTop,
      sixVertexSectorTransferNormalized (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k) c *ᵥ
        sixVertexFixedChargeRotatedNormalizedWave r k c =
      mu c • sixVertexFixedChargeRotatedNormalizedWave r k c)
    (hzero : forall x, ¬ SixVertexSectorNoAdjacent x ->
      sixVertexFixedChargeRotatedLimitingWave r k x = 0) :
    ∀ᶠ c : Real in atTop,
      mu c = sixVertexSectorTopEigenvalue (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (by
            have := sixVertexFixedChargeBetheParticleCount_twice_le r k
            omega) c /
        (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount r k := by
  classical
  let N := sixVertexFourWidth r k
  let n := sixVertexFixedChargeBetheParticleCount r k
  let v := sixVertexFixedChargeRotatedNormalizedWave r k
  let v0 := sixVertexFixedChargeRotatedLimitingWave r k
  let inactive : Finset (SixVertexSector N n) :=
    Finset.univ.filter fun x => ¬ SixVertexSectorNoAdjacent x
  have hn : 0 < n := sixVertexFixedChargeBetheParticleCount_pos r k
  have hnN : n <= N := by
    have := sixVertexFixedChargeBetheParticleCount_twice_le r k
    omega
  have hhalf : 2 * n <= N := sixVertexFixedChargeBetheParticleCount_twice_le r k
  let even := sixVertexAlternatingEvenSector N n hhalf
  let odd := sixVertexAlternatingOddSector N n hhalf
  have hadj : (sixVertexInfinityGraph N n).Adj even odd :=
    sixVertexInfinityGraph_adj_alternating hn hhalf
  have hinfEntry : sixVertexSectorTransferInfinity N n even odd = 1 := by
    rw [← sixVertexInfinityGraph_adjMatrix]
    simp [SimpleGraph.adjMatrix, hadj]
  have hentry : Tendsto
      (fun c => sixVertexSectorTransferNormalized N n c even odd)
      atTop (nhds 1) := by
    simpa [sixVertexSectorTransferNormalized, hinfEntry] using
      tendsto_sixVertexSectorTransfer_normalized_atTop hn even odd
  have hentryLower : ∀ᶠ c : Real in atTop,
      (1 / 2 : Real) < sixVertexSectorTransferNormalized N n c even odd :=
    hentry.eventually_const_lt (by norm_num)
  have hrowSmall : ∀ᶠ c : Real in atTop, forall x,
      ¬ SixVertexSectorNoAdjacent x ->
      (∑ y, sixVertexSectorTransferNormalized N n c x y) < 1 / 2 := by
    apply Filter.eventually_all.mpr
    intro x
    by_cases hx : SixVertexSectorNoAdjacent x
    · exact Filter.Eventually.of_forall fun _ hnx => False.elim (hnx hx)
    · have hrow : Tendsto
          (fun c => ∑ y, sixVertexSectorTransferNormalized N n c x y)
          atTop (nhds 0) := by
        have hs := tendsto_finsetSum Finset.univ fun y _ =>
          tendsto_sixVertexSectorTransfer_normalized_atTop hn x y
        have hlim : (∑ y, sixVertexSectorTransferInfinity N n x y) = 0 := by
          apply Finset.sum_eq_zero
          intro y _
          exact sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx y
        simpa [hlim] using hs
      exact (hrow.eventually_lt_const
        (by norm_num : (0 : Real) < 1 / 2)).mono fun _ hlt _ => hlt
  have hvActive : ∀ᶠ c : Real in atTop, forall x,
      SixVertexSectorNoAdjacent x -> 0 < v c x := by
    apply Filter.eventually_all.mpr
    intro x
    by_cases hx : SixVertexSectorNoAdjacent x
    · exact ((tendsto_sixVertexFixedChargeRotatedNormalizedWave r k x)
        |>.eventually_const_lt
          (sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
            r k x hx)).mono fun _ hlt _ => hlt
    · exact Filter.Eventually.of_forall fun _ hx' => False.elim (hx hx')
  have hinactiveAbs : Tendsto
      (fun c => ∑ x ∈ inactive, |v c x|) atTop (nhds 0) := by
    have hs := tendsto_finsetSum inactive fun x hx =>
      (continuous_abs.continuousAt.tendsto.comp
        (tendsto_sixVertexFixedChargeRotatedNormalizedWave r k x))
    have hlim (x : SixVertexSector N n) (hx : x ∈ inactive) : v0 x = 0 := by
      apply hzero x
      exact Finset.mem_filter.mp hx |>.2
    have hlimSum : (∑ x ∈ inactive, |v0 x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hlim x hx, abs_zero]
    simpa [v, v0, hlimSum] using hs
  have hgap : ∀ᶠ c : Real in atTop, forall x,
      SixVertexSectorNoAdjacent x ->
      0 < v c x - ∑ y ∈ inactive, |v c y| := by
    apply Filter.eventually_all.mpr
    intro x
    by_cases hx : SixVertexSectorNoAdjacent x
    · have ht := (tendsto_sixVertexFixedChargeRotatedNormalizedWave r k x).sub
          hinactiveAbs
      have hv0pos : 0 < v0 x := by
        exact sixVertexFixedChargeLimitingWave_rotated_re_pos_of_noAdjacent
          r k x hx
      exact (ht.eventually_const_lt (by simpa [v, v0] using hv0pos)).mono
        fun _ hlt _ => hlt
    · exact Filter.Eventually.of_forall fun _ hx' => False.elim (hx hx')
  filter_upwards [heig, hentryLower, hrowSmall, hvActive, hgap,
    eventually_gt_atTop (2 : Real)] with c hveig hentry hrows hvpos hgapc hc
  let top := sixVertexSectorTopEigenvalue N n hnN c /
    (c ^ 2 - 2) ^ n
  have hden : 0 < (c ^ 2 - 2) ^ n := pow_pos (by nlinarith) n
  have htopLower : (1 / 2 : Real) < top := by
    have hraw := sixVertexSectorTransfer_entry_le_top
      (c := c) hnN (by linarith) even odd
    have hdiv := div_le_div_of_nonneg_right hraw hden.le
    exact lt_of_lt_of_le hentry (by simpa [top, sixVertexSectorTransferNormalized] using hdiv)
  obtain ⟨u, hupos, hueig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector hnN (by linarith : 0 < c)
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hnN
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image
    (Finset.univ : Finset (SixVertexSector N n)) (fun x => u x)
    Finset.univ_nonempty
  have hiActive : SixVertexSectorNoAdjacent i := by
    by_contra hia
    have hcoord := congrFun hueig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcoord
    have hnorm :
        (∑ j, sixVertexSectorTransferNormalized N n c i j * u j) =
          top * u i := by
      calc
        _ = (∑ j, sixVertexSectorTransfer N n c i j * u j) /
            (c ^ 2 - 2) ^ n := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          simp [sixVertexSectorTransferNormalized]
          ring
        _ = _ := by rw [hcoord]; ring
    have hupper :
        (∑ j, sixVertexSectorTransferNormalized N n c i j * u j) <=
          (∑ j, sixVertexSectorTransferNormalized N n c i j) * u i := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j))
      exact div_nonneg (sixVertexSectorTransfer_nonneg (by linarith) i j) hden.le
    rw [hnorm] at hupper
    have := hrows i hia
    nlinarith [hupos i]
  let S : Real := ∑ j, u j * v c j
  have hSinactive :
      -(u i * ∑ j ∈ inactive, |v c j|) <=
        ∑ j ∈ inactive, u j * v c j := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have huji : u j <= u i := hi j (Finset.mem_univ j)
    have habs : -|v c j| <= v c j := neg_abs_le (v c j)
    have h1 := mul_le_mul_of_nonneg_left habs (hupos j).le
    have h2 := neg_le_neg
      (mul_le_mul_of_nonneg_right huji (abs_nonneg (v c j)))
    nlinarith
  have hSactive : 0 <=
      ∑ j ∈ (Finset.univ.filter fun x : SixVertexSector N n =>
        SixVertexSectorNoAdjacent x).erase i, u j * v c j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hupos j).le (hvpos j (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase hj) |>.2)).le
  have hSdecomp : S = u i * v c i +
      (∑ j ∈ (Finset.univ.filter fun x : SixVertexSector N n =>
        SixVertexSectorNoAdjacent x).erase i, u j * v c j) +
      ∑ j ∈ inactive, u j * v c j := by
    unfold S inactive
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
      SixVertexSectorNoAdjacent (fun j => u j * v c j)
    have hiMem : i ∈ Finset.univ.filter SixVertexSectorNoAdjacent := by
      simp [hiActive]
    have herase := Finset.sum_erase_add
      (Finset.univ.filter SixVertexSectorNoAdjacent)
      (fun j => u j * v c j) hiMem
    linarith
  have hSpos : 0 < S := by
    rw [hSdecomp]
    have hg := hgapc i hiActive
    nlinarith [hupos i, hSinactive, hSactive]
  have hadj : ∑ j, u j *
      (sixVertexSectorTransferNormalized N n c *ᵥ v c) j =
      ∑ j, (sixVertexSectorTransferNormalized N n c *ᵥ
        (fun x => u x)) j * v c j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    have hsym : sixVertexSectorTransfer N n c y x =
        sixVertexSectorTransfer N n c x y :=
      sixVertexTransfer_symmetric N c (sixVertexSectorRow y)
        (sixVertexSectorRow x)
    simp [sixVertexSectorTransferNormalized, hsym, div_eq_mul_inv]
    ring
  have htopEig : sixVertexSectorTransferNormalized N n c *ᵥ
      (fun x => u x) = top • (fun x => u x) := by
    funext x
    have hx := congrFun hueig x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx ⊢
    calc
      _ = (∑ y, sixVertexSectorTransfer N n c x y * u y) /
          (c ^ 2 - 2) ^ n := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        simp [sixVertexSectorTransferNormalized]
        ring
      _ = _ := by rw [hx]; ring
  rw [hveig, htopEig] at hadj
  simp only [Pi.smul_apply, smul_eq_mul] at hadj
  have : mu c * S = top * S := by
    unfold S
    calc
      mu c * ∑ j, u j * v c j = ∑ j, u j * (mu c * v c j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, (top * u j) * v c j := hadj
      _ = top * ∑ j, u j * v c j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  nlinarith

theorem eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_eq_top
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexFixedEvenChargeBetheCandidateNormalized s k c =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s) k)
            (by
              have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
              omega) c /
          (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount (2 * s) k :=
  eventually_eq_top_of_rotatedWave_limit (2 * s) k
    (sixVertexFixedEvenChargeBetheCandidateNormalized s k)
    (eventually_sixVertexFixedEvenChargeRotatedNormalizedWave_eigenrelation s k)
    (sixVertexFixedEvenChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent s k)

theorem eventually_sixVertexFixedOddChargeBetheCandidateNormalized_eq_top
    (s k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexFixedOddChargeBetheCandidateNormalized s k c =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
            (by
              have := sixVertexFixedChargeBetheParticleCount_twice_le
                (2 * s + 1) k
              omega) c /
          (c ^ 2 - 2) ^
            sixVertexFixedChargeBetheParticleCount (2 * s + 1) k :=
  eventually_eq_top_of_rotatedWave_limit (2 * s + 1) k
    (sixVertexFixedOddChargeBetheCandidateNormalized s k)
    (eventually_sixVertexFixedOddChargeRotatedNormalizedWave_eigenrelation s k)
    (sixVertexFixedOddChargeRotatedLimitingWave_eq_zero_of_not_noAdjacent s k)

theorem eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top
    (s k : Nat) :
    ∀ᶠ c : Real in atTop, forall hc : 2 < c,
      sixVertexFixedEvenChargeBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (by
            have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
            omega) c := by
  filter_upwards
    [eventually_sixVertexFixedEvenChargeBetheCandidateNormalized_eq_top s k,
      eventually_gt_atTop (2 : Real)] with c heq hc
  intro hc'
  rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc'] at heq
  have hscale : (c ^ 2 - 2) ^
      sixVertexFixedChargeBetheParticleCount (2 * s) k ≠ 0 := by
    exact pow_ne_zero _ (by nlinarith)
  field_simp [hscale] at heq
  exact heq

theorem eventually_sixVertexFixedOddChargeBetheCandidate_eq_top
    (s k : Nat) :
    ∀ᶠ c : Real in atTop, forall hc : 2 < c,
      sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (by
            have := sixVertexFixedChargeBetheParticleCount_twice_le
              (2 * s + 1) k
            omega) c := by
  filter_upwards
    [eventually_sixVertexFixedOddChargeBetheCandidateNormalized_eq_top s k,
      eventually_gt_atTop (2 : Real)] with c heq hc
  intro hc'
  rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc'] at heq
  have hscale : (c ^ 2 - 2) ^
      sixVertexFixedChargeBetheParticleCount (2 * s + 1) k ≠ 0 := by
    exact pow_ne_zero _ (by nlinarith)
  field_simp [hscale] at heq
  exact heq

end

end StatMech.FrontierD
