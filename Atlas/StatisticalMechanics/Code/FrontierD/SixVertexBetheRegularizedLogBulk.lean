/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRegularizedLogTaylor
import Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalEvenCommonHalfRoot hc s k j))

private theorem sum_even_symmetric_regularized
    (c epsilon : Real) (m : Nat) {p : Fin (m + m) -> Real}
    (hp : SixVertexRootSymmetric p) :
    (∑ i, sixVertexRegularizedBetheLogKernel c epsilon (p i)) =
      2 * ∑ j, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j) := by
  rw [<- sixVertexEvenSymmetricLift_projection m hp, Fin.sum_univ_add]
  have hneg :
      (∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift m
          (sixVertexEvenPositiveHalfProjection m p) (Fin.castAdd m j))) =
      ∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j) := by
    rw [show (∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift m
          (sixVertexEvenPositiveHalfProjection m p) (Fin.castAdd m j))) =
      ∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j.rev) by
      apply Finset.sum_congr rfl
      intro j _
      rw [sixVertexEvenSymmetricLift_castAdd]
      exact even_sixVertexRegularizedBetheLogKernel c epsilon _]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j)))
  rw [hneg]
  simp only [sixVertexEvenSymmetricLift_natAdd,
    sixVertexEvenPositiveHalfProjection_lift]
  ring

theorem eventually_full_regularizedLogDisplacement_eq_two_positive
    {c : Real} (hc : 2 < c) (epsilon : Real) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      (∑ i, (sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k i))) =
        2 * sixVertexCanonicalEvenRegularizedBulkLogDisplacement
          hc epsilon s k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  rw [Finset.sum_sub_distrib,
    sum_even_symmetric_regularized c epsilon (s + k + 1) hk.1.1.2.1,
    sum_even_symmetric_regularized c epsilon (s + k + 1)
      (fun j => sixVertexCanonicalEvenAlignedHalfRoots_rev hc s k j)]
  unfold sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    sixVertexCanonicalFixedEvenDensityPositiveRoots
  have haligned (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k) j =
        sixVertexCanonicalEvenCommonHalfRoot hc s k j := by
    rw [sixVertexEvenPositiveHalfProjection_apply,
      sixVertexCanonicalEvenAlignedHalfRoots_positive]
  simp_rw [haligned]
  rw [Finset.sum_sub_distrib]
  ring

def sixVertexCanonicalEvenRegularizedFullLinearTerm
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  let N := sixVertexFourWidth (2 * s) k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  ∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
      sixVertexCanonicalEvenChargeOffset hc s k i / N

theorem tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s)
      atTop (nhds ((2 * s : Real) *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x))) := by
  let r := 2 * s
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  let G := sixVertexContinuousOffsetFourierBound c
  let Lu := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let D := sixVertexContinuousOffsetFourierLipschitzNNReal c
  let Q := sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D
  let F := U * G / lower
  let integral := ∫ x in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogNormDerivative c epsilon x *
      sixVertexContinuousOffsetFourier c hc x
  let empirical : Nat -> Real := fun k =>
    let N := sixVertexFourWidth r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
      sixVertexContinuousOffsetFourier c hc (q i) /
        sixVertexFiniteRootDensity c N n q (q i)) / N
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hU : 0 <= U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    positivity
  have hG : 0 <= G := by
    dsimp [G, sixVertexContinuousOffsetFourierBound]
    positivity
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
    ((strictMono_nat_of_lt_succ (fun k => by unfold sixVertexFourWidth; omega)).tendsto_atTop)
  have hquad : Tendsto empirical atTop (nhds integral) := by
    let err : Nat -> Real := fun k =>
      (Q : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) /
            ((sixVertexFourWidth r k : Real) * lower)) * (2 * Real.pi) +
        (2 * (r : Real) / sixVertexFourWidth r k) * F +
        2 * F / sixVertexFourWidth r k +
        sixVertexFiniteRootDensityUniformBound c * F *
          ((2 * (r : Real) + 1) /
            ((sixVertexFourWidth r k : Real) * lower))
    have herr : Tendsto err atTop (nhds 0) := by
      have hzero : Tendsto (fun k : Nat =>
          (1 : Real) / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hwidth
      convert hzero.const_mul
        ((Q : Real) * sixVertexFiniteRootDensityUniformBound c *
            ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
          2 * (r : Real) * F + 2 * F +
          sixVertexFiniteRootDensityUniformBound c * F *
            ((2 * (r : Real) + 1) / lower)) using 1
      · funext k
        dsimp [err]
        field_simp [hlower.ne']
      · ring
    rw [Metric.tendsto_atTop] at herr
    apply Metric.tendsto_atTop.2
    intro delta hdelta
    obtain ⟨Kerr, hKerr⟩ := herr delta hdelta
    obtain ⟨Kwit, hKwit⟩ :=
      (eventually_atTop.1
        (eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
          hc s))
    refine ⟨max Kerr Kwit, ?_⟩
    intro k hkmax
    have hkerr : Kerr <= k := le_trans (le_max_left _ _) hkmax
    have hk := hKwit k (le_trans (le_max_right _ _) hkmax)
    have hN : 0 < sixVertexFourWidth r k := sixVertexFourWidth_pos r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    have hcharge : sixVertexFourWidth r k = 2 * n + 2 * r := by
      dsimp [n, r]
      unfold sixVertexFourWidth
      omega
    have hqLip := lipschitzWith_mul_div_sixVertexFiniteRootDensity hc hN
      (by dsimp [n, r]; unfold sixVertexFourWidth; omega) q hlower hU hG
      hk.2
      (lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon)
      (fun x => abs_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon)
      (lipschitzWith_sixVertexContinuousOffsetFourier hc)
      (abs_sixVertexContinuousOffsetFourier_le hc)
    have hbound (x : Real) :
        |sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x /
              sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q x| <= F := by
      rw [abs_div, abs_mul, abs_of_pos (hlower.trans_le (hk.2 x))]
      have hprod :
          |sixVertexRegularizedBetheLogNormDerivative c epsilon x| *
              |sixVertexContinuousOffsetFourier c hc x| <= U * G := mul_le_mul
        (abs_sixVertexRegularizedBetheLogNormDerivative_le
          (x := x) hc hepsilon)
        (abs_sixVertexContinuousOffsetFourier_le hc x)
        (abs_nonneg _) hU
      calc
        _ <= U * G /
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q x :=
          div_le_div_of_nonneg_right hprod
            (hlower.trans_le (hk.2 x)).le
        _ <= U * G / lower :=
          div_le_div_of_nonneg_left (mul_nonneg hU hG) hlower (hk.2 x)
    have h := abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hk.1.1 hk.1.2.1 hlower hk.2 hqLip.continuous hqLip hbound
    have hintegral :
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRegularizedBetheLogNormDerivative c epsilon y *
            sixVertexContinuousOffsetFourier c hc y /
              sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) *
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) =
          integral := by
      dsimp only [integral]
      apply intervalIntegral.integral_congr
      intro y _
      have hry : sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y ≠ 0 :=
        (hlower.trans_le (hk.2 y)).ne'
      exact div_mul_cancel₀ _ hry
    change |empirical k -
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRegularizedBetheLogNormDerivative c epsilon y *
          sixVertexContinuousOffsetFourier c hc y /
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) *
          sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y)| <=
        err k at h
    rw [hintegral] at h
    have herrk := hKerr k hkerr
    rw [Real.dist_eq, sub_zero] at herrk
    exact (h.trans (le_abs_self (err k))).trans_lt herrk
  have hreplace : Tendsto
      (fun k => sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s k -
        (r : Real) * empirical k) atTop (nhds 0) := by
    apply Metric.tendsto_atTop.2
    intro delta hdelta
    have hUpos : 0 < U := by
      dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
      have ha : 0 < c ^ 2 - 1 := by nlinarith
      have hd : 0 < c ^ 2 - 2 := by nlinarith
      positivity
    have hcoef : 0 < U / lower := div_pos hUpos hlower
    let eta := delta / (U / lower)
    have heta : 0 < eta := div_pos hdelta hcoef
    obtain ⟨Kwit, hKwit⟩ := eventually_atTop.1
      (eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s)
    obtain ⟨Koff, hKoff⟩ := eventually_atTop.1
      (eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier hc s heta)
    refine ⟨max Kwit Koff, ?_⟩
    intro k hkmax
    have hk := hKwit k (le_trans (le_max_left _ _) hkmax)
    have hoff := hKoff k (le_trans (le_max_right _ _) hkmax)
    let N := sixVertexFourWidth r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    let rho := sixVertexFiniteRootDensity c N n q
    have hN : 0 < (N : Real) := by exact_mod_cast sixVertexFourWidth_pos r k
    have hterm (i : Fin n) :
        |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| < delta / N := by
      have hrho : 0 < rho (q i) := hlower.trans_le (hk.2 _)
      have hoff' :
          |rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| <
              eta := by
        simpa [rho, q, n, N, r] using hoff i
      rw [show sixVertexCanonicalEvenChargeOffset hc s k i -
          (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
            rho (q i) =
        (rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
          (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)) /
            rho (q i) by field_simp [hrho.ne']]
      rw [abs_div, abs_mul, abs_div, abs_of_pos hN, abs_of_pos hrho]
      calc
        _ <= U * |rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
              (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| /
            rho (q i) / N := by
          apply div_le_div_of_nonneg_right _ hN.le
          have hder :
              |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i)| <= U := by
            simpa [U] using
              (abs_sixVertexRegularizedBetheLogNormDerivative_le
                (x := q i) hc hepsilon)
          calc
            _ <= U *
                (|rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
                  (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| /
                    rho (q i)) :=
              mul_le_mul_of_nonneg_right hder
                (div_nonneg (abs_nonneg _) hrho.le)
            _ = _ := by ring
        _ < U * eta / rho (q i) / N := by
          gcongr
        _ <= U * eta / lower / N := by
          have hnum : 0 <= U * eta := mul_nonneg hU heta.le
          exact div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_left hnum hlower (hk.2 _)) hN.le
        _ = delta / N := by dsimp [eta]; field_simp [hcoef.ne', hlower.ne']
    unfold sixVertexCanonicalEvenRegularizedFullLinearTerm
    dsimp [empirical, N, n, q, r]
    rw [Real.dist_eq, sub_zero]
    have hrearrange :
        (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
            sixVertexCanonicalEvenChargeOffset hc s k i / N) -
          (r : Real) *
            ((∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
              sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) / N) =
        ∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N := by
      calc
        _ = ∑ i,
            (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexCanonicalEvenChargeOffset hc s k i / N -
              (r : Real) *
                (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                  sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) /
                    N) := by
          rw [Finset.sum_sub_distrib]
          congr 1
          calc
            (r : Real) *
                ((∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                  sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) / N) =
              (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) *
                  ((r : Real) / N) := by ring
            _ = ∑ i, (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) *
                  ((r : Real) / N) := by rw [Finset.sum_mul]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    rw [hrearrange]
    calc
      |∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| <=
        ∑ i, |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i : Fin n, delta / N := Finset.sum_lt_sum_of_nonempty
        Finset.univ_nonempty (fun i _ => hterm i)
      _ <= delta := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hnN : (n : Real) <= N := by
          exact_mod_cast (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega : n <= N)
        calc
          (n : Real) * (delta / N) = ((n : Real) / N) * delta := by ring
          _ <= 1 * delta :=
            mul_le_mul_of_nonneg_right ((div_le_one hN).2 hnN) hdelta.le
          _ = delta := one_mul _
  have hmain := hreplace.add ((hquad.const_mul (r : Real)).sub_const
    ((r : Real) * integral))
  simpa [integral, empirical, r] using
    (hreplace.add (hquad.const_mul (r : Real)))

def sixVertexCanonicalEvenRegularizedFullLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ i, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k i))

theorem tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (fun k =>
      sixVertexCanonicalEvenRegularizedFullLogDisplacement hc epsilon s k -
        sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s k)
      atTop (nhds 0) := by
  let r := 2 * s
  let B := sixVertexCanonicalEvenOffsetUniformBound c hc s
  let L := (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
    c epsilon : Real)
  let majorant : Nat -> Real := fun k =>
    L * B ^ 2 / (sixVertexFourWidth r k : Real)
  have hB : 0 <= B := sixVertexCanonicalEvenOffsetUniformBound_nonneg hc s
  have hL : 0 <= L := NNReal.coe_nonneg _
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
    ((strictMono_nat_of_lt_succ (fun k => by unfold sixVertexFourWidth; omega)).tendsto_atTop)
  have hmajor : Tendsto majorant atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hwidth
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun k => norm_nonneg _) _ hmajor
  filter_upwards
    [eventually_abs_sixVertexCanonicalEvenChargeOffset_le hc s]
      with k hoff
  let N := sixVertexFourWidth r k
  let n := (s + k + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let off := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : 0 < (N : Real) := by exact_mod_cast sixVertexFourWidth_pos r k
  have hdiff (i : Fin n) : q i - p i = off i / N := by
    dsimp only [off, sixVertexCanonicalEvenChargeOffset]
    change q i - p i = (N : Real) * (q i - p i) / N
    field_simp [hN.ne']
  have hterm (i : Fin n) :
      |(sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N| <= L * B ^ 2 / N ^ 2 := by
    have ht := abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
      hc hepsilon (q i) (p i)
    have hoff' : |off i| <= B := by simpa [off] using hoff i
    have hpq : p i - q i = -(off i / N) := by
      rw [show p i - q i = -(q i - p i) by ring, hdiff]
    rw [show (sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N =
      -(sixVertexRegularizedBetheLogKernel c epsilon (p i) -
          sixVertexRegularizedBetheLogKernel c epsilon (q i) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (p i - q i)) by rw [hpq]; ring,
      abs_neg]
    calc
      _ <= L * |p i - q i| ^ 2 := ht
      _ <= L * (B / N) ^ 2 := by
        gcongr
        rw [abs_sub_comm, hdiff, abs_div, abs_of_pos hN]
        exact div_le_div_of_nonneg_right hoff' hN.le
      _ = L * B ^ 2 / N ^ 2 := by ring
  rw [Real.norm_eq_abs]
  unfold sixVertexCanonicalEvenRegularizedFullLogDisplacement
    sixVertexCanonicalEvenRegularizedFullLinearTerm
  dsimp [q, p, off, N, n, r]
  rw [<- Finset.sum_sub_distrib]
  calc
    |∑ i, ((sixVertexRegularizedBetheLogKernel c epsilon (q i) -
        sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
      sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
        off i / N)| <=
      ∑ i, |(sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N| := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin n, L * B ^ 2 / N ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ <= L * B ^ 2 / N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hnN : (n : Real) <= N := by
        exact_mod_cast (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega : n <= N)
      have hconst : 0 <= L * B ^ 2 := mul_nonneg hL (sq_nonneg B)
      rw [show (n : Real) * (L * B ^ 2 / N ^ 2) =
        (L * B ^ 2) * ((n : Real) / N) / N by ring]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right hconst ((div_le_one hN).2 hnN)) hN.le

theorem tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenRegularizedBulkLogDisplacement
      hc epsilon s) atTop
      (nhds ((2 * s : Real) / 2 *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x))) := by
  let target := (2 * s : Real) *
    (∫ x in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogNormDerivative c epsilon x *
        sixVertexContinuousOffsetFourier c hc x)
  have hfull : Tendsto
      (sixVertexCanonicalEvenRegularizedFullLogDisplacement hc epsilon s)
      atTop (nhds target) := by
    have h := (tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder
      hc hepsilon s).add
      (tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm hc hepsilon s)
    simpa [target] using h
  have htwice : Tendsto
      (fun k => 2 * sixVertexCanonicalEvenRegularizedBulkLogDisplacement
        hc epsilon s k) atTop (nhds target) :=
    hfull.congr' (eventually_full_regularizedLogDisplacement_eq_two_positive
      hc epsilon s)
  have hhalf := htwice.const_mul (1 / 2 : Real)
  have htarget :
      (1 / 2 : Real) * target = (2 * s : Real) / 2 *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x) := by
    dsimp [target]
    ring
  rw [htarget] at hhalf
  simpa using hhalf

end

end StatMech.FrontierD
