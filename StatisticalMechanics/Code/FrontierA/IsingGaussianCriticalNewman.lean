/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianCollisionDiagonal
import Code.FrontierA.IsingGaussianNewmanBridge








open Filter Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section



def criticalFiniteBoxNormalizedParityFourthCumulant (d n : Nat) : Real :=
  criticalFiniteBoxParityIntegratedFourthCumulant d n /
    (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

theorem criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling
    (d n : Nat) :
    criticalFiniteBoxNormalizedParityFourthCumulant d n =
      -criticalFiniteBoxFullRenormalizedFourthCoupling d n := by
  unfold criticalFiniteBoxNormalizedParityFourthCumulant
    criticalFiniteBoxFullRenormalizedFourthCoupling
  ring



theorem criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (criticalFiniteBoxNormalizedParityFourthCumulant d)
      atTop (nhds 0) := by
  have h :=
    (criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero d hd).neg
  simpa only [neg_zero,
    ← criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling] using h

section FiniteTotalSpin

variable {V : Type*} [Fintype V] [DecidableEq V]



def finiteParityTotalSpinSecondMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) : Real :=
  ∑ i : V, ∑ j : V,
    expectationJ G beta J (grahamPairSupport i j)



def finiteParityTotalSpinFourthMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) : Real :=
  ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
    expectationJ G beta J (grahamFourSupport i j k l)

private theorem sum_pair_product
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : I → J → Real) (B : K → L → Real) :
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ l : L, A i j * B k l) =
      (∑ i : I, ∑ j : J, A i j) * (∑ k : K, ∑ l : L, B k l) := by
  calc
    _ = ∑ i : I, ∑ j : J, A i j * (∑ k : K, ∑ l : L, B k l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ i : I, (∑ j : J, A i j) * (∑ k : K, ∑ l : L, B k l) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_mul]



theorem scalarFourthCumulant_finiteParityTotalSpin_eq_integrated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) :
    scalarFourthCumulant
        (finiteParityTotalSpinFourthMoment G beta J)
        (finiteParityTotalSpinSecondMoment G beta J) =
      ∑ i : V, finiteParityIntegratedFourthCumulant G beta J i := by
  let C : V → V → Real := fun i j =>
    expectationJ G beta J (grahamPairSupport i j)
  let Q : V → V → V → V → Real := fun i j k l =>
    expectationJ G beta J (grahamFourSupport i j k l)
  let S : Real := ∑ i : V, ∑ j : V, C i j
  have hfirst :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i j * C k l) =
        S ^ 2 := by
    rw [sum_pair_product C C]
    ring
  have hsecond :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i k * C j l) =
        S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ k : V, ∑ j : V, ∑ l : V,
          C i k * C j l := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = S ^ 2 := by
        rw [sum_pair_product C C]
        ring
  have hthird :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i l * C j k) =
        S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ l : V, ∑ k : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ l : V, ∑ j : V, ∑ k : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = S ^ 2 := by
        rw [sum_pair_product C C]
        ring
  unfold scalarFourthCumulant finiteParityTotalSpinFourthMoment
    finiteParityTotalSpinSecondMoment finiteParityIntegratedFourthCumulant
    finiteParityFourthUrsell
  dsimp [Q, C, S] at hfirst hsecond hthird ⊢
  simp_rw [Finset.sum_sub_distrib]
  rw [hfirst, hsecond, hthird]
  ring

end FiniteTotalSpin



def criticalFiniteBoxGlobalParityFourthCumulant (d n : Nat) : Real :=
  ∑ i : sctBox d n,
    finiteParityIntegratedFourthCumulant
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i

theorem criticalFiniteBoxGlobalParityFourthCumulant_eq_scalarFourthCumulant
    (d n : Nat) :
    criticalFiniteBoxGlobalParityFourthCumulant d n =
      scalarFourthCumulant
        (finiteParityTotalSpinFourthMoment
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1))
        (finiteParityTotalSpinSecondMoment
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)) := by
  unfold criticalFiniteBoxGlobalParityFourthCumulant
  exact (scalarFourthCumulant_finiteParityTotalSpin_eq_integrated
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)).symm

theorem criticalFiniteBoxGlobalParityFourthCumulant_bound
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ -criticalFiniteBoxGlobalParityFourthCumulant d n ∧
      -criticalFiniteBoxGlobalParityFourthCumulant d n ≤
        (Fintype.card (sctBox d n) : Real) *
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hroot (i : sctBox d n) :
      0 ≤ -finiteParityIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ∧
        -finiteParityIntegratedFourthCumulant
            (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ≤
          2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 :=
    finiteParityIntegratedFourthCumulant_treeDiagram_bound
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
      hbeta (fun _ => by norm_num) (criticalFreeBoxSusceptibility d (2 * n))
      (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
      (criticalFiniteBoxRowSusceptibility_le hd n) i
  have hneg : -criticalFiniteBoxGlobalParityFourthCumulant d n =
      ∑ i : sctBox d n,
        -finiteParityIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
            (fun _ => 1) i := by
    unfold criticalFiniteBoxGlobalParityFourthCumulant
    rw [Finset.sum_neg_distrib]
  rw [hneg]
  constructor
  · exact Finset.sum_nonneg fun i _ => (hroot i).1
  · calc
      _ ≤ ∑ _i : sctBox d n,
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
        exact Finset.sum_le_sum fun i _ => (hroot i).2
      _ = (Fintype.card (sctBox d n) : Real) *
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
        simp [nsmul_eq_mul]
        ring



def criticalFiniteBoxGlobalNormalizedFourthCumulant (d n : Nat) : Real :=
  criticalFiniteBoxGlobalParityFourthCumulant d n /
    (2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

theorem criticalFiniteBoxGlobalNormalizedFourthCumulant_bounds
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ -criticalFiniteBoxGlobalNormalizedFourthCumulant d n ∧
      -criticalFiniteBoxGlobalNormalizedFourthCumulant d n ≤
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 /
            ((2 * n + 1 : Nat) : Real) ^ d +
          6 / ((2 * n + 1 : Nat) : Real) ^ d := by
  let U : Real := -criticalFiniteBoxGlobalParityFourthCumulant d n
  let card : Real := Fintype.card (sctBox d n)
  let chi : Real := criticalFreeBoxSusceptibility d (2 * n)
  let radius : Real := ((2 * n + 1 : Nat) : Real)
  have hU : 0 ≤ U ∧ U ≤ card * (2 * chi ^ 4 + 12 * chi ^ 2) := by
    simpa [U, card, chi] using
      criticalFiniteBoxGlobalParityFourthCumulant_bound hd n
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨criticalFiniteBoxOrigin d n⟩
  have hchi : 0 < chi := by
    have := one_le_criticalFreeBoxSusceptibility hd (2 * n)
    dsimp [chi]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hden : 0 < 2 * card * chi ^ 2 * radius ^ d := by positivity
  have hnormalized :
      -criticalFiniteBoxGlobalNormalizedFourthCumulant d n =
        U / (2 * card * chi ^ 2 * radius ^ d) := by
    dsimp [criticalFiniteBoxGlobalNormalizedFourthCumulant,
      U, card, chi, radius]
    ring
  rw [hnormalized]
  change 0 ≤ U / (2 * card * chi ^ 2 * radius ^ d) ∧
    U / (2 * card * chi ^ 2 * radius ^ d) ≤
      chi ^ 2 / radius ^ d + 6 / radius ^ d
  constructor
  · exact div_nonneg hU.1 hden.le
  · rw [div_le_iff₀ hden]
    calc
      U ≤ card * (2 * chi ^ 4 + 12 * chi ^ 2) := hU.2
      _ = (chi ^ 2 / radius ^ d + 6 / radius ^ d) *
          (2 * card * chi ^ 2 * radius ^ d) := by
        field_simp [ne_of_gt hradius]
        ring



theorem criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (criticalFiniteBoxGlobalNormalizedFourthCumulant d)
      atTop (nhds 0) := by
  have hbounds (n : Nat) :=
    criticalFiniteBoxGlobalNormalizedFourthCumulant_bounds (d := d)
      (by omega) n
  obtain ⟨A, hA, hchiUpper⟩ :=
    exists_criticalFreeBoxSusceptibility_le_quadratic (d := d) (by omega)
  let radius : Nat → Real := fun n => ((2 * n + 1 : Nat) : Real)
  have hradiusNat : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hradius : Tendsto radius atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hradiusNat
  have hpower (p : Nat) (hp : 0 < p) :
      Tendsto (fun n => radius n ^ p) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => ?_) hradius
    have hone : 1 ≤ radius n := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using pow_le_pow_right₀ hone hp
  have henvelope : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d)
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop (hpower (d - 4) (by omega))).add
        (tendsto_const_nhds.div_atTop (hpower d (by omega)))
  have hneg : Tendsto
      (fun n => -criticalFiniteBoxGlobalNormalizedFourthCumulant d n)
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => (hbounds n).1) _ henvelope
    filter_upwards with n
    have hradiusPos : 0 < radius n := by
      dsimp [radius]
      positivity
    have hchiNonneg : 0 ≤ criticalFreeBoxSusceptibility d (2 * n) :=
      criticalFreeBoxSusceptibility_nonneg (by omega) (2 * n)
    have hchiLe : criticalFreeBoxSusceptibility d (2 * n) ≤
        A * radius n ^ 2 := by
      simpa [radius] using hchiUpper (2 * n)
    have hchiSq : criticalFreeBoxSusceptibility d (2 * n) ^ 2 ≤
        (A * radius n ^ 2) ^ 2 :=
      (sq_le_sq₀ hchiNonneg (by positivity)).2 hchiLe
    calc
      -criticalFiniteBoxGlobalNormalizedFourthCumulant d n ≤
          criticalFreeBoxSusceptibility d (2 * n) ^ 2 / radius n ^ d +
            6 / radius n ^ d := by
        simpa [radius] using (hbounds n).2
      _ ≤ (A * radius n ^ 2) ^ 2 / radius n ^ d +
            6 / radius n ^ d := by
        gcongr
      _ = A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d := by
        congr 1
        have hd' : d = (d - 4) + 4 := by omega
        rw [hd', pow_add]
        field_simp
        congr 3
        omega
  simpa using hneg.neg




theorem criticalFiniteBoxCumulantLimits_of_newmanFourthControl
    (d : Nat) (hd : 4 < d)
    (cumulants : Nat → Nat → Real) (variance : Real)
    (hcontrol : NewmanFourthCumulantControl cumulants)
    (hvariance : Tendsto (fun n => cumulants n 2) atTop (nhds variance))
    (hfourth : ∀ n,
      cumulants n 4 = criticalFiniteBoxNormalizedParityFourthCumulant d n) :
    ∀ order,
      Tendsto (fun n => cumulants n order) atTop
        (nhds (scalarGaussianCumulant variance order)) := by
  apply cumulantLimits_of_newmanFourthControl cumulants variance
    hcontrol hvariance
  simpa only [hfourth] using
    criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero d hd



theorem criticalFiniteBoxScalarWickMoments_of_newmanFourthControl
    (d : Nat) (hd : 4 < d)
    (moments cumulants : Nat → Nat → Real)
    (limitMoments : Nat → Real) (variance : Real)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : ∀ order,
      Tendsto (fun n => moments n order) atTop (nhds (limitMoments order)))
    (hcontrol : NewmanFourthCumulantControl cumulants)
    (hvariance : Tendsto (fun n => cumulants n 2) atTop (nhds variance))
    (hfourth : ∀ n,
      cumulants n 4 = criticalFiniteBoxNormalizedParityFourthCumulant d n) :
    ScalarWickMoments variance limitMoments := by
  apply scalarWickMoments_of_newmanFourthControl moments cumulants
    limitMoments variance hrecurrence hmoments hcontrol hvariance
  simpa only [hfourth] using
    criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero d hd

end

end StatMech.FrontierA
