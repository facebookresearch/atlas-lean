/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianCriticalNewman
import Code.FrontierA.IsingGaussianConePolarization









open Filter Finset Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem finiteParityFourthUrsell_eq_finiteIsing_distinct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteParityFourthUrsell G beta J i j k l =
      finiteIsingFourthUrsell G beta J i j k l := by
  have hpair (x y : V) (hxy : x ≠ y) :
      grahamPairSupport x y = {x, y} := by
    ext z
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hquad : grahamFourSupport i j k l = {i, j, k, l} := by
    rw [grahamFourSupport, hpair i j hij, hpair k l hkl]
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  unfold finiteParityFourthUrsell finiteIsingFourthUrsell
  rw [hquad, hpair i j hij, hpair i k hik, hpair i l hil,
    hpair j k hjk, hpair j l hjl, hpair k l hkl]


theorem finiteParityFourthUrsell_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (i j k l : V) :
    finiteParityFourthUrsell G beta J i j k l <= 0 := by
  by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
  · rw [finiteParityFourthUrsell_eq_finiteIsing_distinct G beta J
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2,
      finiteIsingFourthUrsell_eq_current]
    exact finiteCurrentFourthUrsell_nonpos G beta J hbeta hJ
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · have hw :=
      (finiteCollisionFourthWeight_nonneg_le
        G beta J hbeta hJ i j k l).1
    rw [finiteCollisionFourthWeight, if_neg h] at hw
    linarith


def finiteWeightedParityFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) : Real :=
  ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
    a i * a j * a k * a l *
      finiteParityFourthUrsell G beta J i j k l



theorem finiteWeightedParityFourthCumulant_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (a : V -> Real) (M : Real)
    (hM : 0 <= M) (ha0 : forall i, 0 <= a i)
    (haM : forall i, a i <= M) :
    0 <= -finiteWeightedParityFourthCumulant G beta J a ∧
      -finiteWeightedParityFourthCumulant G beta J a <=
        M ^ 4 *
          (-(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
            finiteParityFourthUrsell G beta J i j k l)) := by
  have hterm (i j k l : V) :
      0 <= -(a i * a j * a k * a l *
          finiteParityFourthUrsell G beta J i j k l) ∧
        -(a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) <=
          M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l) := by
    have hU : 0 <= -finiteParityFourthUrsell G beta J i j k l :=
      neg_nonneg.mpr (finiteParityFourthUrsell_nonpos
        G beta J hbeta hJ i j k l)
    have haProd : 0 <= a i * a j * a k * a l :=
      mul_nonneg (mul_nonneg (mul_nonneg (ha0 i) (ha0 j)) (ha0 k)) (ha0 l)
    have haProdLe : a i * a j * a k * a l <= M ^ 4 := by
      have hij : a i * a j <= M * M :=
        mul_le_mul (haM i) (haM j) (ha0 j) hM
      have hkl : a k * a l <= M * M :=
        mul_le_mul (haM k) (haM l) (ha0 l) hM
      calc
        a i * a j * a k * a l = (a i * a j) * (a k * a l) := by ring
        _ <= (M * M) * (M * M) :=
          mul_le_mul hij hkl (mul_nonneg (ha0 k) (ha0 l))
            (mul_nonneg hM hM)
        _ = M ^ 4 := by ring
    constructor
    · nlinarith
    · nlinarith
  unfold finiteWeightedParityFourthCumulant
  have hweightedNeg :
      -(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) =
        ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          -(a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) := by
    symm
    simp_rw [Finset.sum_neg_distrib]
  rw [hweightedNeg]
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        (hterm i j k l).1
  · calc
      _ <= ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
            (hterm i j k l).2
      _ = M ^ 4 *
          (-(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
            finiteParityFourthUrsell G beta J i j k l)) := by
        calc
          (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
              M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l)) =
              M ^ 4 * (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
                -finiteParityFourthUrsell G beta J i j k l) := by
            simp_rw [Finset.mul_sum]
        _ = _ := by simp_rw [Finset.sum_neg_distrib]


def finiteWeightedParitySecondMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) : Real :=
  ∑ i : V, ∑ j : V,
    a i * a j * expectationJ G beta J (grahamPairSupport i j)


def finiteWeightedParityFourthMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) : Real :=
  ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
    a i * a j * a k * a l *
      expectationJ G beta J (grahamFourSupport i j k l)

private theorem weighted_sum_pair_product
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : I -> J -> Real) (B : K -> L -> Real) :
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



theorem scalarFourthCumulant_finiteWeightedParity_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) :
    scalarFourthCumulant
        (finiteWeightedParityFourthMoment G beta J a)
        (finiteWeightedParitySecondMoment G beta J a) =
      finiteWeightedParityFourthCumulant G beta J a := by
  let C : V -> V -> Real := fun i j =>
    a i * a j * expectationJ G beta J (grahamPairSupport i j)
  let S : Real := ∑ i : V, ∑ j : V, C i j
  have hfirst :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i j * C k l) =
        S ^ 2 := by
    rw [weighted_sum_pair_product C C]
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
        rw [weighted_sum_pair_product C C]
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
        rw [weighted_sum_pair_product C C]
        ring
  have hfirstExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i j) *
            expectationJ G beta J (grahamPairSupport k l))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i j * C k l := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hfirst
  have hsecondExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i k) *
            expectationJ G beta J (grahamPairSupport j l))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i k * C j l := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hsecond
  have hthirdExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i l) *
            expectationJ G beta J (grahamPairSupport j k))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hthird
  unfold scalarFourthCumulant finiteWeightedParityFourthMoment
    finiteWeightedParitySecondMoment finiteWeightedParityFourthCumulant
    finiteParityFourthUrsell
  dsimp [C, S] at hfirstExpanded hsecondExpanded hthirdExpanded ⊢
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hfirstExpanded, hsecondExpanded, hthirdExpanded]
  ring

section CriticalBox


def criticalFiniteBoxWeightedParityFourthCumulant
    (d n : Nat) (a : sctBox d n -> Real) : Real :=
  finiteWeightedParityFourthCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) a



def criticalFiniteBoxWeightedNormalizedFourthCumulant
    (d n : Nat) (a : sctBox d n -> Real) : Real :=
  criticalFiniteBoxWeightedParityFourthCumulant d n a /
    (2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

theorem criticalFiniteBoxWeightedParityFourthCumulant_bounds
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (ha0 : forall i, 0 <= a i) (ha1 : forall i, a i <= 1) :
    0 <= -criticalFiniteBoxWeightedParityFourthCumulant d n a ∧
      -criticalFiniteBoxWeightedParityFourthCumulant d n a <=
        -criticalFiniteBoxGlobalParityFourthCumulant d n := by
  have hbeta : 0 <= IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have h := finiteWeightedParityFourthCumulant_bounds
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    hbeta (fun _ => by norm_num) a 1 (by norm_num) ha0 ha1
  simpa [criticalFiniteBoxWeightedParityFourthCumulant,
    criticalFiniteBoxGlobalParityFourthCumulant,
    finiteParityIntegratedFourthCumulant] using h

theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (ha0 : forall i, 0 <= a i) (ha1 : forall i, a i <= 1) :
    0 <= -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a ∧
      -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a <=
        -criticalFiniteBoxGlobalNormalizedFourthCumulant d n := by
  let denominator : Real :=
    2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d
  have hcard : 0 < (Fintype.card (sctBox d n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨criticalFiniteBoxOrigin d n⟩
  have hchi : 0 < criticalFreeBoxSusceptibility d (2 * n) := by
    linarith [one_le_criticalFreeBoxSusceptibility hd (2 * n)]
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hraw :=
    criticalFiniteBoxWeightedParityFourthCumulant_bounds d n hd a ha0 ha1
  have hweightedNormalized :
      -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
        -criticalFiniteBoxWeightedParityFourthCumulant d n a / denominator := by
    dsimp [criticalFiniteBoxWeightedNormalizedFourthCumulant, denominator]
    ring
  have hglobalNormalized :
      -criticalFiniteBoxGlobalNormalizedFourthCumulant d n =
        -criticalFiniteBoxGlobalParityFourthCumulant d n / denominator := by
    dsimp [criticalFiniteBoxGlobalNormalizedFourthCumulant, denominator]
    ring
  rw [hweightedNormalized, hglobalNormalized]
  exact ⟨div_nonneg hraw.1 hdenominator.le,
    div_le_div_of_nonneg_right hraw.2 hdenominator.le⟩



theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedNormalizedFourthCumulant d n (a n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n => -criticalFiniteBoxGlobalNormalizedFourthCumulant d n)
      atTop (nhds 0) :=
    by
      simpa only [neg_zero] using
        (criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero d hd).neg
  have hneg : Tendsto
      (fun n => -criticalFiniteBoxWeightedNormalizedFourthCumulant d n (a n))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d n (by omega) (a n) (ha0 n) (ha1 n)).1
    · exact Filter.Eventually.of_forall fun n =>
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d n (by omega) (a n) (ha0 n) (ha1 n)).2
    · exact hupper
  simpa using hneg.neg

end CriticalBox

end

end StatMech.FrontierA
