/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalTorusLocalLimit
import Code.Probability.KKLfromHC
import Code.Ising.GinibreBoundaryDerivative
import Code.FrontierA.IsingGaussianPhysicalCumulants










open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


def criticalTorusLocalRestriction (A : Finset (Site d)) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d n)) : ConfigSpace {x // x ∈ A} :=
  fun x ↦ sigma (isingSiteToDyadicTorus n x.1)


def criticalInfiniteLocalRestriction (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) : ConfigSpace {x // x ∈ A} :=
  fun x ↦ omega x.1


def criticalTorusLocalObservableExpectation
    (A : Finset (Site d)) (f : ConfigSpace {x // x ∈ A} → Real)
    (n : Nat) : Real :=
  expJ (isingTorusGraph d n).edgeFinset
    (fun _ ↦ IsingFK.betaC (magnetization d)) (fun _ ↦ 0)
    (fun sigma ↦ f (criticalTorusLocalRestriction A n sigma))


def criticalFreeLocalObservableExpectation
    (A : Finset (Site d)) (f : ConfigSpace {x // x ∈ A} → Real) : Real :=
  ∫ omega, f (criticalInfiniteLocalRestriction A omega)
    ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
      Measure (ConfigSpace (Site d)))

theorem khc_walshChar_eq_negOnePow_spinProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (sigma : ConfigSpace V) :
    khc_walshChar B sigma = (-1 : Real) ^ B.card * spinProd B sigma := by
  unfold khc_walshChar spinProd
  have hsign (x : V) : khc_sign (sigma x) = (-1 : Real) * spin sigma x := by
    unfold khc_sign spin
    split <;> norm_num
  simp_rw [hsign]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

private theorem walshChar_torusRestriction
    (A : Finset (Site d)) (B : Finset {x // x ∈ A}) (n : Nat)
    (hinj : Set.InjOn (isingSiteToDyadicTorus n) (↑A : Set (Site d)))
    (sigma : ConfigSpace (IsingDyadicTorus d n)) :
    khc_walshChar B (criticalTorusLocalRestriction A n sigma) =
      (-1 : Real) ^ B.card *
        spinProd ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
          (isingSiteToDyadicTorus n)) sigma := by
  rw [khc_walshChar_eq_negOnePow_spinProd]
  congr 1
  unfold spinProd criticalTorusLocalRestriction
  rw [Finset.prod_image]
  · rw [Finset.prod_map]
    rfl
  · intro x hx y hy hxy
    apply hinj
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      exact u.2
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hy
      exact u.2
    · exact hxy

private theorem walshChar_infiniteRestriction
    (A : Finset (Site d)) (B : Finset {x // x ∈ A})
    (omega : ConfigSpace (Site d)) :
    khc_walshChar B (criticalInfiniteLocalRestriction A omega) =
      (-1 : Real) ^ B.card *
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
  rw [khc_walshChar_eq_negOnePow_spinProd]
  congr 1
  unfold spinProd criticalInfiniteLocalRestriction
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  unfold spin
  rfl

private theorem eventually_injectiveOn_fixedSupport
    (A : Finset (Site d)) :
    ∀ᶠ n in atTop,
      Set.InjOn (isingSiteToDyadicTorus n) (↑A : Set (Site d)) := by
  obtain ⟨R, hAR⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop R] with n hn
  have hAn : (↑A : Set (Site d)) ⊆ box d n := hAR.trans (box_mono d hn)
  exact isingSiteToDyadicTorus_injectiveOn_finset A hAn
    (lt_of_lt_of_le (by omega : 2 * n < 2 * (n + 1))
      (two_mul_succ_lt_isingDyadicSide n).le)

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalObservableExpectation_tendsto
    (hd : 2 < d) (A : Finset (Site d))
    (f : ConfigSpace {x // x ∈ A} → Real) :
    Tendsto (criticalTorusLocalObservableExpectation A f) atTop
      (nhds (criticalFreeLocalObservableExpectation A f)) := by
  let c : Finset {x // x ∈ A} → Real := fun B ↦
    khc_fourierCoeff f B * (-1 : Real) ^ B.card
  have htorus : ∀ᶠ n in atTop,
      criticalTorusLocalObservableExpectation A f n =
        ∑ B : Finset {x // x ∈ A},
          c B * criticalTorusLocalSpinProd d
            (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n := by
    filter_upwards [eventually_injectiveOn_fixedSupport A] with n hinj
    unfold criticalTorusLocalObservableExpectation
    have hpoint (sigma : ConfigSpace (IsingDyadicTorus d n)) :
        f (criticalTorusLocalRestriction A n sigma) =
          ∑ B : Finset {x // x ∈ A},
            c B * spinProd
              ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
                (isingSiteToDyadicTorus n)) sigma := by
      rw [← khc_fourier_expansion f (criticalTorusLocalRestriction A n sigma)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_torusRestriction A B n hinj sigma]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [expJ_sum]
    apply Finset.sum_congr rfl
    intro B _
    rw [expJ_const_mul]
    rfl
  have hsum : Tendsto
      (fun n ↦ ∑ B : Finset {x // x ∈ A},
        c B * criticalTorusLocalSpinProd d
          (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n)
      atTop
      (nhds (∑ B : Finset {x // x ∈ A},
        c B * ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))) := by
    apply tendsto_finsetSum
    intro B hB
    exact (criticalTorusLocalSpinProd_tendsto hd
      (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).const_mul (c B)
  have hlimit : (∑ B : Finset {x // x ∈ A},
      c B * ∫ omega,
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
          ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
            Measure (ConfigSpace (Site d)))) =
      criticalFreeLocalObservableExpectation A f := by
    unfold criticalFreeLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        f (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A},
            c B * spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion f (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_infiniteRestriction A B omega]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul (c B)
  rw [← hlimit]
  exact hsum.congr' (htorus.mono fun n hn ↦ hn.symm)

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalObservableExpectation_tendsto_varying
    (hd : 2 < d) (A : Finset (Site d))
    (f : Nat → ConfigSpace {x // x ∈ A} → Real)
    (limit : ConfigSpace {x // x ∈ A} → Real)
    (hf : ∀ sigma, Tendsto (fun n ↦ f n sigma) atTop (nhds (limit sigma))) :
    Tendsto (fun n ↦ criticalTorusLocalObservableExpectation A (f n) n)
      atTop (nhds (criticalFreeLocalObservableExpectation A limit)) := by
  let c : Nat → Finset {x // x ∈ A} → Real := fun n B ↦
    khc_fourierCoeff (f n) B * (-1 : Real) ^ B.card
  let cLimit : Finset {x // x ∈ A} → Real := fun B ↦
    khc_fourierCoeff limit B * (-1 : Real) ^ B.card
  have hc (B : Finset {x // x ∈ A}) :
      Tendsto (fun n ↦ c n B) atTop (nhds (cLimit B)) := by
    unfold c cLimit khc_fourierCoeff bnt_uexp
    apply Tendsto.mul_const
    apply Tendsto.div_const
    apply tendsto_finsetSum
    intro sigma hsigma
    exact (hf sigma).mul_const (khc_walshChar B sigma)
  have htorus : ∀ᶠ n in atTop,
      criticalTorusLocalObservableExpectation A (f n) n =
        ∑ B : Finset {x // x ∈ A},
          c n B * criticalTorusLocalSpinProd d
            (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n := by
    filter_upwards [eventually_injectiveOn_fixedSupport A] with n hinj
    unfold criticalTorusLocalObservableExpectation
    have hpoint (sigma : ConfigSpace (IsingDyadicTorus d n)) :
        f n (criticalTorusLocalRestriction A n sigma) =
          ∑ B : Finset {x // x ∈ A},
            c n B * spinProd
              ((B.map (Function.Embedding.subtype fun x ↦ x ∈ A)).image
                (isingSiteToDyadicTorus n)) sigma := by
      rw [← khc_fourier_expansion (f n)
        (criticalTorusLocalRestriction A n sigma)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_torusRestriction A B n hinj sigma]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [expJ_sum]
    apply Finset.sum_congr rfl
    intro B _
    rw [expJ_const_mul]
    rfl
  have hsum : Tendsto
      (fun n ↦ ∑ B : Finset {x // x ∈ A},
        c n B * criticalTorusLocalSpinProd d
          (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) n)
      atTop
      (nhds (∑ B : Finset {x // x ∈ A},
        cLimit B * ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))) := by
    apply tendsto_finsetSum
    intro B hB
    exact (hc B).mul (criticalTorusLocalSpinProd_tendsto hd
      (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)))
  have hlimit : (∑ B : Finset {x // x ∈ A},
      cLimit B * ∫ omega,
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
          ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
            Measure (ConfigSpace (Site d)))) =
      criticalFreeLocalObservableExpectation A limit := by
    unfold criticalFreeLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        limit (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A},
            cLimit B * spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion limit
        (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [walshChar_infiniteRestriction A B omega]
      dsimp [cLimit]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul
          (cLimit B)
  rw [← hlimit]
  exact hsum.congr' (htorus.mono fun n hn ↦ hn.symm)



def compactWeightedSpin (A : Finset (Site d)) (a : Site d → Real)
    (sigma : ConfigSpace {x // x ∈ A}) : Real :=
  ∑ x : {x // x ∈ A}, a x.1 * spin sigma x



theorem criticalTorusCompactWeightedMoment_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto
      (fun n ↦ criticalTorusLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n)
      atTop
      (nhds (criticalFreeLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order))) :=
  criticalTorusLocalObservableExpectation_tendsto hd A _




def compactTorusWeight (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (z : IsingDyadicTorus d n) : Real :=
  ∑ x : {x // x ∈ A},
    if isingSiteToDyadicTorus n x.1 = z then a x.1 else 0

theorem finiteIsingWeightedSpinReal_compactTorusWeight
    (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d n)) :
    finiteIsingWeightedSpinReal (compactTorusWeight A a n) sigma =
      compactWeightedSpin A a (criticalTorusLocalRestriction A n sigma) := by
  unfold finiteIsingWeightedSpinReal compactTorusWeight compactWeightedSpin
    criticalTorusLocalRestriction
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (isingSiteToDyadicTorus n x.1)]
  · simp only [if_pos rfl]
    congr 1
  · intro z hz hne
    simp [hne.symm]
  · simp

theorem finiteIsingWeightedRawMoment_eq_expJ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (a : V → Real) (order : Nat) :
    finiteIsingWeightedRawMoment G beta a order =
      expJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
        (fun sigma ↦ finiteIsingWeightedSpinReal a sigma ^ order) := by
  have hweight (sigma : ConfigSpace V) :
      zeroFieldInteractionWeight G beta sigma =
        wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) sigma := by
    unfold zeroFieldInteractionWeight wJ
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  unfold finiteIsingWeightedRawMoment expJ ZJ
  simp_rw [hweight]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma hsigma
  ring



theorem criticalTorusCompactWeightedMoment_eq_finiteRawMoment
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) :
    criticalTorusLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n =
      finiteIsingWeightedRawMoment (isingTorusGraph d n)
        (IsingFK.betaC (magnetization d)) (compactTorusWeight A a n) order := by
  rw [finiteIsingWeightedRawMoment_eq_expJ]
  unfold criticalTorusLocalObservableExpectation
  congr 1
  funext sigma
  rw [finiteIsingWeightedSpinReal_compactTorusWeight]



theorem scalarCumulantsOfMoments_tendsto_of_moments
    (moments : Nat → Nat → Real) (limitMoments : Nat → Real)
    (hmoments : ∀ order,
      Tendsto (fun n ↦ moments n order) atTop (nhds (limitMoments order))) :
    ∀ order, Tendsto
      (fun n ↦ scalarCumulantsOfMoments (moments n) order) atTop
      (nhds (scalarCumulantsOfMoments limitMoments order)) := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp
      | succ order =>
          rw [show order + 1 = order + 1 by rfl,
            scalarCumulantsOfMoments_succ]
          have hsum : Tendsto
              (fun n ↦ ∑ k : Fin order,
                (order.choose k : Real) *
                  scalarCumulantsOfMoments (moments n) (k + 1) *
                    moments n (order - k))
              atTop
              (nhds (∑ k : Fin order,
                (order.choose k : Real) *
                  scalarCumulantsOfMoments limitMoments (k + 1) *
                    limitMoments (order - k))) := by
            apply tendsto_finsetSum
            intro k hk
            exact (tendsto_const_nhds.mul (ih (k + 1) (by omega))).mul
              (hmoments (order - k))
          have h := (hmoments (order + 1)).sub hsum
          convert h using 1
          funext n
          rw [scalarCumulantsOfMoments_succ]


def criticalTorusCompactWeightedCumulant
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) : Real :=
  scalarCumulantsOfMoments
    (finiteIsingWeightedRawMoment (isingTorusGraph d n)
      (IsingFK.betaC (magnetization d)) (compactTorusWeight A a n)) order



def criticalFreeCompactWeightedCumulant
    (A : Finset (Site d)) (a : Site d → Real) (order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m ↦ criticalFreeLocalObservableExpectation A
      (fun sigma ↦ compactWeightedSpin A a sigma ^ m)) order



theorem criticalTorusCompactWeightedCumulant_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant A a n order)
      atTop (nhds (criticalFreeCompactWeightedCumulant A a order)) := by
  unfold criticalTorusCompactWeightedCumulant
    criticalFreeCompactWeightedCumulant
  apply scalarCumulantsOfMoments_tendsto_of_moments
  intro m
  simpa only [← criticalTorusCompactWeightedMoment_eq_finiteRawMoment] using
    criticalTorusCompactWeightedMoment_tendsto hd A a m



theorem criticalTorusCompactWeightedCumulant_sub_tendsto_zero
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto
      (fun n ↦ criticalTorusCompactWeightedCumulant A a n order -
        criticalFreeCompactWeightedCumulant A a order)
      atTop (nhds 0) := by
  have hconst : Tendsto
      (fun _ : Nat ↦ criticalFreeCompactWeightedCumulant A a order) atTop
      (nhds (criticalFreeCompactWeightedCumulant A a order)) :=
    tendsto_const_nhds
  simpa using (criticalTorusCompactWeightedCumulant_tendsto
    hd A a order).sub hconst

end

end StatMech.FrontierA
