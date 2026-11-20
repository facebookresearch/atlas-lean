/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheOddPhysicalExpansion

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexBethePerturbRoot {n : Nat} (p : Fin n → Real)
    (ell : Fin n) (eps : Real) : Fin n → Real :=
  fun j => if j = ell then eps else p j

@[simp] theorem sixVertexBethePerturbRoot_same {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (eps : Real) :
    sixVertexBethePerturbRoot p ell eps ell = eps := by
  simp [sixVertexBethePerturbRoot]

@[simp] theorem sixVertexBethePerturbRoot_ne {n : Nat}
    (p : Fin n → Real) (ell j : Fin n) (hj : j ≠ ell) (eps : Real) :
    sixVertexBethePerturbRoot p ell eps j = p j := by
  simp [sixVertexBethePerturbRoot, hj]

theorem sixVertexBethePerturbRoot_zero {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (hell : p ell = 0) :
    sixVertexBethePerturbRoot p ell 0 = p := by
  funext j
  by_cases hj : j = ell
  · subst j
    simp [hell]
  · simp [sixVertexBethePerturbRoot, hj]

theorem continuous_sixVertexBethePerturbRoot {n : Nat}
    (p : Fin n → Real) (ell : Fin n) :
    Continuous (sixVertexBethePerturbRoot p ell) := by
  apply continuous_pi
  intro j
  by_cases hj : j = ell
  · subst j
    simpa using continuous_id
  · simpa [sixVertexBethePerturbRoot, hj] using
      (continuous_const : Continuous (fun _ : Real => p j))




theorem continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) :
    Continuous (fun eps : Real =>
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps i)) x) := by
  unfold sixVertexBetheCollisionFreeIntervalSum
    sixVertexBetheIntervalTupleWeight
  apply continuous_finsetSum
  intro q hq
  apply continuous_finsetProd
  intro i hi
  apply Continuous.mul continuous_const
  let f : Real → Complex := fun eps => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps i)
  have hf : Continuous f := by
    unfold f sixVertexBethePhase
    exact Complex.continuous_exp.comp
      (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp
          (continuous_sixVertexBethePerturbRoot p ell))))
  exact hf.zpow₀ (q i) (fun eps => Or.inl (Complex.exp_ne_zero _))



theorem sixVertexBetheCollisionFreeIntervalSum_perturbRoot_tendsto
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : Fin (n + 1) → Int) :
    Tendsto (fun eps : Real =>
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps i)) x)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x)) := by
  let f : Real → Complex := fun eps =>
    sixVertexBetheCollisionFreeIntervalSum N c
      (fun i => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps i)) x
  have h : Tendsto f
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (f 0)) :=
    (continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
      N c p ell x).continuousAt.mono_left inf_le_left
  dsimp only [f] at h
  rw [sixVertexBethePerturbRoot_zero p ell hell] at h
  exact h

theorem sixVertexBethePerturbRoot_comp_perm {n : Nat}
    (p : Fin n → Real) (ell : Fin n) (eps : Real)
    (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    sixVertexBethePerturbRoot (fun j => p (sigma j)) (sigma.symm ell) eps i =
      sixVertexBethePerturbRoot p ell eps (sigma i) := by
  unfold sixVertexBethePerturbRoot
  by_cases hi : i = sigma.symm ell
  · subst i
    simp
  · have hsi : sigma i ≠ ell := by
      intro h
      exact hi (sigma.injective (h.trans (sigma.apply_symm_apply ell).symm))
    simp [hi, hsi]



theorem sixVertexBethePerturbRoot_eventually_phase_ne_one
    {n : Nat} (p : Fin n → Real) (ell : Fin n)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    ∀ᶠ eps in nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ,
      ∀ j, sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j) ≠ 1 := by
  have hinter : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ,
      eps ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  filter_upwards [hinter, hne] with eps heps hneps j
  by_cases hj : j = ell
  · subst j
    simp only [sixVertexBethePerturbRoot_same]
    exact sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero heps hneps
  · rw [sixVertexBethePerturbRoot_ne p ell j hj]
    exact hother j hj



def sixVertexBethePerturbedIntervalTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)),
    sixVertexBetheAmplitude c p sigma *
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps (sigma i))) x



def sixVertexBethePerturbedWordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)),
    sixVertexBetheAmplitude c p sigma *
      ∑ w : Finset (Fin (n + 1)),
        sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma x w

theorem continuous_sixVertexBethePerturbedIntervalTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) :
    Continuous (sixVertexBethePerturbedIntervalTotal N c p ell x) := by
  unfold sixVertexBethePerturbedIntervalTotal
  apply continuous_finsetSum
  intro sigma hsigma
  apply Continuous.mul continuous_const
  let q : Fin (n + 1) → Real := fun i => p (sigma i)
  let a : Fin (n + 1) := sigma.symm ell
  have h := continuous_sixVertexBetheCollisionFreeIntervalSum_perturbRoot
    N c q a x
  convert h using 1
  funext eps
  congr 2
  funext i
  rw [sixVertexBethePerturbRoot_comp_perm]



theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedIntervalTotal_tendsto_physicalAction
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : SixVertexSector N (n + 1)) :
    Tendsto (sixVertexBethePerturbedIntervalTotal N c p ell
        (sixVertexSectorIntCoordinates x))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x)) := by
  let F := sixVertexBethePerturbedIntervalTotal N c p ell
    (sixVertexSectorIntCoordinates x)
  have hcont : Tendsto F
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (F 0)) :=
    (continuous_sixVertexBethePerturbedIntervalTotal N c p ell
      (sixVertexSectorIntCoordinates x)).continuousAt.mono_left inf_le_left
  have hzero : F 0 =
      (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x := by
    dsimp only [F, sixVertexBethePerturbedIntervalTotal]
    simp_rw [sixVertexBethePerturbRoot_zero p ell hell]
    rw [hp.physicalZeroPhaseIntervalExpansion hc p ell hell x]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    congr 1
    rw [sixVertexBetheCollisionFreeIntervalSum_zeroPhase N c
      (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
      (sigma.symm ell)]
    · simp [hell]
    · exact sixVertexBetheShiftCoordinates_lt_sector x
  rwa [hzero] at hcont



theorem sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 1) → Int) (hgap : ∀ i,
      sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBethePerturbedIntervalTotal N c p ell x =ᶠ[nhdsWithin
      (0 : Real) (Set.singleton (0 : Real))ᶜ]
      sixVertexBethePerturbedWordTotal N c p ell x := by
  filter_upwards [sixVertexBethePerturbRoot_eventually_phase_ne_one
    p ell hother] with eps hphase
  unfold sixVertexBethePerturbedIntervalTotal
    sixVertexBethePerturbedWordTotal
  apply Finset.sum_congr rfl
  intro sigma hsigma
  congr 1
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  rw [sixVertexBetheCollisionFreeIntervalSum_eq_words N c
    (fun i => z (sigma i)) x hgap
    (fun i => Complex.exp_ne_zero _) (fun i => hphase (sigma i))]
  apply Finset.sum_congr rfl
  intro w hw
  have hcoeff :
      sixVertexBetheWordCoefficient c (fun i => z (sigma i))
          (Equiv.refl _) w =
        sixVertexBetheWordCoefficient c z sigma w := by
    unfold sixVertexBetheWordCoefficient
    apply Finset.prod_congr rfl
    intro i hi
    simp [sixVertexBetheWordEdgeFactor]
  have hmono :
      sixVertexBetheWordMonomial N (fun i => z (sigma i))
          (Equiv.refl _) x w =
        sixVertexBetheWordMonomial N z sigma x w := by
    unfold sixVertexBetheWordMonomial
    apply Finset.prod_congr rfl
    intro i hi
    simp
  rw [hcoeff, hmono]



theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_physicalAction
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : SixVertexSector N (n + 1)) :
    Tendsto (sixVertexBethePerturbedWordTotal N c p ell
        (sixVertexSectorIntCoordinates x))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x)) := by
  apply (hp.perturbedIntervalTotal_tendsto_physicalAction
    hc p ell hell x).congr'
  exact (sixVertexBethePerturbedIntervalTotal_eventuallyEq_wordTotal
    N c p ell hell hopen hother (sixVertexSectorIntCoordinates x)
    (sixVertexBetheShiftCoordinates_lt_sector x))

end

end StatMech.FrontierD
