/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.MinusStateDLR
import Code.FrontierB.CurrentContinuityVaryingTemperature
import Code.FK.FKGeneralQTranslation

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

namespace StatMech.Ising

open ConfigSpace FK Lattice

variable {d : Nat}



theorem fvProb_zero_beta_boundary_independent
    (eta zeta : ConfigSpace (Site d)) (n : Nat)
    (B : Finset (Sym2 (Site d))) (h : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    fvProb eta n B 0 h tau = fvProb zeta n B 0 h tau := by
  simp [fvProb, fvWeight, fvZ]



theorem specApply_zero_beta_boundary_independent
    (eta zeta : ConfigSpace (Site d)) (n : Nat)
    (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) → Real)
    (hf : ∀ omega omega',
      (∀ x ∈ box d n, omega x = omega' x) → f omega = f omega') :
    specApply n B 0 h f eta = specApply n B 0 h f zeta := by
  rw [specApply_eq_sum, specApply_eq_sum]
  apply Finset.sum_congr rfl
  intro tau _
  rw [fvProb_zero_beta_boundary_independent eta zeta n B h tau]
  congr 1
  apply hf
  intro x hx
  rw [glue_mem eta tau hx, glue_mem zeta tau hx]



theorem multiOpen_indicator_eq_of_eqOn_box
    (T : Finset (Site d)) (n : Nat)
    (hT : (T : Set (Site d)) ⊆ box d n)
    (omega omega' : ConfigSpace (Site d))
    (heq : ∀ x ∈ box d n, omega x = omega' x) :
    (fmu_multiOpen T).indicator (fun _ => (1 : Real)) omega =
      (fmu_multiOpen T).indicator (fun _ => (1 : Real)) omega' := by
  have hmem : omega ∈ fmu_multiOpen T ↔ omega' ∈ fmu_multiOpen T := by
    simp only [fmu_multiOpen, Set.mem_setOf_eq]
    constructor
    · intro homega x hx
      rw [← heq x (hT hx)]
      exact homega x hx
    · intro homega x hx
      rw [heq x (hT hx)]
      exact homega x hx
  by_cases homega : omega ∈ fmu_multiOpen T
  · rw [Set.indicator_of_mem homega,
      Set.indicator_of_mem (hmem.mp homega)]
  · rw [Set.indicator_of_notMem homega,
      Set.indicator_of_notMem (fun h => homega (hmem.mpr h))]



theorem isDLRState_eq_of_zero_beta
    (h : Real) (mu nu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : IsDLRState d 0 h mu) (hnu : IsDLRState d 0 h nu) :
    mu = nu := by
  apply StatMech.FK.fkgqt_measure_eq_of_multiOpen_eq
  intro T
  obtain ⟨n, hT⟩ := Lattice.finite_subset_box
    (T : Set (Site d)) T.finite_toSet
  let A : Set (ConfigSpace (Site d)) := fmu_multiOpen T
  have hA : IsClopen A := ipe_multiOpen_isClopen T
  let f : ConfigSpace (Site d) →ᵇ Real :=
    BoundedContinuousFunction.indicator A hA
  have hlocal : ∀ eta zeta : ConfigSpace (Site d),
      specApply n (bondFinsetTouch d n) 0 h (f : ConfigSpace (Site d) → Real) eta =
        specApply n (bondFinsetTouch d n) 0 h
          (f : ConfigSpace (Site d) → Real) zeta := by
    intro eta zeta
    apply specApply_zero_beta_boundary_independent
    intro omega omega' heq
    exact multiOpen_indicator_eq_of_eqOn_box T n hT omega omega' heq
  let c := specApply n (bondFinsetTouch d n) 0 h
    (f : ConfigSpace (Site d) → Real) (minusField d)
  have hspec : ∀ eta : ConfigSpace (Site d),
      specApply n (bondFinsetTouch d n) 0 h
        (f : ConfigSpace (Site d) → Real) eta = c :=
    fun eta => hlocal eta (minusField d)
  have hrecMu := StatMech.FrontierB.specApply_integral_eq_of_isDLRState
    0 h mu hmu n f
  have hrecNu := StatMech.FrontierB.specApply_integral_eq_of_isDLRState
    0 h nu hnu n f
  have hleftMu : (∫ omega, (f : ConfigSpace (Site d) → Real) omega ∂mu) =
      mu.real A := by
    change (∫ omega, A.indicator (fun _ => (1 : Real)) omega ∂mu) = mu.real A
    exact integral_indicator_one (IsClopen.measurableSet_configSpace hA)
  have hleftNu : (∫ omega, (f : ConfigSpace (Site d) → Real) omega ∂nu) =
      nu.real A := by
    change (∫ omega, A.indicator (fun _ => (1 : Real)) omega ∂nu) = nu.real A
    exact integral_indicator_one (IsClopen.measurableSet_configSpace hA)
  have hconstMu :
      (∫ omega, specApply n (bondFinsetTouch d n) 0 h
        (f : ConfigSpace (Site d) → Real) omega ∂mu) = c := by
    simp_rw [hspec]
    simp
  have hconstNu :
      (∫ omega, specApply n (bondFinsetTouch d n) 0 h
        (f : ConfigSpace (Site d) → Real) omega ∂nu) = c := by
    simp_rw [hspec]
    simp
  have hreal : mu.real A = nu.real A := by
    rw [← hleftMu, ← hleftNu, ← hrecMu, ← hrecNu, hconstMu, hconstNu]
  unfold Measure.real at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top mu A) (measure_ne_top nu A)).mp hreal


theorem gibbs_unique_zero_beta
    (h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] (hmu : IsDLRState d 0 h mu) :
    mu = (minusState d 0 h : Measure (ConfigSpace (Site d))) :=
  isDLRState_eq_of_zero_beta h mu _ hmu
    (msdlr_minusState_isDLR_uncond 0 h)

end StatMech.Ising
