/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingSHolo
import Code.BeffaraDC.PlanarFKDuality
import Code.BeffaraDC.SelfDualValue
import Code.FK.MonoBC

















open Finset Complex
open scoped BigOperators

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]




structure FKIsingDobrushinDomain where
  wiredArc : P.V -> Prop
  markedA : P.V
  markedB : P.V
  markedA_mem : wiredArc markedA
  markedB_mem : wiredArc markedB
  sourceEdge : M
  terminalEdge : M
  medialPosition : M -> Complex
  exploration : ConfigSpace (Sym2 P.V) -> List M
  source_mem : forall omega, sourceEdge ∈ exploration omega
  terminal_mem : forall omega, terminalEdge ∈ exploration omega
  winding : ConfigSpace (Sym2 P.V) -> M -> Real
  winding_terminal : forall omega, winding omega terminalEdge = 0

namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


def fkIsingCriticalParameter : Real := selfDualPoint 2

theorem fkIsingCriticalParameter_mem_Ioo :
    fkIsingCriticalParameter ∈ Set.Ioo (0 : Real) 1 :=
  selfDualPoint_mem_Ioo (by norm_num)



def wiring : SimpleGraph P.V :=
  boundaryCliqueGraph D.wiredArc

noncomputable instance wiringDecidableAdj : DecidableRel D.wiring.Adj :=
  Classical.decRel _



def criticalMass (omega : ConfigSpace (Sym2 P.V)) : Real :=
  bcProb P.G D.wiring fkIsingCriticalParameter 2 omega

theorem criticalMass_nonneg (omega : ConfigSpace (Sym2 P.V)) :
    0 <= D.criticalMass omega := by
  exact bcProb_nonneg P.G D.wiring fkIsingCriticalParameter_mem_Ioo.1
    fkIsingCriticalParameter_mem_Ioo.2 (by norm_num) omega

theorem criticalMass_sum_eq_one :
    ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega = 1 := by
  exact bcProb_sum_eq_one P.G D.wiring fkIsingCriticalParameter_mem_Ioo.1
    fkIsingCriticalParameter_mem_Ioo.2 (by norm_num)


def windingPhase (omega : ConfigSpace (Sym2 P.V)) (e : M) : Complex :=
  Complex.exp (Complex.I * ((D.winding omega e / 2 : Real) : Complex))

theorem norm_windingPhase (omega : ConfigSpace (Sym2 P.V)) (e : M) :
    ‖D.windingPhase omega e‖ = 1 := by
  rw [windingPhase, Complex.norm_exp]
  simp



def fermionicSummand (omega : ConfigSpace (Sym2 P.V)) (e : M) : Complex :=
  if e ∈ D.exploration omega then
    (D.criticalMass omega : Complex) * D.windingPhase omega e
  else 0



def fermionicObservable (e : M) : Complex :=
  ∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e


def explorationMass (e : M) : Real :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    if e ∈ D.exploration omega then D.criticalMass omega else 0

theorem explorationMass_nonneg (e : M) : 0 ≤ D.explorationMass e := by
  unfold explorationMass
  apply Finset.sum_nonneg
  intro omega homega
  split_ifs
  · exact D.criticalMass_nonneg omega
  · exact le_rfl

theorem explorationMass_le_one (e : M) : D.explorationMass e ≤ 1 := by
  calc
    D.explorationMass e ≤
        ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega := by
      unfold explorationMass
      apply Finset.sum_le_sum
      intro omega homega
      split_ifs
      · exact le_rfl
      · exact D.criticalMass_nonneg omega
    _ = 1 := D.criticalMass_sum_eq_one



theorem fermionicObservable_eq_explorationMass_mul_phase
    (e : M) (phase : Complex)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e = phase) :
    D.fermionicObservable e = (D.explorationMass e : Complex) * phase := by
  unfold fermionicObservable explorationMass
  calc
    (∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e) =
        ∑ omega : ConfigSpace (Sym2 P.V),
          (((if e ∈ D.exploration omega then D.criticalMass omega else 0) :
            Real) : Complex) * phase := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases he : e ∈ D.exploration omega
      · simp [fermionicSummand, he, hphase omega he]
      · simp [fermionicSummand, he]
    _ = ((∑ omega : ConfigSpace (Sym2 P.V),
          if e ∈ D.exploration omega then D.criticalMass omega else 0 :
            Real) : Complex) * phase := by
      rw [Complex.ofReal_sum, Finset.sum_mul]




theorem exists_nonnegative_boundary_square_of_phase
    (e : M) (normal phase : Complex) (r : Real)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e = phase)
    (hr : 0 ≤ r) (hline : normal * phase ^ 2 = (r : Complex)) :
    ∃ t : Real, 0 ≤ t ∧
      normal * D.fermionicObservable e ^ 2 = (t : Complex) := by
  let mass := D.explorationMass e
  refine ⟨mass ^ 2 * r, mul_nonneg (sq_nonneg mass) hr, ?_⟩
  rw [D.fermionicObservable_eq_explorationMass_mul_phase e phase hphase]
  calc
    normal * ((mass : Complex) * phase) ^ 2 =
        (mass : Complex) ^ 2 * (normal * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 * (r : Complex) := by rw [hline]
    _ = ((mass ^ 2 * r : Real) : Complex) := by push_cast; ring

theorem fermionicSummand_norm_le (omega : ConfigSpace (Sym2 P.V)) (e : M) :
    ‖D.fermionicSummand omega e‖ <= D.criticalMass omega := by
  unfold fermionicSummand
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (D.criticalMass_nonneg omega), D.norm_windingPhase, mul_one]
  · simpa using D.criticalMass_nonneg omega



theorem norm_fermionicObservable_le_one (e : M) :
    ‖D.fermionicObservable e‖ <= 1 := by
  unfold fermionicObservable
  calc
    ‖∑ omega : ConfigSpace (Sym2 P.V), D.fermionicSummand omega e‖ <=
        ∑ omega : ConfigSpace (Sym2 P.V), ‖D.fermionicSummand omega e‖ :=
      norm_sum_le _ _
    _ <= ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega := by
      exact Finset.sum_le_sum fun omega _ => D.fermionicSummand_norm_le omega e
    _ = 1 := D.criticalMass_sum_eq_one



theorem fermionicObservable_terminal :
    D.fermionicObservable D.terminalEdge = 1 := by
  unfold fermionicObservable fermionicSummand windingPhase
  simp_rw [if_pos (D.terminal_mem _), D.winding_terminal]
  simp only [zero_div, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_sum, D.criticalMass_sum_eq_one]
  norm_num



def normalizedFermionicObservable (delta : Real) (e : M) : Complex :=
  D.fermionicObservable e / (Real.sqrt (2 * delta) : Complex)




theorem norm_normalizedFermionicObservable_le
    (delta : Real) (hdelta : 0 < delta) (e : M) :
    ‖D.normalizedFermionicObservable delta e‖ <=
      1 / Real.sqrt (2 * delta) := by
  have hsqrt : 0 < Real.sqrt (2 * delta) := Real.sqrt_pos.2 (by positivity)
  unfold normalizedFermionicObservable
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right (D.norm_fermionicObservable_le_one e)
    hsqrt.le


theorem normalizedFermionicObservable_terminal (delta : Real) :
    D.normalizedFermionicObservable delta D.terminalEdge =
      1 / (Real.sqrt (2 * delta) : Complex) := by
  rw [normalizedFermionicObservable, D.fermionicObservable_terminal]





structure LocalSwitchingTable where
  edges : Fin 4 -> M
  toggle : ConfigSpace (Sym2 P.V) ≃ ConfigSpace (Sym2 P.V)
  pairedContribution : forall omega,
    ∃ X : Complex, forall k : Fin 4,
      D.fermionicSummand omega (edges k) +
          D.fermionicSummand (toggle omega) (edges k) =
        isingF k X

namespace LocalSwitchingTable

variable (T : D.LocalSwitchingTable)


def switchingAmplitude (omega : ConfigSpace (Sym2 P.V)) : Complex :=
  Classical.choose (T.pairedContribution omega)

theorem pairedContribution_switchingAmplitude
    (omega : ConfigSpace (Sym2 P.V)) (k : Fin 4) :
    D.fermionicSummand omega (T.edges k) +
        D.fermionicSummand (T.toggle omega) (T.edges k) =
      isingF k (switchingAmplitude D T omega) :=
  Classical.choose_spec (T.pairedContribution omega) k



def medialVertex : IsingMedialVertex where
  X := (∑ omega : ConfigSpace (Sym2 P.V), switchingAmplitude D T omega) / 2

private theorem sum_toggle (k : Fin 4) :
    (∑ omega : ConfigSpace (Sym2 P.V),
      D.fermionicSummand (T.toggle omega) (T.edges k)) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        D.fermionicSummand omega (T.edges k) := by
  exact Equiv.sum_comp T.toggle
    (fun omega => D.fermionicSummand omega (T.edges k))



theorem fermionicObservable_eq_medialVertex_edgeObs (k : Fin 4) :
    D.fermionicObservable (T.edges k) = (medialVertex D T).edgeObs k := by
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        (D.fermionicSummand omega (T.edges k) +
          D.fermionicSummand (T.toggle omega) (T.edges k))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        isingF k (switchingAmplitude D T omega) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact pairedContribution_switchingAmplitude D T omega k
  rw [Finset.sum_add_distrib, T.sum_toggle D k] at hsum
  have hlinear :
      (∑ omega : ConfigSpace (Sym2 P.V),
        isingF k (switchingAmplitude D T omega)) =
      isingF k (∑ omega : ConfigSpace (Sym2 P.V),
        switchingAmplitude D T omega) := by
    fin_cases k <;>
      simp [isingF, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  rw [hlinear] at hsum
  have hhalf (X : Complex) : isingF k (X / 2) = isingF k X / 2 := by
    fin_cases k <;> simp only [isingF] <;> ring
  unfold fermionicObservable medialVertex IsingMedialVertex.edgeObs
  rw [hhalf]
  linear_combination (1 / 2 : Complex) * hsum



def localFaceObservable (v d : Complex) : Complex -> Complex :=
  isingObservable (medialVertex D T) v d

theorem localFaceObservable_sideValues (v d : Complex)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2) :
    localFaceObservable D T v d
        ((isingFace v d 0 + isingFace v d 1) / 2) =
        D.fermionicObservable (T.edges 0) ∧
      localFaceObservable D T v d
        ((isingFace v d 1 + isingFace v d 2) / 2) =
        D.fermionicObservable (T.edges 3) ∧
      localFaceObservable D T v d
        ((isingFace v d 2 + isingFace v d 3) / 2) =
        D.fermionicObservable (T.edges 1) ∧
      localFaceObservable D T v d
        ((isingFace v d 3 + isingFace v d 0) / 2) =
        D.fermionicObservable (T.edges 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold localFaceObservable isingObservable
    rw [if_pos rfl, ← fermionicObservable_eq_medialVertex_edgeObs D T 0]
  · unfold localFaceObservable isingObservable
    rw [if_neg hpq.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 3]
  · unfold localFaceObservable isingObservable
    rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 1]
  · unfold localFaceObservable isingObservable
    rw [if_neg hps.symm, if_neg hqs.symm, if_neg hrs.symm, if_pos rfl,
      ← fermionicObservable_eq_medialVertex_edgeObs D T 2]



theorem localFaceObservable_contour_zero (v d : Complex)
    (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 1 + isingFace v d 2) / 2)
    (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 2 + isingFace v d 3) / 2)
    (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2)
    (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠
      (isingFace v d 3 + isingFace v d 0) / 2) :
    isingContour (localFaceObservable D T v d) (isingFace v d) = 0 := by
  exact ising_sholo_face_relation (medialVertex D T) v d
    hpq hpr hps hqr hqs hrs



theorem fermionicObservable_sHolo_relation :
    D.fermionicObservable (T.edges 0) + D.fermionicObservable (T.edges 1) =
      D.fermionicObservable (T.edges 2) + D.fermionicObservable (T.edges 3) := by
  have hpoint (omega : ConfigSpace (Sym2 P.V)) :
      (D.fermionicSummand omega (T.edges 0) +
          D.fermionicSummand (T.toggle omega) (T.edges 0)) +
        (D.fermionicSummand omega (T.edges 1) +
          D.fermionicSummand (T.toggle omega) (T.edges 1)) =
      (D.fermionicSummand omega (T.edges 2) +
          D.fermionicSummand (T.toggle omega) (T.edges 2)) +
        (D.fermionicSummand omega (T.edges 3) +
          D.fermionicSummand (T.toggle omega) (T.edges 3)) := by
    obtain ⟨X, hX⟩ := T.pairedContribution omega
    rw [hX 0, hX 1, hX 2, hX 3]
    exact isingF_sHolo_relation X
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) +
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 2) +
            D.fermionicSummand (T.toggle omega) (T.edges 2)) +
          (D.fermionicSummand omega (T.edges 3) +
            D.fermionicSummand (T.toggle omega) (T.edges 3))) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact hpoint omega
  simp only [Finset.sum_add_distrib] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum



theorem fermionicObservable_contourCombination_zero :
    D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) +
        Complex.I * D.fermionicObservable (T.edges 3) -
          Complex.I * D.fermionicObservable (T.edges 2) = 0 := by
  have hpoint (omega : ConfigSpace (Sym2 P.V)) :
      (D.fermionicSummand omega (T.edges 0) +
          D.fermionicSummand (T.toggle omega) (T.edges 0)) -
        (D.fermionicSummand omega (T.edges 1) +
          D.fermionicSummand (T.toggle omega) (T.edges 1)) +
        Complex.I * (D.fermionicSummand omega (T.edges 3) +
          D.fermionicSummand (T.toggle omega) (T.edges 3)) -
        Complex.I * (D.fermionicSummand omega (T.edges 2) +
          D.fermionicSummand (T.toggle omega) (T.edges 2)) = 0 := by
    obtain ⟨X, hX⟩ := T.pairedContribution omega
    rw [hX 0, hX 1, hX 2, hX 3]
    exact (IsingMedialVertex.mk X).contourCombination_zero
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) -
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)) +
          Complex.I * (D.fermionicSummand omega (T.edges 3) +
            D.fermionicSummand (T.toggle omega) (T.edges 3)) -
          Complex.I * (D.fermionicSummand omega (T.edges 2) +
            D.fermionicSummand (T.toggle omega) (T.edges 2)))) =
      ∑ _omega : ConfigSpace (Sym2 P.V), (0 : Complex) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact hpoint omega
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const_zero] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum

end LocalSwitchingTable

end FKIsingDobrushinDomain

end

end StatMech.Universality
