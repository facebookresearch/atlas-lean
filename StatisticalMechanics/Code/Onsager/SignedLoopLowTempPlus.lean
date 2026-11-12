/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempCorrelation
import Code.Ising.FVConsistencyProve









open scoped BigOperators
open Finset SimpleGraph MeasureTheory

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


noncomputable def ons_fvCutEdges {V : Type*}
    (B : Finset (Sym2 V)) (config : ConfigSpace V) : Finset (Sym2 V) :=
  B.filter (fun edge => bond config edge = -1)



theorem sum_bond_finset_eq_card_sub_two_cut {V : Type*}
    (B : Finset (Sym2 V)) (config : ConfigSpace V) :
    (∑ edge ∈ B, bond config edge) =
      (B.card : Real) - 2 * (ons_fvCutEdges B config).card := by
  classical
  unfold ons_fvCutEdges
  rw [← Finset.sum_filter_add_sum_filter_not B
    (fun edge => bond config edge = -1)]
  have hneg :
      (∑ edge ∈ B.filter (fun edge => bond config edge = -1),
        bond config edge) =
        -(B.filter (fun edge => bond config edge = -1)).card := by
    rw [Finset.sum_congr rfl
      (fun edge hedge => (Finset.mem_filter.mp hedge).2)]
    simp
  have hpos :
      (∑ edge ∈ B.filter (fun edge => ¬ (bond config edge = -1)),
        bond config edge) =
        (B.filter (fun edge => ¬ (bond config edge = -1))).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : Real))]
    · simp
    intro edge hedge
    rcases bond_eq_one_or_neg_one config edge with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp hedge).2
  rw [hneg, hpos]
  have hcard :
      (B.filter (fun edge => bond config edge = -1)).card +
        (B.filter (fun edge => ¬ (bond config edge = -1))).card = B.card :=
    Finset.card_filter_add_card_filter_not _
  push_cast [← hcard]
  ring



theorem fvWeight_zero_eq_lowTempCutWeight
    (d n : Nat) (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (beta : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    fvWeight eta n B beta 0 tau =
      Real.exp (beta * B.card) *
        Real.exp (-2 * beta) ^ (ons_fvCutEdges B (glue eta tau)).card := by
  unfold fvWeight fvEnergy
  simp only [zero_mul, sub_zero]
  rw [sum_bond_finset_eq_card_sub_two_cut, ← Real.exp_nat_mul,
    ← Real.exp_add]
  congr 1
  ring



noncomputable def ons_plusLowTempPathSign {d : Nat}
    (config : ConfigSpace (Site d)) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) : Real :=
  if Even (kwd_crossCount (kwd_sideBoundary config) path) then 1 else -1


theorem ons_plusLowTempPathSign_eq_spin_mul {d : Nat}
    (config : ConfigSpace (Site d)) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    ons_plusLowTempPathSign config path = spin config u * spin config v := by
  unfold ons_plusLowTempPathSign
  have hpar := kwd_crossCount_parity config path
  by_cases hsame : config u = config v
  · rw [if_pos (hpar.mpr hsame)]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]
  · rw [if_neg (fun heven => hsame (hpar.mp heven))]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]


noncomputable def ons_plusLowTempPathNumerator
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) : Real :=
  ∑ tau : {x // x ∈ box d n} → Bool,
    ons_plusLowTempPathSign (glue (plusField d) tau) path *
      Real.exp (-2 * beta) ^
        (ons_fvCutEdges (bondFinsetTouch d n)
          (glue (plusField d) tau)).card


noncomputable def ons_plusLowTempContourDenominator
    (d n : Nat) (beta : Real) : Real :=
  ∑ tau : {x // x ∈ box d n} → Bool,
    Real.exp (-2 * beta) ^
      (ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau)).card


theorem integral_plusMeasure_twoPoint_eq_lowTempPathRatio
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    (∫ config, spin config u * spin config v
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
      ons_plusLowTempPathNumerator d n beta path /
        ons_plusLowTempContourDenominator d n beta := by
  let prefactor : Real := Real.exp (beta * (bondFinsetTouch d n).card)
  have hprefactor : prefactor ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ tau : {x // x ∈ box d n} → Bool,
        fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
          (spin (glue (plusField d) tau) u *
            spin (glue (plusField d) tau) v)) =
        prefactor * ons_plusLowTempPathNumerator d n beta path := by
    unfold ons_plusLowTempPathNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau _
    rw [fvWeight_zero_eq_lowTempCutWeight,
      ← ons_plusLowTempPathSign_eq_spin_mul (glue (plusField d) tau) path]
    simp only [prefactor]
    ring
  have hden :
      fvZ (plusField d) n (bondFinsetTouch d n) beta 0 =
        prefactor * ons_plusLowTempContourDenominator d n beta := by
    unfold fvZ ons_plusLowTempContourDenominator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau _
    rw [fvWeight_zero_eq_lowTempCutWeight]
  rw [plusMeasure_coe,
    integral_fvMeasure_eq_sum (plusField d) n
      (bondFinsetTouch d n) beta 0]
  unfold fvProb
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum, hden]
  field_simp [hprefactor]

end StatMech.Onsager
