/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.KramersWannierClose
import Code.Ising.KramersWannierDuality
import Code.Ising.GKS
import Code.Walls.kwd_crosscountparity









open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def ons_lowTempPathSign (config : ConfigSpace V)
    {u v : V} (path : G.Walk u v) : Real :=
  if Even (kwd_crossCount (kwd_sideBoundary config) path) then 1 else -1


theorem ons_lowTempPathSign_eq_spin_mul (config : ConfigSpace V)
    {u v : V} (path : G.Walk u v) :
    ons_lowTempPathSign G config path = spin config u * spin config v := by
  unfold ons_lowTempPathSign
  have hpar := kwd_crossCount_parity config path
  by_cases hsame : config u = config v
  · rw [if_pos (hpar.mpr hsame)]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]
  · rw [if_neg (fun heven => hsame (hpar.mp heven))]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]



theorem isingWeight_eq_lowTempCutWeight (beta : Real)
    (config : ConfigSpace V) :
    isingWeight G beta 0 config =
      Real.exp (beta * G.edgeFinset.card) *
        Real.exp (-2 * beta) ^ (cutEdges G config).card := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [sum_bond_eq_card_sub_two_cut G config, ← Real.exp_nat_mul,
    ← Real.exp_add]
  congr 1
  ring


noncomputable def ons_lowTempPathNumerator (beta : Real)
    {u v : V} (path : G.Walk u v) : Real :=
  ∑ config : ConfigSpace V,
    ons_lowTempPathSign G config path *
      Real.exp (-2 * beta) ^ (cutEdges G config).card


noncomputable def ons_lowTempContourDenominator (beta : Real) : Real :=
  ∑ config : ConfigSpace V,
    Real.exp (-2 * beta) ^ (cutEdges G config).card




theorem isingExpectation_twoPoint_eq_lowTempPathRatio
    (beta : Real) {u v : V} (path : G.Walk u v) :
    isingExpectation G beta 0
        (fun config => spin config u * spin config v) =
      ons_lowTempPathNumerator G beta path /
        ons_lowTempContourDenominator G beta := by
  let prefactor := Real.exp (beta * G.edgeFinset.card)
  have hprefactor : prefactor ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ config : ConfigSpace V,
        isingWeight G beta 0 config *
          (spin config u * spin config v)) =
        prefactor * ons_lowTempPathNumerator G beta path := by
    unfold ons_lowTempPathNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro config _
    rw [isingWeight_eq_lowTempCutWeight,
      ← ons_lowTempPathSign_eq_spin_mul G config path]
    simp only [prefactor]
    ring
  have hden : isingZ G beta 0 =
      prefactor * ons_lowTempContourDenominator G beta := by
    rw [isingZ_low_temp_expansion]
    rfl
  unfold isingExpectation isingProb
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum, hden]
  field_simp [hprefactor]

end StatMech.Onsager
