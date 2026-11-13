/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSectors
import Code.FrontierA.QuantumIsingArfSandwich
import Mathlib.Analysis.SpecificLimits.Basic








namespace StatMech.FrontierA

open StatMech.Ising



theorem inhomogeneousEvenSubgraphSum_pos_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> Real) (hweight : forall edge, 0 <= weight edge) :
    0 < inhomogeneousEvenSubgraphSum G weight := by
  classical
  have hempty : (∅ : Finset (Sym2 V)) ∈ evenSubgraphs G := by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, isEvenSubgraph_empty⟩
  have hnonneg (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) :
      0 <= ∏ edge ∈ F, weight edge := by
    exact Finset.prod_nonneg fun edge hedge => hweight edge
  have hsingle := Finset.single_le_sum hnonneg hempty
  simpa [inhomogeneousEvenSubgraphSum] using
    (show (0 : Real) < 1 from zero_lt_one).trans_le hsingle




theorem triangularTorusEvenSubgraphSum_log_sandwich
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall edge, 0 <= weight edge) :
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    Real.log (arfSectorNormMax sector) <=
        Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) /\
      Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) <=
        Real.log (arfSectorNormMax sector) + Real.log 2 := by
  dsimp only
  apply arfSector_log_sandwich
  · exact inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) weight hweight
  · intro a b
    exact triangularTorusWeightedSpin_norm_le_evenSubgraphSum
      L hweight a b
  · simpa using two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight



theorem triangularTorusEvenSubgraphSum_normalizedLog_gap_le
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall edge, 0 <= weight edge) :
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    let partition :=
      inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight
    0 <= (Real.log partition - Real.log (arfSectorNormMax sector)) /
        (L : Real) ^ 2 /\
      (Real.log partition - Real.log (arfSectorNormMax sector)) /
          (L : Real) ^ 2 <= Real.log 2 / (L : Real) ^ 2 := by
  dsimp only
  have hs := triangularTorusEvenSubgraphSum_log_sandwich L weight hweight
  have hL : 0 < (L : Real) := by
    have hLnat : 0 < L := lt_trans (by omega) (Fact.out : 2 < L)
    exact_mod_cast hLnat
  have hden : 0 < (L : Real) ^ 2 := sq_pos_of_pos hL
  constructor
  · exact div_nonneg (sub_nonneg.mpr hs.1) hden.le
  · exact div_le_div_of_nonneg_right (by linarith [hs.2]) hden.le

noncomputable def triangularTorusEvenSubgraphSequence
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (n : Nat) : Real := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
  exact inhomogeneousEvenSubgraphSum (triangularTorusGraph L) (weight L)

noncomputable def triangularTorusSectorSequence
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (n : Nat) (a b : Fin 2) : Complex := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
  exact triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight L edge : Complex)) a b



theorem triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall L edge, 0 <= weight L edge) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusEvenSubgraphSequence weight n) -
          Real.log (arfSectorNormMax
            (triangularTorusSectorSequence weight n))) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  have hbounds (n : Nat) :
      0 <=
          (Real.log (triangularTorusEvenSubgraphSequence weight n) -
            Real.log (arfSectorNormMax
              (triangularTorusSectorSequence weight n))) /
            (n + 3 : Real) ^ 2 /\
        (Real.log (triangularTorusEvenSubgraphSequence weight n) -
            Real.log (arfSectorNormMax
              (triangularTorusSectorSequence weight n))) /
            (n + 3 : Real) ^ 2 <= Real.log 2 / (n + 3 : Real) ^ 2 := by
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
    simpa [L, triangularTorusEvenSubgraphSequence,
      triangularTorusSectorSequence] using
        triangularTorusEvenSubgraphSum_normalizedLog_gap_le
          L (weight L) (hweight L)
  have hrecip : Filter.Tendsto
      (fun n : Nat => (1 : Real) / (n + 3 : Real))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Real)).comp
        (Filter.tendsto_add_atTop_nat 3)
  have hupper : Filter.Tendsto
      (fun n : Nat => Real.log 2 / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).mul
        (hrecip.mul hrecip)
    simpa [div_eq_mul_inv, pow_two] using h
  apply squeeze_zero'
    (f := fun n : Nat =>
      (Real.log (triangularTorusEvenSubgraphSequence weight n) -
        Real.log (arfSectorNormMax
          (triangularTorusSectorSequence weight n))) /
        (n + 3 : Real) ^ 2)
    (g := fun n : Nat => Real.log 2 / (n + 3 : Real) ^ 2)
  · exact Filter.Eventually.of_forall fun n => (hbounds n).1
  · exact Filter.Eventually.of_forall fun n => (hbounds n).2
  · exact hupper

end StatMech.FrontierA
